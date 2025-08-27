---
title: "Compositional Datalog on SQL: Relational Algebra of the Environment"
date: 2025-08-26
---

I spent some time before making Datalogs that translated into SQL. <https://www.philipzucker.com/tiny-sqlite-datalog/>

There are advantages. SQL engines are very well engineered and commonly available. [SQLite](https://sqlite.org/) and [DuckDB](https://duckdb.org/) are a pretty great one-two punch.

A new twist on how to do this occurred to me that seems very clean compared to my previous methods.

Basically, the relational algebra style of SQL actually meshes with manipulating the Datalog body _environments_ (sets of named variables bindings) better then it meshes with the base Datalog relations themselves (`edge`, `path`, etc).

As a cheeky bonus as the end, you can do semi-naive by using the dual number <https://en.wikipedia.org/wiki/Dual_number> trick from forward mode automatic differentiation over these environment relations.

You can tinker on this post yourself on colab here <https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2025-08-26-compose_datalog.ipynb>

# The Environment As a Relation

The core bits of `SELECT-FROM-WHERE` SQL, select-project-join relational algebra expressions, and datalog bodies are all expressing roughly the same thing: [conjunctive queries](https://en.wikipedia.org/wiki/Conjunctive_query).

I rather like the syntax of a Datalog. It presents as both operational and logical.

It is also pretty close to a SQL query, but it takes a _jussst_ a little work because of incompatibilities

In SQL:

- columns names are properties of the tables like `myrow.name`
- rows can be locally named in `FROM mytable as myrow`

In Datalog:

- The columns are referred to positionally
- entries of rows are bound to variables `edge(1,X)`

If you write a Datalog interpreter, like most interpreters, you'll thread through a environment mapping variables names to values `type Env = dict[Var, Value]`. Datalog interpreters are branching in the sense that to bind a variable there are many choices (which row in the table to use). Roughly, an interpreter of a query has the signature `interp : expr -> database -> env -> set[env]`.

It is a basic trick that I vaguely associated with [finally tagless](https://okmij.org/ftp/tagless-final/index.html) that you can remove the middle man of the AST when you have an expression datatype and instead just use combinators which are basically partially applied versions of the interpreter to the expressions `interp myexp : database -> env -> set[env]`.

You don't actually have to thread that `env` through though.

Really the semantics of a base expressions like `path(X,Y) : db -> set[env]` are a function from the database to a set of environments. You can combine them by performing inner joins on these primitive pieces, joining by variable names in the environments. SQL rocks at inner joins.

As a toy model of these ideas, this is a naive combinator based implementation in Python.

Here I make a combinator `reldecl` that pulls a named table out of the database and filters on the args. This step converts from a base relation to an environment.

```python
from typing import Callable
type Var = str
type Env = dict[Var, object]
type DB = dict[str, set[tuple(object,...)]]
type Query = Callable[[DB], list[Env]]
from dataclasses import dataclass

@dataclass(frozen=True)
class Var():
    name : str

def reldecl(name: str) -> Callable[..., Query]:
    def rel(*args) -> Query:
        def res(db: DB) -> list[Env]:
            R = db[name]
            envs = []
            for row in R:
                env = {}
                for arg, val in zip(args, row):
                    if isinstance(arg, Var):
                        if arg in env and env[arg] != val:
                            break
                        env[arg] = val
                    else:
                        if arg != val:
                            break
                else:
                    envs.append(env)
            return envs
        return res
    return rel


```

Some usage examples. We make a database and get all the `edge` entries through a query

```python
db = {"edge" : {(1,2), (2,3), (3,4), (2,1), (3,3)}, 
      "color" : {("red",), ("blue",), ("green",)}}
edge = reldecl("edge")
color = reldecl("color")
x,y,z = Var("x"), Var("y"), Var("z")
edge(x,y)(db)
```

    [{Var(name='x'): 2, Var(name='y'): 3},
     {Var(name='x'): 1, Var(name='y'): 2},
     {Var(name='x'): 3, Var(name='y'): 3},
     {Var(name='x'): 2, Var(name='y'): 1},
     {Var(name='x'): 3, Var(name='y'): 4}]

All color query

```python
color(x)(db)
```

    [{Var(name='x'): 'blue'}, {Var(name='x'): 'red'}, {Var(name='x'): 'green'}]

Is `"red"` in the color table?

```python
color("red")(db) # succeeds
```

    [{}]

Is `"black"` in the color table?

```python
color("black")(db) # fails
```

    []

All self edges

```python
edge(x, x)(db)
```

    [{Var(name='x'): 3}]

Now we want to be able to conjoin subqueries. You can conjoin them by performing inner joins on these primitive pieces, joining by variable names in the environments. SQL rocks at inner joins, which is what we'll get to next. Here, this is done in the most naive why via a nested loop join <https://en.wikipedia.org/wiki/Nested_loop_join>

```python
def conj(*queries: Query) -> Query:
    def res(db : DB) -> list[Env]:
        envs = [{}]
        for query in queries:
            R = query(db)
            newenvs = []        
            for env1 in R:
                for env2 in envs:
                    if all(env1[k] == env2[k] for k in set(env1.keys()) & set(env2.keys())):
                        newenvs.append(env1 | env2)
            envs = newenvs
        return envs
    return res

conj(edge(x, y), edge(y, x))(db)
```

    [{Var(name='y'): 1, Var(name='x'): 2},
     {Var(name='y'): 3, Var(name='x'): 3},
     {Var(name='y'): 2, Var(name='x'): 1}]

Heads of rules are a semantically distinct thing from the relation expressions that appear in the body of the expression. The head actually mutates the database given an environment. The environment in particular ought to be derived from a query giving a semantic signature  `type Action = Query -> DB -> DB`. You could of course also just mutate the db rather than return a new version purely functionally.

```python
type Action = Callable[[DB, Query], DB]

def headdecl(name : str):
    def rel(*args) -> Action:
        def res(query : Query, db : DB) -> DB:
            envs = query(db)
            Rold = db.get(name, set())
            Rnew = {tuple(env[arg] if isinstance(arg,Var) else arg for arg in args) for env in envs}
            return {**db, **{name : Rnew | Rold}}
        return res
    return rel

edgeh = headdecl("edge")
# edge(x,y) :- edge(y,x), edge(x,x)
edgeh(x, y)(conj(edge(y, x), edge(x,x)), db)

```

    {'edge': {(1, 2), (2, 1), (2, 3), (3, 2), (3, 3), (3, 4)},
     'color': {('blue',), ('green',), ('red',)}}

# SQLizing

We can push this thing around in sort of a staged metaprogramming style <https://okmij.org/ftp/ML/MetaOCaml.html> to instead produce `code (db -> set[env])`, the code in particular being strings of SQL.

In the following, the simplicity of what is happening is largely being obscured by the nastiness of constructing SQL strings but it is basically the same as the above. I typically construct my `froms`, `wheres`, and `selects` in python lists and then join them together into fstrings.

I chose to wrap things in classes in order to get nice operator overloading `path(x,z) <= edge(x,y) & path(y,z)`. It was too cute to not do. This does bulk out the implementation compared to the combinator style I did above.

`EnvRel` is spiritually a `code (db -> set env)`

```python
from dataclasses import dataclass

type SQL = str

@dataclass(frozen=True)
class Var():
    name : str

@dataclass
class EnvRel():
    """
    A relation representing the datalog environment. It has named columns representing
    the datalog variables currently bound.
    For example
    path("x", "y") :- edge("x", "y") has 
    """
    cols : set[Var] # reverse these two.
    code : str
    def __and__(self, other: "EnvRel") -> "EnvRel":
        # Does an inner join. The analog of `conj` from before.
        cols = self.cols | other.cols
        on_clause = " AND ".join(f"t1.{c.name} = t2.{c.name}" for c in (self.cols & other.cols))
        if on_clause != "":
            on_clause = "WHERE " + on_clause
        selects = [f"t1.{c.name} AS {c.name}" for c in self.cols] + [f"t2.{c.name} AS {c.name}" for c in other.cols if c not in self.cols]
        code = f"SELECT {", ".join(selects)}\nFROM ({self.code}) AS t1,\n({other.code}) AS t2\n{on_clause}"
        return EnvRel(cols, code)
    def __or__(self, other : "EnvRel") -> "EnvRel":
        assert self.cols == other.cols, "Can only union relations with same columns"
        return EnvRel(self.cols, f"SELECT {", ".join([c.name for c in self.cols])}\n FROM ({self.code}\nUNION {other.code})")


x,y,z,w = Var("x"), Var("y"), Var("z"), Var("w")
```

Like before, a lot of the action actually happens in converting from the actual applied base relation decl to an environment containing the results of the query.

A nice syntactic trick is to use `myrel(x)` for actions and `myrel[x]` for queries. I believe I first saw this in SLOG <https://arxiv.org/abs/2411.14330> <https://arxiv.org/abs/2211.11573> or maybe Relational AI's thing?

```python
from dataclasses import dataclass

@dataclass
class RelDecl:
    """
    RelDecl is the unapplied function symbol like edge/2 or path/2
    """
    name : str
    arity : int
    def create(self) -> SQL:
        """
        SQL command to create corresponding table with primary key on all columns x0,x1,x2, ... .
        """
        cols = [f"x{i}" for i in range(self.arity)]
        return f"CREATE TABLE IF NOT EXISTS {self.name} ({', '.join(cols)}, PRIMARY KEY ({', '.join(cols)}))"
    def __call__(self, *args) -> "Head":
        """
        rel(...) notation is used in the head. They represent facts to be inserted into the database
        """
        return Head(self, args)
    def __getitem__(self, args) -> "EnvRel":
        """
        rel[...] notation is used in the body. They represent queries on the database.

        This is where the action happens converting the base names into the environment
        """
        # min_arg is a kind of determinstic union find. Pick minimum index as canonical
        min_arg = {a : min(j for j,b in enumerate(args) if a == b) for a in args if isinstance(a, Var)}
        wheres = [f"x{i} = x{min_arg[a]}" for (i, a) in enumerate(args) if isinstance(a, Var) and min_arg[a] != i]
        # constant projections
        wheres +=  [f"x{n} = {str(arg)}" for n,arg in enumerate(args) if not isinstance(arg, Var)]
        if wheres:
            wheres = "WHERE " + " AND ".join(wheres)
        else:
            wheres = ""
        cols = set(a for a in args if isinstance(a, Var))
        if not min_arg:
            selects = "NULL"
        else:
            selects = ", ".join(f"x{j} AS {a.name}" for a,j in min_arg.items())
            #selects = ", ".join(f"x{n} as {arg}" for n,arg in enumerate(args) if isinstance(arg, str))
        return EnvRel(cols, f"SELECT {selects}\nFROM {self.name}\n{wheres}")
```

It is easiest to see how this really works by looking at particular examples of the output SQL.

```python
edge = RelDecl("edge", 2)
path = RelDecl("path", 2)

print(edge[x,y].code)

```

    SELECT x0 AS x, x1 AS y
    FROM edge
    

Here is a constant query

```python
print(edge[2,1].code)
```

    SELECT NULL
    FROM edge
    WHERE x0 = 2 AND x1 = 1

A slightly projective query

```python
print(edge[x,1].code)
```

    SELECT x0 AS x
    FROM edge
    WHERE x1 = 1

Actually running it.

```python
import sqlite3

db = sqlite3.connect(":memory:")
db.execute(edge.create())
db.execute(path.create())
db.execute("INSERT INTO edge (x0, x1) VALUES (1,2), (2,3), (3,4), (4,5), (5,5)")
db.execute(edge[x,y].code).fetchall()
```

    [(1, 2), (2, 3), (3, 4), (4, 5), (5, 5)]

```python
db.execute(edge[x,x].code).fetchall()
```

    [(5,)]

```python
db.execute((edge[x,y] & edge[y,z]).code).fetchall()
```

    [(2, 1, 3), (3, 2, 4), (4, 3, 5), (5, 4, 5), (5, 5, 5)]

```python
db.execute(edge[x,3].code).fetchall()
```

    [(2,)]

I made an auxiliary class for applied `RelDecl` so that I can have nice `<=` notation. `<=` is lower precedence than `&`, which is the precedence I want for datalog rules.

```python
@dataclass
class Head:
    """
    This is the applied function symbol to arguments e.g. rel(1,2,3). Mainly I did this to get <= for the heads of rules.
    """
    r : RelDecl
    args : list[object]
    def fact(self):
        assert all(not isinstance(a, Var) for a in self.args)
        return f"INSERT OR IGNORE INTO {self.r.name}\nVALUES ({', '.join(str(a) for a in self.args)})"
    def __le__(self, body : EnvRel) -> SQL:
        selects = [a.name if isinstance(a, Var) else str(a) for a in self.args]
        return f"INSERT OR IGNORE INTO {self.r.name}\nSELECT {",".join(selects)}\nFROM ({body.code})"

```

Here is SQL resulting from the transitive closure query

```python
print(path(x,y) <= edge[x,y])
```

    INSERT OR IGNORE INTO path
    SELECT x,y
    FROM (SELECT x0 AS x, x1 AS y
    FROM edge
    )

```python
db.execute(path(x,y) <= edge[x,y])
db.execute(path[x,y].code).fetchall()
```

    [(1, 2), (2, 3), (3, 4), (4, 5), (5, 5)]

```python
print(path(x,z) <= edge[x,y] & path[y,z])
```

    INSERT OR IGNORE INTO path
    SELECT x,z
    FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM path
    ) AS t2
    WHERE t1.y = t2.y)

```python
db.execute(path(x,z) <= edge[x,y] & path[y,z])
db.execute(path[x,y].code).fetchall()
```

    [(1, 2), (2, 3), (3, 4), (4, 5), (5, 5), (1, 3), (2, 4), (3, 5)]

# Fixpoints

Ok, but one of the points of datalog is that it has fixpoints. It runs the mutually dependent rules until they produce nothing new. These are nice for doing things like the transitive closure of a relation or performing program analyses.

```python
def naive_fix(db, rels, stmts, limit=4):
    for rel in rels:
        db.execute(rel.create())
    for stmt in stmts:
        if isinstance(stmt, Head):
            db.execute(stmt.fact())
    n = 0
    while True:
        n += 1
        for stmt in stmts:
            if isinstance(stmt, str):
                db.execute(stmt)
        if n > limit:
            return
db.execute("DELETE FROM edge")
db.execute("DELETE FROM path")
path = RelDecl("path", 2)
naive_fix(db, [edge, path], [
    edge(1,2),
    edge(2,3),
    path(x,y) <= edge[x,y],
    path(x,z) <= edge[x,y] & path[y,z]
])
db.execute(path[x,y].code).fetchall()
```

    [(1, 2), (2, 3), (1, 3)]

```python
print(path(x,z) <= edge[x,y] & path[y,z])
```

    INSERT OR IGNORE INTO path
    SELECT x,z
    FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM path
    ) AS t2
    WHERE t1.y = t2.y)

```python
edge(x,y) <= edge[x,y]
db.execute(edge(4,5).fact())
db.execute(edge(y,x) <= edge[x,y])
db.execute(edge[x,y].code).fetchall()
```

    [(1, 2), (2, 3), (4, 5), (2, 1), (3, 2), (5, 4)]

# SemiNaive via Dual Relations

Seminaive evaluation works by observation that any new fact must come from a query involving at least one new fact from the previous iteration.

We can carry through both the primary and the delta relation in a single bundle. This is the analog of automatic differentiation. Pretty neat huh!

<https://stackoverflow.com/questions/47043937/what-is-the-difference-between-naive-and-semi-naive-evaluation>

```python
@dataclass
class DualEnv():
    env : Env
    denv : Env

    def __and__(self, other):
        env = self.env & other.env
        denv = self.denv & other.env | self.env & other.denv
        return DualEnv(env, denv)

@dataclass
class DualDecl():
    r : RelDecl
    dr : RelDecl
    newr : RelDecl
    def __init__(self, name, arity):
        self.r = RelDecl(name, arity)
        self.dr = RelDecl("delta_" + name, arity)
        self. newr = RelDecl("new_" + name, arity)
    def __call__(self, *args) -> "DualHead":
        return DualHead(self.newr, args)
    def __getitem__(self, args) -> "DualEnv":
        return DualEnv(self.r[args], self.dr[args])

@dataclass
class DualHead(Head):
    def __le__(self, body : DualEnv) -> SQL:
        return super().__le__(body.denv)

edge = DualDecl("edge", 2)
path = DualDecl("path", 2)

print((edge[x,y] & path[y,z]).denv.code)

```

    SELECT y, z, x
     FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM delta_edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM path
    ) AS t2
    WHERE t1.y = t2.y
    UNION SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM delta_path
    ) AS t2
    WHERE t1.y = t2.y)

```python
db.execute(edge.r.create())
db.execute(edge.dr.create())
db.execute(path.r.create())
db.execute(path.dr.create())
db.execute(edge.dr(1,2).fact())
db.execute((edge[x,y] & path[y,z]).denv.code).fetchall()
```

    [(2, 3, 1)]

```python
print((edge[1,x] & path[x,3]).denv.code)
```

    SELECT x
     FROM (SELECT t1.x AS x
    FROM (SELECT x1 AS x
    FROM delta_edge
    WHERE x0 = 1) AS t1,
    (SELECT x0 AS x
    FROM path
    WHERE x1 = 3) AS t2
    WHERE t1.x = t2.x
    UNION SELECT t1.x AS x
    FROM (SELECT x1 AS x
    FROM edge
    WHERE x0 = 1) AS t1,
    (SELECT x0 AS x
    FROM delta_path
    WHERE x1 = 3) AS t2
    WHERE t1.x = t2.x)

### Seminaive Fixpoint

The naive fixpoint can also be generalized

```python
def fix(db, rels : list[DualDecl], stmts, limit=None):
    for rel in rels:
        db.execute(rel.r.create())
        db.execute(rel.dr.create())
        db.execute(rel.newr.create())
        db.execute(f"DELETE FROM {rel.r.name}")
        db.execute(f"DELETE FROM {rel.dr.name}")
        db.execute(f"DELETE FROM {rel.newr.name}")
    # Do facts
    facts = [stmt for stmt in stmts if isinstance(stmt, Head)]
    rules = [stmt for stmt in stmts if isinstance(stmt, str)]
    for stmt in facts:
        db.execute(stmt.fact())
    n = 0
    while True:
        n += 1
        for stmt in rules:
            db.execute(stmt)
        for rel in rels:
            # Do the old swaparooni. Delete delta, delta := new - old, old += delta, new := {}
            db.execute(f"DELETE FROM {rel.dr.name}")
            wheres = " AND ".join([f"t1.x{i} = t2.x{i}" for i in range(rel.r.arity)])
            if wheres != "":
                wheres = "WHERE " + wheres
            db.execute(f"INSERT OR IGNORE INTO {rel.dr.name} SELECT * FROM {rel.newr.name} as t1 WHERE NOT EXISTS (SELECT 1 FROM {rel.r.name} as t2 {wheres})")
            db.execute(f"INSERT OR IGNORE INTO {rel.r.name} SELECT * FROM {rel.dr.name}")
            db.execute(f"DELETE FROM {rel.newr.name}")
            #print(n, rel.dr.name, db.execute("SELECT * FROM " + rel.dr.name).fetchall())
        if (limit is not None and n > limit) or all(db.execute(f"SELECT * FROM {rel.dr.name} LIMIT 1").fetchone() is None for rel in rels):
            return

fix(db, [edge, path], [
    edge(1,2),
    edge(2,3),
    edge(3,4),
    path(x,y) <= edge[x,y],
    path(x,z) <= edge[x,y] & path[y,z]
], limit=10)
db.execute(path[x,y].env.code).fetchall()
```

    [(1, 2), (2, 3), (3, 4), (1, 3), (2, 4), (1, 4)]

## Unscientific Benchmarking

Ok, with the caveat that this is a single artificial benchmark

```
.decl edge(x: number, y: number)
.decl path(x: number, y: number)
//.input edge
.output path

edge(n, n+1) :- n = range(0, 1000).
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).
```

`souffle /tmp/test.dl` Takes ~0.2s in interpreted mode, ~0.1s in compiled mode. `-j` parallelization doesn't seem to help much (too small?)

```python
import time
import sqlite3 
db = sqlite3.connect(":memory:")
t = time.time()
fix(db, [edge, path],
[edge(n, n+1) for n in range(1, 1000)] + \
[path(x,y) <= edge[x,y],
path(x,z) <= edge[x,y] & path[y,z]
])
time.time() - t
```

This takes about 0.7s

A seminaive python loop takes about 20s

```python
edge1 = {(n,n+1) for n in range(1, 1000)}
path1 = edge1.copy()
dpath = edge1.copy()
newpath = set()
for i in range(1010):
    for (x,y) in edge1:
        for (y2,z) in dpath:
            if y == y2:
                newpath.add((x,z))
    dpath = newpath - path1
    path1 |= newpath
    newpath = set()
    if not dpath:
        break
```

Seminaive duckdb takes about 6s. Maybe this is because duckdb is not tuned for set semantics? Somewhat surprising since duckdb has the higher performance reputation.

The non seminaive loop is much slower.

I'm satisfied by this. I never expected to beat souffle. I think this is a much simpler, more flexible system at maybe 3-5x overhead on this particular benchmark.

Strangely, the swaparooni is the bottleneck.

An original version of this used `EXCEPT` for the delta differencing rather than `EXISTS NOT` which was radically slower (17s).

# Bits and Bobbles

A small z3 ast to sqlite compiler is here <https://github.com/philzook58/knuckledragger/blob/main/kdrag/solvers/datalog.py> .

- <https://en.wikipedia.org/wiki/Relational_algebra>
- <https://cs186berkeley.net/notes/note6/>

- datatoad <https://github.com/frankmcsherry/blog/blob/master/posts/2025-06-03.md>

- logica <https://github.com/EvgSkv/logica>

- <https://bernsteinbear.com/blog/liveness-datalog/>
- <https://blog.waleedkhan.name/lithe-less-analysis-with-datalog/>

- <https://www.philipzucker.com/notes/Languages/datalog/>
- <https://inst.eecs.berkeley.edu/~cs294-260/sp24/2024-02-05-datalog>

Actually, the thing that I thought was fun was generalizing all of these to Dual relatiosn akin to dual numbers  <https://en.wikipedia.org/wiki/Dual_number> to achieve seminaive

I should also maybe switch to a form using CTEs rather than inlined nested select statements. That would make less repetition.

CHR and graph rewriting on SQL would also be interesting

A thought occurred to me as I was revisiting some of this stuff, considering about submitting to the minikanren workshop (which I did not).

What I did before was a somewhat light pass over an AST to determine which vars to ground at compile them.

I can probably throw garbage into SQL engines and get something ok out (?).

Datalog conjunctive queries have a different flavor than SQL style conjunctive queries. Seemingly, in datalog you give names to slots of the relations `mytable(Myvar)`, whereas in SQL style you give alpha invariant names to entire rows `SELECT myrow.col0 FROM mytable as myrow`.

SQL and relational algebra tables have named columns

But a twist that I don't know how to think about exactly is that the variable names in the environment can be column names.

SQL makes it easy to state relational algebra operations <https://en.wikipedia.org/wiki/Relational_algebra> like projection, selection, and renaming.

There might be a fun version of this post that works off of a relational algebra interface

```python
from typing import Protocol
class RelAlg(Protocol):
    cols: list[str]  # column names
    def rename(self, src: str, dst: str) -> 'RelAlg': ...  # subst : list[tuple[str, str]]
    def proj(self, cols: list[str]) -> 'RelAlg': ...
    def join(self, other: 'RelAlg') -> 'RelAlg': ...
    def union(self, other: 'RelAlg') -> 'RelAlg': ...
    def intersect(self, other: 'RelAlg') -> 'RelAlg': ...
    def diff(self, other: 'RelAlg') -> 'RelAlg': ...
    def select(self, cond: str) -> 'RelAlg': ... # not str
```

```python
class DualEnv():
    env : Env
    denv : Env

    def __and__(self, other):
        env = self.env & other.env
        denv = self.denv & other.env | self.env & other.denv
        return DualEnv(env, denv)




```

```python
import sqlite3
db = sqlite3.connect(":memory:")
db.execute(RelDecl("edge", 2).create())
```

    <sqlite3.Cursor at 0x7b82445140c0>

```python

edge = BaseRel({"x0","y0"}, "edge")
path = BaseRel({"x0","y0"}, "path")
db.execute(edge["y", "x"].code).fetchall()
db.execute(edge("y", "x", body=edge["x", "y"]))
db.execute("SELECT * FROM edge").fetchall()
#db.execute(path("x", "z", body=edge["x", "y"] & path["y", "z"]))
edge["x", "y"] & path["y", "z"]



```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[33], line 1
    ----> 1 edge = BaseRel({"x0","y0"}, "edge")
          2 path = BaseRel({"x0","y0"}, "path")
          3 db.execute(edge["y", "x"].code).fetchall()


    NameError: name 'BaseRel' is not defined

```python
path(x,y) <= edge[x,y]
path(x,z) <= edge[x,y] & path[y,z]

```

    'INSERT OR IGNORE INTO new_path\nSELECT x,z\nFROM (SELECT y, z, x\n FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z\nFROM (SELECT x0 AS x, x1 AS y\nFROM delta_edge\n) AS t1,\n(SELECT x0 AS y, x1 AS z\nFROM path\n) AS t2\nWHERE t1.y = t2.y\nUNION SELECT t1.y AS y, t1.x AS x, t2.z AS z\nFROM (SELECT x0 AS x, x1 AS y\nFROM edge\n) AS t1,\n(SELECT x0 AS y, x1 AS z\nFROM delta_path\n) AS t2\nWHERE t1.y = t2.y))'

## Benchmarking

This is pretty bad.
Maybe sqlite is actually better than duckdb for this use case (set semantics?)
Parse overhead is too high?

Getting some scaling charts would be nice.

But this python loop is only
20/0.18 ~ 100x slowdown

40x slowdown with respect to soufflein duckdb. Is that bad?

```python
def fix(db, rels : list[DualDecl], stmts, limit=None):
    for rel in rels:
        db.execute(rel.r.create())
        db.execute(rel.dr.create())
        db.execute(rel.newr.create())
        db.execute(f"DELETE FROM {rel.r.name}")
        db.execute(f"DELETE FROM {rel.dr.name}")
        db.execute(f"DELETE FROM {rel.newr.name}")
    # Do facts
    facts = [stmt for stmt in stmts if isinstance(stmt, Head)]
    rules = [stmt for stmt in stmts if isinstance(stmt, str)]
    for stmt in facts:
        db.execute(stmt.fact())
    n = 0
    while True:
        n += 1
        t = time.time()
        for stmt in rules:
            db.execute(stmt)
        print("rule time", time.time() - t)
        t= time.time()
        for rel in rels:
            # Do the old swaparooni. Delete delta, delta := new - old, old += delta, new := {}
            t1 = time.time()
            db.execute(f"DELETE FROM {rel.dr.name}")
            t2 = time.time()
            wheres = " AND ".join([f"t1.x{i} = t2.x{i}" for i in range(rel.r.arity)])
            db.execute(f"INSERT OR IGNORE INTO {rel.dr.name} SELECT * FROM {rel.newr.name} as t1 WHERE NOT EXISTS (SELECT 1 FROM {rel.r.name} as t2 WHERE {wheres})")
            #db.execute(f"INSERT OR IGNORE INTO {rel.dr.name} SELECT * FROM {rel.newr.name}")
            t3 = time.time()
            db.execute(f"INSERT OR IGNORE INTO {rel.r.name} SELECT * FROM {rel.dr.name}")
            t4 = time.time()
            db.execute(f"DELETE FROM {rel.newr.name}")
            t5 = time.time()
            #print(n, rel.dr.name, db.execute("SELECT COUNT(*) FROM " + rel.dr.name).fetchall())
            #print("  delete time", t2 - t1, "insert delta time", t3 - t2, "insert old time", t4 - t3, " delete new time", t5 - t4)
        print("delta time", time.time() - t)
        if (limit is not None and n > limit) or all(db.execute(f"SELECT 1 FROM {rel.dr.name} LIMIT 1").fetchone() is None for rel in rels):
            return

fix(db, [edge, path], [
    edge(1,2),
    edge(2,3),
    edge(3,4),
    path(x,y) <= edge[x,y],
    path(x,z) <= edge[x,y] & path[y,z]
], limit=10)
db.execute(path[x,y].env.code).fetchall()
```

    rule time 2.6702880859375e-05
    delta time 0.00026798248291015625
    rule time 8.106231689453125e-06
    delta time 1.4543533325195312e-05
    rule time 6.4373016357421875e-06
    delta time 2.384185791015625e-05
    rule time 4.0531158447265625e-06
    delta time 9.775161743164062e-06
    rule time 3.5762786865234375e-06
    delta time 7.867813110351562e-06





    [(1, 2), (2, 3), (3, 4), (1, 3), (2, 4), (1, 4)]

```python
import time
import sqlite3 
db = sqlite3.connect(":memory:")
t = time.time()
fix(db, [edge, path],
[edge(n, n+1) for n in range(1, 1000)] + [path(x,y) <= edge[x,y],
path(x,z) <= edge[x,y] & path[y,z]
]
)

time.time() - t
```

```python
%%file /tmp/test.dl

.decl edge(x: number, y: number)
.decl path(x: number, y: number)
//.input edge
.output path

edge(n, n+1) :- n = range(0, 1000).
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).

```

    Overwriting /tmp/test.dl

```python
! time souffle /tmp/test.dl
```

    real 0m0.667s
    user 0m8.948s
    sys 0m0.023s

```python
! souffle -o /tmp/test /tmp/test.dl && time /tmp/test -j4
```

    real 0m0.125s
    user 0m0.119s
    sys 0m0.006s

```python
db.execute("CREATE TABLE t1 (id INTEGER, j VARCHAR, PRIMARY KEY (id, j));")
```

    <duckdb.duckdb.DuckDBPyConnection at 0x73d0852b5270>

```python

print(path(x,z) <= edge[x,y] & path[y,z])
```

    INSERT OR IGNORE INTO new_path
    SELECT x,z
    FROM (SELECT y, z, x
     FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM delta_edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM path
    ) AS t2
    WHERE t1.y = t2.y
    UNION SELECT t1.y AS y, t1.x AS x, t2.z AS z
    FROM (SELECT x0 AS x, x1 AS y
    FROM edge
    ) AS t1,
    (SELECT x0 AS y, x1 AS z
    FROM delta_path
    ) AS t2
    WHERE t1.y = t2.y))

```python
def fix(db, rels : list[DualDecl], stmts, limit=None):
    for rel in rels:
        db.execute(f"DELETE FROM {rel.r.name}")
        db.execute(f"DELETE FROM {rel.dr.name}")
        db.execute(f"DELETE FROM {rel.newr.name}")
    # Do facts
    facts = [stmt for stmt in stmts if isinstance(stmt, Head)]
    rules = [stmt for stmt in stmts if isinstance(stmt, str)]
    for stmt in facts:
        db.execute(stmt.fact())
    n = 0
    #bigstmt = rules
    #for rel in rels:
    #    bigstmt.append(f"DELETE FROM {rel.dr.name}")
    #    bigstmt.append(f"INSERT INTO {rel.dr.name} SELECT DISTINCT * FROM {rel.newr.name} as t1")
    #    bigstmt.append(f"INSERT INTO {rel.r.name} SELECT * FROM {rel.newr.name}")
    #    bigstmt.append(f"DELETE FROM {rel.newr.name}")
    #bigstmt = ";".join(bigstmt)

    while True:
        n += 1
        #for stmt in rules:
        t = time.time()
        db.execute("BEGIN TRANSACTION;")
        for i in range(4):
            db.execute(";".join(rules))
            #db.execute(bigstmt)
            #print(n, time.time() - t)
            #t = time.time()
            #print(db.execute("SELECT COUNT(*) FROM new_path").fetchone(), db.execute("SELECT COUNT(*) FROM path").fetchone())
            #print(db.execute("SELECT COUNT(*) FROM new_edge").fetchone(), db.execute("SELECT COUNT(*) FROM edge").fetchone())
            for rel in rels:
                # Do the old swaparooni. Delete delta, delta := new - old, old += delta, new := {}
                #t = time.time()
                #db.execute(f"DELETE FROM {rel.dr.name}")
                #    t1 = time.time()
                #db.execute(f"INSERT OR IGedge eedWe're WeDucjksd6NORE INTO {rel.dr.name} SELECT DISTINCT * FROM {rel.newr.name} as t1 WHERE NOT EXISTS (SELECT 1 FROM {rel.r.name} as t2 WHERE t1.x0 = t2.x0 AND t1.x1 = t2.x1)")
                db.execute(f"""DELETE FROM {rel.dr.name}; 
                INSERT INTO {rel.dr.name} SELECT DISTINCT * FROM {rel.newr.name} as t1;
                INSERT INTO {rel.r.name} SELECT * FROM {rel.newr.name};
                DELETE FROM {rel.newr.name}
                """)
                
                #t2 = time.time()
                #db.execute(f"INSERT OR IGNORE INTO {rel.r.name} SELECT * FROM {rel.dr.name}")
                #t3 = time.time()
                #db.execute(f"DELETE FROM {rel.newr.name}")
                #t4 = time.time()
                #print(f"  delete: {t1 - t:.6f}, insert delta: {t2 - t1:.6f}, insert r: {t3 - t2:.6f}, delete new: {t4 - t3:.6f}")
                #print(n, rel.dr.name, db.execute("SELECT * FROM " + rel.dr.name).fetchall())
        #print(n, "swap", time.time() - t)
            #if n > 1000:
            #    return
        db.execute("COMMIT;")
        print(n, time.time() - t)
        if (limit is not None and n > limit) or all(db.execute(f"SELECT * FROM {rel.dr.name} LIMIT 1").fetchone() is None for rel in rels):
            return

fix(db, [edge, path], [
    edge(1,2),
    edge(2,3),
    edge(3,4),
    path(x,y) <= edge[x,y],
    path(x,z) <= edge[x,y] & path[y,z]
], limit=10)
db.execute(path[x,y].env.code).fetchall()
```

    1 0.019887447357177734
    2 0.013635635375976562





    [(1, 2), (2, 3), (3, 4), (1, 3), (2, 4), (1, 4)]

```python
0.008 * 1000
```

    8.0

```python
path(x,y) <= edge[x,y]
```

    'INSERT OR IGNORE INTO new_path\nSELECT x,y\nFROM (SELECT x0 AS x, x1 AS y\nFROM delta_edge\n)'

```python
def naive_fix(db, rels, stmts, limit=4):
    #for rel in rels:
    #    db.execute(rel.create())
    print(stmts)
    t=time.time()
    for stmt in stmts:
        if isinstance(stmt, Head):
            db.execute(stmt.fact())
    print(time.time() - t)
    n = 0
    rules = [stmt for stmt in stmts if isinstance(stmt, str)]

    while True:
        n += 1
        t=time.time()
        for stmt in rules:
            if isinstance(stmt, str):
                db.execute(stmt)
        print(n, time.time() - t)
        if n > limit:
            return
db.execute("DELETE FROM edge")
db.execute("DELETE FROM path")
naive_fix(db, [edge, path], 
 [edge.r(n, n+1) for n in range(1, 1000)] + 
 [path.r(x,y) <= edge.r[x,y],
 path.r(x,z) <= edge.r[x,y] & path.r[y,z]
 ], limit=1000)
db.execute("SELECT COUNT(*) FROM edge").fetchone()
```

```python
db.execute("SELECT COUNT(*) FROM path").fetchone()
```

    (157122,)

```python
res= db.execute("""
PRAGMA explain_output = 'all';
EXPLAIN ANALYZE
INSERT OR IGNORE INTO new_path
SELECT x as x0, z as x1
FROM (SELECT y, z, x
 FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
FROM (SELECT x0 AS x, x1 AS y
FROM delta_edge
) AS t1,
(SELECT x0 AS y, x1 AS z
FROM path
) AS t2
WHERE t1.y = t2.y

UNION 

SELECT t1.y AS y, t1.x AS x, t2.z AS z
FROM (SELECT x0 AS x, x1 AS y
FROM edge
) AS t1,
(SELECT x0 AS y, x1 AS z
FROM delta_path
) AS t2
WHERE t1.y = t2.y))
""").fetchall()
print(res[0][1])
```

    ┌─────────────────────────────────────┐
    │┌───────────────────────────────────┐│
    ││    Query Profiling Information    ││
    │└───────────────────────────────────┘│
    └─────────────────────────────────────┘
     PRAGMA explain_output = 'all'; EXPLAIN ANALYZE INSERT OR IGNORE INTO new_path SELECT x as x0, z as x1 FROM (SELECT y, z, x  FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z FROM (SELECT x0 AS x, x1 AS y FROM delta_edge ) AS t1, (SELECT x0 AS y, x1 AS z FROM path ) AS t2 WHERE t1.y = t2.y  UNION   SELECT t1.y AS y, t1.x AS x, t2.z AS z FROM (SELECT x0 AS x, x1 AS y FROM edge ) AS t1, (SELECT x0 AS y, x1 AS z FROM delta_path ) AS t2 WHERE t1.y = t2.y)) 
    ┌────────────────────────────────────────────────┐
    │┌──────────────────────────────────────────────┐│
    ││              Total Time: 0.0022s             ││
    │└──────────────────────────────────────────────┘│
    └────────────────────────────────────────────────┘
    ┌───────────────────────────┐
    │           QUERY           │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │      EXPLAIN_ANALYZE      │
    │    ────────────────────   │
    │           0 Rows          │
    │          (0.00s)          │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │           INSERT          │
    │    ────────────────────   │
    │           1 Rows          │
    │          (0.00s)          │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │         PROJECTION        │
    │    ────────────────────   │
    │             x0            │
    │             x1            │
    │                           │
    │           0 Rows          │
    │          (0.00s)          │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │         PROJECTION        │
    │    ────────────────────   │
    │             z             │
    │             x             │
    │                           │
    │           0 Rows          │
    │          (0.00s)          │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │       HASH_GROUP_BY       │
    │    ────────────────────   │
    │          Groups:          │
    │             #0            │
    │             #1            │
    │             #2            │
    │                           │
    │           0 Rows          │
    │          (0.00s)          │
    └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐
    │           UNION           │
    │    ────────────────────   │
    │           0 Rows          ├───────────────────────────────────────────┐
    │          (0.00s)          │                                           │
    └─────────────┬─────────────┘                                           │
    ┌─────────────┴─────────────┐                             ┌─────────────┴─────────────┐
    │         PROJECTION        │                             │         PROJECTION        │
    │    ────────────────────   │                             │    ────────────────────   │
    │             y             │                             │             y             │
    │             x             │                             │             x             │
    │             z             │                             │             z             │
    │                           │                             │                           │
    │           0 Rows          │                             │           0 Rows          │
    │          (0.00s)          │                             │          (0.00s)          │
    └─────────────┬─────────────┘                             └─────────────┬─────────────┘
    ┌─────────────┴─────────────┐                             ┌─────────────┴─────────────┐
    │         HASH_JOIN         │                             │         HASH_JOIN         │
    │    ────────────────────   │                             │    ────────────────────   │
    │      Join Type: INNER     │                             │      Join Type: INNER     │
    │     Conditions: y = y     ├──────────────┐              │     Conditions: y = y     ├──────────────┐
    │                           │              │              │                           │              │
    │           0 Rows          │              │              │           0 Rows          │              │
    │          (0.00s)          │              │              │          (0.00s)          │              │
    └─────────────┬─────────────┘              │              └─────────────┬─────────────┘              │
    ┌─────────────┴─────────────┐┌─────────────┴─────────────┐┌─────────────┴─────────────┐┌─────────────┴─────────────┐
    │         TABLE_SCAN        ││         TABLE_SCAN        ││         TABLE_SCAN        ││         TABLE_SCAN        │
    │    ────────────────────   ││    ────────────────────   ││    ────────────────────   ││    ────────────────────   │
    │        Table: path        ││     Table: delta_edge     ││     Table: delta_path     ││        Table: edge        │
    │   Type: Sequential Scan   ││   Type: Sequential Scan   ││   Type: Sequential Scan   ││   Type: Sequential Scan   │
    │                           ││                           ││                           ││                           │
    │        Projections:       ││        Projections:       ││        Projections:       ││        Projections:       │
    │             x0            ││             x0            ││             x0            ││             x0            │
    │             x1            ││             x1            ││             x1            ││             x1            │
    │                           ││                           ││                           ││                           │
    │       Filters: x0>=2      ││      Filters: x1<=999     ││       Filters: x0>=2      ││      Filters: x1<=999     │
    │                           ││                           ││                           ││                           │
    │           3 Rows          ││           0 Rows          ││           0 Rows          ││           3 Rows          │
    │          (0.00s)          ││          (0.00s)          ││          (0.00s)          ││          (0.00s)          │
    └───────────────────────────┘└───────────────────────────┘└───────────────────────────┘└───────────────────────────┘
    

```python
import time
import duckdb 
db = duckdb.connect()
t = time.time()
for rel in [edge, path]:
    print("CREATE TABLE " + rel.r.name + " (x0 INTEGER, x1 INTEGER, PRIMARY KEY (x0, x1))")
    db.execute("CREATE TABLE " + rel.r.name + " (x0 INTEGER, x1 INTEGER, PRIMARY KEY (x0, x1))")
    db.execute("CREATE TABLE " + rel.dr.name + " (x0 INTEGER, x1 INTEGER, PRIMARY KEY (x0, x1))")
    db.execute("CREATE TABLE " + rel.newr.name + " (x0 INTEGER, x1 INTEGER, PRIMARY KEY (x0, x1))")
    #db.execute("CREATE TABLE " + rel.r.name + " (x0 INTEGER, x1 INTEGER)")
    #db.execute("CREATE TABLE " + rel.dr.name + " (x0 INTEGER, x1 INTEGER)")
    #db.execute("CREATE TABLE " + rel.newr.name + " (x0 INTEGER, x1 INTEGER)")
print(time.time() - t)
fix(db, [edge, path],
[edge(n, n+1) for n in range(1, 1000)] + 
["INSERT INTO new_path\nSELECT x,y\nFROM (SELECT x0 AS x, x1 AS y\nFROM delta_edge\n)",
"""INSERT INTO new_path
SELECT x as x0, z as x1
FROM (SELECT y, z, x
 FROM (SELECT t1.y AS y, t1.x AS x, t2.z AS z
FROM (SELECT x0 AS x, x1 AS y
FROM delta_edge
) AS t1,
(SELECT x0 AS y, x1 AS z
FROM path
) AS t2
WHERE t1.y = t2.y

UNION 

SELECT t1.y AS y, t1.x AS x, t2.z AS z
FROM (SELECT x0 AS x, x1 AS y
FROM edge
) AS t1,
(SELECT x0 AS y, x1 AS z
FROM delta_path
) AS t2
WHERE t1.y = t2.y))
"""
])
time.time() - t
```

```python
%%file /tmp/test.dl

.decl edge(x: number, y: number)
.decl path(x: number, y: number)
//.input edge
.output path

edge(n, n+1) :- n = range(0, 1000).
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).

```

    Overwriting /tmp/test.dl

```python
! time souffle /tmp/test.dl 
```

    real 0m0.180s
    user 0m0.164s
    sys 0m0.015s

7

```python
7/0.18
```

    38.88888888888889

20/.18

```python
%%file /tmp/path.cpp

#include <iostream>
#include <set> // should be using unordered_set
int main() {
    std::set<std::pair<int,int>> edge, path, new_path, delta_edge, delta_path;
    for (int n = 0; n < 1000; n++) {
        edge.insert({n, n+1});
    }
    path = delta_path = edge;
    int n = 0;
    while (!delta_path.empty() || !delta_edge.empty()) {
        n++;
        new_path.clear();
        for (auto [x,y] : delta_edge) {
            for (auto [y2,z] : path) {
                if (y == y2) {
                    new_path.insert({x,z});
                }
            }
        }
        for (auto [x,y] : edge) {
            for (auto [y2,z] : delta_path) {
                if (y == y2) {
                    new_path.insert({x,z});
                }
            }
        }
        delta_path.clear();
        for (auto p : new_path) {
            if (path.insert(p).second) {
                delta_path.insert(p);
            }
        }
        delta_edge.clear();
        //std::cout << n << " " << delta_path.size() << " " << path.size() << "\n";
    }
    std::cout << n << " " << path.size() << "\n";
    return 0;   
}
```

    Overwriting /tmp/path.cpp

```python
! g++ -O3 -march=native -o /tmp/path /tmp/path.cpp && time /tmp/path
```

    1000 500500
    
    real 0m1.991s
    user 0m1.979s
    sys 0m0.008s

```python
%%file /tmp/test.rs
use std::collections::HashSet;
fn main() {
    let mut edge: HashSet<(i32,i32)> = HashSet::new();
    let mut path: HashSet<(i32,i32)> = HashSet::new();
    let mut new_path: HashSet<(i32,i32)> = HashSet::new();
    let mut delta_edge: HashSet<(i32,i32)> = HashSet::new();
    let mut delta_path: HashSet<(i32,i32)> = HashSet::new();
    for n in 0..1000 {
        edge.insert((n, n+1));
    }
    path = edge.clone();
    delta_path = edge.clone();
    let mut n = 0;
    while !delta_path.is_empty() || !delta_edge.is_empty() {
        n += 1;
        new_path.clear();
        for (x,y) in &delta_edge {
            for (y2,z) in &path {
                if y == y2 {
                    new_path.insert((*x,*z));
                }
            }
        }
        for (x,y) in &edge {
            for (y2,z) in &delta_path {
                if y == y2 {
                    new_path.insert((*x,*z));
                }
            }
        }
        delta_path.clear();
        for p in &new_path {
            if path.insert(*p) {
                delta_path.insert(*p);
            }
        }
        delta_edge.clear();
        //println!("{} {} {}", n, delta_path.len(), path.len());
    }
    println!("{} {}", n, path.len());
}
```

    Overwriting /tmp/test.rs

```python
! time cargo +nightly -Zscript /tmp/test.rs # It's a dev build
```

    [1m[33mwarning[0m[1m:[0m `package.edition` is unspecified, defaulting to `2024`
    [1m[32m   Compiling[0m test- v0.0.0 (/tmp/test.rs)
    [K[0m[1m[33mwarning[0m[0m[1m: value assigned to `path` is never read[0m            
    [0m [0m[0m[1m[38;5;12m--> [0m[0mtest.rs:4:13[0m
    [0m  [0m[0m[1m[38;5;12m|[0m
    [0m[1m[38;5;12m4[0m[0m [0m[0m[1m[38;5;12m|[0m[0m [0m[0m    let mut path: HashSet<(i32,i32)> = HashSet::new();[0m
    [0m  [0m[0m[1m[38;5;12m|[0m[0m             [0m[0m[1m[33m^^^^[0m
    [0m  [0m[0m[1m[38;5;12m|[0m
    [0m  [0m[0m[1m[38;5;12m= [0m[0m[1mhelp[0m[0m: maybe it is overwritten before being read?[0m
    [0m  [0m[0m[1m[38;5;12m= [0m[0m[1mnote[0m[0m: `#[warn(unused_assignments)]` on by default[0m
    
    [K[0m[1m[33mwarning[0m[0m[1m: value assigned to `delta_path` is never read[0m      
    [0m [0m[0m[1m[38;5;12m--> [0m[0mtest.rs:7:13[0m
    [0m  [0m[0m[1m[38;5;12m|[0m
    [0m[1m[38;5;12m7[0m[0m [0m[0m[1m[38;5;12m|[0m[0m [0m[0m    let mut delta_path: HashSet<(i32,i32)> = HashSet::new();[0m
    [0m  [0m[0m[1m[38;5;12m|[0m[0m             [0m[0m[1m[33m^^^^^^^^^^[0m
    [0m  [0m[0m[1m[38;5;12m|[0m
    [0m  [0m[0m[1m[38;5;12m= [0m[0m[1mhelp[0m[0m: maybe it is overwritten before being read?[0m
    
    [K[1m[33mwarning[0m[1m:[0m `test-` (bin "test-") generated 2 warnings                
    [1m[32m    Finished[0m `dev` profile [unoptimized + debuginfo] target(s) in 0.10s
    [1m[32m     Running[0m `/home/philip/.cargo/target/e8/a8b1c02d8deab1/debug/test-`
    1000 500500
    
    real 0m8.901s
    user 0m8.813s
    sys 0m0.109s

```python
t = time.time()
edge1 = {(n,n+1) for n in range(1, 1000)}
path1 = edge1.copy()
dpath = edge1.copy()
newpath = set()
for i in range(1010):
    #print(i, len(dpath), len(path1))
    for (x,y) in edge1:
        for (y2,z) in dpath:
            if y == y2:
                newpath.add((x,z))
    dpath = newpath - path1
    path1 |= newpath
    newpath = set()
    if not dpath:
        break
print(time.time() - t)
```

    20.915092945098877

# Bits and Bobbles

```python
class EnvRel():
    def project(self, cols: set[Var]) -> "EnvRel":
        assert cols <= self.cols
        select_clause = ", ".join(f"{c} AS {c}" for c in cols)
        return EnvRel(cols, f"SELECT {select_clause} FROM ({self.code})")
    def rename(self, renames: dict[str,str]) -> "EnvRel":
        new_cols = {renames.get(c,c) for c in self.cols}
        select_clause = ", ".join(f"{c} AS {renames.get(c,c)}" for c in self.cols)
        return EnvRel(new_cols, f"SELECT {select_clause} FROM ({self.code})")

```

```python

```

```python
def fix(db, rels : list[tuple[str,int]], stmts, limit=None):
    for rel,arity in rels:
        db.execute(f"CREATE TABLE {rel}(a int, b int)")
        db.execute("CREATE TABLE delta_{rel} (a)")
        db.execute("CREATE TABLE new_{rel} (a)")
        db.execute("INSERT INTO delta_{rel} SELECT * FROM {rel}")
    n = 0
    while True:
        n += 0
        for stmt in stmts:
            db.execute(stmt)
        for rel,arity in rels:
            db.execute(f"DELETE FROM delta_{rel}")
            db.execute(f"INSERT INTO {rel} SELECT * FROM new_{rel} EXCEPT SELECT * FROM {rel}")
            db.execute(f"DELETE FROM new_{rel}")
            if (limit is not None and n > limit) or db.execute(f"SELECT COUNT(*) FROM delta_{rel}").fetchone()[0] > 0:
                # cleanup
                db.execute("DELETE TABLE delta_{rel}")
                db.execute("DELETE TABLE new_{rel}")
                return
            

```

```python
class Head():
    def __init__(self, rel, vs):
        self.rel = rel
        self.vs = vs
    def __le__(self, body):
        return f"INSERT INTO {self.rel} SELECT {','.join(body.vs)} FROM {body.froms} WHERE {' AND '.join(body.conds)}"

class Rel():
    def __init__(self, rel, vs):
        self.rel = rel
        self.vs = vs

```

```python
type goaly = (int,db) -> list[env]

```

```python
type Env = dict
type goal = Callable[[DB, Env], list[Env]]

class Var():
    name: str

def conj(*args : Env):


class DatalogRel():
    data : set[tuple[object,...]]
    def __call__(self, *args):
    




```

```python
from dataclasses import dataclass

type SQL = str

@dataclass
class SqlRel():
    cols : set[str] # reverse these two.
    code : str
    def __and__(self, other: "EnvRel") -> "EnvRel":
        on = self.cols & other.cols
        assert on, f"Cannot join on no columns {self.cols} {other.cols}"
        on_clause = " AND ".join(f"self.{c} = other.{c}" for c in on)
        return SqlRel(self.cols | other.cols, f"({self.code}) INNER JOIN ({other.code}) ON {on_clause}")
    
    def project(self, cols: set[str]) -> "SqlRel":
        assert cols <= self.cols
        select_clause = ", ".join(f"{c} AS {c}" for c in cols)
        return SqlRel(cols, f"SELECT {select_clause} FROM ({self.code})")
    def rename(self, renames: dict[str,str]) -> "SqlRel":
        new_cols = {renames.get(c,c) for c in self.cols}
        select_clause = ", ".join(f"{c} AS {renames.get(c,c)}" for c in self.cols)
        return SqlRel(new_cols, f"SELECT {select_clause} FROM ({self.code})")
    #def __getitem__(self, cols : set[str]) -> "SqlRel":
    #    return self.project(cols)

@dataclass
class EnvRel(SqlRel): ...



    

edgexy = SqlRel({"x","y"}, "SELECT x0 AS x, y0 as y FROM edge")
pathyz = SqlRel({"y","z"}, "SELECT x0 AS y, y0 as z FROM path")

import sqlite3
db = sqlite3.connect(":memory:")
def dict_factory(cursor, row):
    fields = [column[0] for column in cursor.description]
    return {key: value for key, value in zip(fields, row)}
db.row_factory = dict_factory#sqlite3.Row
db.execute("CREATE TABLE edge (x0 INT, y0 INT, UNIQUE(x0, y0))")
db.execute("CREATE TABLE path (x0 INT, y0 INT, UNIQUE(x0, y0))")
db.execute("INSERT INTO edge VALUES (1,2), (2,3), (3,4)")
(edgexy & pathyz).project({"x", "z"})

db.execute(edgexy.project({"x"}).code).fetchall()

db.execute(edgexy.rename({"x" : "z"}).code).fetchall()
db.execute(f"INSERT OR IGNORE INTO path {edgexy.code}").fetchall()
db.execute(f"INSERT OR IGNORE INTO path {edgexy.code}").fetchall()
db.execute("SELECT * FROM path").fetchall()
#db.execute(f"INSERT OR IGNORE INTO path { (edgexy & pathyz).project({'x','z'}).code}").fetchall()
db.execute("SELECT * FROM path").fetchall()


```

    [{'x0': 1, 'y0': 2}, {'x0': 2, 'y0': 3}, {'x0': 3, 'y0': 4}]

```python

```

    SqlRel(cols={'y', 'z', 'x'}, code='(SELECT x0 AS x, y0 AS y FROM (edge)) INNER JOIN (SELECT x0 AS y, y0 AS z FROM (path)) ON self.y = other.y')

```python
from typing import Protocol

class RelAlg(Protocol):
    cols: list[str]  # column names
    def rename(self, src: str, dst: str) -> 'RelAlg': ...  # subst : list[tuple[str, str]]
    def proj(self, cols: list[str]) -> 'RelAlg': ...
    def join(self, other: 'RelAlg') -> 'RelAlg': ...
    def union(self, other: 'RelAlg') -> 'RelAlg': ...
    def intersect(self, other: 'RelAlg') -> 'RelAlg': ...
    def diff(self, other: 'RelAlg') -> 'RelAlg': ...
    def select(self, cond: str) -> 'RelAlg': ... # not str

class SQLRel(RelAlg):
    cols : list[str]
    code : str

class PyRel(RelAlg):
    rel : frozenset(frozendict)
    
class PolarsRel(RelAlg):
    pass

class DualRel(RelAlg):
    R: RelAlg
    dR: RelAlg






```

Lazy Trie Join
The simplest version just pushes completely.

Minikanren has uniformity.

<https://dodisturb.me/posts/2018-12-25-The-Essence-of-Datalog.html>
<https://stackoverflow.com/questions/28467011/what-are-the-main-technical-differences-between-prolog-and-minikanren-with-resp>

<https://www.cambridge.org/core/journals/journal-of-functional-programming/article/sql-to-c-compiler-in-500-lines-of-code/C38B40C78B6A9C55232D4A850587FC64>

```python
class Var():
    ind : int
#type Var = int
type Env = dict[int, object]
#type rel = Callable[[...], list[Env]]

edge_table = {(1,2), (2,3)}
def edge(x,y):
    def res(db):
        if x is Var:
            return
            
def rel(name, *args):
    def res(db):
        R = db.get(name, {})
        for row in R: ...

def merge_env(e1,e2):
    if len(e1) <= len(e2):
        e1, e2 = e2, e1
    res = e1.copy()
    for k,v in e2:
        if k in res:
            if res[k] != v:
                return
        res[k] = v
    return res

#def bind(v, name):

def forall(A, f):
    def res(db):
        for a in db[A]:
            yield f(a)

def forall(f):
    def res(counter, db):
        return f(counter)(counter+1, db)
    return res




    #for (n,a) in sorted(enumerate(args), key=lambda z: (z[1],z[0])):





def prod(x,y): #  seminiave  ((x*y), x*dy + y * dx)
    def res(db):
        for a in x(db):
            for b in y(db):
                yield merge_env(a,b)
    return res






```

```python
import sqlite3


db = sqlite3.connect(":memory:")
db.execute("CREATE TABLE edge (x0 INTEGER, x1 INTEGER)")
db.executemany("INSERT INTO edge VALUES (?, ?)", [(1,2),(2,3)])
db.execute("CREATE TABLE path (x0 INTEGER, x1 INTEGER)")
db.execute("INSERT INTO path SELECT x as x0, y as x1 FROM (SELECT x0 as x, x1 as y FROM edge)")
db.execute("SELECT * FROM path").fetchall()
```

    [(1, 2), (2, 3)]

```python
class Rel(): ...
    def sql():
    def freevars():
    def __mul__(self, other):
        return Rel(f"({self.sql} JOIN {other.sql})")

class BaseRelation():
    def __init__(self, name, db):
        self.name = name
        self.db = db
    def __call__(self, *args, **kwargs):
        args = {"x" + str(n) : a for n,a in enumerate(args), **kwargs}
        wheres = ["TRUE"]
        env = {}
        for k,v in args.items():
            if isinstance(v, Var):
                if v.ind in env:
                    wheres.append(f"{k} = {env[v.ind]}")
                else:
                    env[v.ind] = k
            else:
                wheres.append(f"{k} = {repr(v)}")
        return Rel(
            f'(SELECT {"," .join([f"{v} As {k}" for k,v in env.items()])} 
                FROM {self.name} 
                WHERE {" AND ".join(wheres)})', 
                env.keys())
    def __getitem__(self, key): ...
        
```

      Cell In[28], line 2
        def sql():
        ^
    IndentationError: unexpected indent

I can translate datalog into relation algerbao f the body.
Then i can directly interpet the relation algebra,
do optimizations finally tagless style
or interpret into SQL.

The key is the senmantcs of the body is the relation of _environments"

Using dual numbers
"edge", "delta_edge"
UNION

THe initial trnalsation from base relations to an environment form is the only complex part.

Using Lazy Trie Join if clean somehow

class Trie():
    # colname : [object]
    rename : [object]  # level 0 = "foo", level 1 = "bar" ... etc.
    trie : dict[dict[dict]]

def intersect(t1,t2)
    if t.level[0] == t.level[1]:
    else:
        if t1.level[0] < t2.level[1]:
            t2,t1 = t1,t2
        return {k : for k,v in t1.trie}

```python
class RelAlg(Protocol):
    def rename(self, **kwargs): ...
    def project(self, *args): ...
    def join(self, other): ...

class RelAlgCode():
    sql : str
class RelAlgSet():







def rel(R):
    def res(*args, **kwargs):
        args = {**{"x" + str(n) : a for n,a in enumerate(args)}, **kwargs}
        Q = set()
        for row in R:
            env = {}
            for k,v in args.items():
                if isinstance(v, Var):
                    if v in env:
                        if env[v] != row[k]:
                            break
                    else:
                        env[v] = row[k]
                else:
                    if row[k] != v:
                        break
            else:
                Q.add(frozendict(env))
        return Q
    return res
```

      Cell In[79], line 1
        class RelAlg()
                      ^
    SyntaxError: expected ':'

```python

@dataclass(frozen=True)
class Var():
    ind : str
x,y,z = Var("x"), Var("y"), Var("z")

def rel(name):
    def res(*args, **kwargs):
        args = {**{"x" + str(n) : a for n,a in enumerate(args)}, **kwargs}
        wheres = ["TRUE"]
        env = {}
        for k,v in args.items():
            if isinstance(v, Var):
                if v in env:
                    wheres.append(f"{k} = {env[v]}")
                else:
                    env[v] = k
            else:
                wheres.append(f"{k} = {repr(v)}")
        return f"""SELECT DISTINCT {", " .join([f"{v} AS {k.ind}" for k,v in env.items()] + ["NULL"])} \
                FROM {name} \
                WHERE {" AND ".join(wheres)}"""
    return res
def conj(*args):
    return ", ".join("(" + arg + ")" for arg in args)
    #return " INNER JOIN ".join("(" + arg + ")" for arg in args)
#def 

edge = rel("edge")
edge(1,2)
#db.execute("SELECT NULL, x0 as a FROM edge where true and x1 = 2").fetchall()
#db.execute(edge(3,4)).fetchall()

db = sqlite3.connect(":memory:")
db.execute("CREATE TABLE edge (x0 INTEGER, x1 INTEGER, PRIMARY KEY (x0, x1))")
db.executemany("INSERT OR IGNORE INTO edge VALUES (?, ?)", [(1,2),(2,3),(2,4)])
db.execute("CREATE TABLE path (x0 INTEGER, x1 INTEGER)")
db.execute("INSERT INTO path SELECT x as x0, y as x1 FROM (SELECT x0 as x, x1 as y FROM edge)")
db.execute("SELECT * FROM path").fetchall()

db.execute("SELECT * FROM" + conj(edge(1, x), edge(x,3))).fetchall()
#conj(edge(1, x), edge(x,3))
#edge(1, x)
#db.execute("SELECT * FROM edge").fetchall()
#conj(edge(1, x), edge(x,3))

def insert(name)
    def res(*args, **kwargs):
        def res2(body):
            args = {**{"x" + str(n) : a for n,a in enumerate(args)}, **kwargs}
            selects = ", ".join([f"{v} AS {k}" for k,v in args.items()])
            return f"INSERT OR IGNORE INTO {name} SELECT {selects} FROM {body}"
        return res2
    return res
insert("path")(1,2)() 

```

    [(2, None, 2, None)]

```python
class State():
    env : dict[int, key]
    data : trie
```

```python
class State():
    env : dict[int, string]
    froms :list[str]
    constrs : list[str]

    def __mul__(self, other):
        return State({**self.env, **self.other},
            self.froms + other.froms,
            self.constrs + other.constrs + [self.env[k] == other.env[k] for k in self.env if k in other.env])

def rel(name, *args):
    return State(  , ["{name} as {row}"], [])

```

```python
from dataclasses import dataclass
from collections import defaultdict
@dataclass
class Var():
    ind:int
    def __le__(self, other):
        if isinstance(other, Var):
            return self.ind <= other.ind
        return True
    def __lt__(self, other):
        if isinstance(other, Var):
            return self.ind < other.ind
        return True

def trie(R, *args):
    def worker(S, nargs):
        if len(S) == 0:
            return None
        if len(nargs) == 0:
            return () if S else None
        else:
            (n, a) = nargs[0]
            if isinstance(a, Var):
                q = defaultdict(set)
                for v in S:
                    q[v[n]].add(v)
                return (n, {k : worker(v, nargs[1:]) for k, v in q.items()})
            else:
                return worker({v for v in S if v[n] == a}, nargs[1:])
    return worker(R, sorted(enumerate(args), key=lambda z: (z[1], z[0])))
edge = {(1,2), (2,3), (2,1)}
trie(edge, Var(0), 1)

```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[8], line 32
         30     return worker(R, sorted(enumerate(args), key=lambda z: (z[1], z[0])))
         31 edge = {(1,2), (2,3), (2,1)}
    ---> 32 trie(edge, Var(0), 1)


    Cell In[8], line 30, in trie(R, *args)
         28         else:
         29             return worker({v for v in S if v[n] == a}, nargs[1:])
    ---> 30 return worker(R, sorted(enumerate(args), key=lambda z: (z[1], z[0])))


    TypeError: '<' not supported between instances of 'int' and 'Var'

```python
def trie(R,n):
    if n == 0:
        return ()
    elif n == 1:
        return {k[0] : () for k in R}
    else:
        q = defaultdict(set)
        for row in R:
            if len(row) >= 2:
                q[row[0]].add(row[1:])

        return {k : trie(v,n-1) for k, v in q.items()}

trie(edge, 2)



```

    {2: {1: (), 3: ()}, 1: {2: ()}}

```python
def trie(R):
    root = {}
    for row in R:
        node = root
        for v in row:
            node = node.setdefault(v, {})
    return root

trie(edge)
```

    {2: {3: {}, 1: {}}, 1: {2: {}}}

```python
def trie(R, args):
    root = {}
    for row in R:
        node = root
        for n, v in sorted(zip(args, row)):
            node = node.setdefault(v, {})
    return root

trie(edge, [0,1])
trie(edge, [1,0])
```

    {3: {2: {}}, 2: {1: {}}, 1: {2: {}}}

```python
def trie(R, pat):
    root = {}
    for row in R:
        env = {}
        for n, v in sorted(zip(pat, row)):
            if isinstance(n,Var) and n in env:
                if env[n] != v:
                    break
                else:
                    env[n] = v
            else:
                if n != v: # literal pattern
                    break
        else:
            node = root
            for n, v in sorted(env.items()):
                node = node.setdefault(v, {})
    return root

trie(edge, [0,1])
trie(edge, [1,0])
```

```python
def run(db):
    for x in db.V:
        for y in db.V:
            
```
