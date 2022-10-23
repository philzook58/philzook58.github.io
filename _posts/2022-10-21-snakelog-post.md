---
date: 2022-10-21
layout: post
title: "Snakelog: A Python DSL for Datalogs"
description: Bundling up litelog and souffle into a package
tags: datalog sql python
---


There is just _something_ about datalog.

Datalog is 
- A database query language with support for recursive table constraints.
- Recursive common table subexpressions on steroids
- A bottom up relative of prolog
- A theorem prover of sorts
- With enough elbow grease a general purpose programming language

It is useful for
- Most things SQL is useful for
- Graph-like problems
- Program analysis problems (constant propagation, pointer analysis)

What aspect you may find most compelling depends on your background and interests.

This post is introducing Snakelog, a python framework for manipulating and solving datalog programs.

You can try it yourself by pip installing the very beta library `pip3 install snakelog`. The github repo is [here](https://github.com/philzook58/snakelog)

This is an example program.

```python
from snakelog import *
from snakelog.litelog import Solver, TEXT
s = Solver()
x, y, z = Vars("x y z")
edge = s.Relation("edge", TEXT, TEXT)
path = s.Relation("path", TEXT, TEXT)

s.add(edge("a", "b"))
s.add(edge("b", "c"))
s.add(path(x, y) <= edge(x, y))
s.add(path(x, z) <= edge(x, y) & path(y, z))
s.run()

s.cur.execute("SELECT * FROM path")
assert set(s.cur.fetchall()) == {("a", "b"), ("b", "c"), ("a", "c")}
```

## Why?

Datalog is a pretty weak language. There are some tricks to encode patterns you might find in other languages. For example the query answer technique let's you mimic function calls. Abstracting over these idioms is not possible in bare datalog.

A datalog embedded in another programming language does not suffer some of these restrictions. There is a similar experience in very constrained, but also powerful declarative languages like linear programming solvers, SMT solvers, and SAT solvers. For example, I have great appreciation for the Z3 python bindings. These bindings enables metaprogramming that may automatically generate complicated expressions or multiple queries.

Also it's fun.

# Common Infrastructure

By defining a common infrastructure for relations, it is possible to run the same datalog program on both souffle, litelog, and other future backends. This is a comfort to me. The flexibility and simplicity of litelog is nice (and we love our own work more than others), but it will never be as fast as souffle. Different datalogs have different strengths.

I tried to design the library such that it feels like other python libraries I have seen, used, and appreciated. A design that I have seen over and over again is explicit declaration of variables and using solver objects. Z3, cvxpy, and sympy all look a bit like this.

Another thing I chose which I hope make it familiar is that solvers expose a SQLite database connection object (SQLite actually ships in the [python standard lib](https://docs.python.org/3/library/sqlite3.html), a fact which continues to surprise me), which you can use to query the saturated database in any way you like.

The basic types are `Var`, `Term`, `Atom`, `Body`, and `Clause`. Defining these gives access to nice python overloading notation like `path(x, z) <= edge(x, y) & path(y, z))`

One difference that I chose from cvxpy and z3 is that you define relations by creating them with respect to a particular solver `s.Relation("myrelname", TEXT, NUMBER)`. Since solvers often need the schema of their relations, this saves an annoying traversal to post hoc collect the schema up from the rules. If you want to create solver generic programs, you should wrap them in a function that takes in the solver as input. This is some form of dependency injection

```python
def gen_prog(s):
    s = Solver()
    edge = s.Relation("edge", TEXT, TEXT)
    s.add(edge("b", "c"))
```

This is the basic structure of the common library, stripped down a bit.

```python
@dataclass(frozen=True)
class Var:
    name: str

def Vars(xs):
    return [Var(x) for x in xs.split()]

@dataclass(frozen=True)
class Term():
    name: str
    args: List[Any]

class Formula():
    pass

@dataclass(frozen=True)
class Eq(Formula):
    lhs: Any
    rhs: Any

@dataclass
class Not(Formula):
    val: Any



@dataclass(frozen=True)
class QuasiQuote:
    expr: str

Q = QuasiQuote


@dataclass
class Atom(Formula):
    name: str
    args: List[Any]

@dataclass
class Body:
    atoms: List[Atom]

@dataclass
class Clause:
    head: Atom
    body: Body

@dataclass
class Proof:
    conc: Formula
    subproofs: List[Proof]
    reason: Any
```

A questionable feature (but powerful) is `QuasiQuote` which let's me inject code into the solver. I'm not sure this is usable without at least some guesses about how the datalog is compiled. It enables me to put extra WHERE clauses and computations in SELECT statements for example easily without having to mode them explicitly in a datatype. It is a backdoor to access solver specific behavior in a pinch.

# Souffle Backend
[Souffle datalog](https://souffle-lang.github.io/) is a very fast and powerful datalog implementation. It is the main name in datalog.

To some degree, outputting to souffle is super easy. Snakelog is largely designed based on my experience using souffle after all. It just pretty prints into a temporary file and then calls souffle as a subprocess and reads in the result.

For running in souffle, I chose to compile `Terms` into a mondo `type term` ADT. THe design was originally communicating to souffle via the sqlite interface, but it turns out that the ADT recordTable is not serialized in this format, so I switched over to CSV. It's too bad.

```python
    def compile(self, head: Atom, body):
        def arg_str(x):
            if isinstance(x, Var):
                return x.name
            elif isinstance(x, Term):
                args = ", ".join(map(arg_str, x.args))
                return f"${x.name}({args})"
            elif isinstance(x, str):
                return f"\"{x}\""
            else:
                return str(x)

        def rel_str(rel: Atom):
            args = ", ".join(map(arg_str, rel.args))
            return f"{rel.name}({args})"
        if len(body) == 0:
            return f"{rel_str(head)}."
        else:
            body = ", ".join(map(rel_str, body))
            return f"{rel_str(head)} :- {body}."

    def run(self):
        stmts = []
        for name, types in self.rels:
            args = ", ".join([f"x{n} : {typ}" for n, typ in enumerate(types)])
            stmts.append(f".decl {name}({args})")
            if self.input_db != None:
                stmts.append(
                    f".input {name}(IO=sqlite, filename=\"{self.input_db}\")")
            stmts.append(
                f".output {name}(IO=sqlite, filename=\"{self.output_db}\")")
        if len(self.funs) != 0:
            constructors = []
            for name, types in self.funs:
                args = ", ".join(
                    [f"x{n} : {typ}" for n, typ in enumerate(types)])
                constructors.append(f"{name} {{{args}}}")
            constructors = " | ".join(constructors)
            stmts.append(f".type term = {constructors}")
        for head, body in self.rules:
            stmts.append(self.compile(head, body))
        with tempfile.NamedTemporaryFile(suffix=".dl") as fp:
            fp.writelines([stmt.encode() + b"\n" for stmt in stmts])
            fp.flush()
            res = subprocess.run([self.execname, fp.name], capture_output=True)
            print(res.stdout.decode())
            print(res.stderr.decode())
```
# Enhancements to Litelog
In two previous posts, I was building out a python datalog that was powered by duckdb and then sqlite.

- [Duckegg post](https://www.philipzucker.com/duckegg-post/) 
- [Datalite post](https://www.philipzucker.com/datalite/).

Connie liked `litelog` better so I changed the name from `datalite`.

Sqlite is ok for this purpose. It is not designed to be a high performance datalog engine. Souffle blows it out of the water (5x on one arbitrary benchmark).
- No dependencies. Sqlite comes in the python standard lib
- Flexibility. Adding user defined functions and datatypes is very easy and does not require leaving python
- Simplicity. The souffle compiler is written in C++ and has many moving parts. I do not even need to write a runtime. I'm biased, but adding experimental features to this base framework is much easier than modifying the souffle compiler. If they are good features, maybe it is worth adding eventually to souffle.

## Dictionary and List Patterns
The easiest way it seems to me to inject terms into litelog is to use the built in json capabilities of SQLite.

I chose to use python dictionaries and lists to represent patterns. These are compiled to match and construct the appropriate json structures in SQLite.

There are some alternative designs.
- We could hash cons structure into a separate table and refer to them by primary key. This is somewhat like what souffle does. This is complex and it is not at all clear that this would be more performant.

- We can flatten structures into regular tables. This is good because it is indexable. The duckegg prototype did this because it kind of had to

## Z3lite
[Formulog](https://github.com/HarvardPL/formulog) is a very interesting datalog variant that embeds being able to talk to SMT solvers like Z3 inside datalog.

Demonstrating the power of being embedded in python, I can just rip basically any functionality in and out of litelog. As an example, I put together some bindings to Z3. It works using the sqlite [adapter converter infrastructure](https://docs.python.org/3/library/sqlite3.html#adapter-and-converter-recipes). This allows us to register functions to serialize and deserialize Z3 datatypes.

Internally, Z3 hash conses it's AST and has a unique id for every AST in play. You can access this number. I store the mapping between the id and the z3 pyobject in a python dictionary and store only the integer id in sqlite.

When litelog needs to manipulate the Z3 items, it uses [user defined sql functions](https://docs.python.org/3/library/sqlite3.html#sqlite3.Connection.create_function) which can be given a python function. These function looks up the ast ids in the dictionary, do the corresponding Z3 op like `And`, `Implies`, etc, and then returns the AST id of the result.


Another way to connect Z3 to sqlite would be to use the sexpr printer of z3. This is nice because it really could be saved into an external database. True serialization and deserialization is a very useful technique. Strings are the ultimate universal types. I used it here for example to put a rational datatype into Souffle.

```python
from z3 import *
import sqlite3
import operator

z3_ast_table = {}

def get_id(x: AstRef):
    id_ = x.get_id()
    z3_ast_table[id_] = x
    return id_


def lookup_id(id_: bytes):
    return z3_ast_table[int(id_)]


sqlite3.register_adapter(AstRef, get_id)
sqlite3.register_adapter(BoolRef, get_id)
sqlite3.register_adapter(ArithRef, get_id)
sqlite3.register_adapter(BitVecRef, get_id)
sqlite3.register_adapter(CharRef, get_id)
sqlite3.register_adapter(DatatypeRef, get_id)

sqlite3.register_adapter(BitVecNumRef, get_id)
sqlite3.register_adapter(RatNumRef, get_id)
sqlite3.register_adapter(IntNumRef, get_id)
sqlite3.register_adapter(AlgebraicNumRef, get_id)

sqlite3.register_converter("AstRef", lookup_id)
sqlite3.register_converter("BoolRef", lookup_id)
sqlite3.register_converter("ArithRef", lookup_id)
sqlite3.register_converter("BitVecRef", lookup_id)
sqlite3.register_converter("CharRef", lookup_id)
sqlite3.register_converter("DatatypeRef", lookup_id)


def check_sat(e: bytes):
    s = Solver()
    s.add(lookup_id(e))
    res = s.check()
    return repr(res)


def enable_z3(con):
    def create_z3_2(name, f):
        def wrapf(x, y):
            return get_id(simplify(f(lookup_id(x), lookup_id(y))))
        con.create_function(name, 2, wrapf, deterministic=True)

    def create_z3_1(name, f):
        def wrapf(x):
            return get_id(simplify(f(lookup_id(x))))
        con.create_function(name, 1, wrapf, deterministic=True)
    # I could possibly do this as an .so sqlite extension instead.
    create_z3_2("z3_and", And)
    create_z3_2("z3_or", Or)
    create_z3_2("z3_implies", Implies)
    create_z3_2("z3_eq", operator.eq)
    create_z3_2("z3_le", operator.le)
    create_z3_2("z3_lt", operator.lt)
    create_z3_2("z3_ge", operator.ge)
    create_z3_2("z3_gt", operator.gt)
    create_z3_2("z3_ne", operator.ne)
    create_z3_2("z3_add", operator.add)
    create_z3_2("z3_mul", operator.add)
    create_z3_2("z3_sub", operator.sub)
    create_z3_2("z3_bvand", operator.__and__)
    create_z3_2("z3_bvor", operator.__or__)
    create_z3_2("z3_rshift", operator.__rshift__)
    create_z3_2("z3_lshift", operator.__lshift__)

    create_z3_1("z3_neg", operator.neg)
    create_z3_1("z3_not", Not)

    con.create_function("check_sat", 1, check_sat, deterministic=True)

```


## Timestamps and Provenance
Provenance is a really neat idea. Because datalog automatically derives tuples into the database, you may want to know what sequence of rules led to that tuples existence.

Considering the datalog rules as inference rules, provenance is a proof data structure.

You might think this is a really difficult and expensive piece of data to store, but it isn't really. You just need to save enough breadcrumbs that you can reconstruct the proof easily enough later.

This situation is very similar to that in bottom up dynamic programming or shortest path finding. The table there just stores the cost of the best solution, but what is the best solution itself? Do you need to store that at every node? No. Because you can essentially do the top down algorithm, but with the clues left behind.

In datalog, this is especially kind of interesting. Top down datalog is ~prolog. But this prolog is a bit different for 2 reasons. 
1. There are no unification variables. Every constant in play is one from the tables.
2. It is guaranteed to terminate. The timestamps are a termination metric that prevents you from looping.

Souffle does this by maintaining a proof depth parameter. An alternative that was inspired/suggested by Max is to use _timestamps_. If for every row, you record at what iteration the tuple was first derived.

These timestamps also enable [datalog with backtracking](https://www.philipzucker.com/backtracking-datalog/). If you run the database to saturation, record the timestamp, add a fact and saturate again, you can revert the database back to that timestamps by merely deleting anything with a greater timestamp. A very simple way to achieve a datalog with a particular form of deletion. You can use this to do arbitrary deletions by backtracking to the deletion and then reasserting everything you want to keep. This is of course more and more expensive the further you backtrack.

The provenance code is ugly as sin right now. I tried to reuse as much from the query engine and sqlite as possible. It searches through the rules for one that could derive the given fact. It 

1. adds head unification constraints as would occur in prolog
2. compiles the body like usual
3. adds timestamp constraints that we must only use facts before the current timestamp
4. constructs the actual sql string. The select parameters include all the body atom arguments and body atom timestamps which we need to recurse. This part is particularly ugly
5. Calls sqlite
6. If we don't find an answer, try another rule. If we do, recurse on the body of the rule with the arguments filled in and using the older timestamps

```python

    def provenance(self, fact: Atom, timestamp: int):
        for rulen, (head, body) in enumerate(self.rules):
            if head.name != fact.name or len(head.args) != len(fact.args):
                continue
            # Head unification constraints
            query = [Eq(a, b) for a, b in zip(
                head.args, fact.args)] + body
            print(query)
            varmap, constants, froms, wheres = compile_query(query)
            wheres += [f"{row}.{keyword}_timestamp < :timestamp" for _, row in froms]
            # This section is repetitive
            if len(wheres) > 0:
                wheres = " WHERE " + " AND ".join(wheres)
            else:
                wheres = ""
            constants["timestamp"] = timestamp

            body_atoms = [
                rel for rel in body if isinstance(rel, Atom)]
            selects = [arg for rel in body_atoms for arg in rel.args]
            assert len(body_atoms) == len(froms)
            assert all([r1.name == table for r1, (table, _)
                        in zip(body_atoms, froms)])
            selects = [construct(arg, varmap, constants) for arg in selects]
            timestampind = len(selects)
            selects += [f"{row}.{keyword}_timestamp" for _, row in froms]
            selects = ", ".join(selects)
            if selects == "":
                selects = " * "
            if len(froms) > 0:
                froms = " FROM " + \
                    ", ".join(
                        [f"{old(table)} AS {row}" for table, row in froms])
            else:
                froms = " FROM (VALUES (42)) "
            # order by sum(timestamps) limit 1
            self.execute(f"SELECT {selects} {froms} {wheres}", constants)
            res = self.cur.fetchone()
            if res != None:
                timestamps = res[timestampind:]
                subproofs = []
                for rel, timestamp in zip(body, timestamps):
                    nargs = len(rel.args)
                    q = Atom(rel.name, res[:nargs])
                    res = res[nargs:]
                    subproofs.append(self.provenance(q, timestamp))
                return Proof(fact, subproofs, rulen)
        raise BaseException(
            f"No rules applied to derivation of {fact}, {timestamp}")

```

I could make this better by adding an `ORDER BY` constraint that minimizes the sum of the timestamps just in case there are multiple answers.

I also made it such that it outputs bussproofs, the latex package for proof trees. Thi is easily done by just printing a depth first traversal of the `Proof` data structure

```python

    def bussproof(self):
        conc = self.conc
        reason = self.reason
        hyps = self.subproofs
        if len(hyps) == 0:
            return f"\\RightLabel{{{reason}}} \\AxiomC{{{self.conc}}}"
        elif len(hyps) == 1:
            return f"{hyps[0].bussproof()} \\RightLabel{{{reason}}} \\UnaryInfC{{{conc}}}"
        elif len(hyps) == 2:
            return f"{hyps[0].bussproof()} {hyps[1].bussproof()} \\RightLabel{{{reason}}}  \\BinaryInfC{{{conc}}}"
        elif len(hyps) == 3:
            return f"{hyps[0].bussproof()} {hyps[1].bussproof()} {hyps[2].bussproof()} \\RightLabel{{{reason}}}  \\TrinaryInfC{{{conc}}}"
        elif len(hyps) >= 3:
            return f"{hyps[0].bussproof()} {hyps[1].bussproof()} \\AxiomC{{{...}}} \\RightLabel{{{reason}}} \\TrinaryInfC{{{conc}}}"

```


## Compile Time Unification
This feature performs unification at compile time when you have constraints of the form ```Eq(Var("x"),something)```. This slightly extends the language of litelog as it was before as now you can have variables that are not grounded by being the slot of an atom. The main reason I did it was to make the unification with the head rule easy for timestamp provenance.

The relationship of datalog with unification remains a fascination for me. Inside a single rule, we can do it at compile time. It is not easy to have unification occur between rules, because datalog is kind of memoryless. I attempted this in [souffle here](https://www.philipzucker.com/first-class-uf/)

Egglog has it's own notion of a global union find, which does some of the right stuff, but not others.

I used a simple [union find dict](https://www.philipzucker.com/union-find-dict/) (a dictionary with unionable keys) for this. I still think this is a neat data structure.

```python

class VarMap():
    '''
    Union Find Dict https://www.philipzucker.com/union-find-dict/
    self.data holds either Var or list as value.
    If Var, iterate lookup until reach list.
    Values held in dict are merged upon union
    '''

    def __init__(self):
        self.data = defaultdict(list)

    def find(self, x):
        # no path compression. Simple.
        varmap = self.data
        while isinstance(varmap[x], Var):
            x = varmap[x]
        return x

    def __getitem__(self, x: Var):
        return self.data[self.find(x)]

    def __setitem__(self, k: Var, v):
        self.data[self.find(k)] = v

    def union(self, x: Var, y: Var):
        x1 = self.find(x)
        y1 = self.find(y)
        varmap = self.data
        if varmap[x1] == []:
            varmap[x1] = y1
        elif varmap[y1] == []:
            varmap[y1] == x1
        else:
            temp = varmap[x1]
            varmap[x1] = y1
            varmap[y1] += temp

    def formatmap(self):
        return {k.name: self[k][0] for k in self.data.keys()}

    def values(self):
        return [x for x in self.data.values() if not isinstance(x, Var)]

```

# Bits and Bobbles
This is not the only metaprogrammable datalog
- Souffle datalog has the C preprocessor and components
- Flix is a full programming language that supports datalog programs as built in construct.
- Ascent is embedded in rust
- Rel is embedded in julia?

The skeleton in the room is [pyDatalog](https://sites.google.com/site/pydatalog/). Why not just use that? 
Well, to be perfectly frank, I wanted to try my hand at the design.

I don't really like some aspects of pyDatalog's design. It has a little too much cuteness that I find confusing, for example injecting variables into the python namespace. This is not idiomatic python from what I've seen. It is trying a different goal of making a truly meshed datalog with python, as evidenced by the object oriented thing. I am explicitly making a deep embedded datalog, where the syntax of datalog is manipulated.

There are some other logic programming packages actually. That I am not that interested in using most of these is probably telling for how likely anyone is interested in using mine. Oh well.

It's amusing that almost every way of combining the words prolog and python have been taken at some point.

- <https://github.com/MNoorFawi/pytholog>
- <https://github.com/RussAbbott/pylog>
- <https://github.com/logpy/logpy>

Format strings are a pretty cool quasiquotation system for doing metaprogramming. I don't see people doing this enough.
A metaocaml style staging + JIT like numba could be pretty cool.

# Todo

- [pypcode](https://github.com/angr/pypcode) bindings. Datalog decompiler anyone?!
- egg-smol backend
- Tabled [pyswip](https://github.com/yuce/pyswip ) backend (SWI prolog) 
 
- A plugin system? Jesus I've become everything I fight.
- datalog modules? <https://www.sciencedirect.com/science/article/pii/S0004370222000662?via%3Dihub>
- push datalog. RPC datalog?

## Notes

This is also basically the first real python package I've tried to make (in a while?)

I used poetry. It seems pretty nice.

Tests are crucial in python in a way I don't find they are in a typed language. Refactoring is very stressful.

`poetry run pytest`

`poetry run python foo.py`

Dependency groups are useful for managing dev dependencies. `poetry add --group test pytest` for example.

After you make these groups optional, don't forget to `poetry install --with test --with docs`

`poetry publish` does something to push to PYPI after adding a credential.

I'm using sphinx-docs. This is surprisingly not one click and go. I needed t edit the makefile to use `poetry run`