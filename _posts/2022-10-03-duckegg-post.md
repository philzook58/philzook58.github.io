---
date: 2022-10-03
layout: post
title: "Duckegg: An Datalog / Egraph Implementation Built Around DuckDB"
description: Taking Yihong's egglite and putting some python and duck in it
tags: egraph duckdb sql python
---

The [HYTRADBOI Jam](https://www.hytradboi.com/jam) gave me the little oomph I needed to go ahead and build something I've been thinking about for a couple months: Duckegg ([repo](https://github.com/philzook58/duckegg)). Duckegg is an embedded python datalog / egraph implementation built around duckdb to supply it's core functionality.

Egraphs are a data structure for performing nondestructive term rewriting and equational reasoning. This graph can be represented and queried as tables (each enode becomes a row in the corresponding table of it's symbol where the last entry is the eclass of the enode itself, the "output" of the function). The various rebuilding operation can also be represented as SQL operations. The hope basically is that duckdb is so good that the translation cost into SQL is worth it.

DuckDB is making waves as a performant, embedded, easy-to-deploy OLAP (analytical processing) database. SQLlite is a marvel, but it is meant for  OLTP workloads. This use case seems like a better fit for duckdb.

For more on egraphs and egglog

- <https://egraphs-good.github.io/>
- <https://www.philipzucker.com/egglog/>
- <https://www.philipzucker.com/souffle-egg4/>
- <https://www.hytradboi.com/2022/writing-part-of-a-compiler-in-datalog>
- <https://www.philipzucker.com/notes/Logic/egraphs/>

Yihong Zhang previously had the idea of building a [relational egglog around sqlite in racket](https://github.com/yihozhang/egraph-sqlite) [PLDI workshop paper](https://src.acm.org/binaries/content/assets/src/2022/yihong-zhang.pdf), and this implementation is very much related and inspired by that one. I think the main misstep here is using racket (no offense), as it severely limits the audience of such a thing.

I tried to utilize DuckDB as much as possible to avoid writing too much code and because everything I write in python will be slow. The whole implementation is at about 300 lines right now. Not too bad.

## Datalog with Terms to SQL

I made a simple DSL with Variables, Atoms, Terms, and Clauses.

```python
@dataclass(frozen=True)
class Var:
    name: str


de__counter = 0


def FreshVar():
    global de__counter
    de__counter += 1
    return Var(f"duckegg_x{de__counter}")


def Vars(xs):
    return [Var(x) for x in xs.split()]


@dataclass
class Atom:
    name: str
    args: list[Any]

    def __repr__(self):
        args = ",".join(map(repr, self.args))
        return f"{self.name}({args})"


@dataclass
class Term:
    name: str
    args: list[Any]
```

Terms are handling by flattening them into tables. This is done by recursing down the term and generating fresh variables.

```python
    def flatten(self):
        clauses = []
        newargs = []
        for arg in self.args:
            if isinstance(arg, Term):
                v, c = arg.flatten()
                clauses += c
                newargs.append(v)
            else:
                newargs.append(arg)
        res = FreshVar()
        newargs.append(res)
        rel = Atom(self.name, newargs)
        clauses.append(rel)
        return res, clauses
```
When you have terms in a datalog, it complicates the implementation somewhat. If the appropriate term has not already been built, you need to generate a fresh id for it. 

It ended up being convenient to take a convention from [dglp](https://graphik-team.github.io/graal/doc/dlgp) where unbound variables in head get a fresh counter value. This is unconventional in a datalog, but makes sense. Variable in the head unbound by the body are implicitly existentially quantified and treated via a skolem chase like operational semantics.

The way I dealt with this is by compiling a rule with terms in the head into multiple rules, one for each possible subterm in the head. The subterms of head term end up in the body of that head's clause. You can see this more clearly by looking at the examples below.

```python
   def expand_functions(self):
        body = []
        # flatten parts of the body
        for rel in self.body:
            newargs = []
            for arg in rel.args:
                if isinstance(arg, Term):
                    v, rels = arg.flatten()
                    body += rels
                    newargs.append(v)
                else:
                    newargs.append(arg)
            body.append(Atom(rel.name, newargs))
        newargs = []
        newhead = []
        # flatten head, but generate accumulative clause per
        for arg in self.head.args:
            if isinstance(arg, Term):
                v, rels = arg.flatten()
                newhead += rels
                newargs.append(v)
            else:
                newargs.append(arg)
        newhead.append(Atom(self.head.name, newargs))
        clauses = []
        while len(newhead) > 0:
            # This is cheeky. We don't need the full flattened head prefix, only one branch
            h = newhead.pop()
            clauses.append(Clause(h, body + newhead))
        return reversed(clauses)  # Clause(newhead, newrels)
```


A `Solver` object controls the database connection and allows you to add rules.

I tried to make the interface of the system vaguely like the Z3 interface, which I think is well designed. There is also [pydatalog](https://sites.google.com/site/pydatalog/), which I've never used. From what I see in the tutorial, there is a little more magic going on in the interface than I prefer.

My clause to sql compiling code is a total mess. I don't know how to do this that cleanly. There were a couple tricks that were kind of nice though.

SQL and datalog notation are just based around vry different notions of variables. You can give names to rows in SQL, but you give names to entries of rows in datalog. When a variable appears into two places in the datalog, you need a WHERE constraint in the sql.

A convenient way to translate them was to collect a variable map pointing from datalog variables to all the sql row entries where that variable appeared. After collecting up this map, I output the WHERE clause saying that all the values in the codomain of that map have to be equal.

SQL's bag semantics were fighting datalog's set semantics very often. To avoid adding redundant tuples to the database, every rule has a `NOT EXISTS (SELECT yada)` that makes sure the tuple doesn't already exist. I actually found adding uniqueness constraints to the tables slowed duckdb down, so screw it.


Simple datalog rules aren't that bad. As an example, this clause translates to this query

```python
s.add(Clause(plus(x, y, z), [plus(y, x, z)]))
```

becomes

```sql
INSERT INTO plus SELECT x, y, z FROM
(SELECT DISTINCT plus0.x1 AS x, plus0.x0 AS y, plus0.x2 AS z
    FROM plus AS plus0  WHERE NOT EXISTS(SELECT * FROM plus
    WHERE x0 = plus0.x1 AND x1 = plus0.x0 AND x2 = plus0.x2));
```


For fresh variables, I used a duckdb feature for [sequences](https://duckdb.org/docs/sql/statements/create_sequence). I can call `nextval('counter')` in the SELECT statement to get a fresh value. A inefficiency I realized is this requires an extra layer of `SELECT DISTINCT` filtering, because you don't want a single query generating multiple tuples that only will differ in the nextval column.

The more complicated rule with subterms translates into two SQL statements.

```python
 s.add(Clause(plus(plusf(x, y), z, w), [plus(x, plusf(y, z), w)]))
```


```sql
-- assoc left 1
INSERT INTO plus SELECT x, y, nextval('counter') FROM
(SELECT DISTINCT plus6.x0 AS x, plus5.x0 AS y
FROM plus AS plus5, plus AS plus6
WHERE plus5.x2 = plus6.x1 AND
NOT EXISTS(SELECT * FROM plus WHERE x0 = plus6.x0 AND x1 = plus5.x0));

-- assoc left 2
INSERT INTO plus SELECT x2, z, w FROM
(SELECT DISTINCT plus9.x2 AS x2, plus7.x1 AS z, plus8.x2 AS w
FROM plus AS plus7, plus AS plus8, plus AS plus9
WHERE plus7.x0 = plus9.x1 AND plus7.x2 = plus8.x1 AND plus8.x0 = plus9.x0 AND
NOT EXISTS(SELECT * FROM plus WHERE x0 = plus9.x2 AND x1 = plus7.x1 AND x2 = plus8.x2));
```

These sql queries are run in a loop.

So all of that gets us a datalog with terms.

I did not implement semi-naive evaluation, a classic datalog optimization. In the limited experiments on egraphs I've done so far, it has not seemed worth it, and it is a bit more complicated.

A different direction to take this project would be to not worry about the egraph part and see what happens when we seminaive this thing. I feel like this could be a pretty decently performant datalog at very little code. Excellent for experimentation.

## EGraph

The congruence closure of the egraph requires a rebuilding mechanism. I believe Yihong extracted out pattern matches and normalized them in racket, but I made it a goal to make duckdb do as much heavy lifting as possible.

A union find is a tree. The textbook union find uses a rank to tie break who becomes whose child when two nodes are merged. I've found it too useful to ignore to instead use a deterministic tie break, like making the minimum of the two ids the parent.

I made 2 tables, `duckegg_edge` and `duckegg_root`. `duckegg_edge` stores primitive equality assertins disocvered via congruence. This is the congruence query

```sql
INSERT INTO duckegg_edge
            SELECT DISTINCT f2.x2, min(f1.x2)
            FROM plus as f1, plus as f2
            WHERE f1.x0 = f2.x0 AND f1.x1 = f2.x1 AND f1.x2 < f2.x2
            GROUP BY f2.x2
```

The group by here is not obvious or requires, but I found it to make the system noticeably faster and it's an easy optimization

Connectivity in a graph can be encoded as a datalog or [recursive cte query](https://duckdb.org/docs/sql/query_syntax/with). By grouping and taking the minimum, we can.

The root table does not include the self edge of the union find. This is convenient, because it makes it smaller, but also filters out for where the intefresting indicies are.

```sql
WITH RECURSIVE
    path(i, j) AS (
        select * from duckegg_edge
        union
        SELECT r1.i, r2.j FROM duckegg_edge AS r1, path as r2 where r1.j = r2.i
    )
INSERT INTO duckegg_root
    select i, min(j) from path
    group by i
```

Finally, using `duckegg_root` we search through the plus table and replace old ids with their canonized equivalence. Rinse and repeat.

This stage is surprisingly computationally expensive, which I think is odd. It is currently the performance bottleneck.
What happens is multiple rows may collpase into the same value, but then these duplicates must be deleted. Deletion is apparently slow. What I found the best I've go so far is to

1. find rows that need to be normalized and put them into a temp table
2. delete the rows that were normalized
3. delete the rows in the temp table from the original table to avoid duplicates
4. insert the temp table into the original table

Here is an example working on the 0th argument `x0` of `plus`

```sql
--step 1
INSERT INTO temp_plus
SELECT DISTINCT {args}
FROM plus, duckegg_root
WHERE x0 = duckegg_root.i

--step 2
DELETE FROM plus
USING duckegg_root
WHERE x{n}=duckegg_root.i

--step 3
DELETE FROM plus
USING temp_plus
WHERE plus.x0=temp_plus.x0 AND plus.x1=temp_plus.x1 AND plus.x2=temp_plus.x2

--step 4
INSERT INTO plus
SELECT * FROM temp_plus
```

You can imagine many ways of doing this step. This is the best one I've got so far. Suggestions welcome. DM me <https://twitter.com/SandMouth>

Benchmarking this implementation on saturating an arithemtic expression (assocaitivity and commutativty) puts this implementation on par basically with my souffle encoding, but being embedded in python brings a lot of benefits. This is much closer to being a usable thing.

Both build a 173000 enode egraph in about 5 seconds on my laptop, which I think isn't too bad.











