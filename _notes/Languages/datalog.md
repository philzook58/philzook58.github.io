---
layout: post
title: Datalog
---
- [What is datalog?](#what-is-datalog)
- [What can you do with datalog?](#what-can-you-do-with-datalog)
  - [Getting Started](#getting-started)
  - [Path Reachability](#path-reachability)
    - [Python](#python)
      - [Naive](#naive)
      - [Semi-Naive](#semi-naive)
      - [Indexing](#indexing)
      - [Lattice](#lattice)
    - [SQL recursive common table subexpressions](#sql-recursive-common-table-subexpressions)
    - [Naive SQL translation](#naive-sql-translation)
      - [Seminaive](#seminaive)
      - [Lattices](#lattices)
    - [Ocaml](#ocaml)
      - [Naive](#naive-1)
    - [Rust](#rust)
    - [Magic Set](#magic-set)
  - [Program Analysis](#program-analysis)
    - [Evaluation](#evaluation)
    - [Constant Propagation](#constant-propagation)
    - [Symbolic Evaluation](#symbolic-evaluation)
    - [Reaching Definitions](#reaching-definitions)
    - [Liveness](#liveness)
    - [Points To](#points-to)
    - [Available Expressions](#available-expressions)
    - [Intersection](#intersection)
    - [Very Busy Expressions](#very-busy-expressions)
    - [Zippers For Program Points](#zippers-for-program-points)
    - [Dominators](#dominators)
    - [Forall Emulation](#forall-emulation)
    - [Doop](#doop)
    - [Datalog Diassembly / Decompilers](#datalog-diassembly--decompilers)
    - [Bap](#bap)
    - [Resources](#resources)
  - [First Class Sets \& Reflection](#first-class-sets--reflection)
    - [BitSets](#bitsets)
      - [Bitset reflection](#bitset-reflection)
    - [Sort Lists](#sort-lists)
    - [Patricia Tries](#patricia-tries)
    - [BDDs](#bdds)
    - [Call](#call)
    - [Meta circular interpreter](#meta-circular-interpreter)
  - [BogoSort](#bogosort)
  - [Translating functional programs](#translating-functional-programs)
  - [Lists](#lists)
  - [Dynamic Programming](#dynamic-programming)
    - [Q learning](#q-learning)
  - [Mandelbrot](#mandelbrot)
  - [Ball and Springs](#ball-and-springs)
  - [Sudoku](#sudoku)
  - [Constraint handling Rules (CHR)](#constraint-handling-rules-chr)
  - [Backprop](#backprop)
  - [Lambda representation](#lambda-representation)
  - [Parsing](#parsing)
  - [Hilog](#hilog)
  - [Equality Saturation](#equality-saturation)
  - [Term Rewriting](#term-rewriting)
    - [Datalog Modulo Term Rewriting](#datalog-modulo-term-rewriting)
    - [Graph rewriting](#graph-rewriting)
  - [Graph Algorithms](#graph-algorithms)
    - [Reachability](#reachability)
    - [Shortest Path](#shortest-path)
    - [Spanning Tree](#spanning-tree)
    - [Clique](#clique)
    - [Cycle](#cycle)
    - [Subgraph Matching](#subgraph-matching)
    - [Coloring](#coloring)
  - [Propagators](#propagators)
    - [Boolean Constraint Propagation](#boolean-constraint-propagation)
    - [Difference Logic](#difference-logic)
    - [Finite Domain](#finite-domain)
  - [Macros](#macros)
  - [Emulating Prolog](#emulating-prolog)
    - [Need Sets](#need-sets)
    - [Magic Set](#magic-set-1)
    - [First class union find](#first-class-union-find)
  - [Translating Imperative Programs](#translating-imperative-programs)
    - [Iteration](#iteration)
  - [Model Checking](#model-checking)
  - [Timestamping](#timestamping)
  - [Theorem Proving](#theorem-proving)
    - [Skolemization for Existential Heads](#skolemization-for-existential-heads)
    - [Goals / Queries](#goals--queries)
    - [Uncurrying](#uncurrying)
    - [Contextual Datalog / Hypothetical Datalog](#contextual-datalog--hypothetical-datalog)
    - [Higher Order Clauses (Harrop)](#higher-order-clauses-harrop)
      - [Stack database / Harrop Datalog / Tentative Datalog](#stack-database--harrop-datalog--tentative-datalog)
    - [Existenial Queries](#existenial-queries)
    - [Universal Quantifier](#universal-quantifier)
    - [Geometry](#geometry)
    - [Categorical Example](#categorical-example)
  - [Typeclass resolution.](#typeclass-resolution)
  - [Borrow Checker](#borrow-checker)
  - [Type checking](#type-checking)
  - [Coinductive or Greatest Fixed Point Datalog](#coinductive-or-greatest-fixed-point-datalog)
    - [DFA Minimization](#dfa-minimization)
  - [CRDTs](#crdts)
  - [MultiSet Semantics](#multiset-semantics)
  - [Access Control Policies](#access-control-policies)
  - [Networks](#networks)
  - [Make](#make)
- [Topics](#topics)
  - [Answer Set Programmng](#answer-set-programmng)
  - [Provenance](#provenance)
  - [Semi Naive Evaluation](#semi-naive-evaluation)
  - [Algebraic Data Types](#algebraic-data-types)
  - [Lattices](#lattices-1)
  - [Subsumption](#subsumption)
    - [Subsumption as a master feature](#subsumption-as-a-master-feature)
      - [Provenance](#provenance-1)
      - [max min](#max-min)
  - [Recurusive Sum and Count](#recurusive-sum-and-count)
      - [Lattices](#lattices-2)
        - [Min/max lattice](#minmax-lattice)
        - [Maybe/Option lattice](#maybeoption-lattice)
        - [Intervals](#intervals)
      - [Widening](#widening)
    - [Dyadic lattice](#dyadic-lattice)
      - [Equivalence relations](#equivalence-relations)
      - [Negation](#negation)
      - [Choice domain](#choice-domain)
  - [Semiring Semantics](#semiring-semantics)
  - [Probability](#probability)
  - [Datalog+- and the chase](#datalog--and-the-chase)
  - [Tabling](#tabling)
  - [Descriptive Complexity and Least Fixed Point Logic](#descriptive-complexity-and-least-fixed-point-logic)
  - [Push based Datalog](#push-based-datalog)
  - [Incremental / Differential Datalog](#incremental--differential-datalog)
  - [Backtracking a Datalog](#backtracking-a-datalog)
- [Implementations](#implementations)
  - [Rel](#rel)
  - [DDlog](#ddlog)
  - [IncA](#inca)
  - [Formulog](#formulog)
  - [Datafrog](#datafrog)
  - [Ascent](#ascent)
  - [Flix](#flix)
  - [dr lojekyl](#dr-lojekyl)
  - [Datafun](#datafun)
  - [QL](#ql)
- [Souffle](#souffle)
  - [intrinsic functors](#intrinsic-functors)
  - [floats](#floats)
  - [Souffle proofs](#souffle-proofs)
  - [Aggregates](#aggregates)
  - [User Defined Functors](#user-defined-functors)
  - [ADTs](#adts)
    - [Contexts are King](#contexts-are-king)
    - [field accessors](#field-accessors)
    - [Vectors](#vectors)
    - [Use ADT instead of autoinc()](#use-adt-instead-of-autoinc)
    - [Record Packing](#record-packing)
  - [Macros](#macros-1)
  - [Components](#components)
  - [Choice Domain](#choice-domain-1)
  - [Negation](#negation-1)
  - [Souffle source](#souffle-source)
- [Resources](#resources-1)
- [class(slotname : f(x,y) , ) :-](#classslotname--fxy----)
  - [building souffle emscripten](#building-souffle-emscripten)

See also notes on:
- Prolog
- Answer Sey Programming
# What is datalog?
Datalog is multifaceted. That's part of what it makes it so cool

From one perspective, it is a database language, a more succinct competitor of sorts to SQL. It has a recursive flavor that makes it easy to express graph and network queries, problems for which you might reach for recursive common table subexpressions and/or triggers in SQL. It is also limited in some respects compared to SQL. SQL allows some imperative commands like `DELETE` or `UPDATE` whereas datalog is typically arranged to never forget information (monotonicity).

From another perspective, it is a relative of the logic programming language Prolog that proceeds by bottom up search instead of top down search. It inherits from this logic programing tradition the fun duality of both an operational and logical reading of the language. Sometimes in this context, the distinction is made from prolog in that datalog only allows atoms and not compound tree-like terms. In practice, many datalog systems do allow this though.

Maybe part of what I like about datalog compared to prolog is
1. complete search strategy
2. logically pure. Kind of like Haskell's laziness kept it pure, Datalog's operation ordering is not obvious after compilation. This means extralogical stuff doesn't fly. Datalog makes control flow explicit. You do not get an implicit goal stack.
3. simple and efficient execution semantics. Pattern match / query over database. Insert new facts accordingly

# What can you do with datalog?
Well, just about anything you can do with ordinary database queries. What do you do with those? I dunno. Search for patterns?

## Getting Started
- [Souffle datalog tutorial](https://souffle-lang.github.io/tutorial), Souffle is an efficient datalog implementation that can be run in an interpreter or compiled to efficient parallel C++ code. It is my go to datalog implementation for most purposes.

## Path Reachability
The #1 example is reachability from edges. It's doofy, but it is a simple recursive query and is my go to for experimenting on a new system or implementing some datalog technique

```souffle
.decl edge(x : number, y : number)
edge(1,2).
edge(2,3).
edge(3,4).

.decl edge(x : number, y : number)
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).
.output edge(IO=stdout)
```

Even in this example there are some things to ask.
What about:
```
path(x,z) :- path(x,y), path(y,z).
```

```
path(x,z) :- path(x,y), edge(y,z).
```

What if we want to express undirected edges. This becomes an equivalence relation
```
.decl path(x : number, y : number) eqrel
// or
path(x,y) :- path(y,x).
```

Many of the applications to follow can be seen as reachability in disguise.

- Connected components of graph
- Equivalence classes
- Transitive closure of a relation
- Ancestors / parents examples
- Finding paths to bad program behavior. Is this bad program state reachable? [Reachability Problem](https://en.wikipedia.org/wiki/Reachability_problem)
- Term rewriting. Terms are vertices, rewrites are edges.
- Regular expressions and paths in finite state machines

Shortest path problems are also of close relation.

### Python

#### Naive

```python

def strata1(edge):
  # path(x,y) :- edge(x,y)
  path = {(x,y) for (x,y) in edge}
  while True:
    newpath = set()
    # path(x,y) :- edge(x,y), path(y,z).
    newpath.update({(x,z) for (x,y) in edge for (y1,z) in path if y == y1})
    # if we have not discovered any new tuples return
    if newpath.issubset(path):
      return path
    else:
      # merge new tuples into path for next iteration
      path.update(newpath)

edge = {(1,2), (2,3), (3,4)}
path = strata1(edge)
print(path)
# {(2, 3), (2, 4), (1, 2), (3, 4), (1, 3), (1, 4)}
```

#### Semi-Naive
Semi-Naive evaluation of corresponds to the intuition that we only need to consider the current frontier of reachable nodes to find the next frontier of reachable nodes. It is easy enough to do by hand to the reachability query, but starts to be kind of annoying for larger more complex queries.

Perhaps you could say this is of some relation to Djikstra's algorithm.

```python

def strata1(edge):
  # path(x,y) :- edge(x,y)
  path = {(x,y) for (x,y) in edge}
  deltapath = path
  while True:
    print(deltapath)
    newpath = set()
    # path(x,y) :- edge(x,y), path(y,z).
    newpath.update({(x,z) for (x,y) in edge for (y1,z) in deltapath if y == y1})
    # if we have not discovered any new tuples return
    if newpath.issubset(path):
      return path
    else:
      # merge new tuples into path for next iteration
      deltapath = newpath.difference(path)
      path.update(newpath)

edge = {(1,2), (2,3), (3,4)}
path = strata1(edge)
'''
{(2, 3), (1, 2), (3, 4)}
{(2, 4), (1, 3)}
{(1, 4)}
'''
```
#### Indexing
Iteration over the full data structure and the filtering is dumb. Query planning.

A simple thing you can do is use perhaps multiple redundant dictionaries rather than sets.

```python
from itertools import groupby
def collect(r):
  res = defaultdict(list)
  for (i,j) in r:
    res[j].append(j)
  return res
# {k: set(g) for (k, g) in groupby(x, key=lambda t: t[0])}

def strata1(edge):
  # path(x,y) :- edge(x,y)
  #default_dict()
  edge_y = {y: list(g) for (y, g) in groupby(edge, key=lambda t: t[1])}
  path = {(x,y) for (x,y) in edge}
  deltapath = path
  while True:
    print(deltapath)
    newpath = set()
    # path(x,y) :- edge(x,y), path(y,z).
    newpath.update({(x,z) for (y,z) in deltapath for (x,_) in edge_y.get(y, [])})
    # if we have not discovered any new tuples return
    if newpath.issubset(path):
      return path
    else:
      # merge new tuples into path for next iteration
      deltapath = newpath.difference(path)
      path.update(newpath)

edge = {(1,2), (2,3), (3,4)}
path = strata1(edge)
```

####  Lattice
```python
# min lattice using && as join
class Min():
  def __init__(self, x):
    self.val = x
  def __and__(self,rhs):
    return Min(min(self.val, rhs.val))
  def __le__(self,rhs):
    return self.val <= rhs.val
  def __ge__(self,rhs):
    return self.val >= rhs.val
  def __add__(self,rhs): # plus is not lattice generic. It just so happens min lat supports it and its monotonic
    return Min(self.val + rhs.val)
  def __repr__(self):
    return repr(self.val)

def strata1(edge):
  # path(x,y) :- edge(x,y)
  path = {(x,y) : Min(1) for (x,y) in edge}
  while True:
    # path(x,y) :- edge(x,y), path(y,z).
    newpath = {(x,z) : d + Min(1) for (x,y) in edge for (y1,z), d in path.items() if y == y1}
    # if we have not discovered any new tuples return
    if all( [ k in path and path[k] <= d for k, d in newpath.items()] ):
      return path
    else:
      # merge new tuples into path for next iteration
      for k,d in newpath.items():
        if k in path:
          path[k] = path[k] & d 
        else:
          path[k] = d

edge = {(1,2), (2,3), (3,4)}
path = strata1(edge)
print(path)
# {(2, 3): 1, (1, 2): 1, (3, 4): 1, (2, 4): 2, (1, 3): 2, (1, 4): 3}
```

Other examples to consider:
- Subsumption
- Semiring
- Provenance

### SQL recursive common table subexpressions
```sql
CREATE TABLE edge(a INTEGER, b INTEGER);
INSERT INTO edge(a,b)
VALUES
    (1,2),
    (2,3),
    (3,4);
SELECT a,b FROM edge;

CREATE TABLE path(a INTEGER, b INTEGER);

-- path(x,z) :- edge(x,y), path(y,z).
WITH RECURSIVE
  path0(x,y) AS
    -- SELECT 1,2
    (SELECT a,b FROM edge UNION SELECT edge.a, path0.y FROM edge, path0 WHERE path0.x = edge.b )
  INSERT INTO path SELECT x,y FROM path0;

SELECT a,b FROM path;
.quit

```

### Naive SQL translation
<https://www.philipzucker.com/tiny-sqlite-datalog/>

Ok, so recursive common table subexpressons are wacky. Also they don't really support all forms of recursion.
There is a way to translate a single application of a rule to a SQL statement.

```sql
CREATE TABLE edge(a INTEGER, b INTEGER, PRIMARY KEY (a,b));
INSERT OR IGNORE INTO edge(a,b)
VALUES
    (1,2),
    (2,3),
    (2,3),
    (3,4);
SELECT a,b FROM edge;

CREATE TABLE path(a INTEGER, b INTEGER, PRIMARY KEY (a,b));

-- path(X,Y) :- edge(X,Y).
INSERT OR IGNORE INTO path SELECT DISTINCT edge0.a, edge0.b   -- the head of the rule gives the insert and select fields  
FROM edge as edge0; -- The body of the rule gives FROM and WHERE  

-- path(x,z) :- edge(x,y), path(y,z).
INSERT OR IGNORE INTO path SELECT DISTINCT edge0.a, path0.b   -- the head of the rule gives the insert and select fields  
FROM edge as edge0, path as path0
WHERE edge0.b = path0.a; -- The body of the rule gives FROM and WHERE  

SELECT *,rowid FROM path; -- there is an implicit row id. This can conceivably be used as a timestamp for smieniave
SELECT MAX(rowid) FROM path;
SELECT MAX(rowid) FROM edge;
```
#### Seminaive
Either maintain explicit delta relations, or use timestamp tricks.
Create a vector timestamp
```sql
CREATE TABLE edge(a INTEGER, b INTEGER, PRIMARY KEY (a,b));
INSERT OR IGNORE INTO edge(a,b)
VALUES
    (1,2),
    (2,3),
    (2,3),
    (3,4);
SELECT a,b FROM edge;

CREATE TABLE path(a INTEGER, b INTEGER, PRIMARY KEY (a,b));
INSERT OR IGNORE INTO path SELECT DISTINCT edge0.a, edge0.b   -- the head of the rule gives the insert and select fields  
FROM edge as edge0; -- The body of the rule gives FROM and WHERE  


SELECT * FROM path;
CREATE TABLE trans_rule(edge_time INTEGER, path_time INTEGER); -- the vector timestamp
INSERT INTO trans_rule VALUES (0,0);

INSERT INTO trans_rule SELECT MAX(edge.rowid), MAX(path.rowid) FROM edge, path;

SELECT * FROM trans_rule;

```
`WHERE edgo0.rowid > prevedfe OR path0.ro

```python


class Rule():
  """
  Rule tracks the timestamps of the relations it depends on. At least one new tuple must appear to possibly derive a new fact.
  """
  def __init__(self, head : str, selects, froms , where="TRUE"):
    """
    head is a table name
    selects is string of comma separated sql expressions. It goes in a select clause
    froms is a list of tuples of (table_name, row_binder_name)
    where is a filtering SQL expression
    """

    #select_str = ", ".join(selects)
    from_str = ", ".join(f"{table} AS {row}" for table,row in froms)
    seminaive_filter_str = " OR ".join( f"{row}.rowid > ?" for _,row in froms ) 
    self.sql = f"""
    INSERT OR IGNORE INTO {head} SELECT DISTINCT {selects}  -- head
    FROM {from_str}  -- body
    WHERE ({where})  -- body
    AND ({seminaive_filter_str})  -- seminaive
    """

    self.timestamp = tuple(-1 for _ in froms)
    select_str = ", ".join(f"MAX({row}.rowid)" for _,row in froms)
    self.ts_query = f""" 
    SELECT {select_str} FROM {from_str} 
    """
    

    self.froms = froms
    self.where = where
    self.head = head
    self.selects = selects
  def update_timestamp(self,cur):
    self.timestamp = cur.execute(self.ts_query).fetchone()

  def execute(self,cur):
    ts = self.timestamp # the last time this rule was run
    print(self.sql, self.timestamp)
    self.update_timestamp(cur) # update timestamp to now
    cur.execute(self.sql, ts)  # 

  def __repr__(self):
    from_str = ", ".join(f"{table}({row})" for table,row in self.froms)
    return  f"{self.head}([{self.selects}]) :- {from_str}, {self.where}."


def dump_db():
  print("path", cur.execute("select * from path").fetchall())
  print("edge", cur.execute("select * from edge").fetchall())

def fixpoint(cur, ruleset):
  done = False
  while not done:
    done = True
    dump_db()
    for rule in ruleset:
      old_ts = rule.timestamp 
      rule.execute(cur)
      done &= old_ts == rule.timestamp
      print(old_ts, rule.timestamp)

    

def create_table(cur, name, *fields):
  fields = ", ".join(fields)
  sql = f"CREATE TABLE {name}({fields}, PRIMARY KEY ({fields}))"
  print(sql)
  cur.execute(sql) # Set semantics

import sqlite3
#import duckdb
con = sqlite3.connect(":memory:")
cur = con.cursor()
create_table(cur,"edge", "a", "b")
create_table(cur,"path", "a", "b")

base = Rule("path", "edge0.a, edge0.b",
                     [("edge", "edge0")])
trans = Rule("path", "edge0.a, path0.b",
                     [("path", "path0"), ("edge", "edge0")],
                     where="edge0.b = path0.a")

print(trans.sql)



cur.executemany("insert into edge values (?, ?)", [(1,2), (2,3), (3,4)])
base.execute(cur)

dump_db()
fixpoint(cur,[trans])

dump_db()
trans.execute(cur)
dump_db()
print(trans)
print(trans.timestamp)
```
Langston pointed out that metadata could be stored in a different table that you join in when you need it. You just need defaults if it isn't there.

Retaining the timestamp _sequence_ is a form of lightweight provenance. It tells you exactly which tuples were derived using this rule.

For every iteration, there are 3 timestamps at play. The last time the rule was run, the timestamp of the db before the rule, and the timestamp after the rule.

#### Lattices
Store either nullable lattice value at end
Or in separate table. Every rule needs to deal with lattice value? That's annoying.
```sql
create table edge(a,b,w, unique (a,b));
create table path(a,b,w, unique (a,b));

INSERT INTO edge values (1,2,1), (2,3,1), (3,1,1);
INSERT INTO path select * from edge;

INSERT INTO path select (edge.a, path.b, edge.w + path.w) from edge,path where edge.b = path.a 
ON CONFLICT UPDATE SET w = min(w, excluded.w); -- https://www.sqlite.org/lang_UPSERT.html

```


### Ocaml
#### Naive
```ocaml
#use "topfind";;
#require "core_kernel ppx_jane";;
open Core_kernel
let add_list s l = List.fold l ~init:s ~f:Set.add

module Edge = struct
  module T = struct type t = int * int [@@deriving compare,sexp] end
  include T
  include Comparator.Make(T)
end

let edge = [(1,2); (3,4); (2,3)]
let path =
  let (let* ) x f = List.bind x ~f in
  let rec strata1 path0 = 
      (* Initialize new *)
      let hpath = Set.empty (module Edge) in
      let path = Set.to_list path0 in
      (* Each rule. Order doesn't matter *)
      (* path(x,z) :- edge(x,y), path(y1,z), y1 = y. *)
      let hpath = add_list hpath (
        let* (x, y) = edge in
        let* (y1,z) = path in
        if y1 = y then [(x,z)] else []
      ) in
      (* Check termination *)
      if (Set.is_subset hpath ~of_:path0) then
          path0 (* done*)
      else strata1 (Set.union path0 hpath)
  in
  (* path(x,y) :- edge(x,y). *)
  let path = (Set.of_list (module Edge) edge) in
  let path = strata1 path in
  path


let () = List.iter (Set.to_list path) ~f:(fun (x,y) -> printf "%d %d; " x y)
```
### Rust
Probably using HashSet is not a great idea.

```rust
use std::collections::HashSet;
fn main(){
  let edge : Vec<(usize,usize)>= vec![(1,2), (2,3), (3,4)];
  let mut path  : HashSet<(usize,usize)> = edge.clone().into_iter().collect();
  let mut dpath : HashSet<(usize,usize)> = edge.clone().into_iter().collect();
  while !dpath.is_empty() {
    let mut newpath : HashSet<(usize,usize)> = HashSet::new();
    for (i,j) in &edge{
      for (j1,k) in &dpath{
        if j == j1 {
            newpath.insert((*i,*k));
        }
      }
    }
    dpath = newpath.difference(&path).map(|(i,j)| (*i,*j)).collect();
    dbg!(&dpath, &path, &newpath);
    for p in newpath.drain(){
      path.insert(p);
    }
  }


}
```


### Magic Set
Do we need all node reachability? What if we are only interested in 
`path(1,4)` or we only want all nodes reachable from 1 `path(1,X)`. Or what if we want strongly connected components
`path(X,Y), path(Y,X)`

It feels like we should be able to do something more limitted and efficient in the context of these queries and this is the case.


How do we write this query raw in other systems?


## Program Analysis


Points to analysis tutorial
Doop

See 
- Nielson and Nielson
- Souffle tutorial
- 

It is common to reduce your program into some kind of graph like form. One way to do this is to lbael program points (these may be machine addresses, stmt identifiers, or maybe line numbers) and state which points can follow other points in a relation `next(l1 : stmt, l2 : stmt)` . You may also want to collect statements into blocks.

You will also need to summarize the effects of the constructs of your language into a relational form. 
Some possibilities
- In `stmt_foo : x = 3 + 4;` `x` is written to. `writes(l:stmt, x:var)`
- `reads(l:stmt, x:var)`




### Evaluation

What could be more primitive than evaluating a concrete state?
There is still some interesting a subtlely. We need names to seperate apart runs. In skolem thinking, runs are labelled by an initial state record or map. Perhaps if you start a run at another point, the combo of the initial state and program point.

```souffle
.type Stmt = Move {x : symbol, y : symbol}
.type Prog = [s : Stmt, tl : Prog]
.type Ctx = Prog
#define MYPROG [$Move("x", "y"), [$Move("y", "z"), nil]]
#define ENDCTX [$Move("y", "z"), [$Move("x", "y"), nil]]
.type pt = [todo : Prog, hist : Ctx] // program point
#define START [MYPROG, nil]
#define END   [nil, ENDCTX]

.type run <: symbol
.type value <: number
.decl var_store(r : run, p : pt, x : symbol, v : value)
var_store("run0", START, "x", 3).
var_store("run0", START, "y", 4).
var_store("run0", START, "z", 5).

var_store("run1", START, "x", 657).
var_store("run1", START, "y", 756).
var_store("run1", START, "z", 324).





var_store(run , [todo, [stmt, ctx]], x, v) :- var_store(run, [[stmt, todo], ctx], x, v), 
    stmt = $Move(y,_z), x != y.
var_store(run , [todo, [stmt, ctx]], x, v) :- var_store(run, pt, x, _), 
    pt = [[stmt, todo], ctx],
    stmt = $Move(x,z), var_store(run, pt, z, v).

.output var_store(IO=stdout) 

```

You need a notion of first class map, but if you know at souffle compile time how many you need, you can name them. Then no problem. Or perhaps at a different strata is enough?


```souffle

.type AExpr = Add {x : AExpr, y : AExpr} | Lit {n : number} | Var {x : symbol}

.decl aexpr(e : AExpr)
aexpr(x), aexpr(y) :- aexpr($Add(x,y)).

// can have seperate env relation if you'd like
//.decl env(name : symbol, x : symbol, v : number)
// eval(r, $Var(x), v) :- aexpr($Var(x)), env(r, x, v).


.decl eval(name : symbol, e : AExpr, v : number)

eval(r, e, vx + vy) :- aexpr(e), e = $Add(x,y), eval(r,x,vx), eval(r,y,vy).
eval(r, e, n) :- aexpr(e), e = $Lit(n), runs(r).

.decl runs(name : symbol)
runs(r) :- eval(r,_,_).


aexpr($Add($Var("x"),$Add($Lit(1),$Lit(2)))).
eval("run0", $Var("x"), 42).

.output eval(IO=stdout)


```

### Constant Propagation
Constant propagation is kind of like a partial evaluation. The evaluator above just stops if it can't progress. In a sense it is already a constant propagator.

```
.type AExpr = Lit {n : number} | Var {x : symbol}
.type Stmt = Move {x : symbol, e : AExpr}
```

```
.type tid <: symbol
.type blk = [tid : tid, data : defs, ctrl : ]
.type def = [tid : tid, lhs : var, rhs : exp]
.type defs = [hd : def, tl : defs]
.type jmp = [tid : tid, cnd : exp, dst : , alt : ]
.type jmp_kind = 
  Call {} 
  | Goto {}
  | Ret {} 
  | Int {}

.type sub = [tid : tid, name : symbol, args : args, blks : blks]


.decl blk( tid , nstmts : unsigned, )


```

Purely functional constant propagation.

```souffle

.type AExpr = Add {x : AExpr, y : AExpr} | Lit {n : number} | Var {x : symbol}

.decl aexpr(e : AExpr)
aexpr(x), aexpr(y) :- aexpr($Add(x,y)).

.decl const(e : AExpr, c : number)
const(t,n ) :- aexpr(t) , t =  $Lit(n).
const(t,n1 + n2) :- aexpr(t), t = $Add(x,y), const(x,n1), const(y,n2).

.decl reduced(t : AExpr, t1 : AExpr)
reduced(t, $Lit(n)) :- aexpr(t), const(t, n).
reduced(t, $Add(x1,y1) ) :- aexpr(t), !const(t,_), t = $Add(x,y), reduced(x, x1), reduced(y,y1). 
reduced(t, t) :- aexpr(t), t = $Var(_n).

aexpr($Add($Var("x"),$Add($Lit(1),$Lit(2)))).

.output reduced(IO=stdout)

/*
reduced
t       t1
===============
$Var(x) $Var(x)
$Lit(1) $Lit(1)
$Lit(2) $Lit(2)
$Add($Lit(1), $Lit(2))  $Lit(3)
$Add($Var(x), $Add($Lit(1), $Lit(2)))   $Add($Var(x), $Lit(3))
===============
*/

```
### Symbolic Evaluation
Inside a block we can symbolically execute to inline all definitions.
(We can also do something in multiple blocks, but let's stick to this for now.)

```souffle
.type AExpr = Add {x : AExpr, y : AExpr} | Lit {n : number} | Var {x : symbol}
.type Stmt = Move {x : symbol, e : AExpr}
.type Prog = [s : Stmt, tl : Prog]
.type Ctx = Prog
.type pt = [todo : Prog, hist : Ctx] // program point

.type var <: symbol
.decl aexpr(e : AExpr)
aexpr(e) :- eval_e(_,e).

.decl eval_e(x : AExpr, e : AExpr)
eval_e($Var(z), $Add(vx,vy)) :- eval(_, z, $Add(x,y)), eval_e(x, vx), eval_e(y,vy).

.decl eval( p : pt, x : var, e : AExpr)

eval_e(t, $Add(vx,vy)) :- aexpr(t), t = $Add(x,y), eval_e(x, vx), eval_e(y,vy).


// eval_e(ctx, $Var("x"), v) :- eval([todo,ctx], x, v).
// Hmm. This sucks. Why does this suck?
// Having both recursvie and imperative code is annoying
// We basically need to double our work
// Or is it not having SSA which sucks.

/*
eval([todo, [stmt, ctx]], x, v) :- eval([[stmt, todo], ctx], x, v), 
    stmt = $Move(y,_z), x != y.
eval([todo, [stmt, ctx]], x, vz) :- eval(pt, x, _), 
    pt = [[stmt, todo], ctx],
    stmt = $Move(x,z), eval_e(z, vz).
*/

.decl pts(p : pt)
pts([todo, [stmt, ctx]]) :- pts([[stmt, todo], ctx]).

eval_e(y, vz) :- pts([[stmt, todo], ctx]), 
    stmt = $Move(y,z), eval_e(z, vz).

// Indeed the order of the statements doesn't matter anymore.

#define MYPROG [$Move("x", $Add($Var("y"), $Lit(1))), [$Move("z", $Var("x")), nil]]
#define START = [MYPROG,nil]
pts(START).


.output eval(IO=stdout) 

```



Inlining of SSA block:

```souffle


.type AExpr = Add {x : AExpr, y : AExpr} | Lit {n : number} | Var {x : var}
.decl live_in(v : var)
.decl live_out(v : var)

.type var <: symbol 
.decl mov(x : var, e : AExpr)

.decl eval(x : AExpr, e : AExpr)
eval($Var(v), $Var(v)) :- live_in(v).

.decl aexpr(e : AExpr)
aexpr(e) :- mov(_, e).
aexpr(x),aexpr(y) :- aexpr($Add(x,y)).

eval(t, $Add(vx,vy)) :- aexpr(t), t = $Add(x,y), eval(x, vx), eval(y,vy).
eval($Var(x), e1) :- mov(x, e), eval(e, e1).

//explicit live_in
//live_in("y").
// implicit live_in
live_in(v) :- aexpr($Var(v)), !mov(v, _).

mov("x", $Add($Var("y"),$Var("y"))).
mov("z", $Add($Var("x"),$Var("x"))).

.output eval(IO=stdout)

// block summary
.decl summary(x : var, e : AExpr)
summary(x, e) :- live_out(x), eval($Var(x), e).

```


### Reaching Definitions
<https://souffle-lang.github.io/examples#defuse-chains-with-composed-types>

```
def_use(x : var, def : stmt, use : stmt) //reaches?
def(x: var , label : stmt)
use(x : var, label : stmt)
```

Variables becomes labeled by both name and program point at which they were defined.
Really that is unnecessary

```

.decl defpt(x : var, p : pt)

```




### Liveness
Variables that will be needed on at least one path
A backwards analysis
Union

### Points To

https://yanniss.github.io/cclyzer-sas16.pdf 
https://github.com/GaloisInc/cclyzerpp 
https://github.com/plast-lab/cclyzer
https://github.com/souffle-lang/souffle/pull/2231 
https://galoisinc.github.io/cclyzerpp/implementation.html#unification-based-analysis-via-subsumption-and-choice 
https://github.com/souffle-lang/souffle/issues/2302 

### Available Expressions 
[Lecture notes on static analysis in datalog](https://www.cse.psu.edu/~gxt29/teaching/cse597s19/slides/06StaticaAnalysisInDatalog.pdf)
https://courses.cs.washington.edu/courses/csep501/18sp/lectures/T-dataflow.pdf

The expression is computed and/or the connection between expression and store state is not severed by subsequent write. on every path 
Not that available expressions _does not_ mean expression is available.
```
x = a + b
x = 0
```
AE says `a+b` is available at the ned of this snippet. So it's a bit subtler what AE means. It means that with a little fiddling the expression _could be_ available.


Every path means we need an intersection. Datalog does unions more naturally, so we need to work wth the inverse relation notavailable. The intersection of available is the union of notavailable
 
Program
```
start:
  x = readinput
  a = readinput
  b = readinput
  br x, l1, l2
l1:
  z = a + b
  br l3
l2:
  z = b + a
  br l3
l3:
  print a + b // if a + b is available we don't have to recompute
```

```souffle


.type blk <: symbol 
.type Expr  = Add {x : Expr, y : Expr}| Var {x : symbol}
.decl gen(blk : blk, e : Expr)

gen("l1" , $Add($Var("a"),$Var("b"))).
//gen("l2" , $Add($Var("a"),$Var("b"))). // uncomment to see a + b in l3 avail expr
gen("l2" , $Add($Var("b"),$Var("a"))).

.decl expr(e : Expr)
expr(e) :- gen(_,e).
expr(a), expr(b) :- expr($Add(a,b)).

.decl var(v : symbol)
var("z").
var("x").
var("b").
var("a").

.decl free(v : symbol, e : Expr)
free(x, e) :- expr(e), e = $Var(x).
free(x, e) :- expr(e), e = $Add(a,b), (free(x,a); free(x,b)).


.decl kill(b : blk, e : Expr)
kill("start",e ) :- expr(e), (free("x", e) ; free("a", e) ; free("b", e)).
kill("l1",e ) :- expr(e), free("z",e).
kill("l2",e ) :- expr(e), free("z",e).

//?x + ?y <-> ?y + ?z.
/*
gen(l,e2) :- gen(l,e1), eq(e1,e2).
but don't do the same for kill? This feels like cheating.
We can supercharge gen but we also supercharge kill. Eh?
Well maybe not.
*/


.decl next(blk1:blk, blk2:blk)
next("l1","l3").
next("l2","l3").
next("start","l1").
next("start","l2").

.decl label(b : blk)
label(l) :- next(l,_) ; next(_,l).

.decl notavail_entry(b : blk, e : Expr)
.decl notavail_exit(b : blk, e : Expr)
notavail_entry("start", e) :- expr(e).

notavail_exit(l, e) :- (notavail_entry(l, e) ; kill(l,e)), !gen(l, e).
notavail_entry(L2,e) :- notavail_exit(L1,e), next(L1,L2).

.decl avail(l : blk, e  : Expr)
avail(l,e) :- label(l), expr(e), !notavail_exit(l,e).
.output avail
```

So what do I need to do to extend this to equivalent expressions?

### Intersection
De morgan intersections into unions.

```souffle
.type var = symbol
.type node = number
.decl edge(x : node, y : node)
.decl avail(x : node, v : var)
.decl vars(v : var)
.decl nodes(x : node)
vars("x"). vars("y").
avail(1,"x").
nodes(n) :- edge(n,_); edge(_,n).
edge(1,2).edge(1,3).edge(2,4).edge(3,4). // edge(5,4).
/* The graph:
    1
  /   \
  2   3  
  \   /
    4    */


// Bounded forall method.
// avail_cnt is a running count of predecessor nodes for which v is available.
.decl avail_cnt(x : node, prev : node, v : var, n : number)
avail_cnt(x, p, v, 1) :- nodes(x), p = min p1 : {edge(p1,x)}, avail(p,v).
avail_cnt(x,p2, v, n + 1) :- edge(p1,x), avail_cnt(x,p1,v,n),
                          edge(p2,x), p1 < p2, avail(p2,v).

// If count of all predecessors with avialable equals total incoming edges
// then all of them have it available
avail(x, v) :- avail_cnt(x, _, v, c), c = count : { edge(_,x) }.


// Method 2. De Morgan the intersection
.decl not_avail(x : node, v : var)
not_avail(1, "y").
not_avail(x,v) :- not_avail(p,v), edge(p,x).
.output not_avail(IO=stdout)

```




### Very Busy Expressions
Expressions that are needed on every path
Intersection


### Zippers For Program Points
It is possible to generate program points from the Imp AST via using zippers

```souffle
.type Expr = Lit { x : number }
           | Var { x : symbol }
           | Add {e_1 : Expr, e_2 :Expr}
.type Stmt = Set { x : symbol, e : Expr}
           | Seq {s_1 : Stmt, s_2 : Stmt}
.type StmtHole = LSeq {s : Stmt} | RSeq {s : Stmt}
.type Zipper = Cons { hd : StmtHole , rest : Zipper} | Nil {}
.type Label =  [ctx : Zipper, stmt : Stmt] 
// Do I need this? .decl label(; : Label, ctx : Zipper, stmt : Stmt)
.decl prog(s : Stmt)

.decl stmt(ctx : Zipper, s : Stmt)
stmt($Nil(), s) :- prog(s).
stmt($Cons($LSeq(r), ctx), l), stmt($Cons($RSeq(l) , ctx), r) :- stmt(ctx, $Seq(l,r)).

.decl expr(ctx : Zipper, e : Expr)
expr(ctx, e) :- stmt(ctx, $Set(_,e)).
expr(ctx, y), expr(ctx, x) :- expr(ctx, $Add(x,y)).

.decl next(ctx : Zipper, s : Stmt, ctx2 : Zipper, s2 : Stmt)

next($Cons($LSeq(r), ctx), l, $Cons($RSeq(l), ctx), r) :- stmt(ctx, $Seq(l,r)).
next($Cons($RSeq(l), ctx), r, ctx2, s2) :- next(ctx, $Seq(l,r), ctx2, s2).

prog(
  $Seq($Set("x", $Lit(0)),
  $Seq($Set("y", $Add($Var("x"),$Lit(1))),
       $Set("x", $Var("y"))
      ))
).


.decl hasvar(e : Expr, x : symbol)
hasvar($Var(v), v) :- expr(_, $Var(v)).
hasvar($Add(x,y), v) :- expr(_,$Add(x,y)), (hasvar(x,v) ; hasvar(y,v)).
```

From another perspective, this is a relative of "need sets" and magic sets.
The zipper here represents the implicit stack of an ordinary Imp interpreter. We also may need a first class map to actually run programs precisely
The transformation foo(firstclassmap) -> foo(i), map(i, k,v) is lossy in the presence of multiple executions. From an abstract interp persepctive this is not so bad.

<https://souffle-lang.github.io/examples#context-sensitive-flow-graph-with-records>


### Dominators
https://pages.cs.wisc.edu/~fischer/cs701.f07/lectures/Lecture20.pdf
https://twitter.com/taktoa1/status/1548109466620424193?s=20&t=G28jQnYTSb1KEI--BWennw
https://codeql.github.com/codeql-standard-libraries/cpp/semmle/code/cpp/controlflow/Dominance.qll/module.Dominance.html

Dominators probably require first class sets. Bitsets are a very convenient one for small sets. Hmm no I guess not. The turning intersection into negated union trick works better.

```souffle

.type blk <: number
.decl next(x : blk, y : blk)


// .type bitset <: number
// hmm. 
// .decl dom(x : blk, s : bitset)
// dom(x, bset) :- inter bset : { next(prev, blk), dom(prev, bset) } .

next(0,1).
next(1,2).
next(2,3).
next(1,4).
next(4,3).

/*
  0
  |
  1
 / \
2   4
\  /
  3

*/

.decl blks(n : blk)
blks(x) :- next(x,_);next(_,x).

// implicitly we're talking about the exit of the block

.decl not_dom(n : blk, m : blk)
// start node is not dominated by everything
not_dom(0, blk) :- blks(blk), blk != 0.

not_dom(here, z) :- next(prev, here), not_dom(prev, z), z != here.

.decl dom(n : blk, m : blk)
dom(n,m) :- blks(n), blks(m), !not_dom(n,m).

.output dom(IO=stdout)

```

### Forall Emulation
https://www.cse.psu.edu/~gxt29/teaching/cse597s19/slides/06StaticaAnalysisInDatalog.pdf

[bicycle problem](https://github.com/souffle-lang/souffle/discussions/2256)

```souffle
.decl bicycle(id: symbol, tire_id: symbol)
bicycle("B1", "T1").
bicycle("B1", "T2").
bicycle("B2", "T3").
bicycle("B2", "T4").

.decl tire(id: symbol, condition: symbol)
tire("T1", "Good").
tire("T2", "Good").
tire("T3", "Good").
tire("T4", "Flat").

.decl safeBicycle(id: symbol)
// Only safe if every tire in good condition
// safeBicycle(id) :- bicycle(id, tid), tire(tid, "Good").

// Should only output "B1"
.output safeBicycle

// Only safe if every tire in good condition
safeBicycle(id) :- bicycle(id, _), !unsafeBicycle(id).

// Should only output "B1"
.output safeBicycle

.decl unsafeBicycle(id: symbol)
unsafeBicycle(id) :- bicycle(id, tid), tire(tid, "Flat").
```

### Doop
I should probably know more about this but I don't.
Java.


### Datalog Diassembly / Decompilers
- [grammatech - Datalog Disassembly](https://www.usenix.org/system/files/sec20fall_flores-montoya_prepub_0.pdf)
- [gigahorse](https://github.com/nevillegrech/gigahorse-toolchain) - decompiler for smart contracts based on souffle
- Dr lojekyll [dr. disassembler](https://github.com/lifting-bits/dds) and blog post
- [securify2](https://github.com/eth-sri/securify2/tree/71c22dd3d6fc74fb87ed4c4118710642a0d6707e/securify/staticanalysis/souffle_analysis)

```souffle
.type reg = R0 {} | R1 {} | R2 {}
.type insn = Mov {dst : reg, src : reg}
           | Imm {dst : reg, v : number}
           | ILoad { dst : reg, src : number }
           | IStore { dst : number, src : reg}
           | Add {dst : reg , src : reg}
           | Jmp {dst : number}
           | BZ { c : reg, dst : number }
           | IJmp {dst : reg}
           | Store {dst : reg, src : reg}
           | Load {dst : reg, src : reg}

.decl insns(addr : number, i : insn)
.decl next(addr: number, addr2 : number)

next(addr, addr+1) :- insns(addr, $Mov(_,_)).
next(addr, addr2) :- insns(addr, $Jmp(addr2)).

// if can have exactly one value. Constant propagation
.decl oneval(addr: number, r : reg, v : number)
oneval(addr+1, r, v) :- insns(addr, Imm(r,v)).
oneval(addr+1, r1, v1 + v2) :- insns(addr, Add(r1,r2)), oneval(addr,r1, v1), oneval(addr, r2,v2).
// Things mostly just propagate.

.decl isdata(addr : number)
.decl iscode(addr : number)

// insns(addr, @dis(bits)):- iscode(addr), raw(addr, bits).

```



What makes disassembly hard?
data and code can be intermixed.

There is a strata of different assembly instructions to consider

- straight line code: mov, binop, unop, ILoad and IStore, Jmp
- BZ becomes more complex. This is still essentialy a CFG though
- indirect jumps IJmp makes things very hard. Part of the goal of disassembly is undertsnading these
- Store and Load makes aliasing analysis difficult.

Registers vs memory. What difference does it make? It doesn't really (for analysis purposes) until you start to have indirect accesses. The other real difference between registers and memory is speed. You typically don't have indirect register access in a cpu?

### Bap

Should I use `symbol` to represent simple enum adts? They are syntactically a bit more convenient. It would be a bit more uniform to use souffle adts.

[bap in souffle](https://github.com/philzook58/bap-notes/blob/main/souffle/bap.dl)


```souffle



// http://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Bil/index.html#type-exp

.type cast <: symbol
.type var <: symbol // need more info? Size? id?
.type binop <: symbol
.type unop <: symbol

.type exp =
    Load { mem : exp, addr : exp , endian : endian, size: size}
  | Store {}
  | BinOp { op : binop , a : exp, b : exp}
  | UnOp { op: unop, a : exp}
  | Var {v : var}
  | Int {i : unsigned} // possibly with bitwidth?
  | Cast {} // TODO
  | Let {v : var, e : exp, b : exp}
  | Unknown {s : symbol, t : typ}
  | Ite {cond : exp, then : exp, else : exp}
  | Extract {lo : unsigned, hi : unsigned, e : exp}
  | Concat {a : exp , b : exp}

.type typ =
    Imm {width : unsigned}
  | Mem {a : addr_size, s : size}
  | Unk {}

.type stmts = [hd : stmt, tl : stmts]
.type stmt =
    Move { v: var, e : exp}
  | Jmp {e : exp}
  | Special {s : symbol}
  | While {e : exp, s : stmts}
  | If {c : exp, t : stmts, e : stmts}
  | CpuExn {n : unsigned}


.type endian <: symbol
// http://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Size/index.html#type-all
// 8 - 256
.type size <: unsigned
.type addr_size <: unsigned 

// helpers
#define ADD(x,y) $BinOp("Add", x, y)

#define LittleEndian "LittleEndian"
#define BigEndian "BigEndian"


#define BINOP(op, a, b, c) (op = "Add", c = a + b; op = "Sub", c = a - b ; ... )



// d.decl insn(addr : unsigned, sem : stmts)
// flatten()
// .decl may_fallthrough(From, To)
// .decl must_fallthrough(From, To)
//
```

Does / what does bap's C api look like? https://github.com/BinaryAnalysisPlatform/bap-bindings
If we want to do specualtive disassembly, this might be the way to go.
If we want to just analyze what bap already finds, we can print souffle database using a plugin.

[alias analysis for disassembly](http://reports-archive.adm.cs.cmu.edu/anon/2006/CMU-CS-06-180R.pdf)
[Holmes: Binary Analysis Integration Through Datalog](https://kilthub.cmu.edu/articles/thesis/Holmes_Binary_Analysis_Integration_Through_Datalog/7571519)


use pcode?

### Resources
- [Using Datalog for Fast and Easy Program Analysis](https://yanniss.github.io/doop-datalog2.0.pdf) A Doop paper
- [Unification based pointer analysis](https://github.com/souffle-lang/souffle/pull/2231) "Steensgaard style" vs Anderson style
- [hash consed points to sets](https://yuleisui.github.io/publications/sas21.pdf)
- [datalog for static analysis](https://prl.ccs.neu.edu/blog/static/datalog-for-static-analysis.pdf)
- 
- 
- [graspan](http://web.cs.ucla.edu/~wangkai/papers/asplos17)
- [Using Datalog with Binary Decision Diagrams for Program Analysis bddbddb](https://people.csail.mit.edu/mcarbin/papers/aplas05.pdf)

- [codeql](https://codeql.github.com/docs/ql-language-reference/about-the-ql-language/) semmle


## First Class Sets & Reflection

Groupby is an interesting construct. It's useful for parallelization because you can toss each group onto one node of computation.

If you have first class sets, it is much eaiser to achieve certain kinds of summarization data that need globals views on the relation.


### BitSets
```souffle
.type bitset <: unsigned
// Operations
#define BOT 0x0
//assuming 32 bit
#define TOP  0xFFFFFFFF 
#define SING(x) (0x1 bshl x)
#define UNION(x,y) (x bor y)
#define ADD(x,set) UNION(SING(x), set)
#define INTER(x,y) (x band y)
#define COMP(x) (TOP bxor x)
#define DIFF(x,y) (x bxor INTER(x,y))

// Predicates
#define ISEMPTY(x) (x = 0)
#define NONEMPTY(x) (x != 0)
#define SUBSET(x,y) ISEMPTY(DIFF(x,y))
#define ELEM(x, set) NONEMPTY(INTER(SING(x), set))

.decl test(l : symbol, b : bitset)
test("ex1", SING(1)).
test("ex1", SING(2)).
test("ex2", DIFF(set, SING(2))) :- test("ex1", set).
test(l,UNION(s1,s2)) :- test(l, s1), test(l,s2).
test(l,s1) <= test(l,s2) :- SUBSET(s1,s2).

.output test(IO=stdout)

```
```
#define FLAG0 0x0
#define FLAG1 0x2
#define FLAG2 0x4
```


A different kind of bitset. Strings are insanely versatile

hmm. I can't get char codes easily

string based vectors. Why not just use a list?
```souffle

.decl test(x : symbol, s : number)
test("x", as(c,number)) :- c = "x".
.output test(IO=stdout)



```



 
```souffle
.decl test(x : symbol, s : number)
test(to_string(32434901), to_number("000045")) :- true.
.output test(IO=stdout)

.decl zeropad(n : number, z : symbol)
zeropad(0, "").
zeropad(n+1, cat("0", z) ) :- zeropad(n, z), n <= 10. 

// Max32 = 4294967296
#define DIG32 10

#define INDEX(x, i)  substr(x, i * DIG32, DIG32)
#define PUSH(xs, x)  cat(xs, x)
#define SLICE(xs, i, j)   substr(xs, i * DIG32, j * DIG32)
#define PAD(x, px)   (tx ## x = to_string(x), zeropad(DIG32 - strlen(tx ## x), zp ## x), px = cat(zp ## x, tx ## x))

// test(padx, 42 ) :- (tx42 = to_string(42), zeropad(10 - strlen(tx42), zp42), padx = cat(zp42, tx42)).

test(padx, to_number(padx) ) :- PAD(42, padx).


```
Interesting metalevel skolemization. Very hacky



#### Bitset reflection
Can I use bitsets to reflect? Yes. Up to 32 entries allows.
More if we use records of bitsets, n  * 32 element sets.


```souffle
.type bitset <: unsigned
// Operations
#define SING(x) (0x1 bshl x)
#define UNION(x,y) (x bor y)
#define INTER(x,y) (x band y)
#define DIFF(x,y) (x bxor INTER(x,y))

// Predicates
#define ISEMPTY(x) (x = 0)
#define NONEMPTY(x) (x != 0)
#define SUBSET(x,y) ISEMPTY(DIFF(x,y))
#define ELEM(x, set) NONEMPTY(INTER(SING(x), set))

.type findomain = A {} | B {} | C {}
.decl foo(a : findomain)
foo($A()).
foo($C()).

// reflection
.decl refl_foo(a : bitset)
refl_foo(SING(as(x, unsigned))) :- foo(x).
refl_foo(UNION(s1,s2)) :- refl_foo(s1), refl_foo(s2).
refl_foo(s1) <= refl_foo(s2) :- SUBSET(s1,s2).

// reify
.decl reify_foo(x : findomain)
reify_foo(as(x, findomain)) :- x = range(0,3), refl_foo(s), ELEM(x,s). // could make range 32 without hurting anything
.output reify_foo(IO=stdout)
.output refl_foo(IO=stdout)
```

Could we perhaps use sparse bitsets? If there are universes of 2^n we can encode into a record with unsigned representing if we a priori know limit of sparsity.
Possibly better is to use a lattice approximate reflection. Like factored over approximation.

```
factor_reflect(sing(arg1), sing(arg2)) :- rel(arg1, arg2).
```
The cartesian product of these sets over approximates `rel`. Rather reminds me of relational division.

Speculative idea: Could have reflection as a true primitive. User defined functors? Don't really get access to relations. 
We need persitent set data structures if we want to do this. Garbage collection? We could mark them as special reflective relations `.decl foo() reflective`
`reflect("rel_foo")`
Something like this.
```
rel reflect(string name){
   program.get_relation(name)
}
```
Oh, user defined functors woould support this `store(k,v, oldmap)` or `add(v, oldset)`. It would be nice if we could somehow just make sets pointers to souffle's structure themselves, or projections thereof? I mean what can you really do in that case?


Reflection by grouping.
```
reflect(group : unsigned, bitset)
reflect(n / 32, sing(n % 32)) :- rel(n)
```
Can the process be iterated?

We could build a binary search tree ADT and reflect to that. What does that really do though? Uhhh. Yeah That makes sense. ADTs are persistent data structures. Maybe something other than binary tree is most appropriate? It would make sense to make sure we have a canonical representation of a particular set. I don't think the record table gets garbage collected. So we might build a set for every subset of the relation. Not good.

Another possibility, reflect into a bloom filter via hashing. Kind of a fun "lattice"? Yeah it is right?

Reifying back into a relation
n lg n overhead:
need to define split macro. to split set in two. Maybe it takes the upper and lower range.

```
#define split(upper,lower,bs) ((-1 << lower) & (-1 >> upper) & bs)
.decl reify(size : unsigned, offset: unsigned, set : bitset)
reify(32, 0, n) :- bitset(n).
reify(n/2, m, bs1), reify(n/2,m + n/2, bs2) :- reify(n,m, bs), n > 1, bs1 = split(m, m + n/2 bs), bs2 = split(m+n/2, m + n, bs)
done(v) :- reify(1, v, bs), NONEMPTY(b)
```

Oh, of course you could straight up unroll it
```
#REIFY(r2, r1, n) r2(1) :- r1(bs), ELEM(n,bs)
// done(1) :- bitset(bs), ELEM(1,bs). 
REIFY(done,bitset,1).
REIFY(done,bitset,2).
REIFY(done,bitset,3).
// and so on
```

Or it could be componentized.
### Sort Lists
Sorted Lists are a canonical set representation, maybe even a good one in some instances.
See above for some List functions.

### Patricia Tries
[fillaitre](https://www.lri.fr/~filliatr/ftp/ocaml/ds/ptset.ml.html)
[fast mergable maps okasaki gill](https://ittc.ku.edu/~andygill/papers/IntMap98.pdf)

Patricia tries have a canonical shape for any given set. Hence hash consing them makes sense. 

Note that lookup shouldn't be just an `in(x,tree)` relation. We need to know when stuff isn't in the tree too. That's the beauty of first class sets. Really, it's more desirable to make external functors to do this stuff. We don't need to materialize these things. A nice property of patricia tries in this context is that lookup is memoizing on subtries, which are sets themselves, so the subqueries aren't necessarily wasted work.


```souffle
.type Bool = True {} | False {}
// Patricia Trie
.type Dict =
   Empty{}
 | Lf {x : number}
 | Br {prefix : number, mask : number, l : Dict, r : Dict}

.decl br(prefix:number, mask: number, l : Dict, r : Dict, res : Dict) inline
// impossible br(_m, $Empty(), $Empty(), $Empty()).
br(_p, _m, t, $Empty(), t) :- $Lf(_j) = t.
br(_p, _m, $Empty(), t, t) :- $Lf(_j) = t.
br(p, m, t0, t1, $Br(p, m, t0, t1)) :- t0 = $Lf(_j1), t1 = $Lf(_j2).



.decl lookup(k : number, d : Dict, res : Bool)
.decl lookup_q(k : number, d : Dict)
lookup(k,d,res):- lookup_q(k,d), 
                ( d = $Empty(), res = $False() ; 
                  d = $Lf(j), (j = k, res = $True(); j!= k, res = $False()) ;
                  d = $Br(prefix, mask, t0,t1), (
                    prefix != k band (mask - 1), res = $False();
                    prefix = k band (mask - 1), (k band mask = 0, lookup(k,t0,res) ; 
                                                 k band mask != 0, lookup(k, t1,res))
                    )
                ).
lookup_q(k,t) :- lookup_q(k,$Br(prefix, mask,t0,t1)), prefix = k band (mask - 1),
                 (k band mask = 0,  t = t0; 
                  k band mask != 0, t = t1).


.decl join(p0 : number, t0 : Dict, p1 : number, t1 : Dict, res : Dict) inline
join(p0,t0,p1,t1,res) :- branchingbit(p0,p1,m),
    (
        p0 band m = 0,   res = $Br(p0 band (m - 1), m, t0,t1);
        p0 band m != 0,  res = $Br(p0 band (m - 1), m, t1,t0)
    ).

.decl branchingbit(p0 : number, p1 : number, res : number) inline
branchingbit(p0,p1,res) :- x = p0 bxor p1, res = x band (- x).


.decl insert(k : number, d : Dict, res : Dict)
insert(k, t, res) :- insert_q(k,t),
    (
        t = $Empty(), res = $Lf(k);
        t = $Lf(j), (j = k, res = t;
                     j != k, join(k, $Lf(k), j, t, res));
        t = $Br(p,m,t0,t1), 
            ( p = m band (k - 1), (
                 k band m = 0, insert(k , t0, res1), res = $Br(p,m, res1, t1);
                 k band m != 0, insert(k , t1, res1), res = $Br(p,m, t0, res1)
            );
              p != m band (k - 1), join(k,$Lf(k), p,t, res) 
            )
    ).

.decl insert_q(k : number, d : Dict)
insert_q(k,t0) :- insert_q(k,$Br(p,m,t0,_t1)), p = m band (k - 1), k band m = 0.
insert_q(k,t1) :- insert_q(k,$Br(p,m,_t0,t1)), p = m band (k - 1), k band m != 0.


insert_q(10, $Empty()).
insert_q(10, $Lf(20)).
insert_q(10, $Lf(12)).
insert_q(0, $Lf(0)).
insert_q(1, $Lf(0)).
insert_q(2, $Lf(0)).
insert_q(3, $Lf(1)).
insert_q(7, $Lf(15)).
insert_q(15, $Lf(7)).
insert_q(0, $Lf(2)).

lookup_q(0, $Br(0, 2, $Lf(0), $Lf(2))).
lookup_q(7, $Br(0, 2, $Lf(0), $Lf(2))).
lookup_q(7, $Br(0, 2, $Lf(0), $Lf(2))).

.output insert(IO=stdout)
.output lookup(IO=stdout)

.decl test(x : number)
test(res) :- branchingbit(0,2,res).
.output test(IO=stdout)
```


```souffle
.type ptrie = Empty {} 
            | Leaf {x : unsigned} 
            | Branch {prefix : unsigned, branchbit : unsigned, l : ptrie, r : ptrie}

.type Bool = False {} | True {}

#define ZERO_BIT(k,m) = (k band m)

.decl _mem(x : unsigned, t : ptrie)
.decl mem(x : unsigned, t : ptrie, res : Bool)
mem(x, $Empty(), $False()) :- _mem(x, $Empty()).
mem(x, t, $True()) :- _mem(x, t), t = $Leaf(x).
mem(x, t, $False()) :- _mem(x, t), t = $Leaf(y), x != y.
_mem(k, l) :- _mem(k, $Branch(_,m,l,r)), k band m = 0.
_mem(k, r) :- _mem(k, $Branch(_,m,l,r)), k band m != 0
.

/*
.decl mem(x : unsigned, t : ptrie, tf : Bool)
mem($Empty(), _, $False()). // not valid
*/
//.decl add(x : unsigned, t : ptrie, t2 : ptrie)
//add(x, $Empty(), $Leaf(x)).
//add(x, $Leaf(x)), $Leaf(x)).

```




### BDDs
bddbdddb is a datalog that used binary decision diagrams as it's backing store. It's an interesting idea. BDDs are very powerful.

BDDs are a relaitve of hash consing.See [type safe modular hash consing](https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf) section 3.3

Souffle ADTs are a variety of hash cons.

```souffle
.type BDD = True {} | False {} | ITE {c : number, t : BDD , e : BDD}

bdd_and(x : BDD, y : BDD, z : BDD)
//bdd_and($True(), $True(), $True()).
//bdd_and($True(), $False(), $False()).
//bdd_and($False(), $True(), $False()).
//bdd_and($False(), $False(), $False()).
bdd_and(x,y, $False()) :- need_bdd_and(x, y), {y = $False() ; x = $False()}.
bdd_and(x,y, x) :- need_bdd_and(x, y), y = $True().
bdd_and(x,y, y) :- need_bdd_and(x, y), x = $True().
//bdd_and(x,y, $ITE( cx , ) ) :- need_bdd_and($ITE(cx, tx, ex), $ITE(cy,ty,ey)), cx < cy, bdd_and(tx,   ) .
//bdd_and(x,y, $ITE( cx , ) ) :- need_bdd_and($ITE(cx, tx, ex), $ITE(cy,ty,ey)), cx < cy, bdd_and(  ) .
bdd_and(x,x,x) :- need_bdd_and(x,x).
bdd_and(x,y,z) :- need_bdd_and(x,y), x = $ITE(cx, tx, ex), y = $ITE(cy,ty,ey), x != y,
      {
        cx < cy, bdd_and(tx, y, zx), bdd_and(xe, y, ze), zc = xc;
        cx = cy, bdd_and(tx, ty, zx), bdd_and(xe, ye, ze), zc = $ITE(cx, zt, ze);
        cx > xy, bdd_and(x, yt, zt), bdd_and(x, ye, ze), zc = yc
      }, z = $ITE(zc,zt,ze).
```

Wait... are bdds of the bits kind of like hash consed patricia trees?

### Call

Prolog has a notion `call` which let's you call data as predicates.
It is emulatable by manually lifting https://www.metalevel.at/prolog/metapredicates

We can make an adt called `rel` which has one constructor for every relation. In principle this could be compiler magic that doesn't require actually duplicating (or worse) the data, but oh well

```souffle

.type rel = Edge {i : number, j : number} | Path {i : number, j : number} | Call {p : rel}

.decl edge(i : number, j : number)
.decl path(i: number, j : number)

.decl call(p : rel)

// arguably maybe these different modes of call should be differen predicates?
// push and pull?
// find?
// different binding patterns?
edge(i,j) :- call($Edge(i,j)).
call($Edge(i,j)):- edge(i,j).

path(i,j) :- call($Path(i,j)).
call($Path(i,j)):- path(i,j).

call(p) :- call($Call(p)).
// eh. I dunno about this one. call($Call(p)):- call(p).


```



### Meta circular interpreter
See extensive prolog literature on meta circular intepreters
https://www.metalevel.at/acomip/

This appears to be annoying to achieve. You have to manually manipulate the variable binding context and substitute. There doesn't seem to be a good way to piggy back on datalog's variables

Maybe first write you program in normal form with one conjunction (invent new per rule predicates that store intermediate variable bindings). Then it isn't quite as hard?

```souffle

.type pnum = Var {x : symbol} | Lit {n : number}
.type rel = Path {pnum, pnum} | Edge {pnum, pnum}
// alternaitve: normalize that only concrete stuff appears in eq
// This is the flavor of manual datalog with if checks.
// .type rel = Path {symnbol, symbol} | Eq1 {symbol, number} | Eq2 {symbol, symbol}
.type body = [p : rel, tl : body]
//or .type body = Rel {p : rel} | Conj {body, body} | True.
.type head <: rel
.type clause = [head, body]

// assoc list
.type ctx = [ x : symbol, n : number, tl : ctx]
// add or merge contexts.


pull(r)

// every possible pattern? 2^n? Ugh
// add really needs to be dealt with using functional magic set style
add(ctx,x,x1) :- call($Path($Var(x), $Num(i)), ctx), path(x1, i).


```

What about going point free? only binary relations?

foo :- Comp(f,g) | Par {} | Fst | Id
.type tup =     Tup {tup, tup} | 
eval($Comp(f,g), fin, gout) :- _eval($Comp(f,g)), eval(f,fin,fout), eval(g,ga,gb), fout = gin.
https://www.philipzucker.com/aop-minikanren/ similar to this

eval($Edge, i, j) :- edge(i,j)
eval($Path, i, j) :- path(i,j)


$Clause($Path, $Edge)
$Clause($Path , $Comp($Edge, $Path))

```souffle
.type rel =
    Lit {name : symbol}
  | Sing {x : val, y : val}
  | Comp {p : rel, q : rel}
  | Conv {p : rel}
  // | Fst {} | Snd {} | Dup {} | Dump {} | Id {}
  | Proj1 {p : rel}
  | Proj2 {p : rel}
  | Trans {p : rel}
  // Union {rel, rel} (basicaly a ';' or, which isn't necessary in stock datalog)
.type val =
    Num {n : number}
  | Sym {s : symbol}
  | UNum {u : unsigned}
  | Rel {r : rel}
  | Unit {}
  | Tup {x : val, y : val}

.decl _eval(r : rel)
.decl eval(r : rel, i : val, j : val)

.decl clause(head : symbol, body : rel)
// reflection into actual relations
// call(head, i, j):- clause(head, body), eval(body, i, j).
eval($Lit(head), i, j):- clause(head, body), eval(body, i, j).
_eval(body) :- clause(_head,body).

eval(t, i, j):- _eval(t), t = $Sing(i,j).

_eval(p), _eval(q) :- _eval(t), t = $Comp(p,q).
eval(t, i, k) :- _eval(t), t = $Comp(p,q), eval(p,i,j), eval(q,j,k).

_eval(p) :- _eval(t), (t = $Conv(p); t = $Proj1(p); t = $Proj2(p); t = $Trans(p) ).
eval(t, j, i) :- _eval(t), t = $Conv(p), eval(p,i,j).
eval(t, i, j) :- _eval(t), t = $Proj1(p), eval(p,i,$Tup(j,_)).
eval(t, i, j) :- _eval(t), t = $Proj2(p), eval(p,i,$Tup(_,j)).
eval(t, $Tup(i,j), k) :- _eval(t), t = $Trans(p), eval(p,i,$Tup(j,k)).

// Hmm. fst and such are not so straightforward actually.
// ? :- _eval($Fst())
// Could merge with comp
// maybe don't make i, j so special?
//eval(t, c, a) :- _eval(t), t = $Comp(p, $Fst()), eval(p, c, $Tup(a,b))



clause("edge", $Sing($Num(1), $Num(2))).
clause("edge", $Sing($Num(2), $Num(3))).
clause("edge", $Sing($Num(3), $Num(4))).
clause("path", $Lit("edge")).
clause("path", $Comp($Lit("path"), $Lit("path"))).

.output eval(IO=stdout)
#define EDGE $Lit("Edge")
#define PATH $Lit("Path")

.decl path(i : number, j : number)
path(i,j) :- eval($Lit("path"), $Num(i), $Num(j)).
.output path(IO=stdout)

// dynamic typecheck
// typefail() :- eval($Lit("path"), a,b), (a != $Num(_),; b != $Num(_)
```


Could also use n-ary combinators instead of binary categorical combinators. Relation algerbra I guess?


```souffle
//.type Pred = [name : symbol, args : TList]
//.type Clause = {head : }
.type pat = Var {x : symbol} | Lit { x : number}
.type relpat = R0 { rel : symbol } | R1 {rel : symbol, x : pat} // | R2 {}
.type body = [ hd : relpay, tl : body ]

// .type body = Conj {a : body, b : body} | Pat {p : relpat}
// or inline 

// alternatively make clause a data structure. But whatever. clause becomes a global object.
.decl clause(hd : relpat, body : body)
clause(hd, body).
// clause(program, hd, body) for multiple programs

.type ctx = [ snoc : body, cons : body ]


// Probably shouldn't be so controlling about match
match(   nextctx) :- match($R1(r, $Lit(x)), ctx), unaryrel(r, x)
headstate(   ) :- pat_in(body, $R1($Var(x)) ), headstate($R1(r, $Var(x)) , body)
// no but you need more state than just what's in the head. edge(x,y), path(y,z) needs y around for consistency

// eq( body , , ). for union find? 

:- match(_snoc, nil)
           :- $R1

.type varbind = [x : number , vbind ; varbind ]
index( varbind, n : unsigned, x : number)
index()
// require labelling variables in order they appear to simplify
// Pre Normalize out unification?
(  ctx, $R1(r, $Var())  ,varbind), unrel(r,y), index(varbind ,n,$Var())
(  ctx, $R1(r, $Var(n))  ,varbind), index( ,n,$Lit(y)), unrel(r, y).


```

## BogoSort
Hmmmm... Can I do this?

```souffle
.decl array(index : unsigned, n : number)
array(0,14)
array(1,934).
array(2,49).
array(3,-23209).

// permute
array(i+1,n) :- array(i,n), i < 3.
array(i-1,n) :- array(i,n), i > 0.

// subsume bad possibilities...?
array(i-1, n) <= array(i, n) :- i > 0, 
```
What about building a relation of pairs
```
pair(a,b) <= pair(b,a) :- b <= a, a <= b
```


bubble sort
```
// could use max over input iindices instead of N
#define N 4
.decl in(index : number, v : symbol)
in(2 , "a").
in(0 , "b").
in(1 , "c").
in(3 , "d").

proc(i, x1, t + 1), proc(i+1,y1, t + 1):- proc(i, x,t), proc(i+1, y, t), t%2 = i%2 , t < N * N, 
   (  x < y, x1 =x,y1 = y;  x >= y, x1 = y, y1 = x).

out(i,x) :- proc( i, x, N).
```

path based. Take shortest oriented edges. Graph is then 
```
v(1)
v(2)
v(3)

// shortest edges
edge(i,j) :- v(i), v(j), i < j.
edge(i,j) <= edge(i,k) :- k <= j.

//edge(i,i) :- min().
//edge(i,j) :-  edge(i,j)

path(0,i,i) :- min(i : v(i) ).
path(n+1,i,k) :- path(n, i,j), edge(j,k).

out(i,x) :- path(i,_,x).

```

Radix sort?

## Translating functional programs 
https://drops.dagstuhl.de/opus/volltexte/2022/16235/pdf/LIPIcs-ECOOP-2022-7.pdf Functional Programming with Datalog

Lift function to relation by making return value part of relation
fib(n) becomes fib(b,ret)

Datalog is bottom up. You need to rip apart all the recursive calls. What is the most principled way to see this? Principled transformation to bottom up call?
```souffle
fact(0,1).
fact(1,1).
fact(n + 1, (n+1) * m) :- fact(n, m), n < 10.
```

I like the build a table of all possible arguments.
```souffle
needed(n).
needed(n - 1) :- needed(n), n > 0. 
fact(0,1).
fact(1,1).
fact(n + 1, (n+1) * m) :- fact(n, m), needed(n).
```
For ADTs this ends up being a table of all subterms.

Is needed a representation of call frames maybe?

## Lists

```souffle
.comp List<A>{
  .type t = [hd : A, tl : t]
  .decl _length(l : t)
  .decl length(l : t, res : unsigned)
  
  _length(tl) :- _length([_hd,tl]).
  length(nil,0).
  length([hd,tl], n+1) :- _length([hd,tl]), length(tl,n).

  .decl _nth(l : t, n : unsigned)
  .decl nth(l : t, n : unsigned , res : A)
  _nth(tl, n - 1) :- _nth([_hd,tl], n), n > 0.
  nth([hd,tl],0,hd) :- _nth([hd,tl], 0).
  nth([hd,tl], n, res):- _nth([hd, tl], n), nth(tl, n-1, res).

  .decl _rev(l : t)
  .decl __rev(l : t, rem : t, acc : t)
  .decl rev(l : t, res : t)
  __rev(l, l, nil) :- _rev(l).
  __rev(l, tl, [hd,acc]) :- __rev(l, [hd, tl], acc).
  rev(l, acc) :- __rev(l, nil, acc).

  .decl _append(x : t, y : t)
  .decl append(x : t, y : t, z : t)
  _append(tl, y) :- _append([_hd, tl], y).
  append(nil, y, y) :- _append(nil, y).
  append([hd,tl], y, [hd, z]) :- _append([hd,tl], y), append(tl, y, z).


  // https://stackoverflow.com/questions/33566414/ocaml-mergesort-and-time

  .decl _merge(x : t, y : t)
  .decl merge(x : t, y : t, res : t)
  merge(nil, y, y) :- _merge(nil, y).
  merge(x, nil, x) :- _merge(x, nil).
  _merge(xs, [y,ys]) :- _merge([x,xs], [y,ys]), x < y.
  _merge([x,xs], ys) :- _merge([x,xs], [y,ys]), x >= y.
  merge([x,xs], [y,ys], [x,z]):- _merge([x,xs], [y,ys]), merge(xs,[y,ys],z), x < y.
  merge([x,xs], [y,ys], [y,z]):- _merge([x,xs], [y,ys]), merge([x,xs],ys,z), x >= y.

  .decl _split(l : t)
  .decl __split(l : t, rem : t, x : t, y : t)
  .decl split(l : t, x : t, y : t)
  __split(l,l,nil,nil):- _split(l).
  __split(l, tl, y, [hd,x]) :- __split(l, [hd,tl], x, y).
  split(l, x ,y) :- __split(l, nil, x, y).


  .decl _sort(l : t)
  .decl sort(l : t, res : t)
  sort(nil,nil) :- _sort(nil).
  sort([x,nil], [x,nil]) :- _sort([x,nil]).
  _split(l) :- _sort(l).
  _sort(x), _sort(y) :- _sort(l), split(l, x, y).
  _merge(x1, y1) :- _sort(l), split(l, x, y),  sort(x,x1), sort(y,y1).
  sort(l, z) :- _sort(l), split(l, x, y), sort(x,x1), sort(y,y1), merge(x1, y1, z).

  //_sort(l), split(l, x, y),  sort(x,x1), sort(y,y1).


  // insert element x into sorted list
  .decl _insort(x : A , l : t)
  .decl insort(x : A , l : t, res : t)
  insort(x,nil, [x,nil]) :- _insort(x,nil).
  _insort(x, tl) :- _insort(x, [hd,tl]), x > hd.
  insort(x, [hd,tl], [x,[hd,tl]]) :- _insort(x, [hd,tl]), x <= hd.
  insort(x, [hd,tl], [hd,res]) :- _insort(x, [hd,tl]), x > hd, insort(x, tl, res).

  .decl _mem(x : A, l : t)
  .decl mem(x : A, l : t, res : number)
  mem(x, nil, 0) :- _mem(x, nil).
  mem(x, [hd,tl], 1) :- _mem(x, [hd,tl]), x = hd.
  _mem(x, tl) :- _mem(x, [hd,tl]), x != hd.
  mem(x, [hd,tl], res) :- _mem(x, [hd,tl]), x != hd, mem(x, tl, res).

}

.init NumList = List<number>

NumList._rev([1,[2,[3,nil]]]).
.output NumList.rev(IO=stdout)

NumList._append([1,[2,[3,nil]]], [4,[5,nil]]).
.output NumList.append(IO=stdout)

NumList._sort([134,[23,[344,[1,[63,[5,nil]]]]]]).
.output NumList.sort(IO=stdout)


NumList._insort(10, [1,[2,[14,[18,nil]]]]).
.output NumList.insort(IO=stdout)

```

What is the best sort in the presence of memoization? Is tail recursion still good? It seems to allow less sharing of computation

Is there a macro or construct I could add to datalog that would make these functional expressions less verbose?

Note that sorted lists are a canonical set representation. merge is set union. insort adds. mem is elem

Really all of the above are functions and it is a plum shame that I am materializing the intermediate states. _maybe_ it's ok to materialize the result but even then.

A linear datalog that consumes the _pred might be nice.
Could destroy them with subsumption.


## Dynamic Programming
### Q learning
Grid world + subsumption / lattice.


## Mandelbrot
Translated from the [SQLlite docs on recursive ctes](https://www.sqlite.org/lang_with.html)
```sql
WITH RECURSIVE
  xaxis(x) AS (VALUES(-2.0) UNION ALL SELECT x+0.05 FROM xaxis WHERE x<1.2),
  yaxis(y) AS (VALUES(-1.0) UNION ALL SELECT y+0.1 FROM yaxis WHERE y<1.0),
  m(iter, cx, cy, x, y) AS (
    SELECT 0, x, y, 0.0, 0.0 FROM xaxis, yaxis
    UNION ALL
    SELECT iter+1, cx, cy, x*x-y*y + cx, 2.0*x*y + cy FROM m 
     WHERE (x*x + y*y) < 4.0 AND iter<28
  ),
  m2(iter, cx, cy) AS (
    SELECT max(iter), cx, cy FROM m GROUP BY cx, cy
  ),
  a(t) AS (
    SELECT group_concat( substr(' .+*#', 1+min(iter/7,4), 1), '') 
    FROM m2 GROUP BY cy
  )
SELECT group_concat(rtrim(t),x'0a') FROM a;
```



```souffle
#define dx 0.05
#define dy 0.0625
.decl xaxis(x : float)
.decl yaxis(y : float)
.decl m(iter:unsigned, cx : float, cy : float, x : float, y : float)
.decl m2(iter:unsigned, cx : float, cy : float)
.decl collect(cx:float, cy:float, line:symbol)
.decl a(cy:float, line:symbol)

xaxis(-2).
yaxis(-1.00000001).
xaxis(x + dx) :- xaxis(x), x < 1.2.
yaxis(y + dy) :- yaxis(y), y < 1.

m(0,x,y, 0,0) :- xaxis(x), yaxis(y).
m(iter+1, cx, cy, x*x-y*y + cx, 2.0*x*y + cy ) :- m(iter, cx,cy,x,y),iter < 28, x*x + y*y < 4.0.
m2(iter, cx,cy) :- xaxis(cx), yaxis(cy), iter = max i : m(i, cx,cy, _,_).

collect(-2.00,cy,"") :- yaxis(cy).
collect(cx+dx,cy,line2) :- m2(iter,cx+dx,cy), collect(cx,cy,line), line2 = cat(line,c), 
                         ( iter < 16 , c = " " ; iter >= 16,  c = "#" ).
a(1+cy,line) :- cx = max x : xaxis(x), collect(cx,cy,line).

.output a(IO=stdout)
/*
---------------
a
cy      line
===============
-9.9999999392252903e-09                                        #                        
0.062499990000000061                                         #                          
0.12499999000000006                                         ##                          
0.18749999000000006                                       ######                        
0.24999999000000006                                       ######                        
0.31249999000000006                                #       ####                         
0.37499999000000006                                ###  ########### #                   
0.43749999000000006                                 ####################                
0.49999999000000006                                 ###################                 
0.56249999000000006                               #####################                 
0.62499999000000006                              ########################               
0.68749999000000006                    ##  #     #######################                
0.74999999000000006                     ######   ######################                 
0.81249999000000006                    ################################                 
0.87499999000000006                #  #################################                 
0.93749999000000006                 ###################################                 
0.99999999000000006     #############################################                   
1.0624999900000001                  ###################################                 
1.1249999900000001                 #  #################################                 
1.1874999900000001                     ################################                 
1.2499999900000001                      ######   ######################                 
1.3124999900000001                     ##  #     #######################                
1.3749999900000001                               ########################               
1.4374999900000001                                #####################                 
1.4999999900000001                                  ###################                 
1.5624999900000001                                  ####################                
1.6249999900000001                                 ###  ########### #                   
1.6874999900000001                                 #       ####                         
1.7499999900000001                                        ######                        
1.8124999900000001                                        ######                        
1.8749999900000001                                          ##                          
1.9374999900000001                                           #                          
1.9999999900000001                                             #                        
2.0624999900000001                                                                      
===============
*/
```
## Ball and Springs

Balls and springs are a model of a partial differential equation. We can model the equations of motion, initial conditions, and boundary conditions using datalog. What fun!

```souffle
#define T 10
.decl ball(t : number, n : number, x : float, v : float)
// initial conditions

ball(0, n, 0, 0) :- n = range(0,11), n != 5.
ball(0, 5, 10, 0).

// ball(0, n, x, v) :- n = range(1,10), x = to_float(n) * 0.1, v = 0.
// ball(0,0,0,0).
// ball(0,10,0,0).


// Boundary condition. iniital and final ball fixed
ball(t+1,0,0,0) :-  t = range(0,T).
ball(t+1,10,0,0) :- t = range(0,T).

// dynamics
ball(t+1, n,  newx, newv) :- 
  t < T, 
  ball(t, n-1, x0, _v0), 
  ball(t, n, x, v), 
  ball(t, n+1, x2, _v2),
  newx = x + 0.1 * v,
  newv = v + 0.1 * (x0 - x + x2 - x).
.output ball(IO=stdout)


```


```python
#some plotting code
from matplotlib import pyplot as plt
from numpy import genfromtxt
import pandas as pd
import imageio
df = pd.read_csv('ball.csv', delimiter=r"\s+", header=None)
print(df.values)
x = df.to_numpy()
filenames = []
for i in range(100):
    t = x[11*i:11*(i+1)]
    # print(t)
    xs = t[:, 2]
    vs = t[:, 3]
    plt.figure()
    plt.plot(xs, '--o', c='blue', mfc="red", )
    ax = plt.gca()
    #ax.set_xlim([xmin, xmax])
    ax.set_ylim([-10, 10])
    file = f"img/t{i}.png"
    plt.savefig(file)
    plt.close()
    filenames.append(file)

with imageio.get_writer('mygif.gif', mode='I') as writer:
    for filename in filenames:
        image = imageio.imread(filename)
        writer.append_data(image)

```

## Sudoku

```souffle

.type bitset <: number
.decl x(row : number, col : number, val : bitset)

.decl digits(x : number) inline
digits(x) :- x = range(1,10).

#define FULL (2 ^ 9) - 1
.decl union(x : bitset, y : bitset, res : bitset) inline
union(x,y,res) :- res = x bor y.
x(row, col, FULL):- digits(row), digits(col).
.output x
x(row,col,) :- digits(row), x(row,0,s0), x(row,1,s1), x(row,2,s2), x(row,3,s3), s = s0 bor s1 bor s2 bor s3.
x(row,col2, s2 / s) :- x(row,col,s), SING(s), col != col2, x(row,col2,s2).


```

## Constraint handling Rules (CHR)
See note on prolog for more on CHR

Constraint handling rules have some similarity to datalog with subsumption and sometimes you can translate programs.
Datalog has set semantics, CHR has multiset semantics. Sometimes you add CHR rules to make set semantics
subsumption allows some deletion.

Timestamps and water marks?
max(t1,t2)+1  :- foo( , t1), bar(t2) 

:- watermark(t), foo(t1), , t1 < t
foo() <= foo() :- watermark(t)

deletion watermark?

DDlog has a multiset thing. Seems reasonable this is better for chr.

You can have multiset if you include justification/provenance fields. See section below. This also prevents refirings.

```
a() \ b(1) <=> guard | b(2)
\\ is similar to
b(2) :- a(), b(1), guard.
b(1) <=  b(2) :- a(), guard.

```

```souffle
/*
CHR: 
  a() \ b(1) <=> guard | b(2) 
is similar to
Datalog:
  b(2) :- a(), b(1), guard.
  b(1) <=  b(2) :- a(), guard.

Merge Sort in CHR, given values as next(start,Value)
next(A,B) \ next(A,C) <=> A<B,B<C | next(B,C).
*/
.decl next(a : number, b : number)
next(b,c) :- next(a,b), a < b, b < c, next(a,c).
next(a,c) <= next(b,c) :- next(a,b), a < b, b < c.

next(0,7). next(0,4). next(0,3).
.output next
/*
---------------
next
a       b
===============
0       3
3       4
4       7
===============
*/
```

## Backprop

A difficulty of backprop is that you need to accumulate the backpropped value from all usage sites of a subexpression. This is an annoying thing to do in datalog. It is a non stratified summation, which _is_ possible using first class sets (although I'm not sure how it'll work out here). If we can guarantee all derivatives are _positive_, which is rare, it is a bit easier because we can prune for merely the largest summation value.

A cute trick is to make every usage site of a subexpression _linear_ by using contructors `Dup1` and `Dup2`. I seriosly mean linear. If you use a `$Dup1` you have to use a `Dup2` somewhere or else it doesn't work

This dup trick is reminiscent of <https://github.com/Kindelia/HVM> [Reverse Mode Differentiation is Kind of Like a Lens II](https://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) [The simple essence of automatic differentiation](http://conal.net/papers/essence-of-ad/). It is very important to pay attention to dups in reverse differentiation. There is something beautiful there

Datalog is perfectly good at representing graphs. Many implementations of backprop push the values back along a back prop graph. The tagging here demonstrates how you could do a kind of distributed backprop, not that I know why you'd want to do such a thing. Seems very inefficient.

Egraphs?

[Automatic Differentiation using Constraint Handling Rules in Prolog](https://arxiv.org/abs/1706.00231)

```souffle
.type expr = 
  Add {x : expr, y : expr} 
| Mul {x : expr, y : expr} 
| Lit {x : float} 
| Var {x : symbol}
| Dup1 {x : expr}
| Dup2 {x : expr}


.decl term(n : unsigned, x : expr)
term(n, x), term(n,y) :- term(n, $Add(x,y)) ; term(n, $Mul(x,y)).
term(n, x) :- term(n, $Dup1(x)) ; term(n, $Dup2(x)).

term(n,t) :- eval(n,t,_).
term(n,t) :- diff(n,t,_).

// evaluate forward
.decl eval(n : unsigned, e : expr, v : float)
eval(n, t, va + vb) :- term(n,t), t = $Add(a,b), eval(n, a, va), eval(n, b, vb).
eval(n, t, va * vb) :- term(n,t), t = $Mul(a,b), eval(n, a, va), eval(n, b, vb).
eval(n, t, va) :- term(n,t), (t = $Dup1(x) ; t = $Dup2(x)), eval(n, x, va).
eval(n, t, v) :- term(n,t), t = $Lit(v).

// propagate derivative backwards
.decl diff(n : unsigned, e : expr, v : float)
diff(n, a, dt ), diff(n, b, dt) :- diff(n, t, dt), t = $Add(a,b).
diff(n, a, dt * vb), diff(n, b, va * dt) :- diff(n, t, dt), t = $Mul(a,b), eval(n, a, va), eval(n, b, vb).
diff(n, x, dx1 + dx2) :- diff(n, $Dup1(x), dx1),  diff(n, $Dup2(x), dx2).

#define X $Var("x")
#define Y $Var("y")
#define T0 $Mul($Dup1(X),$Dup2(X))
#define T1 $Add($Dup1(X),$Dup2(X))

eval(0, X, 3.0).
diff(0, $Add(X,$Lit(1)), 1).

eval(1, X, 3.0).
diff(1, T1, 1).

eval(2, X, 3.0).
diff(2, T0, 1).
.output eval(IO=stdout)
//.output term(IO=stdout)
.output diff(IO=stdout)


// a fiendish macro. Never do this, but it is cute.
#define DUP(x)  $Dup1(x),$Dup2(x)
// could be used like this: x1 = DUP(foo) = x2
```
## Lambda representation

[Lambda Normalization for Souffle Datalog](https://www.philipzucker.com/lambda-datalog-souffle/)

What is the most appropriate way? Probably we want to implement some kind of machine flavored implementation.
Or maybe a graph like representation.

I could literally do hash cons modulo alpha. I can dor xor trick. Hmm. PosTree is a trie.

Could make user defined functor for substition.

I could make udf for normalization. And memoize into a choice domain?

Combinators

lambda datalog. Pattern matching on ground lambda terms is good.

Yihong's let and fresh.
Might still need first class maps for environements.

https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

```souffle
.type term = Lam {body : term} | Var {i : unsigned} | App {f : term, x : term}
.type value = Closure {t : term, e : env}
.type env = [hd : value , tl : env]

.decl _eval(e : env, t : term)
.decl eval(e : env, t : term, v : value)
// Lookup
eval([hd,tl], $Var(0), hd) :- _eval([hd,tl], $Var(0)).
_eval(tl, $Var(n-1))      :- _eval([_hd,tl], $Var(n)), n > 0.
eval([hd,tl], $Var(n), v) :- _eval([hd,tl], $Var(n)), n > 0, eval(tl, $Var(n-1), v).

eval(ctx, $Lam(b), $Closure(b,ctx)) :- _eval(ctx, $Lam(b)).

_eval(ctx, x), _eval(ctx, f) :- _eval(ctx, $App(f,x)).
_eval([x1 , ctx2] , b) :- _eval(ctx, $App(f,x)), eval(ctx, f, $Closure(b,ctx2)), eval(ctx, x, x1).
eval(ctx, $App(f,x), v) :- _eval(ctx, $App(f,x)), eval(ctx, f, $Closure(b,ctx2)), eval(ctx, x, x1), eval([x1 , ctx2] , b, v).

//_eval(nil, $App($Lam($Var(0)), $Lam($Var(0)))).
_eval(nil, $Lam($App($Lam($Var(0)), $Var(1)))).
.output eval(IO=stdout)
```

Krivine machine.

## Parsing
What about good error parsing? It feels like the flexibility of a datalog could be nice. It's sort of why-not provenance.

[CYK Parsing](https://en.wikipedia.org/wiki/CYK_algorithm) is an example of dynamic programming.
Earley = magic set of CYK. Doing it on demand

`substr` makes this feasible. This unfortuantely is going to reintern the string though. So hard to believe it'll ever be efficient.


```souffle

.decl str(x : symbol)
.type char <: symbol
.decl chars(x : symbol, i : number, c : symbol )
chars(x, i, c) :- str(x), i = range(0, strlen(x)), c = substr(x, i, 1).

str("())()").
str("()()").
str("((()))").
//.output chars(IO=stdout)


.decl parens(x : symbol, i : number, j : number)
parens(x, i, i) :- str(x), i = range(0, strlen(x)+1).

//parens(x, i-1, j+1) :- i >= 1, "(" = substr(x,i-1,1), parens(x, i, j), ")" = substr(x,j,1).
parens(x, i-1, j+1) :- i >= 1, chars(x,i-1,"("), parens(x, i, j), chars(x, j, ")").

// pretty expensive
#define cat3(x,y,z) cat(x,cat(y,z))
#define cat4(x,y,z,w) cat(x, cat3(y,z,w))
parens(x, i-1,j+1) :- i >= 1, parens(x,i,j), substr(x,i-1,j-i+2) = cat3("(", substr(x,i,j-i) , ")").

parens(x, i, k) :- parens(x,i,j), parens(x,j,k).
.output parens(IO=stdout)
.decl parsed(x : symbol)
parsed(x) :- parens(x, 0, strlen(x)).
.output parsed(IO=stdout)

.type myparens = Append {x :myparens , y : myparens} | Parens {x : myparens} | Empty {}

.decl parens2(x : symbol, i : number, j : number, p : myparens)
// P --> eps
parens2(x, i, i, $Empty()) :- str(x), i = range(0, strlen(x)+1).
// P --> (P)
parens2(x, i-1, j+1, $Parens(a)) :- i >= 1, chars(x,i-1,"("), parens2(x, i, j, a), chars(x, j, ")").
// P --> PP
parens2(x, i, k, $Append(a,b)) :- parens2(x,i,j, a), parens2(x,j,k, b), a != $Empty(), b != $Empty().

.decl parsed2(x : symbol, p : myparens)
parsed2(x, a) :- parens2(x, 0, strlen(x), a).
.output parsed2(IO=stdout)



```




Chomsky normal form. Only allow epsilon at start

Magic set. The query we actuall want in `parsed(x)`.
needparens(x,i,j) guard predicate in front. But so what


I
```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
#define cat4(x,y,z,w) cat(x, cat3(y,z,w))
.decl str(x : symbol)
.decl needparens(x : symbol)
.decl parens(x : symbol)
str("()()").
str("()(()())").
// inefficient, but cleaner to write. Don't have to track i,j
// Maybe it's not even that inefficient when you consider semi naive
// We get sharing between different parses also.
needparens(y) :- str(x), i = range(0,strlen(x)), len = range(1,strlen(x) - i + 1), y = substr(x, i, len).
parens("").
parens(y) :- needparens(y), parens(x), y = cat3("(", x, ")").
parens(z) :- needparens(z), parens(x), parens(y), z = cat(x,y).
.output parens(IO=stdout)

// Could also make more efficient if we use smarter needsparens.
// should only propagate needs parens if the first and last characters are parens or something.
// We're also filling up our symbol table here. Eh.

// If I donthave the needsparens guard, this wouldn't terminate. cat3 would keep making new strings.

```

```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
.type parens =  Empty {} | Parens {x : parens} | Append {x : parens, y : parens} 
.decl str(x : symbol)
.decl needparse(x : symbol)
.decl parses(x : symbol, p : parens)
str("()(()())").
needparse(y) :- str(x), i = range(0,strlen(x)), len = range(1,strlen(x) - i + 1), y = substr(x, i, len).
parses("", $Empty()). // P --> eps
parses(y, $Parens(p)) :- needparse(y), parses(x,p), y = cat3("(", x, ")"). // P --> (P)
parses(z, $Append(px,py)) :- needparse(z), parses(x,px), parses(y,py), z = cat(x,y), // P --> PP
                             px != $Empty(), py != $Empty(). // For termination
.output parses(IO=stdout)
/*x       p
===============
()(()())        $Append($Parens($Empty), $Parens($Append($Parens($Empty), $Parens($Empty))))
                $Empty
()              $Parens($Empty)
(()())          $Parens($Append($Parens($Empty), $Parens($Empty)))
()()            $Append($Parens($Empty), $Parens($Empty)) */
```

Easy way to regexp?
If I want identifiers
```python
import string
print(" ".join([f"lower(\"{c}\")." for c in string.ascii_lowercase  ]))
print(" ".join([f"upper(\"{c}\")." for c in string.ascii_uppercase  ]))
print(" ".join([f"digit(\"{c}\")." for c in range(10)  ]))
```

```souffle
.decl lower(c : symbol)
.decl upper(c : symbol)
.decl char(c : symbol)
.decl digit(c : symbol)
lower("a"). lower("b"). lower("c"). lower("d"). lower("e"). lower("f"). lower("g"). lower("h"). lower("i"). lower("j"). lower("k"). lower("l"). lower("m"). lower("n"). lower("o"). lower("p"). lower("q"). lower("r"). lower("s"). lower("t"). lower("u"). lower("v"). lower("w"). lower("x"). lower("y"). lower("z").
upper("A"). upper("B"). upper("C"). upper("D"). upper("E"). upper("F"). upper("G"). upper("H"). upper("I"). upper("J"). upper("K"). upper("L"). upper("M"). upper("N"). upper("O"). upper("P"). upper("Q"). upper("R"). upper("S"). upper("T"). upper("U"). upper("V"). upper("W"). upper("X"). upper("Y"). upper("Z").
digit("0"). digit("1"). digit("2"). digit("3"). digit("4"). digit("5"). digit("6"). digit("7"). digit("8"). digit("9").

alpha(c) :- lower(c) ; upper(c).


```


Earley parsing. Put the carefullness in needparse instead
```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
#define FIRST(rem) substr(rem,0,1)
#define LAST(rem) substr(rem,strlen(rem)-1,1)

.type parens =  Empty {} | Parens {x : parens} | Append {x : parens, y : parens} 
.decl str(x : symbol)
.decl needparse(x : symbol)
.decl parses(x : symbol, p : parens)
needparse("()(()())").
needparse(y) :- needparse(x), FIRST(x) = "(", LAST(x) = ")", y = substr(x,1,strlen(x)-2).
// only one iterator so that's nice I guess. And only because it's such a nasty rule
needparse(y), needparse(z) :- needparse(x), i = range(0,strlen(x)), y = substr(x,0,i), z = substr(x,i,strlen(x)-i). 



parses("", $Empty()). // P --> eps
parses(y, $Parens(p)) :- needparse(y), parses(x,p), y = cat3("(", x, ")"). // P --> (P)
parses(z, $Append(px,py)) :- needparse(z), parses(x,px), parses(y,py), z = cat(x,y), // P --> PP
                             px != $Empty(), py != $Empty(). // For termination
.output parses(IO=stdout)
```

```souffle

.type list_sexp = [hd : sexp, tl : list_sexp]
.type sexp = List {x : list_sexp} | Atom {x : symbol}

word(s,i,j) :- chars(s, i-1, c), alpha(c), word(s, i, j).


```


DCG
parser combinator
We need like a whole stack then. Blugh
```souffle
#define NEXT(rem) substr(rem,1,strlen(rem1)-1)
#define FIRST(rem) substr(rem1,0,1)
parse(x,NEXT(rem)) :- parse(x,rem1), FIRST(rem) = ")".


// regexp
#define NEXT(rem) substr(rem,1,strlen(rem1)-1)
#define FIRST(rem) substr(rem1,0,1)
#define FIRST(rem, c) substr(rem1,0,1) = c

#define STAR(class) parse(x,NEXT(rem)) :- parse(x,rem1), FIRST(rem) = c, class(c).
starupper(x,NEXT(rem)) :- starupper(x,rem1), FIRST(rem) = c, upper(c).

// as transition system
recog("nextstate",x, rem) :- recog("upper", x, rem) , FIRST(rem) = c, !upper(c), 

// as transition system. don't need x really. uhhh. Yes we do. We need a bottom up transform then.
recog("nextstate", rem) :- recog("upper", rem) , FIRST(rem) = c, !upper(c), 



```
So it seems like this is a general transfomation. I can exchange a global context parameter x that I dig into with substr for a need predicate.
The two are uncoupled. Recurse over the thing first to reak it up, then bottom up the pieces. Don't do in one pass.


Slices
[i : unisnhged, n : unsigned, s : symbol] === substr(s, i , n)
Can use as difference list.

```souffle


.decl str(s : symbol)
.decl rparen(s : symbol, i: number, n : number)
.decl lparen(s : symbol, i: number, n : number)
.decl ws(s : symbol, i : number, n : number)

lparen(s, i ,1) :- str(s), i = range(0, strlen(s)), substr(s,i,1) = "(".
rparen(s, i ,1) :- str(s), i = range(0, strlen(s)), substr(s,i,1) = ")".
ws(s, i ,0) :- str(s), i = range(0, strlen(s)).
ws(s, i ,1) :- str(s), i = range(0, strlen(s)), substr(s,i,1) = " ".

ws(s, i, k+n) :- ws(s, i, n), ws(s, i+n, k).
str("(((((    )))   ))").


.decl matched(s : symbol, i: number, n : number)
matched(s,i,0) :- str(s), i = range(0,strlen(s)). 
// matched(s, i, 1 + k + m + q + 1) :- lparen(s , i, 1), j = i + 1 , ws( s, j , k ), l = j + k, matched(s, l, m), l + m = p,  ws(s, p, q ), x = p + q, rparen(s, x, 1).

// "difference list" formulation
// This might strictly speaking have some unexpected results. what if difference is negative?
matched(s, i, x + 1 - i) :- 
lparen(s , i, j-i), ws(s, j , l-j ), matched(s, l, p-l), ws(s, p, x - p ), rparen(s, x, 1).
// hmm seems ok
str(")(").

.output lparen(IO=stdout)
.output ws(IO=stdout)
.output matched(IO=stdout)

```


- [earley parsing](https://github.com/souffle-lang/souffle/blob/master/tests/example/earley/earley.dl)
- [parser in datalog](https://homes.cs.washington.edu/~bodik/ucb/cs164/sp13/lectures/09-Datalog-CYK-Earley-sp13.pdf) bottom up parsing
- [parsing and generation as datalog queries](https://aclanthology.org/P07-1023.pdf)
- [DCGs + memoizing = Packrat Parsing](https://mercurylang.org/documentation/papers/packrat.pdf)

## Hilog
```souffle
.type binreltag = Edge {} | Star {r : binreltag}
// Closure is a bad name for this example

.decl binrel( r : binreltag, x : number, y : number)
binrel($Star(r), x, y) :- needstar(r), binrel(r, x, y). // hmm this'll never stop becaus we'll keep starring stars. Perhaps needs to be predicated upon need.
binrel($Star(r), x, z) :- needstar(r), binrel(r, x, y), binrel($Star(r), y, z).

.decl needstar(r : binreltag)
needstar($Edge()).

binrel($Edge(), 1, 2).
binrel($Edge(), 2, 3).
binrel($Edge(), 3, 4).

.output binrel(IO=stdout)
```
It may also be nice to make a universal type (for which number actually serves pretty well?).




## Equality Saturation
See blog posts

egglog

See also perhaps first class union find

## Term Rewriting
It's similar to "path" in some respects.

Maybe don't bother with "t" parameter?

```
.type Term = Lit {x : signed} | Add {a : Term, b : Term} | Var {x : symbol}
.decl simplify(t : Term, t2 : Term)

simplify(t,t2) <= simplify(t,t3) :- t2 <= t3.

// recursive cases
simplify(t,$Add(ta2,tb2)) :- simplify(t, $Add(ta,tb)), simplify(ta, ta2), simplify(tb, tb2).

// patterns
simplify(t, a) :- term(t), t = $Add($Lit(0), a).

// should have the analog of "edge" here
simplify(t,t2) :- simplify(t,t1), simplify(t1,t2).
//simplify(t0,a) :- simplify(t0,t), t = $Add($Lit(0),a).


simplify(t,t) :- term(t).

//initiliaze
term(t) :- start(t).
term(a), term(b) :- term($Add(a,b)).

```
### Datalog Modulo Term Rewriting
There is an interesting alternative design to egglog that has some of the same mouthfeel.

Many rewrite rules are obvious simplification rules. 
There really is not much reason not to take them eagerly.

Better yet, rather than rewrite rules, consider merely a partial ordering relation on terms.
`a <= a + 0`

Using subsumption, any term that is less than another can be deleted. By attaching this notion to the _type_ rather than the relation, we get something that feels like datalog modulo term rewriting.  We can in fact use guarded subsumption and guarded rewrites.

A rewrite rule `a | guard -> b` is translated/considered as a shorthand for the following rules for every entry of any relation `foo` that has a slot of term type.

```
foo(a) :- foo(b), guard.
foo(a) <= foo(b), guard.
```

This is similar to how one can emulate lattices using subsumption.

Being confluent and terminating are probably sufficiently good properties for one to make promies about the result database.

If you aren't confluent, that isn't persay a problem, but you'd need to somehow guarantee you've applied every possible rule before deleting the subsumed terms. This is not a guarantee souffle subsumption is set up to do? Actually this would work I think. Add a guard on subsumption for every possible rule that could apply

```
foo(rule1) :- foo(subsumed).
foo(rule2) :- foo(subsumed).
foo(rule3) :- foo(subsumed).
foo(subsumed) <= foo(rule1) :- foo(rule2), foo(rule3).
```

Nontermination isn't that bad. `a -> a + 0` is ok, you just won't terminate. Fine. We've become accustomed to nontermination in egglog. Hmm. But this rule should _not_ have subsumption semantics.

Ah. You'll also want to be rewriting subterms. This requires a demand transformation. The souffle encoding starts to feel clunky.
Well, we could just refuse to rewrite subterms?

```
foo(b) :- foo(a), replace(a,lhs,rhs,b)
```

This framework for example could encompass datalog modulo beta reduction.

### Graph rewriting
Subsumption might enable one to snip out old regions if you use timestamps. We're kind of trying to mimic CHR in datalog
See note on:
- Term Rewriting


## Graph Algorithms
Graph form of monoidal category in soufflé?
Graph rewriting? We have graph matching. How do we say some subgraph is better than some other.
Graph combinator reduction?

Flow problems?
Ford fulkerson
```
// Tinkering. This isn't right.
/ Maybe I can't do this. Need to track paths?


// start data
cap(i,j,c).

pathcap(x,z,c3), flow(x,y,c3) :- cap(x,y, c), flow(x,y,f), pathcap(y,z, c2), c3 = min(c - f, c2)
flow(i,j,f) <= flow(i,j,f2) :-  f <= f2.
pathcap(i,j,f) <= flow(i,j,f2) :-  f2 <= f2.

```
### Reachability
### Shortest Path
```souffle

.type vert = symbol
.decl edge(x : vert, y : vert, cost : number)
.decl path(x : vert, y : vert, cost : number)
edge("x","y",2). edge("x","y",3). edge("x","y",4).
edge("y","x",1).
edge("y","z",5).

.decl verts(x : vert)
verts(x) :- edge(x,_,_); edge(_,x,_).
edge(x,x,0) :- verts(x).


path(x,y,c) :- edge(x,y,c).
path(x,z,c1+c2) :- edge(x,y,c1), path(y,z,c2).



path(x,y,c1) <= path(x,y,c2) :- c2 <= c1. 
.output path(IO=stdout)
```

Note this is also useful for difference logic propagation.
See difference logic in propagators





A*

Provenance of reachability _is_ the path.
### Spanning Tree

### Clique
### Cycle

### Subgraph Matching
Doesn't really require datalog. No recursion.
You can write patterns as queries. You can do this in sql. This is what graph databases do.

### Coloring
With the choice construct.
Not an optimal coloring. Or probably even a very good heuristic coloring.


The increase of information from propagation is learnign what colors something can't be.

```
colors()
color(node, color) choice-domain node
notcolor(node,color)

notcolor(n,c1):- colors(c1), color(node,c), c != c1.
color(n, "g") :- notcolor(n,"r"), notcolor(n, "b") // all colors gone. Hard to express generically. Bitsets could help.
notcolor(n2,c) :- edge(n1,n2), color(n1, c).


```

Maybe with a iter choice parameter. And you keep the lowest branching solution?
iter could be an a priori ordering of nodes.
```
// hmm doesn't work
color(iter:unsigned,node , color)
color(i+1,n,c) :- !notcolor(i, n,c).
color(n+1,n,c) :- !notcolor(n, n,c).

```
All possible branches? Pruned branches?
```
.type branch = Cons { n :  node, c : color,  branch } | Nil


```

Mod out color choice.
```
same_color(x,y)
diff_color(x,y) :- edge(x,y)
```

## Propagators
### Boolean Constraint Propagation

```souffle
// Boolean constraint propagation

// 3-SAT encoding.
// x \/ y \/ z

.type var = number
// negative number represents "not x" as in DIMACS
.decl clause(x : var, y : var, z : var)

false(-n) :- true(n).
true(-n) :- false(n).

true(z) :- clause(x,y,z), false(x), false(y).
true(x) :- clause(x,y,z), false(y), false(z).
true(z) :- clause(x,y,z), false(x), false(y).

true(1). // 1 is true
/*
#define VAR(x) (as(x,number)+10000)
.type formula = Var {n : number} | True {} | False {} | And {x : formula, y : formula} | Or {x : formula, y : formula}
.decl assert(f : formula)
true(n) :- assert($Var(n)).

.decl assert(formula, ret : number)
.decl _assert(formula) // demand relation
_assert(x), _assert(y) :- _assert($And(x,y)).
_assert(x), _assert(y) :- _assert($Or(x,y)).

assert($Var(n), n) :- _assert($Var(n)).
true(nx), true(ny) :- assert(x,nx), assert(y,ny), _assert(e), e = $And(x,y).
assert() :- _assert(e), e = $Not(x).

uhhhh, what am I doing?




*/

```

### Difference Logic
path(x,y,c) <=> x - y <= c

can also encode equality and  x <= c constraints with zero node.

```souffle
.type var = symbol
// this relation represents x - y <= c
// It is interesting analogous to the relation path(x,y,cost)
// https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-smt/diff_solver.html
.decl diff_le(x : var, y : var, c : number)

.decl vars(x : var)
vars(x) :- diff_le(x,_,_); diff_le(_,x,_); diff_ge(x,_,_); diff_ge(_,x,_).
diff_le(x,x,0) :- vars(x).

// Helper definitions
// x - y >= c
.decl diff_ge(x : var, y : var, c : number)
// x - y >= c -> y - x >= -c
diff_le(y,x,-c) :- diff_ge(x,y,c).

// x <= c
.decl le(x : var, c : number)
diff_le(x, "zero", c) :- le(x,c).

// x >= c
.decl ge(x : var, c : number)
diff_ge(x, "zero", c) :- ge(x,c).

// x - y = c
.decl diff_eq(x : var, y : var, c : number)
diff_ge(x,y,c), diff_le(x,y,c) :- diff_eq(x,y,c).

// x = c
.decl eq(x : var, c : number)
ge(x,c), le(x,c) :- eq(x,c).

// Transitivity.
// x - y <= c1 /\ y - z <= c2  -> x - z <= c1 + c2
diff_le(x,z,c1+c2) :- diff_le(x,y,c1), diff_le(y,z,c2).

// tightest bound / shortest path
diff_le(x,y,c1) <= diff_le(x,y,c2) :- c2 <= c1.

/*
diff_le("x","y",2). diff_le("x","y",3). diff_le("x","y",4).
*/
diff_le("y","x",1).
diff_le("y","z",5).


.output diff_le(IO=stdout)
.output diff_ge(IO=stdout)

eq("x",2).
diff_eq("x","y", 5).

// x - y <= c /\ y - x <= -c -> x - y = c
diff_eq(x,y,c) :- diff_le(x, y, c), diff_le(y, x, -c).
// x - 0 = c -> x = c
eq(x, c):- diff_eq(x, "zero",c).
.output eq(IO=stdout)


// It is a choice whether to encode everything in term of diff_le
//diff_ge(y,x,-c) :- diff_le(x,y,c).
// diff_ge(x,x,0) :- vars(x).
// x - y >= c1 /\ y - z >= c2  -> x - z >= c1 + c2
//diff_ge(x,z,c1+c2) :- diff_ge(x,y,c1), diff_ge(y,z,c2).
// diff_ge(x,y,c1) <= diff_ge(x,y,c2) :- c1 <= c2.
```

```
(rule (<= (- x y) (Num c)) (<= (- y z) (Num c2)) ((<= (- x z) (Num (+ c1 c2)))))
; but then we aren't getting the merge goodness.
; so reflect the relational form into equational form (and back?)
(rule (<= (- x y) (Num c)) (set (upbound (- x y) (Num c)))
(rule (= (upbound (- x y)))

; (diff-bound x y) = c

; They do have different schema. But then we pollute the database with irrelevant facts. Hmm.
; But modelling wise I want to use <=.
; Either macros or inline relations. But only for some usages of <=
; (<= (- x y) (Num c)) <---> 


```
### Finite Domain

Use first class sets? Not necessarily
alldifferent?

```

//not_num(n).
num() :- num(i,j,n).

```
One hot encoding can be useful even if using not to represent sets


```souffle
// send more money

.decl S(n : number)
.decl not_S(n: number)


singleton(2 bshl n) :- range(n)

:- S(n), singleton(n)
range(),


```

I mean surely hakank has done this in clingo
```clingo

{s(0..9)}. {e(0..9)}.
{n(0..9)}. {d(0..9)}.


```




## Macros

```souffle

// souffle already offers heador h1, h2 :- body.
#define HEADOR(h1,h2,body)  h1 :- body. h2 :- body.

// h :- b1 ; b2.
#define BODYOR(h,b1,b2)  h :- b1. h :- b2.

// Compositional bodyor? Harder. In fact very hard...?
// h :- x, (b1 ; b2).


// x ; y :- z
//#define CALL(x,y,z)  x, z. y :- z.
//#define CALL2(a,b,c,d) c :- d. a :- b,d.
// How can these be chained?

// Ugh this is GROSS. But it can be chained. It will make duplicate predicates at the tail, but these will be pruned?
#define CALL(y, z)  z. y :- z

.decl fact(n : number, f : number)
.decl fact_q(n : number)

fact(0,1) :- fact_q(0).
fact(m,m * n1) :- fact(m-1, n1), CALL(fact_q(m-1), (fact_q(m) , m >= 0)).

fact_q(3).
.output fact(IO=stdout)

.decl fib(n : number, f : number)
.decl fib_q(n : number)
fib(0,1). fib(1,1).
fib(n, n1+n2) :- fib(n-2, n2), fib(n-1,n1)  , 
   CALL( fib_q(n-2) , CALL( fib_q(n-1)  , (fib_q(n), n >= 1))). 


//fib(n, n1+n2) :- fib(n-2, n2), fib(n-1,n1), 
//   CALL( ( fib_q(n-2), fib_q(n-1) )  , (fib_q(n), n >= 1)). 
// expands to:
//fib(n, n1+n2) :- fib(n-2, n2), fib(n-1,n1),
//   (fib_q(n), n >= 1). (fib_q(n-2), fib_q(n-1)) :- (fib_q(n), n >= 1).
// Ah. Hmm. No parenthesis allowed in head. Hence no way to call multiple predicates.

fib_q(4).
.output fib(IO=stdout)
```

The combinator is (a ; b) :- c where `a` can end up being a curried clause.
z :- x :- y. == z :- x,y.

We need a writer monad? We can store clauses at the back or front of the expansion, otherwise we might need to hold in a structure
```souffle
//PAIR(x,y)
#define FST_PAIR(x,y) x 
#define SND_PAIR(x,y) y 
#define FST(x) FST_ ## x
#define SND(x) SND_ ## x

FST(PAIR(7, "hello"))

```
Hmm. But it needs to be delayed.


```cpp
#define IMPL(h,b) PAIR(b , h :- b.)
#define BODY(...) __VA_ARGS__
#define BODY(x, ...)  x, FST(BODY(__VA_ARGS))

EVAL(IMPL(head, BODY(x,y,z)))

#define EVAL(x) E_ ## x

#define E_BIND(x, f)   PAIR( FST(f(FST(x))) , SND(f(FST(x)) SND(x) )


```
```c
#define E_FST_PAIR(x,y) x 
#define E_SND_PAIR(x,y) y 
#define E_FST(x) EVAL(FST_ ## x)
#define E_SND(x) EVAL(SND_ ## x)
#define E_BIND(x, f)   PAIR( FST(f(EVAL(FST(x)))) , SND(f(EVAL(FST(x))) SND(x) ))
#define EVAL(x) E_ ## x

```
```bash
cpp $0 && exit 0

#define FST(x,y) x
#define SND(x,y) y

#define APPLY(f,x) f x
#define ID(x) x

APPLY(SND, (1,3))
SND(1,2)
APPLY(SND, ID( (1,2) ))
SND(,)

```
```souffle
.pragma "dummy"
```

Writer monad for clauses and bodies.

```bash
cpp $0 && exit 0
#define RET(x) ( x , )
#define ORIMPL(x,y,z)  ( (x, FST z) ,  y :- (FST z). SND z )
#define IHEAD(y,z)  ( FST z ,  y :- (FST z). SND z )
#define CONJ(y,z)  (  (y, FST z) ,  SND z )
#define RUN(x)  SND x

#define FST(x,y) x
#define SND(x,y) y
RUN(IHEAD(fib(n, m1 + m2) , 
          CONJ(  (fib(n-2,m2), fib(n-1,m1)  ) , 
            IHEAD( fib_q(n-2) , 
            IHEAD( fib_q(n-1) ,
                 RET( (fib_q(n), n >= 1)  ))))))

```

I'm suggesting I wangt the disjunction of a goal and (g ; h)? That's pretty bizarre.
((h2 :- b1) ; h1) :- b2 

fib(n, n1+n2) :- ORIMPL( (fib(n-2, n2), fib(n-1,n1)) ,
                   fib_q(n-2), fib_q(n))
                  ORIMPL( ?, fib_q(n-1) ,     )).
This isn't working. There is something very odd about the recursion pattern here.


// These are non compositional.
#define ORBODY(h,b1,b2) CLAUSE(h, b1) CLAUSE(h, b2)
#define ORHEAD(h1,h2,b) CLAUSE(h1,b) CLAUSE(h2,b)
#define IMPLBODY(h, b1, b1) CLAUSE( h, (b1, b2) )
#define IMPLHEAD()

```

### List macros
Counting varargs
https://stackoverflow.com/questions/2308243/macro-returning-the-number-of-arguments-it-is-given-in-c
```souffle
#define NVARS(...) NVARS_(__VA_ARGS__, REV_NVARS())
#define REV_NVARS() 4,3,2,1
#define NVARS_(...) NVARS_N(__VA_ARGS__)
#define NVARS_N(_1,_2,_3,_4,_N, ...) _N

NVARS(x,y,z,w)

```

simpler. The idea is the the larger var args is, the 
```souffle
#define NVARS(...) NVARS_(__VA_ARGS__,4,3,2,1)
#define NVARS_(_1,_2,_3,_4,_N, ...) _N

NVARS(x,y,z,w)

```

Once you can count the number of vars you're good.

Better list syntax in souffle using cpp macro.

```souffle
#define LIST_1(x) [x, nil]
#define LIST_2(x,...) [x, LIST_1(__VA_ARGS__)]
#define LIST_3(x,...) [x, LIST_2(__VA_ARGS__)]
#define LIST_4(x,...) [x, LIST_3(__VA_ARGS__)]
#define LIST_5(x,...) [x, LIST_4(__VA_ARGS__)]
#define LIST_6(x,...) [x, LIST_5(__VA_ARGS__)]
#define LIST_7(x,...) [x, LIST_6(__VA_ARGS__)]
#define LIST_8(x,...) [x, LIST_7(__VA_ARGS__)]
#define LIST_9(x,...) [x, LIST_8(__VA_ARGS__)]

#define NVARS(...) NVARS_(__VA_ARGS__,9,8,7,6,5,4,3,2,1)
#define NVARS_(_1,_2,_3,_4,_5,_6,_7,_8,_9,_N, ...) _N

#define LIST(...) GLUE(LIST_, NVARS(__VA_ARGS__))(__VA_ARGS__) 
#define GLUE(x,y) GLUE_I(x,y)
#define GLUE_I(x,y) x ## y

.type list = [hd : number, tl : list]
.decl test(x : list)
test(LIST(14,57,34,46,52,7,34)).
.output test(IO=stdout)
/*
---------------
test
x
===============
[14, [57, [34, [46, [52, [7, [34, nil]]]]]]]
===============
*/
```
https://twitter.com/SandMouth/status/1551384178494668800?s=20&t=RCRFQkOrxezpvPdn1ABsBA ed kmett is up to some crazy looking shit.

really the most boring version of this is to just spell out the cases and not use VA_ARGS. I will admit va_args makes it tighter. And just label the pattern LIST_N by it's size, you whiner. The macro weirdness to infer N is probably not worth it.  If you make the last argument by convention the tail of the list, these are useful for patterns like `a :: b :: xs` too.
Also these can be chained like so : `LIST_3( 1,2,LIST_3(32,324,nil))`
Eh. Maybe the above isn't so bad. Counting the args is kind of a pain.

```souffle
#define LIST_2(_2,_1) [_2, _1]
#define LIST_3(_3,_2,_1) [_3, LIST_2(_2,_1)]
#define LIST_4(_4,_3,_2,_1) [_4, LIST_3(_3,_2,_1)]
#define LIST_5(_5,_4,_3,_2,_1) [_5, LIST_4(_4,_3,_2,_1)]
#define LIST_6(_6,_5,_4,_3,_2,_1) [_6, LIST_5(_5,_4,_3,_2,_1)]
#define LIST_7(_7,_6,_5,_4,_3,_2,_1) [_7, LIST_6(_6,_5,_4,_3,_2,_1)]

.type list = [hd : number, tl : list]
.decl test(x : list)
test(LIST_7(57,34,46,52,7,34,nil)).
.output test(IO=stdout)

```

Hmm. Rather than skolemization, inlining seems good. Gives us sound (hopefully) existentials.

foo(x,y) :- 




## Emulating Prolog
Datalog is bottom up and prolog is top down. In a sense datalog feels “push” and prolog feels “pull”. These viewpoints can be translated to some degree to each other. Prolog can gain some benefits of datalog via tabling, which is a memoization technique. Likewise datalog can become goal driven via the “magic set transformation”, The following is a simplified but intuitive presentation I believe of the vague idea.

Relations in prolog can be used in different [modes](https://www.swi-prolog.org/pldoc/man?section=modes) (this is prolog terminology btw. An interesting concept). It’s part of the beauty of prolog that relations are sometimes reversible or generative if written to be so. Sometimes prolog programs are written to only behave correctly if used as if they were essentially a function.

What is and isn't datalog?

What is and isn't function symbols? Function symbols are a subtle thing. You can encode function symbols into flat relations with different powers. Functions are a subset of relations after all. Existentials and gensyms

What is and isn't ground?

What is and isn't pattern matching vs unification. In some sense datalog is a pattern matching language, not unifying language.






### Need Sets


If you find yourself needing what is essentially a function call on a relation, you can define “need” relation for that relation that takes the arguments. Then the regular clauses producing that relation also take the need relation to push in the actually needed instantiations of the clause. Here is an example for factorial. We examine the body of fact to see that we need the recursive call evaluated in order to evaluate.

```souffle
.decl fib(n : unsigned, m : unsigned) //choice-domain n
.decl need_fib(n : unsigned)

fib(0,0).
fib(1,1).
fib(n, i + j) :- need_fib(n), fib(n-1,i), fib(n-2,j), n > 1.
need_fib(n-1), need_fib(n-2) :- need_fib(n), n > 1.

need_fib(6).
.output fib(IO=stdout)
.output need_fib(IO=stdout)
```

We have the expense of the extra table but we have gained pull based evaluation. Bottom up evaluation of fact would not terminate without an a priori bound on the argument. We could use subsumption to reduce the size of this table in this case.

Choice domain may present an optimization. It is marking the relation as functional in character, which in principle could allow soufflé to use an optimized data structure. I hope it makes things faster and doesn’t just add unnecessary checks on insert.
I a little bit suspect it will just make things slower.

Basically the idea is, you need to pick which top down modes you want to support, i.e. which of the prolog fields you expect to be grounded and which you don't. Then you can make a new relation that holds only the grounded fields. You make clauses that push down the need for every recursive call.
When you're translating typical functional algorithms, there is typically only the one functional mode required `-+`.

If you are using ADTs then perhaps one should consider the flattened version of the adt? ADTs only support some particular modes in the first place either ---+ or +++-. Give all args or give term and get args.


We could possibly subsume to reclaim need_fib? Hardly seems worth it.
```
need_fib(n) <= need_fib(m) :- fib(n,_). // doesn't do anything. Subsumption bug?
need_fib(n) <= need_fib(m) :- fib(n,_), n < m. // this one works. I don't know why n < m is required.
```

In what sense is need_set representing the call stack?

A common pattern when working with ADTs is I need a predicate of all subterms. This can be viewed as part of the need_set pattern. Recursive Functions that fold over terms are capable of sharing need sets. `terms` is really the need set of `fold`. That's interesting. So if you use combinators / recursion schemes to abstract over the recursion, you can use a `cata` need set. In some sense perhaps datalog can only express anamorphisms. `fold` is often seen a a fundamental combinator, capable of expressing anything (if you have highr order functions too).

A lot of what I'm doing is defunctionalizing a continuation

CHR also has need sets. Things that unlock computation.

### Magic Set

Magic sets are a way to emulate some flavor of the top down execution of prolog in datalog.

Magic set talks about binding patterns. In prolog, one can use relations in different modes. A field of a prolog relation may be an unknown unification variable or it may be a concrete ground term. In datalog, relations only receive ground terms. We can partially emulate the "unknownness" by lifting to an Option datatype.

```souffle
.type OptionNum  = None {} | Some {x : number}

.decl fib(x : number , y : OptionNum)
// fib(1,$Some2)) is the same as fib_bb(1,2) and
// fib(2,$None()) is the same as fib_bf(2)
```

In a lattice based datalog, we can use Option as a lattice type, filling in the value later at our leisure and erasing the scaffolding we used to make it.







Specializes datalog program to a particular query / output.
Query answer transfomation

We could imagine applying dataflow analysis techniques to prolog programs. We can write dataflow analysis in a pleasant way using datalog. The languages of datalog and prolog coincide. Datalog terminates.

I suppose I identify datalog with bottom up execution, which is not necessarily the case depending on author.

In prolog SLD resolution, there are program points. We could create relations describing the store at these points. These are the supplementary 
For annotated predicates we could move the annotations as extra fields of the predicates instead of as annotations. This feels more natural when interpreting as a dataflow analysis. Annotations are a describing the binding state? (annotations are lattice? Maybe so but not in the right way)

"It is a form of partial evaluation: at query time, rewrite (specialize) the entire program to an equivalent one, then evaluate it bottom-up. A binding-time analysis identifies which predicates benefit from specialization. Sideways-information passing strategy guides the rewrite."

"I see it as a way to "hack" a bottom-up execution (from facts) into computing top-down (from queries). John Gallagher's query-answer transformation is related to that and used for program analysis https://arxiv.org/pdf/1405.3883.pdf, https://bishoksan.github.io/papers/scp18.pdf"



Emulating clp evaluation of prolog. The constraint store. Dif constraint into egglog.
What matters in a prolog context.
Order of goals hypothetically doesn’t matter? We want to hash cons to unique representatives of stuff that doesn't matter.
Scoping of fresh vars? Maybe a list of clauses that produced fresh vars. Does that order matter in principle? It might because unification can
Dif kind of lets us do a piece of scope escape prevention. Doesn’t contain.
What causes unification vars to exists? Presence fresh in a rule.
De bruin as cause. The binders cause variables to exist. Hence de bruin is close to a canonical rep.
Varmap says usage sites cause to exist?
Existential var in body. We can choose to ignore in datalog. Or we can say it would have been grounded eventually by some grounding site. (Or terminated on a ground fact.) yeah. A non ground fact could be seen as a new kind of constant?

[magic set slides](http://users.informatik.uni-halle.de/~brass/lp07/c7_magic.pdf)
- tail recursion is more efficient in sld resolution.
- metainterpeter. partial evaluation of metainterpeter with respect ot program and query, but not database. "sldmagic"

[A Framework for Bottom-Up Simulation of SLD-Resolution](https://users.informatik.uni-halle.de/~brass/push/publ/iclp14.pdf) bottom up metainterpeters
SLDMagic
"Sniped! I have never understood it but have wanted to. The output has always looked to me like constprop (bottom-up) and specialization (top-down), repeating." - Goodman
Resprenting sets of goals.


binding patterns using Option. Could also allow options in fields of adts.
```
.comp Option<T> {
  .type t = None {} | Some {x : t} 
}

fib()
```
What about `foo(X,X,1)`? `foo(None, None, Some(1))` is an over approximation of this case, losing the equivalence info. Well, therse constraints are also probably finitely enumerable.


sideways information passing strategy - SIPS. I think this is kind of picking an equivalent prolog evaluation order

[Efficient bottom-up computation of queries on stratified databases 1991](https://www.sciencedirect.com/science/article/pii/074310669190030S)

[Query evaluation in recursive databases: bottom-up and top-down reconciled bry](https://www.sciencedirect.com/science/article/abs/pii/0169023X90900178)


[Abstract Interpretation of Logic Programs Using Magic Transformations](https://www2.cs.arizona.edu/~debray/Publications/magic.pdf)

[Demand transformation](https://arxiv.org/pdf/1909.08246.pdf)
Is this he proper term for "need set"?
[More Efficient Datalog Queries: Subsumptive Tabling Beats Magic Sets∗](http://epilog.stanford.edu/logicprogramming/readings/tekle.pdf)
Is this saying need_sets may transfer to each other? Or subsume each other?
Can't even express this i don't think
p(x,y) <= p(x) :- 
Unless you use the $Var | $Lit wrapper
But this isn't even right.
p($Var(), $Var()) <= p($Lit(), $Lit())


KT Tekle
Liu


```souffle
.type UList = UL {n : number} | Cons {a : symbol, b : UList} | Nil {}
.type UNum = UL {n : symbol} | Lit {n : number}

// append([],A,A). 
// append([A | X], Y, Z) :- append(X,Y,Z1), Z = [A | Z1].

.decl append(x : UList, y : UList, z : UList)
.decl d_append(x : UList, y : UList, z : UList) // demand. Flow down.
append($Nil(), $UL(n), $UL(n) ) :- d_append($Nil(), $UL(n), $UL(_)). // or pick max?
append($Nil(), x, x ) :- d_append($Nil(), $UL(_), x).
append($Nil(), x, x ) :- d_append($Nil(), x, $UL(_)).

d_append(x,y,z) :- d_append($Cons(_,x), y, z).

// We need a pattern matching case? What if two UL alias?
d_append($Nil(), y,z) :- d_append($UL(m),y,z). // d_append($Nil(), y,z) should be another case. This isn't even right anyway


append($Cons(a,x), y, z) :- d_append($Cons(a,x), y, z), append(x,y,z1), z = $Cons(a,z1).

d_append($UL(0), $UL(1), $Cons("a", $Nil())).

.output append
```

Do immediate unification ahead of time?
Alternatively use explicit eq

```souffle
.type UList = UL {n : number} | Cons { }
.type UNum = U {n : symbol}

// append([],A,A). 
// append([A | X], Y, Z) :- append(X,Y,Z1), Z = [A | Z1].

.decl append(x : UList, y : UList, z : UList)
eq(y,z) :- append($Nil(), y, z), (y = $UL(_) ; z = $UL(_)).
// structural unification
eq(a,a1), eq(b,b1):- eq( $Cons(a,b), $Cons(a1,b1)).

// how do we have eq handle the two branching cases.


```

### First class union find
Need to carry an explicit union find field to thread? Slash an explicit substition mapping (slash homomorphism which is insane terminology)

eqrel gives _global_ union find. Sort of the question is how to have local consistent union finds.
reflecting local to global when it is good?

```
.type uf_num = {Ref {id : number, parent : uf_num}} | Lit {n : number} | UnBound {id : number}
// vs
.type uf_num = Ref {id : number} | Lit {n : number}
// vs
KV<number,Option<number>> // even more first class
```

 Inside scope of a single relation, we can keep things self correlated. To join uncorrelated predicates.
To some degree datalog is like a message passing system. The operational guarantees of ordering are quite low. Each relational entry is like a message. I can send a message requesting some information and then recieve a response saying what the result was.

A curried notation would be nice for functional patterns where we send demand and then receive.
( ( res :- continue  , recv)   , send :- start )

## Translating Imperative Programs
similar to translating to functional style.
Figure out the state. Make them all parameters to relation
One style is:
```
foo(nextstate) :- foo(state).
```

You need program counter to do in this style.
Instead can use store style. Every statement of program gets own relation. Need to pass entire store

```
line2(newx) :- line1(x), newx = x + 1.
line3(x,y) :- line2(x), y = x * 3
```

We're edging on dataflow analysis at this point.

```souffle
line2("x", x + 1):- line1("x", x).
line3("x",x) :- line2("x",x).
line3("y", x *3) :- line2("x",x).
```

Note the big difference here though. We have _factored_ the old line3 relation. The new version is not capable of storing seperate runs without dataloss. We no longer would know which "x" corresponded to which "y".
This is of some relation to lossless joins and things in database theory.
This factoring can be useful as an overapproximation technique.

### Iteration 
This is related to timestamping.
See mandelbrot example.
Iteration isn't quite as silly as you'd think. Semi naive means we only work on the frontier of the loop.
Loop counters are the state of the loop.

```souffle
/*
acc = 0;
for(i = 0; i < 10; i++){
  acc += i;
}
*/
.decl sumn(iter : number, acc : number)
sumn(0,0).
sumn(i+1, s + i) :- sumn(i,s), i < 10.
.output sumn(IO=stdout)

```




## Model Checking
See Chapter 8 State-Space Search with Tabled Logic Programs

Farmer puzzle

Die Hard puzzle
```souffle
.pragma "provenance" "explain"
.decl reach(big : unsigned, small : unsigned)
reach(0,0).
// move water small to big
reach(big + small, 0) :- reach(big,small), big + small <= 5.
reach(5,  small - (5 - big)) :- reach(big,small), !big + small <= 5.
// move water big to small
reach(0, big + small) :- reach(big,small), big + small <= 3.
reach(big  - (3 - small),  3) :- reach(big,small), !big + small <= 3.
// empty big
reach(0, small) :- reach(_,small).
// empty small
reach(big,0) :- reach(big,_).
// fill big
reach(5, small) :- reach(_,small).
// fill small
reach(big,3) :- reach(big,_).

.decl big_is_4(small : unsigned)
big_is_4(small) :- reach(4,small).
.output big_is_4(IO=stdout)
/*
---------------
big_is_4
small
===============
0
3
===============
Explain is invoked.
Enter command > setdepth 10
Depth is now 10
Enter command > explain big_is_4(3)
reach(0, 0)                          
--------(R8)                         
reach(5, 0)  5 > 3                   
---------------(R5)                  
    reach(2, 3)                      
----------------(R7)                 
    reach(2, 0)      2 <= 3          
------------------------(R4)         
        reach(0, 2)                  
-------------------------(R8)        
         reach(5, 2)          7 > 3  
--------------------------------(R5) 
            reach(4, 3)              
---------------------------------(R1)
             big_is_4(3)             
*/
```


## Timestamping 
Transtion systems. All possible executions. Model Checking.
Dedalus
```souffle
.decl foo(a : number, b : number, time : unsigned)
foo(a,b,t) <= foo(a1,b1,t2) :- t < t2. //possibly allow subsumption of new states only. This won't build all possible paths though.
foo(x,y,t) :- bar(x,t1), biz(y, t2), t = max(t1,t2) + 1.

reached(a,b) :- foo(a,b,t). // how will this interact with subsumption? Why even bother timestamping if you just want reached.
```

Using datalog to control reactive systems

```souffle
//.pragma "libraries" "libc.so.6"
.functor time(): unsigned // unix system call
.decl timestamp(t : unsigned)
timestamp(@time()) :- true.
.output timestamp(IO=stdout)
```
Ah I see 
<https://github.com/souffle-lang/souffle/blob/d1522e06c6e99c259951dc348689a77fa5f5c932/src/interpreter/Engine.cpp#L381>
I can't open libc.so.6 because this string is being made in this way. libc.so is not the right kind of file.

[Integrity Constraints for Microcontroller Programming in Datalog](https://users.informatik.uni-halle.de/~brass/micrologS/) arduino timestamping, external pin relations. pretty cool.
[Microlog - A Datalog for Microcontrollers and other Interactive Systems](https://dbs.informatik.uni-halle.de/microlog/)

[Dedalus](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2009/EECS-2009-173.pdf) http://bloom-lang.net/faq/

Timely dataflow - modelling frontiers in datalog? What frontiers reach where is kind of a static analysis

## Theorem Proving
A lot of these techniques are taken from interpeting the Lambda Prolog rules.
Question: Is it possible to consider static analysis over lambda prolog to systematically understand some of these tricks?

Consider Jens Otten tutorial

When is the difference between an ATP system like Vampire and Datalog really? They are closer than you might think on first inspection. Both are bottom up systems. Datalog significantly restrict their clause structure. Datalog matches, but doesn't unify.

### Skolemization for Existential Heads
$ \forall x, \psi(x) \implies \exists y, \phi(x,y)$ can be replaced with 
$ \forall x, \psi(x) \implies \phi(x,y(x))$ where y is now the function that selects the approproate existential value. You can represent function symbols of this kind wtih ADTs. ADTs are great because they know if you've already made the symbol or not.
```
.type Skolemized = Y { x : xtype } | Lit { a : ytype}
```
An alternative semantics might be to try

$ \forall x, \psi(x) \implies \phi(x,autoinc())$ but then the thing will never terminate.

### Goals / Queries
Souffle doesn't quite have a notion of goal. But `.output` relations are the analog of goals/queries.
The magic set transform works this way.

If in prolog you would write
```
?- foo(X), bar(X,Y,7).
```
as a query, you can do the same thing by naming this query

```souffle
myquery(x,y) :- foo(x), bar(x,y,7).
.output myquery
```

In theorem proving, your axioms because clauses, and your to-be-proved theorem will become a goal of this variety.

### Uncurrying 
A logical formula of the form
$p \implies q \implies r$
is equivalent to 
$p \land q \implies r$
`r :- p, q`
So you can express axioms of this type by uncurrying.

A alternative approach to dealing with the same class of formula is "defunctionalization". Make predicates for each partial application of a horn clause.

```
part_rule1(x) :- p(x)
r(z) :- part_rule(x), q()
```
### Contextual Datalog / Hypothetical Datalog
[hypothetical datalog](http://www.fdi.ucm.es/profesor/fernan/FSP/Sae13c.pdf) https://www.sciencedirect.com/science/article/pii/0304397590900116

https://www.philipzucker.com/contextual-datalog/


### Higher Order Clauses (Harrop)
$ (p \implies q) \implies r$ is a different animal from the above.
I'm not super sure how to deal with these.
I'd suggest that predicates need to be extended with a notion of context. Higher order rules like these are interpetted as something like

```
r(ctx_without_p) :- q(ctx_with_p)
```

What precisely I mean by ctx is unclear here. It seems like I'd need to internalize relations and or clauses into the language of datalog itself.
Contexts do have a partial order. Derivations in weaker contexts can subsume strong ones.
I suspect we are running into serious problems where we are just lacking the appropriate primitive to do this efficiently.


Consider
```
bar(x,y) -> (biz(x) -> baz(x,y)) -> foo(x) / rule7
```
We can curry / materialize the subquery
```
bar(x,y) -> need_bizbaz(x,y)
```

This defunctionalize thing becomes the need set / magic set of a contextual query.
We can partially evaluate the ctx to be part of the rules or not
```
.type Ctx = Glob {} | BizBaz {x : number, y : number}
```

We 
```
//insert the body of the higher order rule.
biz($BizBaz(x,y), x) :- need_bizbaz(x,y).
// maybe we can fuse need_bizbaz out and just directly have biz($BizBaz(x,y), x) :- bar(x,y).

// finally if we succeed we can lower back into the global context.
foo($Glob(), x) :- baz($BizBaz(x,y), x, y).

// ordinary rules just carry the context along
far(ctx, 7).

// or we can lift any rule to a higher context
far($BizBaz(x,y), z) :- ctx($BizBaz(x,y)), far(Glob(), z)

// or we can just use the lower context in rules with the needset

// need_bizbaz(x,y), 

```

We can make context arbitrarily deep, but we have to make a cutoff. Probably going higher than 2 is gonna not be so good. 
This is similar feeling to k-CFA.

Anything that can be produced from biz needs a contextual verision. bar(x,y) can be considered the same as bar(Glob(),x,y). That's a different convention. Instead of adding context everything have bar and bar_ctx, where implicilty bar is Glob.

Can use subsumption if you learn fact should go in database.

#### Stack database / Harrop Datalog / Tentative Datalog
Blog post: [Contextual Datalog: Steps Towards Lambda Datalog](https://www.philipzucker.com/contextual-datalog/)

You can organizing your database into a stack. You can refactor this in a number of ways. 
In seminaive you have a old, new, and delta table per  relation. You can make old into `[old]` and only commit into the top of the stack. 
You could also factor the entore `[database]` into a stack of databases instead of per relation.
You could also add an extra stack height key into every row and then call `DELETE where stack >= N` when you want to pop (even pop far).

`a :- (b :- a)` is an idiom for "suppose a. If I find b, commit to a.

hypothetical predicate a's variables need to be grounded by other predicates in the body of the clause, in the datalog style.

Note that egglog + stack database gives similar power to scoped union find. And extra parameter in all rows is similar to explicit scope parameter.

Taking inspriation from scoped union find:
We don't need it to be a stack. It can be a tree of databases. We may need provenance information on the edges between parent and child to avoid rederivation. Commutativty of hypotehticals can be quite wasteful. The first fact that goes in the new child would be the hypothetical fact. Before doing hypothetical, one should check if fact already exists or not. If so, (b <- a) is effectlively b by modus ponens.

Does commutativity mean that it isn't a tree of databases, but a dag?

Termination seems questionable even with requirement of atomic terms.

One should maintain that deeper tree leaves are set differenced from their parents. Maintain "triggers" that say what fact needs to be derived to remerge up into their parents. This remerging may require a set diffing on the parent's other children.

Is this diff-tree a general pattern over lattices / posets?

We mostly don't want to index on context, so putting it out the outer level doesn't seem right.

anti chain lattice

```python
class AntiChain():
  def __init__(self, sets):
    self.sets = sets
    #for s in sets:
    #  self = self.add(s)
  # makign this not mutate was dumb
  def add(self,s):
    if any([s1.issubset(s) for s1 in self.sets]):
      return self
    else:
      ac = AntiChain([ s1 for s1 in self.sets if not s.issubset(s1) ])
      ac.sets.append(s)
      return ac
  def normalize(self):
    a = AntiChain([])
    for s in self.sets:
      a = a.add(s)
    return a
  def __len__(self):
    return len(self.sets)
  def __repr__(self):
    return repr(self.sets)
  def bottom():
    return AntiChain([])
  def join(self, rhs):
    if len(self) < len(rhs):
      a = self.sets
      b = rhs.sets
    else:
      a = rhs.sets
      b = self.sets
    a = AntiChain(a.copy())
    for s in b:
      a = a.add(s)
    return a

a = AntiChain([{1,2}, {2,3}])
print(a)
b = a.add({1})
print(b)
print(b.join(a))
print(b.add(set()))
a = AntiChain([{1,2}, {2,3}, {1}])
print(a)
print(a.normalize())
'''
[{1, 2}, {2, 3}]
[{2, 3}, {1}]
[{2, 3}, {1}]
[set()]
[{1, 2}, {2, 3}, {1}]
[{2, 3}, {1}]
'''
```
Could order sets by size. That could trim down on what to look at.
s <= s1 only is possible if len(s) <= len(s1)

heuristic: look at set size itself bucket (to try and find the set itself), then look from largest down.

If we didn't use hashsets, instead some kind of trie set, we could have a set of sets.

[set trie](https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0245122) there is no way this should be a 2021 paper?
Ah they use sorted lists as the sets. That's interesting. 

https://github.com/KaiserKarel/set-trie

```python
class Trie():
  def __init__(self, data=None):
    self.data = data
    self.children = dict()
  def lookup(self,k):
    if len(k) == 0:
      return self.data
    else if k[0] in self.children:
      self.children[k[0]].lookup(k[1:])
    else:
      return None
  def insert(self, k):
    if len(k) == 0:
      return
    else if k[0] in self.children:
      self.children[k[0]].insert(k[1:])
    else:
      c = Trie()
      self.children[k[0]] = c
      c.insert(k[1:])
  def delete(self,k):
    if k[0] in self.children:
      if len(k) == 1:
        del self.children[k[0]]
      else if len(k) > 1:
        self.children[k[0]].delete(k[1:])

```

Q : when are first class sets necessary and when can you get away with an external or tagged set? `myset(tag, x,y,z).`
Presumably when you need to know something "global" about the set. But they have a lattice character? So like...?  Well the lattice is the antichain lattice, not the sets themselves. They kind of anti-cgrow. not_in_ctx(tag,x,y,z)?
If I had every possible context in there to start. Sure. That's silly though. If I need a tag uniquelt derivable from the set itself... hashing a set with xor?
// I can build tagged unions
set(t1, ), not_set(t1, )
not_set
set(t3, a), set(t3,b) :- set(t1, a), union(t1,t2, t3), set(t2,b).
not_subset(t1,t2, "true") :- set(t1,a), !set(t2,a). This isn't so good.
not_eq(t1,t2) :- set(t1,a), not_set(t2,a).
eq(t1,t2) :- forall a : set(t1,a), set(t2,a).
 We can't derive set equality or diseqauality.

The point of first class sets is closedness. Maybe this is a kind of peculiar stratification (partially ordered time?)? We need to ask aggregate questions of the set (forall, exists, count).

Another kind of reflection. We can memoize if you like all operations.
```
set3(s, @myindex(s,0), @myindex(s,1), @myindex(s,2)) :- set(s), s = [3,_data]
set2(s, @myindex(s,0), @myindex(s,1)) :- set(s), s = [2,_data]
```

We could use a bounded quantifier if we retain the size?
:- set(size,tag), forall i : range(n): setind(tag,ind,a)
for union size <= size1 + size2.
So size would be a lowering quantity.
explicit index fights the useful capability of deleting duplicates

first class maps gives us first class eqclass. f(x) = min(y : eq(x,y))

### Existenial Queries
Existentials in bodies and toplevel query are interpreted as pattern matching.

Possible alternative: contextual eq relation.
If there aren't that many variables at play, can encode into integer. And also if they can't get grounded. Hmmm.

```
foo(X,X,Y).
//foo(7,A).
foo(X,Y,X).
foo(d,Y,Z).

?- foo(a,B,C).
```
emulate this in datalog.

```
need_foo(empty_uf, $A_const(), $B(), $C()).
foo(ADD(x,y,ctx) ,x,y,z) :- need_foo(eq, x,y,z), can_unif(eq,x,y).
foo(ADD(x,z,ctx) ,x,y,z) :- need_foo(eq, x,y,z), can_unif(eq,x,z).
```

```
.type Lift = A_const {} | B {} | C {} | D_const{} // | Lit {n : number}
```


A canonical notion of first class equiv rel is mapping from elements to maximum element of their eq class.
or set. should always make constants higher than unif variables
Bitset map is just ordered assoc list. 32 bits can support 9 -> 9 mappings. 8 -> 8 is easier. every 4 bits.
234222.
A tuple set take n^2 bits. Uh we can order them. n(n-1)/2 bits = 32. Hmm. So that is also 8 elements. Annoying to update though. I guess the other one is annoying to update too. THe canonicalization is annoying.




### Universal Quantifier
$\forall x, foo(x)$ is not a probem in unification based prolog, but it is in pattern matching based datalog where everything needs to be grounded in the head by the body of a clause.

Bounded quantification is one solution.
$\forall x \elem [0,10], foo(x)$
`foo(x) :- x = range(0,10)`

Not particularly satisfying.
We might also try to globally collect up all constants of that type. This is similar to the above, but a slightly diffferent flavor.
`foo(x) :- allsymbols(x)`

`allsymbols` can be manually instantiated as ground facts or generated from any predicate that uses symbol of said type
```
allsymbols(x) :- biz(x,_,_).
allsymbols(x) :- biz(_,_,x).
allsymbols(x) :- baz(x,_). 
```


Some foralls that are part of rules can just be dropped. $\forall x, \phi(x) \implies \phi(x)$. I suppose this could be considered an optimization of the `allsymbols` strategy.


We can initialize the database with a set of "fresh" symbols. And carry around explicit signature
`foo(sig,ctx) := sig ; ctx |- foo`
 By making sig a first class set, we don't need to worry about permutations of elements inside sig.
 We should worry about permutation inside fields of ctx. We will rederive essentially identical theorems for more names of fresh vars. :(
 ctx needs to be free of a to derive forall
 `forall_foo(sig \ {a}, ctx, bvar(0)) :- foo(sig, ctx, a), elem(a,sig), free(a, ctx).`

 We need to seed predicates that a can be possible value of domain
``` 
For fresh vars:

-------------------- Ax1
a ; foo(a) |- foo(a)

For actual "meaningful" (top level) values.

    val(x)
-------------------Ax2
 {} ; foo(x) |- foo(x)
```

```
values(SING(a), a).
foo(ctx,SING($Foo(v))) :- values(SING(a), a).
```
We also may have subsumption of the signature in the same way as ctx. We need to assure the varable appears in neither ctx nor fields before we can delete it.

If sig is nameless, when we combine/join sigs from separate relations, what do we get? All possible ways of matching up the two? Or maybe we just concat the sigs? That is the most general theorem. And we are always free to identify elements in the sigs? Is that a valid form of weakening the signature? We can also susbtitute?
`foo({}, ctx, x) :- foo({a}, ctx, a), value(x)`
From top down, the sig vars are fresh, very rigid. From bottom up they are the opposite. They can become anything, including a forall.
We could only support linear production of sig vars. Then they are represented as Var. Connect via explicit =. Hmm. but they do have to connect in the context to the front. Ok, what about in the context they are position maps (einlcudng empty ) into the front of |-. That is a canonical order. exlicpit A = B in context can do some stuff. Can't have cnnectec variables in context that don't appear in head. Can represent refl rule. Head is a kind of binder?
Can always I suppose add extra dummy predicates to place hold stuff. Kind of funky.
When we transfer contexts `foo( ctx1 U ctx2, y) :- bar(ctx1, x), biz(ctx2,y).` this is now a much more invasive thing. We need to traverse the contexts and remap them. If we lost the reference to x, now ctx1 can't be genralized to things.
Ok what if fresh vars can refer to var in the head _or_ to the explicit ordered sig list. We've lessened permutation problems at least.
There isn't a problem giving vars in the head number label. Then we can have equality constraints in the head. Order them left to right. We can also use these numbers in the ctx. Don't need maps anymore.

universal without contexts as simpler problem

existentials causes skolems, universals cause frees? Kind of reversed feeling from my gut. turning a forall into a var in backward mode is making a fresh var. In forward mode it is sealing a flexible var, a unification variable of sorts.
The subst rule of harrison.


```souffle
.type wrapnum =   Lit {n : number}
                | Skolem {a : symbol, args : vec}  // | Skolem0 { a : symbol} | Skolem1{a :symbol, n : number}
                | Free {k : unsig ned}
                | BVar {k : unsigned}

// instnating
foo($Lit(n)) :- foo($Free(_)), vals(n).

eq($Free(0), $Free(0)). // eq(X,X).
forall_foo($BVar(0)) :- foo($Free(0)).

foo($Free(0)) :- forall_foo($BVar(0)).
// or
foo(x) :- forall_foo($BVar(0)), val(x).
// but really this is transitively true
foo() :- foo($Free(0)).

// The cases are finitely enumerable, since the relations are flat.
bar(x,y) :- bar($Free(0), $Free(1)), val(x), val(y).
bar(x,x) :- bar($Free(0), $Free(0)), val(x).

// datalog is probably smart enough to deal with this.
bar(x,y) :- bar($Free(n), $Free(n)), val(x), val(y), ((n = m, x = y); n != m).

```
forall x, foo(x) /\ bar(x).
We need to defunctionalize foo_bar and/or forall_foo_bar.
```
forall x, foo(x) /\ bar(x)
--------------------------
foo(x) |- bar(x)      bar(x) |- foo(x)
```

Eh what's the point of this one. forall x, foo(x) /\ bar(x) ==> forall x, foo(x)
forall x, foo(x)  /\ forall x, bar(x) ==> forall x, foo(x) /\ bar(x)
So this is all fine. We don't need to worry about that shared predicate really.

We're kind of locally namelessing but very shallowly? And we are canonically naming free variables by first appearance in depth first traversal of tree, so they may need to be renamed as substitutions screw that up. Not desirable in a lambda term.

Free is kind of doing a union find. Maybe some kind of local union find could help?

We have to do a ton of shifting of indices in the context.
It really helps to ignore ADTs and just talk about forall for flat datalog-like things.

Logic with these instantiable variables is a very primitive thing.


Options:
- Limit avaialable variable patterns
- Discrimiination tree. At leaves point to actual variable names. Variable in tree are labelled or no.
- Matching modulo permutation of variable names
- 

Clauses in ATP must have solved this problem. Deduplication of clauses, subsumption of clauses.
Maybe universal is what makes it not datalog anymore
prune context tables like rebuilding?
Just ignore problem


No I thought I had it, but there are still very serious permutation issues.
The signature is somehow trying to capture a permutation invariance in the same way the set like character of the context is.

A trie of tries. Tries themselves are trees.
To build a trie in souffle, we'll need maps. Assoc vectors.
Try using ascent? Why not.
ref counted opauqe objects in souffle. But how would we call dec on ref count?

Normalized Variables representation. See term indexing chapter pg 1889
Could use polynomials to represent in souffle without branching.
use min to represent unification

```
append($Var(0),$Nil(), $Var(0)).
append($Cons($Var(0), x), y, $cons($Var(0), z) ) :-
  append(x,y,z), lift(x,y,z).

//memoized
max($Var(0), 0).
max($Var(1), 1).
max($Cons(x,y), mz) :- max(x,mx), max(y,my), mz = max(mx,my).

shift()

```

Man embdding this in souffle seems tough. We really need to destructure
If however I use a custom term representation
```souffle
// type term = [head : symbol, args : vec]

//.type term = [head : symbol, nargs : unsigned, args : number]
// ambiguous record. This stinks.
// #define ADD(x,y) ["add", 2, as([x,y], number)]

//.type AExpr = Add {id : number, }
.type term =  T0 {head : symbol} 
            | T1 {head : symbol, x : term}
            | T2 {head : symbol, x : term, y : term}
            // binary terms is sufficient, but painful
// we can detect T0 T1 from C++ side.
#define ADD(x,y) $T2("add",x, y)

.decl test(f : term)
//test(nil).
test(ADD($T0("x"),$T0("y"))).
```

First class union find [0,1,1,1]
@perm3(uf, 2,1,1). returns uf of var [v2,v1,v1], which in this case would be [0,0,0]. since v2 and v1 point to each other. 
Decouples naming variables from the data structure itself.
Variant checking and a subclass of subsumption become easy.
`foo(x,y,z, uf1) <= foo(x,y,z,uf2) :- @subuf(uf1,uf2).`

Awkward and error prone to manually program with. Needs metadatalog.
```
.decl nvar(t : term, n : unsigned)
#define GROUND(t) nvar(t,0)
``` 
Sometimes this may be necessary to step over unexpanded terms.

Relative of co-de bruijn. Also relative of term indexing. Discrimination trees.
Bad indexing for non concrete terms.
We can tell the difference easily between `$Var()` and `a` in a pattern. 

```
#define NIL $Symbol("nil")
#define T2(f,a,b) $App($App(f,a),b)
#define CONS(x,xs) T2($Symbol("cons"), x, xs)


append_a($Var(),$Symbol("nil"), $Var(), [0,0]).
append_a(CONS($Var(), x), y, CONS($Var(), z), uf) :-
  append_q(), append_a(x,y,z, uf1), nvar(x,nx), nvar(y,ny), nvar(z,nz), uf = @perm(uf, ???).
append_q().
```
@nvars(t:term):unsigned
The union find surgery is more complex than I thought. Go figure.
@slice(uf, 0, nx)
@swap(uf, i, j)
@insert(uf, n, i) (may require shuffling)
@concat(uf1, uf2)
@makeset(uf)
@union(uf, i, j)
@find(uf, i) ??? Will I need this?
Maybe append(x,ufx, y,ufy, z, ufz) is better convention? toplevel packing of uf with tree?
We could bite the bullet and just traverse terms.

For context we need first class map.  _multiset_ of (unmarked var) terms in context which . first class map from terms to number of them. UF should have some convention for breaking ties. Now it isn't 
Otherwise same diff.

This seems great.

.type t1 = term
.type t2 = [x : term, y : term]
norm1():t1
norm2(x:term,y:term):t2
norm3()
.type countterm = [nvar : unsigned, t : term]
norm(t, offset):countterm
norm(old:term, olduf:uf, new:term)

Another representation: Use a set of location map trees. We don't care about order.
```
.type map = Left {map} | Right {map} | Here {} | Both {map, map}
```
Assume left associated form for things with more than 2 args.

foo(Var,Var), { Both(Here,Here)  } vs {  Left(Here), Right(Here) }

The trees are _disjoint_
We then need to 
This somehow is a unification tree or no?

It's difficult to find the tree that corresponds to Something.
Could have function that takes single path and returns entire tree.
If trees are equal, vars are equal. Hmm.
@map_left
@map_right
@map_both - add a both to every tree in set.

Could be need to destruct every tree in set?
match_left
match_right

Do beta and free var norm?
@norm( $App($Sym("foo"), $App(x, y)))
@norm1
@norm2
@norm3
That is a nearly usable interface. Hmm.


### Geometry
<http://www.mmrc.iss.ac.cn/~xgao/paper/jar-gdbase.pdf> see appendix

Hmm they store canonical forms of relations. That's cool.

equivalence classes to represent some predicates - collinear(l1,l2) is an equivalence relation.

```souffle
.type pt = symbol
.decl coll(a : pt, b : pt, c : pt)

// collinearity of points
coll(a,c,b) :- coll(a,b,c).
coll(b,a,c) :- coll(a,b,c).
coll(c,d,a) :- coll(a,b,c), coll(a,b,d).


// parallel lines
.decl para(a : pt, b : pt, c : pt, d : pt)

para(A, B, D, C):- para(A, B, C, D).
para(C, D, A, B):- para(A, B, C, D). // symmettry of parallel
para(A, B, E, F ):- para(A, B, C, D), para(C, D, E, F ). // transitivity of parallel

// perpendicular lines
.decl perp(a : pt, b : pt, c : pt, d : pt)

perp(A, B, D, C):- perp(A, B, C, D).
perp(C, D, A, B):- perp(A, B, C, D).
para(A, B, E, F ):- perp(A, B, C, D), perp(C, D, E, F ). // two perps make a paralel
perp(A, B, E, F ):- para(A, B, C, D), perp(C, D, E, F ).

// rewriting in terms of lines feels somewhat natural.
// .type Line = {a : pt, b : pt}
// (= (Line a b) (Line b a))
// (= (line a b) (line a c)) === coll(a,b,c). Collinearity of points is an equivalence relation over lines
// collinear is the for real equality over lines
// parallelism is a distinct equivalence class.
// para(l1) = para(l2)
// dot(l1,l2) = dot(l2,l1)
// covers a lot of the above.

// midpoint of lines
.decl midp(mid : pt, a : pt, b : pt)
midp(M, A, B):- midp(M, B, A).

.decl cong(a : pt, b : pt, c : pt, d : pt)
// circle is circle center + 2 points. Why?
.decl circle(a : pt, b : pt, c : pt, d : pt)
circle(O, A, B, C) :- cong(O, A, O, B), cong(O, A, O, C).

// length being equal is a good descrption of cong. len(seg1) = len(seg2)

// cyclic is circle described by 4 points?
.decl cyclic(a : pt, b : pt, c : pt, d : pt)
cyclic(A, B, C, D) :- cong(O, A, O, B), cong(O, A, O, C), cong(O, A, O, D).
cyclic(A, B, D, C) :- cyclic(A, B, C, D).
cyclic(A, C, B, D) :- cyclic(A, B, C, D).
cyclic(B, A, C, D) :- cyclic(A, B, C, D).
cyclic(B, C, D, E) :- cyclic(A, B, C, D), cyclic(A, B, C, E).


// two angles each of which described by two lines
// angle(l1) = angle(l2)
.decl eqangle(a : pt, b : pt, c : pt, d : pt, e:pt, f:pt, g : pt, h : pt)

eqangle(B, A, C, D, P , Q, U, V ):- eqangle(A, B, C, D, P , Q, U, V ).
eqangle(C, D, A, B, U, V , P , Q):- eqangle(A, B, C, D, P , Q, U, V ).
eqangle(P , Q, U, V , A, B, C, D):- eqangle(A, B, C, D, P , Q, U, V ).
eqangle(A, B, P , Q, C, D, U, V ):- eqangle(A, B, C, D, P , Q, U, V ).
eqangle(A, B, C, D, E, F, G, H ):-
  eqangle(A, B, C, D, P , Q, U, V ), eqangle(P , Q, U, V , E, F, G, H ). // transitivity
```

Hmm. Vector algebra is the method. Parametrize objects. Use trig identities. Logic is super algebra.
Hmm.

```egglog
(rule (on (line a b) a))
(rewrite (line a b) (line b a))
(= (para l1) (para l2))
(angle l1 l2)
(line (seg a b))
(seg a b) = (seg b c) is cong()
(circle o a) = (circle o b)

```

### Categorical Example

```souffle
// these constructors are actually the skolemizaion of axioms
.type Morph = Comp {f : Morph, g : Morph} | Id {a : Ob} | M {f : symbol}
.type Ob <: symbol

.decl ob(a : symbol)

.decl eq(f : Morph, g : Morph) eqrel
.decl hom(f : Morph, a : Ob, b : Ob)

// category axioms
// identity morphism exists
hom($Id(a), a, a) :- ob(a).
eq(f, $Comp(f,$Id(b))), eq($Comp($Id(a),f), f) :- hom(f,a,b).
// composition exists
hom($Comp(f,g),a,c) :- hom(f, a, b), hom(g, b, c).//, f != $Id(_), g != $Id(_).
// associativity axiom rewrite rules
eq(fgh2, fgh), hom(fgh2, a, b) :- hom(fgh, a, b), fgh = $Comp(f,$Comp(g,h)), $Comp($Comp(f,g),h) = fgh2.
eq(fgh2, fgh), hom(fgh, a, b) :- hom(fgh2, a, b), fgh = $Comp(f,$Comp(g,h)), $Comp($Comp(f,g),h) = fgh2.
 

// typing rule guarded on eq
hom($Comp(f,g), a, c):- eq($Comp(f,g), _), hom(f, a, b), hom(g, b, c).
// Just filling out stuff.
eq(f,f), ob(a), ob(b) :- hom(f,a,b).

/*
.decl depth(t : Morph, n : unsigned)
depth($M(f), 1) :- hom($M(f), _, _).
depth($Id(a), 1) :- hom($Id(a), _, _).
depth($Comp(f,g), max(m,n) + 1) :- hom($Comp(f,g), _, _), depth(f,n), depth(g,m).
*/

hom(f,a,b) <= hom(f2,a,b) :- eq(f,f2), depth(f2, d2), depth(f,d1),  d2 <= d1.

hom($M("f"),"a","b").
hom($M("g"),"b","c").

.limitsize hom(n=15)
.output hom(IO=stdout)
```

Hmm. Comp(Id, f) is going off the rails. Any loop will. Can subsume on term size? Not clear who wins subsumption vs building bigger. Tag size inside of term?

Mayybe it's worth it to do Comp { symbol, morph} list style. Hard to do.
Could block composition rule on Id. Kind of a cheap shot


```souffle
.type obj <: symbol // Sometimes we need constructors, like Otimes.
.type typ = Obj {} | Hom {a : obj, b : obj}
// skolem symbols go into user defined type because we need to generate them
.typ Morph = Comp {f : Morph, g : Morph} | Id {a : Obj} | Sym {s : symbol}
#define F $Sym("f")
#define G $Sym("g")

// .decl morph( , a : obj. b : obj)
.decl typ()
.decl eqm(f : Morph, g : Morph) eqrel

comp(f : Morph, g : Morph : h : Morph)
comp() :- typ(), comp

```

## Typeclass resolution.
See Lean paper Tabling Typeclasses
See Chalk (which uses datafrog?) https://github.com/rust-lang/chalk

Write typeclass rules as datalog/prolog clauses. The provenance tree is enough to actually construct the type class instances.


## Borrow Checker
Hmm the borrow checker is seperate from the trait engine chalk probably
See ascent paper which compares itself with datafrog based polonius
Polonius https://www.youtube.com/watch?v=_agDeiWek8w
switches polonius from diff dataflow to datafrog https://github.com/rust-lang/polonius/pull/36#issuecomment-390393717
https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md datafrog blog post
[An alias-based formulation of the borrow checker](http://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/) soufle datalog rules
[rust board discussion](https://internals.rust-lang.org/t/blog-post-an-alias-based-formulation-of-the-borrow-checker/7411)
"NLL"? Non lexical liftetimes https://stackoverflow.com/questions/50251487/what-are-non-lexical-lifetimes
This is perhaps related to alias analysis? But maybe not.
Also perhaps to subtyping.

[the move borrow checker](https://twitter.com/b1ackd0g/status/1526251533758738432?s=20&t=bg0gpKH5p3kCZWau-XE4ng) some kind of smart contract borrow checker


region variables.
lifetimes
```souffle
// just collected up from post above

.decl cfg_edge(P:point, Q:point)
.input cfg_edge


.decl subset(R1:region, R2:region, P:point)
// Rule subset1
subset(R1, R2, P) :- base_subset(R1, R2, P).
// Rule subset2
subset(R1, R3, P) :- subset(R1, R2, P), subset(R2, R3, P).
// Rule subset3 (version 1)
subset(R1, R2, Q) :- subset(R1, R2, P), cfg_edge(P, Q).

.decl borrow_region(R:region, L:loan, P:point)
.input borrow_region

.decl region_live_at(R:region, P:point)
.input region_live_at

.decl requires(R:region, L:loan, P:point)
// Rule requires1
requires(R, L, P) :- borrow_region(R, L, P).
// Rule requires2
requires(R2, L, P) :- requires(R1, L, P), subset(R1, R2, P).
// Rule requires3 (version 1)
requires(R, L, Q) :-
  requires(R, L, P),
  !killed(L, P),
  cfg_edge(P, Q).

.decl killed(L:loan, P:point)
.input killed

.decl invalidates(P:point, L:loan)
.input invalidates

.decl loan_live_at(R:region, P:point)

// Rule loan_live_at1
loan_live_at(L, P) :-
  region_live_at(R, P),
  requires(R, L, P).

.decl error(P:point)

// Rule error1
error(P) :-
  invalidates(P, L),
  loan_live_at(L, P).

// Rule subset3 (version 2)
subset(R1, R2, Q) :-
  subset(R1, R2, P),
  cfg_edge(P, Q),
  region_live_at(R1, Q), // new 
  region_live_at(R2, Q). // new

// Rule requires3 (version 2)
requires(R, L, Q) :-
  requires(R, L, P),
  !killed(L, P),
  cfg_edge(P, Q),
  region_live_at(R, Q). // new
```

[polonius and region errors](http://smallcultfollowing.com/babysteps/blog/2019/01/17/polonius-and-region-errors/)
A sequel to the above post with other souffle rules

[Polonius and the case of the hereditary harrop predicate](http://smallcultfollowing.com/babysteps/blog/2019/01/21/hereditary-harrop-region-constraints/)
Hmm... So he's mixing harrop, lifetimes, datalog. My kinda guy.

[lifetimes.lifetime inference in souffle ](https://github.com/rljacobson/lifetimes)

## Type checking
Related of course to the above.
See the table on page 3 of [this bidirectional typing tutorial](https://arxiv.org/pdf/1908.05839.pdf). This is more or less a transcription of these rules to datalog. It is interesting how explicit the moding and forward / backward reasoning becomes. `has` becomes a seperate entity from `infer` and `check`. The latter two are top down / backwards requests for proofs, whereas `has` is a bottom up / forward reasoning assertion of truth.


```souffle
.type type = Unit {} | Arr {a :  type, b : type}
.type term = TT {} | Lam {b : term} | App {f : term, x : term} | Var {n : number} | Annot {t : term, ty : type}
.type ctx = [ ty:type, g : ctx]

.decl has(g : ctx, t : term , ty : type) // bottom up
.decl infer(g : ctx, t : term) // mode -+ topdown
.decl check(g : ctx, t : term, ty : type) // topdown

// variable.
// base case
has([ty,ctx], $Var(0), ty) :- infer([ty,ctx], $Var(0)).
// recursive case
infer(ctx, $Var(n-1)) :- infer([_ty,ctx], $Var(n)), n > 0.
has([ty,ctx], $Var(n), ty2) :- infer([ty,ctx], $Var(n)), has(ctx, $Var(n-1), ty2).

// infer instead of check if possible
infer(ctx,t) :- check(ctx,t,_ty).

// subtyping or equality rule
// has(ctx, t, ty) :- check(ctx,t,ty), has(ctx,t,ty2), sub(ty,ty2).

// annotation rule
check(ctx, t, ty) :- infer(ctx, $Annot(t,ty)).

// unit rule
has(ctx,$TT(), $Unit()) :- check(ctx, $TT(), $Unit()).

// Lam case
check([a, ctx], body, b) :- check(ctx, $Lam(body), $Arr(a,b)).
has(ctx, $Lam(body), $Arr(a,b)) :- check(ctx, $Lam(body), $Arr(a,b)), has([a, ctx], body, b).

// App case.
infer(ctx, f) :- infer(ctx, $App(f,_x)).
check(ctx, x, a) :- infer(ctx, $App(f,x)), has(ctx, f, $Arr(a,_b)).
has(ctx, $App(f,x), b) :- infer(ctx, $App(f,x)), has(ctx, f, $Arr(a,b)), has(ctx, x, a).

check(nil, $Lam($Lam($App($Var(1),$Var(0)))), 
      $Arr($Arr($Unit(), $Unit()), $Arr($Unit(), $Unit()))).

.output has(IO=stdout)
/*
.decl check_top(t : term, ty : type)
check(nil,t,ty):- check_top(t,ty).
.decl has_top(t : term, ty : type)
has_top(t,ty ):- has(nil, t, ty).


check_top($TT(), $Unit()).
check_top($Lam($Var(0)), $Arr($Unit(),$Unit())).
check_top($Lam($Lam($Var(0))), $Arr($Unit(),$Unit())).
check_top($Lam($Lam($Var(0))), $Arr($Unit(),$Arr($Unit(),$Unit()))).
check_top($Lam($Lam($Var(1))), $Arr($Unit(),$Arr($Unit(),$Unit()))).
check_top($Lam($Lam($Var(2))), $Arr($Unit(),$Arr($Unit(),$Unit()))).
check_top($App($Lam($Var(0)), $TT()), $Unit()).

check_top($Lam($Lam($App($Var(1),$Var(0)))), 
      $Arr($Arr($Unit(), $Unit()), $Arr($Unit(), $Unit()))).
*/
//.output check(IO=stdout)
//.output infer(IO=stdout)
//.output has(IO=stdout)
//.output has_top(IO=stdout)
```

Hmm. Infer and has can be collapsed?

```souffle
.type type = Unit {} | Int {} | Bool {} | List {a : type} | Maybe {a : type} | Sum {a : type, b : type} | Prod {a : type, b : type}
.type term = TT {} | TInt { x : number} | True {} | False {} | Nil {} | Cons { hd : term, tl : term } | None {} | Some {x : term}
   | Annot {t : term, ty : type} | Var { n : unsigned} | Lam {body : term} | App {f : term, x : term}

//.type ctx = [ t : term, t:type, g : ctx ] 
.type ctx = [ ty:type, g : ctx ]   // don't need variable if we're doing de bruijn


//| $GNil {} $GCons { t :term, ty : type, ctx } 


/*
hastype($TT(), $Unit()).
hastype($TInt(n), $Int()) :- n = range(1,10). // cheating a little
hastype($True(),$Bool()).
hastype($False(), $Bool()).
*/
.decl hastype(t : term , ty : type) // mode++ sort of
.decl infertype(t : term) // mode -+ top down
.decl checktype(t : term, ty : type) // mode -- topdown
.decl prove(ty:type) // mode +-
// the proof provenance of hastype() will basically mirror the lambda term anyhow.
// This perhaps shows the parameter is unnecessary / inefficient.
// We could instead record the rule used and subsumption to shortest one.

// The only bottom up mode is ++ since we don't have non ground terms.


hastype(t, $Int()) :- infertype(t), t = $TInt(_).

// annotation rule
checktype(t, ty) :- infertype($Annot(t,ty)).

// Sub rule. Doesn't hurt anything
infertype(t) :- checktype(t,_).
hastype(t,b) :- hastype(t,a) , eq(a,b).


hastype($TT(), $Unit()) :- checktype($TT(), $Unit()).

checktype([ a , ctx], body, b) :- checktype(ctx, $Lam(body), $Arr(a,b)).

// Var=> rule
hastype( ctx, $Var(0), t) :- infertype(ctx, $Var(0)), ctx = [t,_].
// This is probably not how to do it.
hastype() :- infertype(ctx, $Var(n)), index(ctx, n, t).
needindex(ctx,n) :- infertype(ctx, $Var(n)).
infertype(ctx, $Var(n-1)) :- infertype([_, ctx], $Var(n)), n != 0.

// Can we reify the ctx into a relation? possibly
// and insert immediately alos when we create the context.
inctx([a,ctx], a) :- checktype($Lam(body), )
inctx([a,ctx], x) :- inctx([a,ctx], _ ), inctx(ctx, x).

index([a,ctx], 0. a) :- checktype($Lam(body), )
index([a,ctx], n + 1, x) :- index([a,ctx], _, _), index(ctx, n, x).

// This part is a mess. Would not using debruijn be better somehow?

```

Thinking in terms of tabling, there is a difference between query and answer. 

[bidirectional typing](https://arxiv.org/pdf/1908.05839.pdf)
I suppose bidi checking feels nice because we are already used to thinking of the different modes as different predicates. We also need to make these distinctions for magic set transform

[Rust lifetime analysis written in souffle](https://github.com/rljacobson/lifetimes)


eqrel for hindley milner? Yihong had something like this
souffle-z3 for refinement typing?


## Coinductive or Greatest Fixed Point Datalog

Does this make sense?
There is coinductive logic programming which is prolog

In semantics of ASP, stable semantics, I seem to recall them talking about the ast and greatest model.

LFP is the minimum 
GFP is the maximal consistent set


```
// a co-fact
:- foo().

// can be translated into datalog. This is intuitionistic-ish negation
neg_foo().

// A co-axiom / co-rule
bar() :- foo(), biz().
// expands to 2 backwards derivation rules. Feels a bit like seminaive expansion
// Also kind f demand-y. Maybe magic set-t
neg_foo() :- biz(), neg_bar().
neg_biz() :- neg_bar(), foo().



```
Datalog builds finite sets. Co-datalog builds co-finite sets.

This _is_ a valid ASP program, but maybe we're targetting a subset that is treatble
```clingo
:- foo().
bar() :- foo(), biz().
```


Making a negatin relation is a good trick. It turns the union of datalog into an intersection.
One could imagine a datalog that fills the database o start with and removes facts as they become inconsistent, but why not just list the facts that are known to not hold.

The well founded semntics seems to be the best match here.



has non terminating path is a kind of liveness property. It is analagous in some respects to reachability (vertex specialized path query).
has-infinite-trace is another way of putting it.

```souffle
.type vert = number

.decl no_cycle(v : vert)
.decl edge(x : vert, y : vert)
//.decl no_edge(x:vert, y:vert)

edge(1,2). edge(2,3). edge(3,3).
edge(3,4). edge(4,5). edge(3,5).

edge(7,8). edge(8,7).
verts(v) :- edge(v,_) ; edge(_, v).
//no_edge(x,y) :- 

.decl verts(x : vert)
// This is out0
no_cycle(v) :- verts(v), !edge(v, _). // no outgoing egde, can't have a cycle
// no_cycle(x) :- forall y: edge(x,y), no_cycle(y).
// finite expansiosn. no. Well, if we specialzied the rules to the particular graph.
// in2 in3 in4
.decl out1(v : vert)
out1(v) :- verts(v), 1 = count : {edge(v,_)}.
.decl out2(v : vert)
out2(v) :- verts(v), 2 = count : {edge(v,_)}.
.decl out3(v : vert)
out3(v) :- verts(v), 3 = count : {edge(v,_)}.

no_cycle(x) :- out1(x), edge(x,y), no_cycle(y).
no_cycle(x) :- out2(x), edge(x,y1), no_cycle(y1),
               y1 != y2, edge(x,y2), no_cycle(y2).
no_cycle(x) :- out3(x), edge(x,y1), no_cycle(y1),
               y1 != y2, edge(x,y2), no_cycle(y2),
               y1 != y3, y3 != y3, edge(x,y3), no_cycle(y3).

// maybe recursive count would work if that existed
// Bounded quantification by edge in previous strata is in principle nonproblematic.
// no_cycle(x) :- forall edge(x,y) : { no_cycle(y)  }
// no_cycle(x) :- verts(x), count : { edge(x,y) } = count : { edge(x,y1), no_cycle(y1) }

.output no_cycle()
.output verts

// Compare with this definition
.decl cycle(v : vert)

.decl path(x : vert, y : vert)
path(x,y) :- edge(x,y).
path(x,z) :- edge(x,y), path(y,z).
cycle(x) :- path(x,x).

cycle(x) :- edge(x,y), cycle(y).
.output cycle
// Ok this is a very natural encoding. Is it missing anything?


// I ges finitely expanding the cycles is an extremely stupid idea.
//cycle(x) :- edge(x,x).
// Misses the 7,8 cycle
// We could finitely expand the primitive cycle finder though up to N. Is this really worse than the finite expansion I did above?
// cycle(x) :- edge(x,y), edge(y,x).
// transitive closure to reach cycle
```
If there are multiple rules, they all have to fail to propagate a negation.
The negation also plays into the quantifier structure.
This is perhaps related to performing the (clark) completion of a program.


For co-datalog, this ought to be the only rule necessary.
`inf_trace(x) :- edge(x,y), inf_trace(y)`
start with all possiblites in inf_trave, run "backwards" through rule? Since this is linear, can see it, but what about nonlinear or mutually recursive ruls?
forall x, (exists y, edge(x,y), t(y)) -> t(x)
Has to be run "seminaive"?
forall x, not (exists edge /\ t(y)) \/ t(x)
forall x, (not not forall (not edge \/ not t(y)) \/ t(x)
forall x, (not not forall (not edge \/ not t(y)) \/ t(x)

forall x, not not t(x) \/ (exists edge, t(y))



Hmm. Clingo is not panacea I pretended it might be. Clingo is still very least fixpoint based.
```clingo
edge(1,2). 
edge(2,3). 
edge(3,3).
edge(3,4). 
edge(4,5). 
edge(3,5).
vert(V) :- edge(V,_).
vert(V) :- edge(_, V).

%inf_trace(X) :- vert(X), not edge(X,_).
%{inf_trace(V): edge(V, W)} :- inf_trace(W).
%{-inf_trace(V)} :- vert(V). 
%-inf_trace(Y) :- edge(X,Y), -inf_trace(X).

-inf_trace(X) :- vert(X), -inf_trace(Y) : edge(X,Y).
inf_trace(X) :- vert(X), not -inf_trace(X). %If it's not disprovable, it's true.
```

I don't _really_ feel like clingo is necessary, but it does have some nice features.
The conditional rule using bounded quantification to a previous strata is safe.

Maybe I need to construct all possible proofs and only remove somthing when there are no allowable extant proofs.
### DFA Minimization
```souffle
.type state = symbol
.type action = number
.decl states(s : state)
.decl start(s : state)
.decl accept(s : state)
.decl trans(s : state, a : action, s1 : state)
// https://en.wikipedia.org/wiki/DFA_minimization
states("a"). states("b"). states("c"). states("d"). states("e"). states("f").
start("a").
accept("d"). accept("c"). accept("e").
trans("a",0,"b").trans("a",1,"c").
trans("b",0,"a").trans("b",1,"d").
trans("c",1,"f").trans("c",0,"e").
trans("d",0,"e").trans("d",1,"f").
trans("e",0,"e").trans("e",1,"f").
trans("f",0,"f").trans("f",1,"f").

.decl distinct(s : state, t : state)
distinct(a,b) :- accept(a), states(b), !accept(b).
distinct(s,t) :- trans(s,a,s1), trans(t,a,t1), distinct(s1,t1). 
distinct(s,t) :- distinct(t,s). //symmetry

.decl eq(s : state, t : state)
eq(a,b) :- states(a), states(b), !distinct(a,b).

//.decl root(s : state, t : state)
//root(a,b) :- states(a), min b: eq(a,b).
.output eq
```

[local and symbolic bisimlation using tabled constraint logic programming](https://www3.cs.stonybrook.edu/~cram/Papers/BMRRV_ICLP01/paper.pdf)

```clingo
obs(hd,a,3).
obs(tl,a,b).
obs(hd,b,4).
obs(tl,b,a).
eq(X,X) :- obs(hd, A, X).
-eq(X,Y) :- obs(O,X,OX), obs(O,Y,OY). %not eq(OY,OX). % OX != OY. %-eq(OY,OX).


```

## CRDTs
CRDT are a latticy based structure. It makes sense that it might be realted or modellable in datalog

[expressing crdts as queries using datalog](https://speakerdeck.com/ept/data-structures-as-queries-expressing-crdts-using-datalog)
https://github.com/frankmcsherry/dynamic-datalog/blob/master/problems/crdt/query.dl souffle example
https://github.com/frankmcsherry/dynamic-datalog

## MultiSet Semantics
If you give a reason for each tuple, you can get multiset semantics.

paths in a dag
```souffle
.type reason = Base {n : number} | Trans { x : reason, y : reason}

.decl edge(n : number, m : number, r : reason)
edge(1,2, $Base(0)).
edge(2,3, $Base(1)).
edge(1,3, $Base(2)).
.decl path(n : number, m : number, r : reason)
path(i,j, r) :- edge(i,j,r).
path(i,k,$Trans(x,y)) :- edge(i,j,x), path(j,k,y).

.output path

```

If you start subsumpting these reasons you get something similar to provenance as explained above in subsumption.

## Access Control Policies

[Is Datalog a good language for authorization?](https://neilmadden.blog/2022/02/19/is-datalog-a-good-language-for-authorization/)
[open policy language rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
[polar and oso](https://docs.osohq.com/learn/polar-foundations.html#the-search-procedure)
[biscuit](https://www.biscuitsec.org/)
[Datalog with Constraints: A Foundation for Trust Management Languages](https://crypto.stanford.edu/~ninghui/papers/cdatalog_padl03.pdf)
[Specifying and Reasoning about Dynamic Access-Control Policies Daniel J. Dougherty,1 Kathi Fisler,1 and Shriram Krishnamurthi 2](https://web.cs.wpi.edu/~dd/publications/ijcar06.pdf)
googlew "access control datalog" you get a bunch of hits. The references in these paper

description logics https://www.cs.man.ac.uk/~ezolin/dl/

AWS zelkova is not datalog

Differential dataflow useful?
vs alloy vs tla+ vs smt?

[souffle example](https://github.com/souffle-lang/souffle/blob/master/tests/example/access-policy/access-policy.dl)

## Networks
[Checking Beliefs in Dynamic Networks](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nod.pdf)
[Efficient network configuration verification using optimized datalog](https://ieeexplore.ieee.org/document/8406876)
[An Operational Semantics for Network Datalog](https://www.andrew.cmu.edu/user/liminjia/research/papers/ndlogsemans-tr.pdf) [NDlog thesis](https://digitalassets.lib.berkeley.edu/techreports/ucb/text/EECS-2006-177.pdf)
[declarative netowrking book](https://ieeexplore.ieee.org/document/6813052?arnumber=6813052)

## Make
Build systems like make a logic programing rukles
[lpmake for ciao](https://github.com/ciao-lang/lpmake/blob/master/examples/latex/Makefile.pl)
[Propositions as Filenames, Builds as Proofs: The Essence of Make](https://bentnib.org/posts/2015-04-17-propositions-as-filenames-essence-of-make.html)

CSS is prolog
https://twitter.com/soundly_typed/status/1513500166359298048?s=20&t=-ertSPtY87GogVCFq4f-Rw 

# Topics

## Answer Set Programmng
Grounding is a form of provenance

Conditional literals are a really good feature. If the condition appears ina previous strata, it is monotone and hence (?) actually a datalog feature.

recursive Cardinality constraints with lower bound in the body are also a datalog feature. Upper bound and hence equality cardinality need to be stratified.

Maybe with the double negation feature you could do it. https://twitter.com/taktoa1/status/1548109067855376385?s=20&t=mIwj8pQtmBh4ysUcnNC4vg . Parity-stratified negation in codeql
https://www.swi-prolog.org/pldoc/man?predicate=forall/2 forall x:A, B = forall x, A -> B = not exists x (A /\ not B) = not exists x:A, not B. This is a classical correspondence. Intuitionisitically, you can go left to right but not right to left I suspect.

```souffle
// Not accepted because cyclic negation
.decl foo(a : symbol)
.decl bar(a : symbol)
.decl cond(a : symbol)
foo("a").
cond(X) :- foo(X), !bar(X).
bar("b").
// bar("a") :- bar("b"), !cond(_X). //{foo(X), !bar(X)}.

// recursive count not allowed.
// bar("a") :- count : {foo(X), bar(X) } = count : {foo(X)}.

.decl rec_count(n:number)
rec_count(0,x) :- foo(x), bar(x).
rec_count(n+1,x) :- rec_count(n,y), x > y, foo(x), bar(x). 
rec_count(count : foo(x), max : foo(x)).

```

## Provenance
[Explaining Outputs in Modern Data Analytics∗](http://www.vldb.org/pvldb/vol9/p1137-chothia.pdf) prvoencnace in differential dataflow <https://github.com/frankmcsherry/explanation> <https://github.com/frankmcsherry/blog/blob/master/posts/2016-03-27.md>

[decalarative datalog debugging for mere mortals](https://yanniss.github.io/DeclarativeDebugging.pdf)

Provenance can be done by tagging the rule that applied.
You can either give rules names or
Master provenance can be done by reflecting the rules themselve into an AST al la metainterpeters

```souffle
.type val = Sym {s : symbol} | Num {n : number}
.type vallist = [hd : ]
.type rel = [name : symbol, args : vallist]
.type rule = [head : , body]

```

Timestamps are a form of provenance. 
## Semi Naive Evaluation
I remember a time when semi naive seemed pretty cryptic to me. I still amnot sure I understand it perfectly, but I have crossed the threshld 

Naive evaluations only needs one table per relation. You can keep track of if there is anything to do by checking whether you find new tuples as you go along.
You could do it instead with two tables
- old
- new
  
And then at the final step, take the set `old \ new` , see if it is empty for termination check, and add it into old


For every logical relation you need to keep 3 tables
- old (stable)
- delta (recent)
- new (to_add)
You need these three because you need a place to put new facts, but also you want to keep the most recent updated tuples as a seperate thing.
`delta = new \ old`

## Algebraic Data Types


Termination is no longer guaranteed. How do you guarantee termination?
Well one way is perhaps to only produce _new_ terms "smaller" than ones discovered. This is like termination in functional programming with the caveat that you may recursively not make progress.
`foo (x : xs) = foo (x : xs)` is non terminating in haskell
`foo([x,xs]) :- foo( [x,xs]).` is perfectly fine terminating in datalog.

You may also use any terms discovered whole hog.

One way to treat existential is to search for them in the already known database.

## Lattices
Lattices give a natural way to "fix" broken functional dependencies of the tables.

Flix, Ascent many others support a notion of relation fields being defined as lattices with a special "merge" operation.

Datalog is declarative. You don't really control the order in which things happen. Lattices are an algebraic structure that supports a conveninent notion of merging. 
1. Merging order doesn't matter (commutative and associative)
2. Merging twice doesn't matter (idempotence)


Datalog itself can be considered as a expansive operator operating over the space of powersets of tuples. Powersets of tuples form a lattice with subset inclusion being the order, union being join and intersection being meet. Somehow this notion of lattice operates at more of a "metalevel" than the internal notion of lattice. 

It is possible, for example, to allow first class sets as elements of your datalog relation. Then 

Other common lattices include MinInt, MaxInt, sets, Intervals, polyhedra, octagons, unknown-true-false-inconsistent, `Option<a>`,

This lattice notion of "join" has no connection to the relational database word "join". This is infortunately confusing.


## Subsumption
[1995 subsumption paper](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.28.103&rep=rep1&type=pdf)






Linear "datalog" - destructive state update
Using Sqllite - https://www.sqlite.org/lang_with.html recursive ctes seem to get you a lot. Cool examples. Mandelbrot

bottom up Dynamic programming in datalog? Rod cutting.

### Subsumption as a master feature

Subsumption is kind of the master feature. Now, you can kind of also model these just ignoring the fact you're producing way to many tuples. But subsumption let's you at least keep it kind of under control

#### Provenance
Provenance using subsumption. Provenance works by deleting longer derivations.

```souffle
.type Explain = Base {} | Trans {u : unsigned}
.decl edge(a : unsigned, b : unsigned)
edge(1,2).
edge(2,3).
edge(1,3).
edge(3,4).
.decl path(a : unsigned, b : unsigned, why : Explain, proof_depth : unsigned)
path(a,b, $Base(), 1) :- edge(a,b).
path(a, c, $Trans(b), depth + 1) :- edge(a,b), path(b,c, _, depth).
path(a,b, w1, d1) <= path(a, b, w2, d2) :- d2 <= d1.
.output path(IO=stdout)
```

#### max min
Max, min using subsumption. 
```
mymax(z) :- reltomax(z).
mymax(z) <= mymax(z2) :- z1 <= z2.
```

## Recurusive Sum and Count
Can I do sum and count? Maybe not. Not without tracking what we've already used. You could do this with bitsets. Requires reflection I guess. c
Ah, I don't need to require tracking the set of already used, only count. Oh. Wait. no.
```
mysum(count : unsigned, partial_sum : unsigned)
mysum(1,n) :- foo(n).
mysum(n+1,) 
nope
```
But if I cluster them into groups, I can take approximate sums.
What if I track the current biggest element in the sum. This is tracking the state of a naive summation algorithm. We can lways necode an imperative algorithm to datalog by tracking state. This relies on summing positive numbers only
```
mysum(n,n) :- foo(n).
mysum(n, partsum + n) :- mysum(top,partsum), foo(n), top < n.
mysum(n,sum) <= mysum(n,sum') :- sum <= sum'.
```

count
```
mycount(n,1) :- foo(n).
mycount(n, partcount + 1) :- mysum(top,partcount), foo(n), top < n.
mysum(n,count) <= mysum(n,count2) :- count <= count2.
```

Could hyperloglog be relevant for approximate counts? https://en.wikipedia.org/wiki/HyperLogLog

A* search. Interesting. If you have the a bound on distance you can subsumpt away bad possible paths. Path search is a canonical datalog program. Subsumption allows shortest path search (which I showed above).

#### Lattices
See also bitset lattice above

Lattices are in some respects just an optimization. They allow the database to coalesce rows in a principled way. One could allow the database to be filled with the junk of lesser lattice values.

Lattices can be sometimes encoded into finite sets. Consider the 4 valued lattice of unknonw, true, false, conflict. These are the power sets of a set of size 2. This can be represented as two tables which can be in different states of full. Because of stratified negation, it is not always possible to observe things. You shouldn't really observe anything other than filter questions anyhow though. Anf you're always above unknown.
true(a), false(a)

You often need 1 rule to combine pieces with the join of the lattice and 1 rule for subsumption. This is probably not efficient, but it is works.
It would be be nice to have a construct that did both at once efficiently. We should be immeditaly erasing a and b when we compute their join.

```souffle
rel(join(a,b)) :- rel(a), rel(b).
rel(a) <= rel(b) :- lattice_order(a, b).
```

Perhaps you could make a generic lattice compment parametrized over join

```
.comp Lattice<T> {
  .decl join(x: T, y : T, z : T) overridable
  .decl r(x:T, y:T)
  r(z) :- r(x), r(y), join(x,y,z).
  r(x) <= r(y) :- join(x,y,y).
}
```
But filling out joi will be annoying. There isn't a great way to parametrize over functors so far as I can tell.



Todo:
- vsa


##### Min/max lattice

labaeller Max lattice
I suppose in a sense this is the lattice of the function space `T -> int` defining join pointwise. If that's your bag.

```souffle
.comp Upper<T> {
   .decl upper(label: T, x : unsigned)
   upper(l,x) <= upper(l,x1) :- x <= x1.
}

.comp Lower<T> {
   .decl lower(label: T, x : unsigned)
   lower(l,x) <= lower(l,x1) :- x1 <= x.
}

.init symu = Upper<symbol>

symu.upper("x", 1).
symu.upper("x", 7).
symu.upper("y", 4).
.output symu.upper(IO=stdout)

```

If you have both, you have an interval, see below.

##### Maybe/Option lattice

```prolog

.type optionsymbol = None {} | Some {val : symbol}

.decl A(v : optionsymbol)

A($Some("foo")).
A($Some("fiz")).
A($Some("foz")).
//A($None()).

A($None()) :- A(x), A(y), x != y.
A(x) <= A($None()) :- A($None()).

.output A(IO=stdout)
```

Also you can make N max set lattice. Keep sorted. Insertion sort. Kind of a pain if you get too many

```
.type Nary = None {} | One {a : T} | Two {a : T, b : T} | Top {}
```


##### Intervals

```souffle
.type Interval = [l : float, u : float]
.type Expr = Add {a : Expr, b : Expr} | Lit { a : float} | Var {x : symbol} 

// all expressions
.decl expr(e : Expr)
expr(a), expr(b) :- expr($Add(a,b)).

expr($Add($Var("x"), $Lit(1))).

.decl iexpr(e : Expr, i : Interval)
iexpr($Lit(n), [n,n]):- expr($Lit(n)).
iexpr(e, [la + lb, ua + ub]) :- iexpr( a, [la,ua] ), iexpr(b, [lb, ub]), e = $Add(a,b), expr(e).

// also vice versa back down the tree
iexpr(b, [ l1 - ua, u1 - la]) :- iexpr($Add(a,b), [l1,u1]), iexpr(a, [la,ua]).


iexpr($Var("x"), [-1,1]).
iexpr($Var("x"), [0,1]).
iexpr($Add($Var("x"), $Var("x")), [0.5,0.75]).

// meet semantics
iexpr(e, [max(l1,l2), min(u1,u2)]) :- iexpr(e, [l1,u1]), iexpr(e, [l2,u2]).
iexpr(e, [l1,u1]) <= iexpr(e, [l2,u2]) :- l1 <= l2, u2 <= u1.  
.output iexpr(IO=stdout)
```
It may not be worth packing into a record though. This almost certainly has performance cost. Records never get deleted. So you should just unpack into a relation. 


```
// intervals getting bigger
/*
components?
We'd need to know at compile time how many possible instantations
.comp Interval<T>{
    .decl upper(x : T)
    .decl lower(x : T)
}


*/
.decl upper(t : symbol, x : float)
upper(t,x) <= upper(t, y) :- x <= y.
.decl lower(t : symbol, x : float)
lower(t,x) <= lower(t, y) :- y <= x.

.output upper(IO=stdout)
.output lower(IO=stdout)

upper("foo", 7).
upper("foo", 8).
upper("fiz", 9).

lower("foo", 8).
lower("fiz", 9).
lower("foo", -3).


.comp Interval<T>{
    .decl upper(x : T)
    upper(x) <= upper(y) :- x <= y.
    .decl lower(x : T)
    lower(x) <= lower(y) :- y <= x.
}
.init i1 = Interval<float>

i1.upper(3).
i1.upper(14).
.output i1.upper(IO=stdout)
```
#### Widening
It is the case that an analysis may not terminate or just plain take too long.
What can we do that is principled and still helps? Various definitions of widening, aggressive over approximation.

Widening in trad datalog is not much of a topic. YOu need primitives / lattices before you care. 



lat(wide(w)) :- lat(w).
lat(join(x,y)):- lat(x), lat(y).

Why not
lat(wide(join(x,y))):- lat(x), lat(y).

This is just a mapping into a different lattice. wide has to be monotone. wide is part of a galois connection between 2 lattices.

Widening examples -
coarsen intervals to nearest power of 2. -[2^-n, 2^n].  `[l,r] -> [bshr (bshl l), (bshl u + `
It's kind of a float.
Also simple in ball arith [2^n * offset, 2^n * (offset + 1)] <-> (offset, n)

Or a max width interval.


shoot intervals to infinite
maintain iteration count timestamp? kind of like an iteration tracking ghost var. Count visit per block?
join count (n, l) \/ (m, k) = if l == k then min(n, m) else max(n,m) +1, l / k . Join count is breaking lattice abstraction.
(n, l) \/ (m, k) = if l <= k then (m, k) if k <= k then else max(n,m) +1, l / k
No wait. this is lexicographic with count as max lattice. Then if I tweak some cutoff..?

Two predicates. The pure joining predicate and the widening predicate. This doesn't really work does it. It needs to be stratified. How can the join know it is done?

lat(t) :- widened(x), t = yadayada(x)
lat(@join(t1,t2)):- lat(t1), lat(t2)
widened(@wide(x,t)) :- widened(x), lat(t)

At least this feels like it is offering a possibility for non commuativity.
How do widened conflicts get resolved? The smallest one?


### Dyadic lattice

```souffle
#define ROUND2(a,b) (a ## 0 = a - 1    ,a ## 1 = a ## 0 bor (a ## 0 bshr 1), \
                    a ## 2 = a ## 1 bor (a ## 1 bshr 2),\
                    a ## 4 = a ## 2 bor (a ## 2 bshr 4),\
                    a ## 8 = a ## 4 bor (a ## 4 bshr 8),\
                    a ## 16 = a ## 8 bor (a ## 8 bshr 16),\
b = a ## 16 + 1) 

.decl round2(x : unsigned, y : unsigned) inline
round2(a, b) :- a0 = a - 1, 
                a1 = a0 bor (a0 bshr 1), 
                a2 = a1 bor (a1 bshr 2),
                a4 = a2 bor (a2 bshr 4),
                a8 = a4 bor (a4 bshr 8),
                a16 = a8 bor (a8 bshr 16),
                b = a16 + 1.

.decl norm(u : unsigned, l : unsigned, u1: unsigned, l1: unsigned) inline
norm(u, l, u1, l1) :-
    u < 2^32,
    d = u - l,
    round2(d,d1),
    //avg = (u + l) / 2,
    //u1 = avg + d1/2,
    //l1 = avg - d1/2.
    l1 = (l / d1) * d1 ,
    u1 = ((u - 1) / d1 + 1) * d1.

// Hmm. Different choices. Keep same average or round to power of 2 points.
// 

.decl test(x : unsigned, round : unsigned)
test(x,y) :- x = 5, ROUND2(x, y) .
test(x,y) :- x = 343245, round2(x, y).
test(x,y) :- x = 345, round2(x, y).
//test(x,y) :- x = 343245, ROUND2(x, y) .
.output test


.decl test2(u : unsigned, l : unsigned, u1: unsigned, l1: unsigned) 
test2(u,l,u1,l1) :- u = 3, l = 0, norm(u,l,u1,l1).
test2(u,l,u1,l1) :- u = 12, l = 8, norm(u,l,u1,l1).
test2(u,l,u1,l1) :- u = 17, l = 7, norm(u,l,u1,l1).


.output test2


.decl chain(u : unsigned, l : unsigned)
chain(101,100).
chain(u1, l1) :- chain(u,l), norm(max(u, u+1), min(l,l-1) , u1, l1). 

.output chain
```


Simple Type checking
```
is_symbol(s : symbol) inline
is_symbol(s) :- true.
```
This will accept any type below symbol too?

#### Equivalence relations
You can make a findParent relation to get a lot of the functionality of equivalence relations. Eq relations are already the same thing as
```souffle
eq(x,y) :- eq(y,x). //sym
eq(x,z) :- eq(x,y), eq(y,z). //trans
```

But this is more efficient. The relation is linear sized instead of quadratic in the size of the eq classes.

```souffle
#define EQ(x,y) canon(x,z), canon(y,z)
.decl canon(x : symbol, y : symbol)
.decl symbol(x : symbol)
symbol("x").
symbol("y").
symbol("z").
canon(x,x) :- symbol(x).
canon(x,z) :- canon(x,y), canon(y,z).
canon(x,y) <= canon(x,z) :- y <= z.
canon("x","y").
canon("y","z").
.output canon(IO=stdout)
```


#### Negation
Can I emulate negation using subsumption? Maybe remove negated clauses from rule, and later delete them?

Need to duplicate all clauses to negated versions?

f(a,b) <= f(dummy,dummy) :- not_f(a,b)
not_f() <= not_f() :- f(a,b).

f(a,b) :- g(a,b)
not_g(a,b) :- not_f(a,b)



But f(a,b) does damage we need to undo?

#### Choice domain

Choice using subsumption, static or dynamic notion of "better".



## Semiring Semantics
[Convergence of Datalog over (Pre-) Semirings](https://arxiv.org/abs/2105.14435)

Can consider tensor calculations an example of datalog.
Shortest path
[provenance semirings](https://twitter.com/wilton_quinn/status/1516919665125036032?s=20&t=hmaJXnp6Mp_aUsdRpkOMcQ)

Different kinds of semirings. Idempotent helps it look more like ordinary datalog
Relations can be functions into some structured value than a bool.
Ordered semirings

`,` and  `;` are overloaded.




## Probability
Perhaps related to semiring semantics
[scallop](https://scallop-lang.github.io/) neurosymbolic datalog. Probablistic datalog. Uses provenance. topkrpoofs other methods. 

## Datalog+- and the chase
[Datalog+-](https://dl.acm.org/doi/pdf/10.1145/1514894.1514897) A Unified Approach to Ontologies and Integrity Constraints. Integraes datalog with equality and tuple generating dependencies. 
[Datalog+- questions and answers](https://www.aaai.org/ocs/index.php/KR/KR14/paper/viewFile/7965/7972)
- weakly acyclic
- guarded - one relation holds all atoms
- sticky


[DLV](https://en.wikipedia.org/wiki/DLV) datalog with disjunction. 
https://www.dlvsystem.it/dlvsite/dlv-user-manual/ 
constraints - empty headed rules...? I've also seen them as `! :- ` in dglp
some funky features here. I wonder what the execution semantics is. Maybe disjunctive heads go in constraint store?

negation as failure vs stable model

## Tabling
See 
 - prolog#tabling


Tabling in prolog leads to something very similar in power to the memoizing datalog. However, you still have unification and logic variables, so it is not clear it is truly equivalent.

Datalog only works on ground terms.

Semi-naive evaluation is like informing the consumers that a new answer is available.

Datalog puts more at compile time than tabling does (naively?).

"Query Answer Transformation"

## Descriptive Complexity and Least Fixed Point Logic

[https://en.wikipedia.org/wiki/Fixed-point_logic#Least_fixed-point_logic](https://en.wikipedia.org/wiki/Fixed-point_logic#Least_fixed-point_logic) descriptive complexity theory says datalog is same thing as first order logic with fixpoints. Curious because datalog is also in some sense restricted horn clauses whereas this is saying in another sense it is full FO + fixpoint. 



## Push based Datalog
- [Brass's website](https://users.informatik.uni-halle.de/~brass/)
- [push based datalog](https://users.informatik.uni-halle.de/~brass/push/talks/inap17.pdf)
- [push method](https://users.informatik.uni-halle.de/~brass/push/)

push method ~ like seminaive of only one fact? Hmm. Interesting.
function calls correpond to heads. They memoize. Then they push themselves to any location predicate appears in body. Cute.
This gets you something like seminaive eval.
hmm. binding patterns are related to map vs set vs iterator storage.
This might lend itself really nicely to an embedded datalog. datakanren.
minikanren makes the horn clause aspect more hidden. It heavily uses the function call mechanisms of the host language for heads.
This uses host languae mechanism for bodys. It kind of has an object oriented feel for some reason to me. relations need to support call and iterate.
There's this big fixpoint.
Many language already support some kind of auto memoization.
```
class Rel():
  def __init__(self,name,arity):
  def __call__():
  def __iter__():
    # register as usage site here?
 @memo
 def f(x,y):
  
class Rule():

```


Maybe the way to look at this is to reorganize your clauses. I find this style repetitive and slightly unnatural, but maybe I'm just not used to it.

path(i,j) -> (edge(j,k) -> path(j,k))
edge(i,j) -> (path(j,k) -> path(i,j) ; path(i,j))

```python
class PushRel(set):
  def __init__(self,func):
    super(PushRel,self).__init__()
    self.func = func
  def __call__(self,*args,**kwargs):
    if args not in self:
      self.add(args)
      self.func(*args, **kwargs)
  def __iter__(self):
    # To deal with RuntimeError: Set changed size during iteration.
    # This is kind of a shame. Probably there is a better way
    return iter(self.copy())

# I'm a little surprised this is working? Is it? The mutally recursvie definition is weird
@PushRel
def edge(i,j):
  path(i,j)
  for j1,k in path:
    if j == j1:
      path(i,k)

@PushRel
def path(j,k):
  for i,j1 in edge:
    if j1 == j:
      path(i,k)

edge(1,2)
edge(2,3)
edge(3,4)
#edge(4,1)
print(edge)
print(path)

#PushRel({(2, 3), (1, 2), (1, 3)})


```

Call master fixpoint function?
Shadow the local ones?

```python
import functools

'''
nah this sucks
def push_rel(func):


  #func.__next__ = 

  @functools.wraps(func)
  def wrapper(*args, **kwargs):
    wrapper.data.add(args)
    return func(*args, **kwargs)

  wrapper.data = set()
  wrapper.__contains__ = lambda self,item: item in self.data
  wrapper.__iter__ = lambda self: iter(self.data)
  return wrapper
'''

@rel
def path(i,j):
  for j1,k in edge:
    if j1 == j:
      path(i,k)

@rel
def edge(i,j):
  path(i,j)
  for j1,k in path:
    if j == j1:
      path(i,k)
# alternative style
@rel
def edge(i,j):
  path(i,j)
  [path(i,k) for j1,k in path if j == j1]

# if we enable some kind of currying / indexing
def edge(i,j):
  path(i,j)
  [path(i,k) for k in path[j]]
```

function()for push , index[] for lookup.

If I made a total fixpoint function, could this be put into naive style?

```python
def loop():
  for i,j in edge:
    path(i,j)
  for i,j in edge:
    for j1,k in path:
      if j == j1:
        path(j,k)

edge = PushRel(loop)
path = PushRel(loop)
```

This is stupid though, right? We run way too many loops in a silly way.

What is the difference between push based datalog and tabling? Or rather can push based datalog be indentified with half of tabling? Calling a function is producing an answer for that predicate. The notion of query is missing.
Does this tabling perspective lead to a clue on how to implement push based datalog cleanly.

This also brings to mind Peter Goodman's communicating datalog servers and Warren's communicating machine model.


## Incremental / Differential Datalog
See 
  - incremenetal notes
  - DDlog.
  - note on Databases Streaming

Seminaive evaluation is a canonical example of incremental computation already.

While souffle does not support incrementality, you can manually do it by semi naive transforming your program yourself? Put the incrmenetality at the bash level
Make every relation duplicated rel -> rel, drel. 
drel is an input delta relation.
```

.decl dedge(x : number, y : number)
.decl edge(x : number, y : number)
.decl path(x : number, y : number)

.input path
.input edge // you don't even need edge in this case
.input dedge
path(x,y) :- dedge(x,y).
path(x,y) :- dedge(x,y), path(x,y). // is this ok to look over all of path? I think so.

edge(x,y) :- dedge(x,y).

.output path
.output edge
```
 You can also output deltas if you want to manually feed seminaive between differetn souffle subprograms.

meta-seminaive
Is this the multi time differential dataflow?
Inner seminaive is douffle program
outer is bash loop


Multiset semantics

edge path query
```python

edge = [(i,j,t,delta)]
t = (period, iter)

```

A_t = \sum_{s<t} \delta A_s
At certain points you can coalesce these sums?

retracting facts feels important?
You could just run semi-naive again if you're only adding in.
provenance required to retract? just counting the ways?
:- edge(), path()





```python
scope = 0
edger = {}
pathr = {}
def push():
  global scope
  scope += 1
def pop():
  global scope, edger, pathr
  # we could index this better
  # non destructive version:
  edger = {k : s for k,s in edger.items() if s < scope}
  pathr = {k : s for k,s in pathr.items() if s < scope}
  ''' # error: dictionary changed size during iteration. hmm.
  for k,s in edger.items():
    if s < scope:
      del edger[k]

  deledge = {k : s for k,s in edger.items() if s >= scope}
  edger.delete(deledge)
  '''
  scope -= 1

def add_edge(x,y):
  if (x,y) not in edger:
    edger[(x,y)] = scope

def strata():
  for k, s in  edger.items():
    if k not in pathr:
      pathr[k] = s
  #path = {(x,y) : s for (x,y), s in edger.items()}
  while True:
    newpath = {(x,z) for (x,y) in edger.keys() for (y1,z) in pathr.keys() if y == y1}
    if newpath.issubset(pathr.keys()):
      return
    for (x,y) in newpath:
      if (x,y) not in pathr:
        pathr[(x,y)] = scope


  #for (x,y) in edger.keys():
  #  for (y1,z) in path.keys():
  #    if y == y1:
  #      add_path(x,z)

add_edge(1,2)
add_edge(2,3)
add_edge(4,5)
strata()
print(pathr)
push()
add_edge(3,4)
strata()
print(pathr)
pop()
print(pathr)
```

There's way too much inefficiency here, but it has the bones of the point.
I need to be doing semi naive before
Also indexing on scope so that pop becomes fast.
We could also lazily pop by just saying to ignore anything with a higher scope during search. That's kind of nice.
But then we need to clean out before we push again. So that's not nice.

Scopes can be related to the min lattice for scope. Yeah. Huh. So you don't even need to run to saturation before you push.

But at the same time, it is the same thing as contextual datalog, just contexts are numbers / totally ordered instead or partially ordered. 



The second incA paper actuaklly had a description of differential datalog that sounds plausible to me, alhtough I can't quite tell if it makes sense. Record only the number of ways of deriving something at the iteration it was found. Now deletions come in and can reduce this number. If the number is reduced all the way to zero, it is actually deleted (but may be rederived at later iteration).

```
consider
edge(1,4).
1 -> 2 -> 3 -> 4

delete 2 -> 3

```


DRED - Delete anything that may have used a fact (recursively). make a delta of thing to delete. Run it through recusrively semi naive style. This is an over approximation of things to delete. Delete them. Now run regular datalog with the fact in question removed. You _may_ have savings. Do you need to do one fully naive step?

## Backtracking a Datalog
<https://philipzucker.com/backtracking-datalog/>

# Implementations
- Souffle
- Flix
- Rel
- IncA, [LADDDER](https://www.pl.informatik.uni-mainz.de/files/2021/04/inca-whole-program.pdf) differential dataflow sequel to Inca
- [Datafun](http://www.rntz.net/datafun/). lambda calculus with type system for tracking lattice monotonicity. and built in set type with comprehensions.
- [differential datalog](https://github.com/vmware/differential-datalog) DDlog
- dr lojekyll
- formulog
- [datafrog](https://github.com/rust-lang/datafrog) - kind of a manual datalog library in rust. Powers polonius, the experimental rust borrow checker
- ascent https://dl.acm.org/doi/pdf/10.1145/3497776.3517779 <https://docs.rs/ascent/latest/ascent/> Rust macro based datalog.
- uZ3 (mu z3) built into z3
- logicblox
- [flora2](http://flora.sourceforge.net/) ergo lite. Is this a datalog?
- [dynamic datalog](https://github.com/frankmcsherry/dynamic-datalog)

- yedalog
- EVE
- datomic
- [cascalog](https://github.com/nathanmarz/cascalog) - clojure runs on hadoop 

- bigdatalog - some kind of big data datalog. 
- [XTDB](https://xtdb.com/) XTDB is a general-purpose bitemporal database for SQL, Datalog & graph queries. What the hell does that mean
- percival https://percival.ink/

- Bloom

- https://github.com/chessai/hsdatalog
## Rel
[vid](https://www.youtube.com/watch?v=WRHy7M30mM4&t=136s&ab_channel=CMUDatabaseGroup)
Relational AI

## DDlog
Incremental datalog. You can assert and unassert facts.
Datalog compiler in haskell. Produces rust project. Rust project uses differential dataflow which in turn uses timely dataflow.

```ddlog
typedef UUID = bit<128>
input relation Host(id : UUID, name : string, ip : IP4)

// syntax to pick named fields
Host(.id=host_id)

"${x}" // string interpolation
// newtype wrapper / structs
typedef ip_addr_t = IPAddr{addr: bit<32>}
// match
var strs = match(value) {
    Some(s) -> string_split(s, ":")
}

//FlatMap to make generative functors.
[1,2,3] //vec litreral
["foo" -> 0] //map literals

extern functions
@ to pattern match and have name

groupby

Ref<>
Intern<> - istring. intern(), ival()

MultiSets
Streams
variants
typedef paylod = Eth1 {} | Eth2 {} | Eth3 {}

modules
```

## IncA
An incremental datalog for program analysis. Incremental can be a big deal in terms of developer interactivity. Also supports lattices


## Formulog
SMT formulas as data. Interesting distinction with CHC where smt formula are predicates.
Refinement type checker.
Symbolic Execution

## Datafrog
Engine behind polonius?
A kind of unsugared rust dsl
[Description](https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md)
I remember this being totally incomprehensible. I guess I must have lost my mind becaus it seems kind of nice now.

## Ascent
Rust macro based datalog. Good integration with rust for that reason. Supports lattices

rust-script 
```rust
// cargo-deps: ascent
use ascent::ascent;
ascent!{
   relation edge(i32, i32);
   relation path(i32, i32);
      
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

fn main() {
   let mut prog = AscentProgram::default();
   prog.edge = vec![(1, 2), (2, 3), (3,4),(4,5)];
   prog.run();
   println!("path: {:?}", prog.path);
}
```

## Flix
https://github.com/flix/book

Supports lattices.
Has a full programming language to.

[online playground](https://play.flix.dev/)
Also install as a vs code plugin. very nice.
[Fixpoints for the masses: programming with first-class Datalog constraints](https://dl.acm.org/doi/abs/10.1145/3428193)

[comments](https://news.ycombinator.com/item?id=31448889)

First class datalog programs. Macros for datalog? Is this different than having a datalog AST data type?

## dr lojekyl
https://blog.trailofbits.com/2022/01/05/toward-a-best-of-both-worlds-binary-disassembler/
https://www.petergoodman.me/docs/dr-lojekyll.pdf

## Datafun
[Seminaïve evaluation for a higher-order functional language](https://dl.acm.org/doi/abs/10.1145/3371090)

## QL

https://codeql.github.com/docs/ql-language-reference/recursion/#non-monotonic-recursion
https://codeql.github.com/publications/
[algebraic data types](https://codeql.github.com/publications/algebraic-data-types.pdf)
[QL: Object-oriented Queries on Relational Data](https://drops.dagstuhl.de/opus/volltexte/2016/6096/pdf/LIPIcs-ECOOP-2016-2.pdf)
pairty recursion - even number of negqtions is ok. Hmm. 
 https://codeql.github.com/docs/ql-language-reference/recursion/#non-monotonic-recursion

```
 predicate isExtinct() {
  this.isDead() and
  not exists(Person descendant | descendant.getAParent+() = this |
    not descendant.isExtinct()
  )
}
```

QL has semantics in datalog. 
typing predicates.
`this` is a parameter. fields are parameters.
special result parameter for functions

charcteristic predicates
even(n) :- digit(n), n % 2 = 0.
this varies over interection of  super types
ember predicates have this vary over

isSmall(this) :- digit(this)

abstract classes hold union of all value of subclasses
subtyping relationship. we can reify class names to runtime.

codeql I could define a "functor" class with method `call`. this is some kind of lambda lifting thing.


Classical correspondence a => b ==  not a or b. This is true. Doesn't allow hypohtetical reasoning though right? I feel like classical correspondences are not valid.
# Souffle

Souffle is a datalog implementation that is fast. It can be compiled to parallel C++ code. It also has a number of very intriguing datalog extensions available
- records
- algebraic data types
- subsumption
- aggregates
- choice domains



[choice domain](https://www.youtube.com/watch?v=TnLGbUqOsBc&ab_channel=ACMSIGPLAN) Functional dependencies of pieces of relation. 
eligible advisors, total order, bipartite matching, more dogs than cats, highest mark in grade.
Defined at relation level. Makes check before any insertion to see if something already defines functional dependency

`.plan` statements

`--show=initial-ram` and other options are quite interesting. The RAM is quite readable at least for small examples.


`as(a, number)` I can cast ADTs to numbers?
https://github.com/yihozhang/souffle/blob/conglog/tests/congruence/math.dl  interesting


[Examples directory](https://github.com/souffle-lang/souffle/tree/master/tests/example)
- convex hall
- anderson pointer, hmmer, java-pointsto
- dfa dataflow analysis
- edit distance
- josephus
- minesweeper
- nfsa2fsa nondet automata to det
- farmer wolf cabbage
- rewrite
- turing - turing machine implementation
- [trie](https://github.com/souffle-lang/souffle/blob/master/tests/example/sequences/sequences.dl) maybe this is what to do first.
- [palindrome](https://github.com/souffle-lang/souffle/blob/master/tests/example/palindrome/palindrome.dl)
- [matrix multipy](https://github.com/souffle-lang/souffle/blob/master/tests/example/mmult/mmult.dl)
- [early parser](https://github.com/souffle-lang/souffle/blob/master/tests/example/earley/earley.dl)
- graph domaintors
- 2sat

Convert string to relation. To avoid 
```souffle
str(s, char, i) :- range(0, len(s)) = i, char = substr(i, i+1, s) 
```



## intrinsic functors
`cat` `strlen` `substr(string,index,length)` `ord`

`lor` `land` `lxor` `band` `bxor` `bshl` `bshr` `bshru`


every non zero number is considered true.
max min + * % ^

`f(@g()) :- true` Sometimes you need to put true in the rhs position.


## floats
https://github.com/monadius/ocaml_simple_interval/blob/master/interval1.ml - very simple intervals


```souffle
.decl test(x : float, id : symbol)
//test(nan).
//test(inf).
//test(-inf).
test(-0, "-0").
test(1/-0, "-inf").
test(1/0, "inf").
test(1/0 - 1/0, "-nan").
test(1/0 + 1/0, "inf").
test(1/0 + 1/(-0), "-nan"). 
test(0, "0").
.output test(IO=stdout)

```

## Souffle proofs
Manual exploration of just dump it. Does the dump memoize?

`-t explain`
`.pragma "provenance" "explain"
```
output proof.json
format json
explain path(1,2)
exit
```

You can emulate proof production using subsumption. See below.


## Aggregates
min, max, count, sum.

Aggregates require stratification

Aggregates can be emulated using subsumption (see subsumption section). This technique avoids the stratification requirement.

The witness problem

Aggregates by key correspond to something like a mapreduce computation or a groupby computation.

 


## User Defined Functors
What about normalization? That's intriguing
BitSets

[souffle lib](https://github.com/souffle-lang/souffle-lib)

Some experiments of mine

- [souffle-z3](https://github.com/philzook58/souffle-z3) We can use the Z3 C bindings if we make a little helper function to generate a Z3 context.
- [souffle-lua](https://github.com/philzook58/souffle-lua) We can ffi call into lua for easier more dynamic user defined functor writing. Maybe I should try using guile?

For foreign data types you need to make your own external interning table, or the cheap prototyping thing to do is use serialization / deserialization to store as strings.
In Z3 you can use pointers, but that is because Z3 is internally hash consing.
You can briefly hold pointers as unsigned inside a rule, but you should probably compile souffle in 64 bit mode.

gnu multiprecision
Nah, this won't work. I need to do allocation. Unless I can call malloc?
```
.pragma "libraries" "gmp"
.type mp_int <: unsigned
.type mp_str <: symbol
.functor mpz_get_str(unsigned,unsigned,mp_int):symbol
.functor mpz_init(mp_int) // hmm. This won't work
.functor mpz_set_str(mp_int, mp_str, ):number
```



lib_ldscript
use `whereis` if ascii `cat` the file and include the things in group
`souffle libc.dl -lm-2.31 -lmvec`


```
.pragma "libraries" "m-2.31"
.pragma "libraries" "mvec"
.functor acosf(x: float): float
.decl test1(x : float)
test1(@acosf(0.1)) :- true.
.output test1(IO=stdout)
```

Holy crap this works

```souffle
.pragma "libraries" "z3"
.functor Z3_get_full_version(): symbol
.decl test1(x : symbol)
test1(@Z3_get_full_version()) :- true.
.output test1(IO=stdout)
```

```souffle
.pragma "libraries" "z3"
.functor Z3_get_full_version(): symbol
.functor Z3_mk_config() : Z3_config // It's cute but these are almost certainly 64 bit pointers. So a helper lib is probably better.
.type Z3_config :< unsigned
.functor Z3_mk_context(Z3_config): Z3_context
.functor Z3_eval_smtlib2_string(unsigned, symbol) : symbol
#define is_sat(x) Z3_eval_smtlib2_string(ctx, )

.decl test1(x : symbol)
test1(@Z3_get_full_version()) :- true.
.output test1(IO=stdout)
```

I can't figure out how to get libc, but it is the weirdest library of all.

Formulog via linking to Z3. Do my own interning for handling int32? Or compile souffle in 64bit mode. String manipulation of smtlib? Pool of z3 ctx? This is probably good because we may want to run parallel souffle.
```souffle
#define BINOP(op,x,y) cat(cat(cat(cat(cat("(", op), ", x), " "), y), " )") 
#define AND(x,y) BINOP("and", x, y)
#define OR(x,y)  BINOP("or", x, y)
#define IMPL(x,y) BINOP("=>",x,y)
#define TRUE "true"
// but like interpolated with cat.
.type smtint <: symbol
.type smtbool <: symbol
.type smtreal :< symbol

```
Hmm But how to deal with `define-const`.

Ah. This is in a sense striaghtforward ish CLP? CLP but in datalog.

CHR constraint handling rules. Can I embed into subsumption?


Syscalls. libc might already be available?

```souffle
.pragma "library-dirs" "/usr/lib/x86_64-linux-gnu/"
.pragma "libraries" "c"
.functor puts(symbol) : number

.decl test(x : number)
test(@puts("Hellow world")) :- true.
.output test(IO=stdout)

```

You can't defined your own user-defined functors inline. Two options that get you a lot of the way there are:
1. use cpp macros `#define FOO(x,y)`
2. Use auxiliary choice-domain relations. Memoization of functions. Many functions are so cheap you don't want to memoize them though.
3. use inline souffle relations


```
// souffle is by default 32 bit
// ptrs can be handled via a record storing upper and lower half.
.type ptr = [high : number, low : number]


```




## ADTs

ADTs are an incredible feature. They expand the expressive succinctness of souffle by so much it is unreal. It is somewhat possible to emulate them using other souffle features.

You can flatten adts into their relational form `$Add(x,y) = z ---> add(x,y,z)`. Perhaps you can get autoinc + choice to make them uniquely constructed.

See also <https://www.philipzucker.com/souffle-functor-hack/>

It is somewhat unfortnuate that there are not accessors for ADTs? It would make macro writing more satisfying

[interesting discussion of adt storage](https://github.com/souffle-lang/souffle/issues/2181)
- simple enums = ramdomain values
Converting simple enums to numbers. unsigned or number should do the same thing until you get to 2^31 or so
```
as($A(), number)
```

- Values with single fields representable as interger become `[tag: unsigned, value : A]`
- Compound values becomes [tag : unsigned, [all the stff]]


You can access the "id" associated with a value also `as([1,2,3],number)` for devious ends

### Contexts are King
a very useful thing to note is that you should use
contexts, delimited continuations, goal stack, zippers, to implement control flow.
Datalog is bottom up. In a sense it's a giant while loop. When you bottom upify or loopify recursive algorithms, sometimes you need to reify the call stack (or whatever else you might call it). See defunctionalize the continuation talk.
These contexts are expressible as 

### field accessors
It is a pain that there isn't a good way to make trustworthy fresh variables using `mcpp` due to lack of `__COUNTER__`. Best I can figure is hacks using `__LINE__` and concatenation. Otherwise insist on variables coming from outside into macro.

```souffle
#define FST(a,r) (r = [a,_])

.type myrec = [a : number, b : number]
.decl test(x : myrec)
.decl myfst(a : number)
myfst(a) :- test(r), FST(a,r).
test([1,2]).
.output myfst(IO=stdout)
```

This does _not_ work.
```souffle
#define FST(a,r) (r = $A(a, _))

.type myadt = A {x : number, b : number} | B {}
.decl test(x : myadt)
.decl myfst(a : number)
myfst(a) :- test(r), FST(a,r).
test($A(1,2)).
.output myfst(IO=stdout)
```

We _could_ probably cast to records to get the same effect. If you dare.

### Vectors
I am in no way endorsing this. Actual representation of vectors have size field in them. Eh maybe I can't even do this. I was thinking maybe I could do a unsafe cast, but that's a pain too. Maybe this is possible with some truly horrific macro programming + unsafe casts. Yikes.
```souffle
.type vector = [size : unsigned, key : unsigned]
```

safer alternative: We can make finite sized vectors as an adt
```
.comp Vector<T>{
.type vector = V0 {} | V1 {x1 : T} | V2 {x1 : T, x2 : T} | V3 {x1 : T, x2 : T, x3 : T} | V4 {x1 : T, x2 : T, x3 : T, x4 : T}
}

```

Or we can partially unroll a linked list to avoid so much indirection cost.

```
.comp Vector<T>{
.type vector = V0 {} | V1 {x1 : T} | V2 {x1 : T, x2 : T} | V3 {x1 : T, x2 : T, x3 : T} | V4 {x1 : T, x2 : T, x3 : T, x4 : T}
     | Cons {x1 : T, x2 : T, x3 : T, x4 : T, tail : vector}  
}
```



### Use ADT instead of autoinc()
autoinc() is a generative counter. It is nice because it is efficient. However, the stratification requirements on it are gnarly. It is too imperative, not declarative enough andyou get in trouble.
ADTs are also generative though. If you makea new object with them, you can make things that didn't exist in the original dataset. They sort of track how they were made by their arguments. This helps prevent you from instantiating the same thing twice. ADTs are basically hash consed/interned.

### Record Packing
Sometimes your number of fields in the relation get crazy. Like let's say you want to describe some abstract domain like an interval. You need to carry 2 parameters everywhere when you're really talking about 1.

You may however be taking a big performance hit. There is always a indirection hit of records vs unpacked records. Here is it felt more accutely because it isn't just a memory deref, it's a whole table lookup (? how exactly are records imlepmented).

It is a bummer that souffle doesn't have record access notation. It's be nice for macros.

If you want join semantics on lattice records
```
.type Interval = [l : unsigned, u : unsigned]
.type VSA = [l, u, stride, ]

```
// default souffle has 32 unsigned. You can make your own 64 bit by combination. Taking a big perfroamcne hit
.type U64 =  [l : unsigned, u : unsigned]

## Macros
You get the C preprocessor run by default over souffle files. I find this incredibly useful. Admittedly, the need for a C preprocessor can be considered evidence of a weakness in a language (meaning many many languages are weak. C, 
haskell, etc.)

Note that you can pick a different preprocessor via `--preprocessor=`. I think this might be realitvely new.

```souffle
// pragma unfortunately is too late in the process to control this?
// .pragma "preprocessor" "cpp"

#define FOO 3
#define CONST1(x) __COUNTER__

.decl test(x : number)
test(CONST1(3)).
.output test(IO=stdout)

```


## Components

## Choice Domain
<https://souffle-lang.github.io/choice> picks first one to come along
Can I combine choice domain and lattice. But choice domain once you pick you're done...
well. I can recover lattice style via an explicit congruence closure. So. it doesn't matter I guess.


## Negation
Stratification

See answer set programming and stable model semantics

What about

foo(x) :- biz, !foo(z).

and making it stratified by deleting all negative atoms (an overpapproximation?) And then using the overapproximation of !.

foo1(x) :- biz.
foo(x) :- biz, !foo1(z)

What about guarded negation? For example if you turn off stratification but are able to supply an explicit `strata(n)` guard. This could be useful for 


##  Souffle source
- synthesizer - actual code printers
- include/souffle - the runtime of souffle
- ram, relational abstract machine
- 


# Resources
[Database Theory](https://github.com/pdm-book/community) book


[Modern Datalog Engines](https://www.nowpublishers.com/article/Details/DBS-073) 68 page book 2022

[Cozo](https://news.ycombinator.com/item?id=33518320) https://github.com/cozodb/cozo


[treeedb](https://github.com/langston-barrett/treeedb) use tree sitter to get languages into souffle
https://github.com/langston-barrett/tree-sitter-souffle souffle tree-sitter

[cclyzerpp](https://github.com/GaloisInc/cclyzerpp)

[A Datalog Engine for GPUs](https://www.dcc.fc.up.pt/~ricroc/homepage/publications/leap/2013-WFLP.pdf)

[Modular materialisation of Datalog programs](https://www.sciencedirect.com/science/article/pii/S0004370222000662?via%3Dihub) how to use foreign functions to implement datalog rules correctly?

D/RED derive reduce - to delete a fact, delete any facts that _may_ have use that fact (reucrsively you need to delete any facts that may have used these derived facts and so on). Put these in a table. You can then check for still allowed ways to redeirve them. Because you know the head, that will filter the available bodies, so you don't _need_ to do a fully naive pass.

vectors std::sort.


automatic differentiation like chr?

[initial limite datalog](https://research-information.bris.ac.uk/en/publications/initial-limit-datalog-a-new-extensible-class-of-decidable-constra) extension of datalog Z?

datalog ilp? Using FLP?


[the expressive power of higher order datalog](https://arxiv.org/pdf/1907.09820.pdf)

[Overview of Datalog Extensions with Tuples and Sets (1998)](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.39.9904)
LDL. Hilog. COL. Relationlog. Datalog with set objects and grouping is an old idea.


[Neural Datalog through time](https://arxiv.org/pdf/2006.16723.pdf)


[Datalog with Negation and Monotonicity semipositive datalog](https://drops.dagstuhl.de/opus/volltexte/2020/11943/pdf/LIPIcs-ICDT-2020-19.pdf) The theory of removing negation? I guess that makes sense as a pursuit. It's what I always try to trick my way into.

[survey of deductive databases ullam nramakrishnan 1993](https://core.ac.uk/download/pdf/82655241.pdf)

Stefania Gabriela Dumbrava - verified datalog https://web4.ensiie.fr/~stefania.dumbrava/ https://hal.archives-ouvertes.fr/hal-01745566/document datalogcert


[bag datalog](https://twitter.com/NickSmit_/status/1510832523701456896?s=20&t=5y91-I1SPrIGomAWSqs69w) https://arxiv.org/pdf/1803.06445.pdf
bag rewriting. derivation tree. rule(reason1,reason2) :- R(reason).R(reason)
No subsumption.
What about making these things the same thing. We have an equiavalence class of proofs. We extract a smallest one.
How do you record eq? downcast ids to integers
eq(i, i, reason)
proof extraction becomesan egrtaph extraction
We get the hash consing property for free.



topics:
- incremental datalog
- differential datalog https://github.com/frankmcsherry/blog/blob/master/posts/2016-06-21.md

[big datalog on spark]http://yellowstone.cs.ucla.edu/~yang/paper/sigmod2016-p958.pdf

[Modern Datalog systems at sigmod and vldb](https://github.com/frankmcsherry/blog/blob/master/posts/2019-09-06.md)
[Scaling-Up In-Memory Datalog Processing: Observations and Techniques]() Recstep




unsafe stratification:
strata_finish(), !query_strata.
Timestamps can d something similar
watermark(t), !query(t1), t1 < t 
or safe deletion
delete(t).
You can partial evaluate to satisfy rel_0 rel_1 rel_2... it is annoying though and not very scalable


[QL: Object-oriented Queries on Relational Data](https://drops.dagstuhl.de/opus/volltexte/2016/6096/pdf/LIPIcs-ECOOP-2016-2.pdf)

[datalog reloaded](https://link.springer.com/book/10.1007/978-3-642-24206-9?page=2#toc) a datalog compendiium 2011
 
[algebraic modelling in datalog](https://dynresmanagement.com/uploads/3/5/2/7/35274584/datalog_warrenbookchapter.pdf)
Some logicblox stuff. Datalog meets mathemtical programming?

Generic Join



If you wrote a decompiler or compiler in datalog, provenance becoes something more concrete to talk about


Compare and contrast datalog vs CHR. subsumption allows us some of the deletion of CHR. Proapgation rules of chr are similar to datalog rules. We could possibly emulate multisets using subsumption by adding extra multiplicty parameter to realtions.


[datalog : concept history outlook 2018](https://dl.acm.org/doi/10.1145/3191315.3191317)
[declarative logic programming](https://www.google.com/books/edition/Declarative_Logic_Programming/CMatvAEACAAJ?hl=en)




`call/N` is emulatable clause by clause in prolog.
Is there an analogous meta predicate?
foo(a,b) :- push(["foo", a,b]).
bar(a) :- push(["bar", a]).



What about interfacing with prolog?
What about interfacing with lua or python? ocaml haskell, minizinc.




[Synthesizing Datalog Programs Using Numerical Relaxation](https://arxiv.org/abs/1906.00163) difflog
[provenance based synthesis of datalog programs](https://www.youtube.com/watch?v=cYAjOGhclcM&ab_channel=ACMSIGPLAN)
Building a compiler in datalog. I can parse. I can do program analysis. How do I backend? Backend takes arbitrary non monotonic choices.
Use choice domain? that could work. I could force an ordering through the program.
```souffle
// linear assembly sequence
.type Op = Mov {out , in , }
asm(1, "mov", "x", "y").
asm(2, ")

liveness(instr, var)

assign("x", : reg)


```

```souffle
.decl A(k:number, v:number)
.output A(IO=stdout)
A(1, 1).
A(1, x+1):-
    A(1, x),
    x < 10.
A(x, v1) <= A(_, v2):-
    v1 < v2.
```

[topdown vs bottom up datalog](https://twitter.com/wilton_quinn/status/1496393635533066241?s=20&t=XQ6lmI5ivNs5z5-EwnGKMQ)

[datalog and recursive query processing](http://blogs.evergreen.edu/sosw/files/2014/04/Green-Vol5-DBS-017.pdf)

What if i did a call to minizinc formulog style?

A reversible compiler. would requires exists and equality. ... egraph?
[dr lojekyll](https://www.petergoodman.me/docs/dr-lojekyll.pdf)

So an object oriented datalog.

"These are generative functors? Is that how they return a relation? Do these functors take arguments?. Would the analog in souffle to be running the C++ program api in a user defined functor?"

[geometric database](http://www.mmrc.iss.ac.cn/~xgao/paper/jar-gdbase.pdf) horn clauses. good clean fun
[So You Want To Analyze Scheme Programs With Datalog?](http://webyrd.net/scheme_workshop_2021/scheme2021-final2.pdf)
[parser in datalog](https://homes.cs.washington.edu/~bodik/ucb/cs164/sp13/lectures/09-Datalog-CYK-Earley-sp13.pdf) bottom up parsing


[analysis are arrows](https://luctielen.com/posts/analyses_are_arrows/)

[Static analysis in datalog slides](http://www.cse.psu.edu/~gxt29/teaching/cse597s19/slides/06StaticaAnalysisInDatalog.pdf)

[modulog](https://github.com/bobatkey/modulog) - datalog with ocaml style modules

[crepe](https://github.com/ekzhang/crepe) a rust prcoedural macro datalog

Dedalus datalog. Is it datalog with a time variable or something more? I think it may have changed the stratification conditions.


<https://twitter.com/csaba_hruska/status/1456575302906355715?s=20> subsumptive datalog good for lattices?

<http://logicprogramming.stanford.edu/readings/tekle.pdf>
More efficient datalog queires - subsumtive tabling beats magic sets

<https://www3.cs.stonybrook.edu/~kifer/TechReports/OpenRuleBench09.pdf> openrulebench. Some described benchmark problems for rule engines

<https://edmcman.github.io/papers/ccs18.pdf> Using Logic Programming to Recover C++ Classes and Methods from Compiled Executables

<https://github.com/grin-compiler/souffle-cfa-optimization-experiment>


Using SQL engines as backend. https://duckdb.org/2021/10/29/duckdb-wasm.html

https://www.youtube.com/watch?v=HRO3RkOHe_4&ab_channel=MayurNaik - constraint based analysis lecture 7

Nielson books seems a lot more readable to me now.

Z3 datalog has intervals? How do i find a list of supported domains
So I could use C-cube datalog
Or I could use Z3 datalog.
If I want to go in browser (and of course I do), then Z3 is not wise.
Neither is souffle.
Could roll own bad datalog.
Ogre?

https://souffle-lang.github.io/examples simple points to analysis

Is datalog actually a good fit
https://tudelft-cs4200-2020.github.io/ - hmm sppoofax
https://www.youtube.com/watch?v=Qp3zfM-JSx8&ab_channel=ACMSIGPLAN - souffle
[Demand Interprocedural Program Analysis Using Logic Databases](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.648.1834&rep=rep1&type=pdf) - reps
Engler 96


prosynth - leanr datalog rules from data?

.type Binop = 
.type Expr = 
.type Stmt = 
   While 




https://arxiv.org/abs/2107.12909 - so you want to analyze scheme with datalog https://www.youtube.com/watch?v=oiXL44WlC-U&ab_channel=ACMSIGPLAN

Might this not be a nice pass for higher-order theorem proving?

CFA - labelling all subespressions =? program points?
In functional programs value and control flow are more intertwined

https://en.wikipedia.org/wiki/Use-define_chain

https://matt.might.net/articles/implementation-of-kcfa-and-0cfa/ - k-CFA: Determining types and/or control-flow in languages like Python, Java and Scheme
Might does stuff with this. Abstracxting abstract machines is about 
Van horn. Darais
Gilray. Micinski
It's in that Nelson book

olin shivers

https://dl.acm.org/doi/10.1145/2926697.2926698 - chloe paper Liveness-based garbage collection for lazy languages

https://www.youtube.com/watch?v=7fDfWBsiqok&ab_channel=ACMSIGPLAN - visualzing abstract absract machines


https://yanniss.github.io/
Points to analysis. Doop
https://yanniss.github.io/M221/
https://www.youtube.com/playlist?list=PLheERyVBk39SefKqkGEo5YesOn9rkl8fS in greek
https://www.youtube.com/watch?v=3RHv44Ehd5Y&list=PLRUJ115QHa0WMyGyP2j_1KRFJjaT0kFOu&ab_channel=plast-lab - doop and datalog tutorials

objects are represented by allocation sites. firest abstraction. Good idea.
Actual program textual positions
context sensitivity is what makes an analysis precise (call stack, maybe loop unroll?)
andersen style analysis.
pointer analysis
flow-sensitive, field-sensitive, heap cloning, bdd, k-cfa
mutual recursion

source, alloc, and move instructions. a databse of each one.

```prolog
varpointsto(var, obj) :- alloc(var, obj).
varpointsto(to, obj) :- move(to, from), varpointsto(from,obj).

%assignemnts are local
assign(to,from) :- assignlocal(from, to, _).

%but also any function call is an assigneent
assign(formal, actual) :- calgraphedge(invocation, toMethod), formalparam[index, toMethod] = formal, ActualParam[index,uinvocation] = actual.

% and returns
assign(local,return) :- callgraphedge(invocation,toMethod), returbnvar(return, toMethod), assignReturnValue[invocation] = local.

varpointsto(var,heap) :- assignheapallocation(heap,var, inMethod),  reachable(inMethod).
varpointsto(to, heap) :- assign(to from)

// base.fld = from
fieldpointsto(baseheap, fld, heap) :- storinstancefield(from, base, fld, _), varpto(base,baseheap), varpto(from,heap).

// to = base.fld
varpto(to,heap) :- loadinstancefield(base,fld,to), vpto(base,baseheap), fieldpto(baseheap,fld, heap).

// base.toMethod(...) 
reachable(tomethod), callgraphedge(invocation, tomethod), varpto(this,heap) :-
    reachable(inmethod), instruction:method([invocation]), 
    virtualmethodinvocation( invocation ) = base,
    varpointsto(base, heap),



```

a model of context senssitive
call site sensitivity
variables are qualified by the call site of their enclosing method



prelude.ml = open KB yada yada

#include prelude.ml


could I compile datalog to bap?
class(slot,slot,slot) :- class(slot,slot,slot),
class(slotname : f(x,y) , ) :-
==
request body
promise head,

build rule.

differences
- classes have named columns, not positional (extensible). They also have unique ids always. Kind of more similar to souffle records?
- Modedness. Can I even promise multiple slots at once? In a sense datalog is not interestingly moded.
- It's more of a tabled prolog. Top down requests which lazily trigger table instantation

val promise : ('a, 'p) slot -> ('a obj -> 'p t) -> unit
('a, 'p) slot -> 'a obj -> 'p t

program(obj@{ insn : q , semantics : s }) :-   
program( obj: o, semantics : s, ) :-

Program.cls
promise slot1 (fun obj -> 

)

Hmm obj is incoming. slots are possibly incoming or outgoing

provides <-trigger(slot, obj), collects
    (slot : slotexpr :- obj)    -- the api of promise has obj incoming and slot outgoing
    Things don't _have_ to be built off of obj, but it sure helps.

An option domain is closest to ordinary datalog / tabled prolog


we can only promise on one slot. We can provide them all though. Individual slots are joined.
a list of lattice tuples vs lattice with projections

so datalog gives uniqueness of an entry easily
path(x,z) :- edge(x,y), path(y,z).
path(x,y) :- edge(x,y)
edge(1,2)
edge(2,3)

vertex(1).
vertex(2).
path(1,_).
path(2,_).
path(3,_).

path(a, _) :- vertex(a). -- trigger on path? but path doesn't exist


p@path( head_slot , tail_slot ) :- 



datalog over intervals. Maybe this would be an interesting blog post.
The relation itself has to implement the lattice api. Not the individual fields
What makes semi naive evaluation possible is the difference operator (heyting?)
Datalog does require a notion of projection. And a notion of relation composition/database join
E' = proj( A /\ B /\  C /\ D )
E1 = E \/ E'


Sometimes I've had knowledge base objects for which I immediately fill a slot upon creation, because that slot is essentially part of the objects identity. As an example, I have path objects in the KB. The only time i make one is when I have a particular path to talk about and I'm never going to offer another opinion about what that path is, all other information is derived from it. It feels slightly awkward that I have to define this slot using an optional domain, basically as far as I can tell, because I have to create an empty object and then provide for the slot on the next line. So I'm only using the `None` case for the briefest moment, but now have to deal with that case or use `Option.value_exn` whenever I access it. Is there a more elegant way to deal with nonoptional slots? I could use the `flat` domain with `[]` as a default but that is conflating 

- 

https://kilthub.cmu.edu/articles/thesis/Holmes_Binary_Analysis_Integration_Through_Datalog/7571519
homles binary analysis through datalog
https://github.com/maurer/marduk/tree/master/mycroft
https://github.com/maurer/holmes


http://reports-archive.adm.cs.cmu.edu/anon/anon/usr/ftp/2006/CMU-CS-06-180R.pdf alias analysis datalog



hmm. temporally oblivious. Interesting.
This idea of using explicit time is interesting. Why didn't I consider using an epoch variable?

Synactic sites. also interesting. Syntax is intrinisically finite.

doop, paddle, wala, bddbdbdbd


https://www.youtube.com/playlist?list=PLamk8lFsMyPXrUIQm5naAQ08aK2ctv6gE - SOOT lectures. 

https://yanniss.github.io/ptaint-oopsla17.pdf - unified points to and taint tracking

Interpeting programs into datalog?


Context sensitivty. I kind of imagine copies of the CFG coming out of the plane of the screen. Finite loop unrolling and then just regular widening. A mapping from block to visitation # might work for example. Many combos might not exist. This probably won't get you much


What would be a simple functional language to do this on?


https://arxiv.org/abs/2101.04718 Declarative Demand-Driven Reverse Engineering

https://link.springer.com/chapter/10.1007/978-3-030-11245-5_11 - demand control flow analysis



## building souffle emscripten
We revmoed all the extra flags turned off tests
removed all mentions of libffi
src/CMakeLists.txt - removed werror
CMakeLists.txt

removed ffi.h from interpeter/engine.cpp by removing the entire case

ok the frontend needs a bunch of stuff. It calls mcpp first.
This strips comments maybe?
Can link in mcpp, but for now, just remove that stage. use fopen and fclose instead of popen

We need to load into emscripten file system. It crashes kind of opaquely
/media/philip/phils_gud_disk/emsdk/upstream/emscripten/em++  -O3     -s ERROR_ON_UNDEFINED_SYMBOLS=0 -fuse-ld=lld @CMakeFiles/souffle.dir/objects1.rsp  -o souffle.js @CMakeFiles/souffle.dir/linklibs.rsp --preload-file test.dl 

remove loadDLL in engine.cpp. Maybe we can turn that back on. Do we even need it?

https://github.com/hoodmane/libffi-emscripten
https://github.com/emscripten-core/emscripten/issues/11066
It's conceviable libffi could be made to work

I could probably easily enough manually remove any stratification restrictions.

Actually, yizong mentioned some flags to do that
--disableTransformers=SemanticChecker 
"it may not do what uou expected"



Why can I not use the souffle implementation of ADT?
There is a cool directory of examples. There is a rewriting example in there





https://twitter.com/luctielen/status/1416319909055827970 datalog paper and haskell implementation
 https://souffle-lang.github.io/pdf/cc.pdf

Datalog for disassembly dldasm https://www.usenix.org/system/files/sec20fall_flores-montoya_prepub_0.pdf
instruction starts and ends is actually a hard problem. variable instruction lenght + stripping

instruction_start(insn : int, byte : int), instruction_end(insn : int, byte : int) 
bits(byte : int,  bits : byte ) ?

block(blk, insn)
Blockhead
blocktail


Identify instruction starts
Identify function starts
Build the CFG
Do a simple VSA

control flow

is_jmp(insns)
next(insn1 : , insn2 : ).



Dfiferential dataflow?
Jhanme street incremental?
https://en.wikipedia.org/wiki/Incremental_computing
Instead of datalog?
what does change mean?
diff x y
apply x dx = y

a -> (b, db -> da)
id = \x -> (x, \dx -> dx) 
everything starts at 0

stream processing
data Flow da db = da -> (db, Flow da db)

demand driven
(a -> (b, (unit -> b) -> (() -> a)  
datalog as an embedded DSL (semi naive eval really)
(Rel,Rel,Rel) -> Rel
join :: (Rel, Rel) -> Rel
join = \(r1,r2) -> r1 ++ r2, \(dr1, dr2) -> dr1 ++ dr2
fix :: (Rel -> Rel) -> Rel -> Rel
fix l = \x -> let (y, dl) = l x in
              let dx = diff y x in
              match dx with
              | [] -> (x, dl)
              | _ ->  y ++ dl dx
fix :: (Rel -> Rel) -> (Rel -> Rel)
fix 

relation foo x y z = 
fresh (\x -> 
 
)
fix :: Flow a a -> Flow a a
fix f = \da -> db, f2 = f a in 
              match db with
              | 0 -> (0, fix f2)
              | _ -> let (db2, f3) = fix f2 db in
                     (db + db2, fix f3)

trace :: ((Rel,Rel) -> (Rel, Rel)) -> Rel -> Rel




f(f(a)) = f(a) problem

% mark equiv as equivalence relation.

a(0).
f(1, 0).
f(2, 1).
equiv(1,2).

%congruence closure 1
% different orders of these?
% this is a very direct interpetation of congruence clsoure inference rule.
equiv(A, A') :- equiv(B, B'), f(A, B), f(A', B').


%alternative form
eclass( id , head, args) :- 

% get proof.

% f(Self, )
% f(Self, n )

Datalog might be a good DSL for specifying egraph computation problems. It allows multipatterns. 
A special relation = for egraph equality. We disallow unification?
Stratified negation can be allowed in egraph pattern matching.
The egraph is a database.

pat1(A,B,C) :- 

Can't we use unification variables as eclasses?

We can't generate new eclasses though.

equiv(X,Y) :- lhspat, rhs(X)
rhschunk(Fresh, ) :- lhspat
rhschunk(Fresh, ) : lhspat

The de moura bjorner matcher is some kind of brother of the WAM.


This might enable integrating congurence closure with program analysis passes.


Datalog is a specification language of relations. It is similar in some respects to SQL.

A relation is a set of tuples. One method for storing it is to use an array of tuples.

A slightly expanded form of datalog we could require that every variable is unique unless using a special `=` clause. 
It has a simple precodural reading

However, this naive storage method and algorithm is not the most efficient. Ideally, you want to use some pieces of the tuples as indices and use fast data structures for them (hashmaps or search trees). There is also much redundant computation here.
We want to push from small relations into larger ones and use indexing to 

factored form:
ancestor() :-  parent() ; (), ()
Kind of like a function call now.
generators that return only unique elements
Hmm. That's kind of a curious thing. It's push memoization rather than pull memoization.

def ancestor():
    seen = set()

    if newtup not in seen:
        yield newtup

Top down + Memoization

function parent()
    return [(:greg, :larry)]
end

function ancestor(x,y,z)
    for (x,z) parent()
end

a relation lifter.

Or could use explicit fix? memofix 
function rel(f, args...) 
    ctx = Dict()
    for arg in args
        if arg isa Symbol

    end
end

We really want to extend previous definitions not override them

Stream memoization.
How can I get the other modes for free? If you implement the fully producing mode, receiving mode is easy.
But unduly expensive.
How do you solve mode constraints.
Asymptotic costs. log_n( n^5 * ) 


https://www3.cs.stonybrook.edu/~warren/xsbbook/node5.html assign once variables.
@prolog x = y 

if inscope(x)
if inscope(y)
You could catch the undefvarerror? maybe.

I guess we could macro the entire function and change the semantics of =.
@nondet block for multiple function defintiions

I guess we could return unique IDs along the channels too
Using mutiple dispatch
f(::X, ::Y)
f()

@nondet()
f(x) = 
f(x) = 
end
rewrites to
f(x)
    [def1, def2]
end

How do we encode the mutliples:
1. array
2. channel
3. coroutine?
3. iterator

Hmmm. I could use tabled swipl instead of souffle.
