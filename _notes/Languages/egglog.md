
- [Examples](#examples)
  - [Geometry](#geometry)
  - [Egglog0 posts](#egglog0-posts)
  - [Souffle Posts](#souffle-posts)
  - [Refining equalities](#refining-equalities)
  - [Integration](#integration)
  - [Merging Database](#merging-database)
  - [Extraction as datalog](#extraction-as-datalog)
- [Misc](#misc)
  - [Modulo theories](#modulo-theories)
  - [Propagators](#propagators)
  - [AC](#ac)
    - [slog](#slog)
- [Partial Application](#partial-application)
  - [RVSDG](#rvsdg)


# Examples
```eggsmol
(datatype Foo (Bar))

```

## Geometry

```eggsmol
(datatype Point)
(datatype Seg)
(function seg (Point Point) Seg)
; hmm. Questionable. Should I define segments to be commutative?
(rewrite (seg x y) (seg y x))

;(function len (Seg) ?)

(datatype Line)
(function extend (Seg) Line)
(function line (Point Point) Line)

(birewrite (line x y) (extend (seg x y)))

; parallel lines form an equivalence class. Reflexive, transitive, symettric.
; ParaClass is a set of lines.
(datatype ParaClass)
(function para (Line) ParaClass)


(relation perp (Line Line))
(rule ((perp a b)) ((perp b a)))
(rule ((perp a b) (perp b c)) ((set (para a) (para c)))
(rule ((perp a b) (= (para c) (para b)) ((perp a c)))

(datatype Angle)
(function angle (Line Line) Angle)

(datatype Circle)
(function center-circ (Point Point) Circle)


; I wanted to deempasize coordinates, but we can construct points using coordinates if you like.
(function coord (Rational Rational) Point)

```



## Egglog0 posts
<https://www.philipzucker.com/egglog>

## Souffle Posts



## Refining equalities
Geometry example - directed lines refine

partial functions - restriction of domain

equal up to epsilon. An equality over epsilon families - everythign that has same derivatives

## Integration

```
d(x*x) = x*d(x) + d(x)*x
chain rule can't be written
d(cos(e)) = -sin(e)*d(e) no, this is the chain rule
d(sin(e)) = cos(e)*d(e)

xd(x)

2xcos(x)d(x) -> cos(x*x)d(x*x) 
This works
d(e1 + e2) = d(e1) + d(e2)
d(pow(e,n)) -> pow(e, n-1)*d(e)

d(u*v) = d(u) * v + u * d(v)
d(u)*v -> d(u*v) - v * d(u) - integ by parts
- u substition happen by definition.

(cross u v) 

(* a b)  -> (neg (* b a)) :when (dim a = odd)
d (/ a b) 

int(a,b,f)
int(Domset,f)
sphere_int


int(sphere(R), )
rot_sym(r)
rot_sym(x), rot_sym(y) -> rot_sym(x*y)
rot_sym(x), rot_sym(y) -> rot_sym(x + y)
rot_sym(x) -> rot_sym(f(x))
rot_sym(lit(n))

int(sphere(R), e*d(r)), rot_sym(r) -> 4 * pi * 
int(ball(R))
int(interval(a,b), e*d(x)), dim(e) = 0 -> int(interval(0,1), d(y))
```


Differential forms works. These aren't binding operations anymore. sonova.


`sin(x) = 1`. we are learing about x. exists x. sin(x) = 1

`f(x) = 1`. we are learning about f. closer to forall x. f(x) = 1

The function sin(x) is more like the second. `x` is a coordinate function M -> R.
`sin : (R -> R) -> (M -> R)` is partially applied `comp(sin : R -> R,_)`.
Because of this, we can build in the chain rule.


A different modelling paradigm is to use hoas.
`int(\x -> sin(x))` Now x is alpha bound.


sum, set, fun, differential. WHat are the meanings of these symbols? 


Integration:
See rubi
See winston lecture

```prolog

int(sin)

```


https://github.com/egraphs-good/egg/blob/c590048817a35236ce9910e7c1e0b1fac670822c/tests/math.rs#L179
Is there an example where the naive approahc is wrong?

Interesting. Metatheory used extraction then diff technqiue
https://github.com/JuliaSymbolics/Metatheory.jl/blob/9045c7df97b910e57a644bf9c5ddc152d7b0d869/test/integration/cas.jl#L78


Egraph starts at syntax and moves progressively towards semantics. You have to have a semantics in mind.


Can I do summation? Discrete exterior calculus I guess. Manifestly working in "2d" simplicial space avoids summation swapping problem.

Contour integrals




## Merging Database
It's interesting (to me) how similar this is to the union find dict. The difference is that all the tables share the same union find.
This formulation of merge and default functions is not mine. Some mix of yihong, max, remy, or zach came up with it.

```python
class BadUF():
  # no path compression. no depth stroage.
  def __init__(self):
    self.parent = []
  def find(self,i):
    p = self.parent[i]
    while p != self.parent[p]: # walrus?
      p = self.parent[p]
    return p
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    return x
  def set_size(self,n):
    while len(self.parent) < n:
      self.makeset()
    return
  def union(self,i,j):
    i = self.find(i)
    j = self.find(j)
    self.parent[i] = j
    return j


class DB:
  uf: BadUF
  tables: Dict[str,Any]
  merge: Dict[str,]
  default:Dict[str,]

  def set_(self, tablename, key, value):
    table = self.tables[tablename]
    if key in table:
      table[key] = self.merge[tablename](table[key], value)
    else:
      table[key] = value
  def union(self, x,y):
    return self.uf.union(x,y)
  def define(self, tablename, key):
    table = self.tables[tablename]
    if key in table:
      return table[key]
    else:
      v = self[tablename].default(key)
      table[key] = v
      return v
  def __get__(self, k):
    tablename, *k = k
    return self.tables[tablename][k]
  def rebuild(self):
    uf = self.uf
    for tablename, table in self.tables.items():
      temp = {}
      for k,v in table.items():
        temp[map(uf.find, k)] = uf.find(v)
      # Is this mutation wise? maybe not.
      self.tables[table] = temp
        
# struct of arrays ve array of structs




# merge dicts have their own definition of union
```


```python
from typing import TypeVar, Generic, Callable
K = TypeVar('K')
V = TypeVar('V')

# merge dict is a very natural extension of python's
# built in defauldict
# can capture uf in closures.

# man python typing is goofy
class MergeDict(Generic[K, V]):
  table: dict[K,V]
  default: Callable[K,V]
  merge: Callable[[K,K],V]

  def __init__(self, default=None, merge=None):
    self.table = {}
    self.default = default
    self.merge = merge
  def extend(self, items):
    for k,v in items:
        self[k] = v
  def items(self):
    yield from self.table.items()

  def keys(self):
    yield from self.table.keys()

  def __setitem__(self, key, value):
    if key in self.table:
      if self.merge != None:
        self.table[key] = self.merge(self.table[key], value)
      else:
        if self.table[key] != value:
            raise KeyError
    else:
      self.table[key] = value
    
  def __getitem__(self,key):
  # Is get memoized or not?
    if key in self.table:
      return self.table[key]
    else:
      if self.default != None:
        v = self.default(key)
        self.table[key] = v
        return v 
      else:
        raise KeyError
  def __repr__(self):
    return repr(self.table)


def UnitRelation():
    return MergeDict(merge = lambda x,y: ())

path = UnitRelation()
edge = UnitRelation()


edge[(1,2)] = ()
edge[(2,3)] = ()


def run(edge,path):
    path.extend([((x,y), ()) for x,y in edge.keys()]) # path(x,y) :- edge(x,y).
    path.extend([((x,z), ()) for x,y in edge.keys() for y1,z in path.keys() if y == y1]) # path(x,z) :- edge(x,y),path(y,z).

for i in range(10):
    run(edge,path)
print(edge)
print(path)


path = MergeDict(merge=lambda x,y:min(x,y))
edge = MergeDict(merge=lambda x,y:min(x,y))

edge[(1,2)] = 10
edge[(2,3)] = 3
edge[(1,3)] = 20


def run(edge,path):
    path.extend([((x,y), cost) for (x,y),cost in edge.items()]) # path(x,y) :- edge(x,y).
    path.extend([((x,z), c1 + c2) for (x,y),c1 in edge.items() for (y1,z),c2 in path.items() if y == y1]) # path(x,z) :- edge(x,y),path(y,z).

for i in range(10):
    run(edge,path)
print(edge)
print(path)
```

- The edges of comprenhensions start creaking. They aren't really overloadable enough
- flattening `add[(add(x,y),z)`. This is tablized adt datalog, not persay egglog
- 

```python

class Var():
    name:str
    def __call__(self, k):
        return {self.name: k}
class MergeDict():
    def __call__(self,*args):
        for ks,v in self.items():            
            for k, arg in zip(ks,args):
                yield from arg(k) kind of
```
Modelling as
type gen = (subst, outval) -> list subst 
This is basically top down ematching search.
I guess we could use [] for bottom up, and () for top down... that's not horrible.
Could literally try to do embedded gj. The idea being it is in some sense simpler.

Hmm. It's kind of an overloading of how subst dicts are merged... We could do normalization there?


Flattening is related to compiling to assembly. Very related. Hmm.
```ocaml
type expr = loc * bindings
let foo (a, froms, wheres) = 
  "freshrow.res", (foo,"freshrow") :: ,  ("freshrow.x = " ^ a) :: wheres   
```

It's a writer monad for froms and wheres. We should go top down to make biding pattern variables easy.

```python
counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def foo(a):
  def res():
    (rid, froms, wheres) = a()
    row = freshrow()
    return (f"{row}.rowid",  [f"foo as {row}"] + froms, [f"{rid} = {row}.a"]+ wheres)
  return res

def x():
  row = freshrow()
  return (row + ".rowid" ,[f"x AS {row}"], [])

def func(f):
  def res(*args):
    def res1():
      args = [arg() for arg in args]
      rids, froms, wheres = zip(*args)
      row = freshrow()
      (f"{row}.rowid",  [f"{f} as {row}"] + froms, [f"{rid} = {row}.arg{n}" for n,rid in enumerate(rids)] + wheres)
    return res1
  return res

print(foo(foo(x))())

```
How do we deal with variables? It's like datalog problems but more so.
`from foo as row, (select row.a) as x, ` does this work?
analog of turn `let x = row.a` into `for x in [row.a]` where select plays role of []. Not really that much less complex. You still need to maintani a compile time env with a bool instead of a column.


What about GJ. GJ is actually pretty simple.

Trie. `(k, )` `dict[dict]
[None] = data held
```python
def insert(trie, k, v):
  node = trie
  for n in k:
    tnode = node.get(n)  
    if tnode == None:
      tnode = {}
      node[n] = tnode
    node = tnode
  node[None] = v

def lookup(trie, k):
  node = trie
  for n in k:
    node = node.get(n)
    if node == None:
      return None  
  return node.get(None)

t1 = {}
insert(t1,"aaa", "fred")
insert(t1,"aab", "larry")
insert(t1,"aac", "larry")
insert(t1,"ac", "gary")
print(lookup(t1, "aa"))
print(t1)

def of_keys(keys):
  t = {}
  for k in keys:
    insert(t,k, ())
  return t
print(of_keys([(1,2), (3,4), (1,4)]))

def rel2(table):
  empty_row = ()
  def res(nx,ny): # take in the order of where will appear?
    return of_keys([ (empty_row[nx] := row[0])[ny] := row[n1]   for row in table]) # this is not valid python
  # ok. We Have to address compression.
  # Then the semantics is just sets over all variables in play in a particular order.
  # path |= forall(lambda (x,y,z,w): (& & & &).proj(x,y))
```

```sql
-- canonicalize
insert into mytab select root(a), root(b), root(c) from mytab on conflict set c = union(c, excluded.c)
```


In the experiment, I tried internalizing the union find into sql. Maybe it is simpler not to

Wasm based union find? Would that be fun?
```python
class BadUF():
  # no path compression. no depth stroage.
  def __init__(self):
    self.parent = []
  def find(self,i):
    p = self.parent[i]
    while p != self.parent[p]: # walrus?
      p = self.parent[p]
    return p
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    return x
  def set_size(self,n):
    while len(self.parent) < n:
      self.makeset()
    return
  def union(self,i,j):
    i = self.find(i)
    j = self.find(j)
    self.parent[i] = j
    return j


import sqlite3
uf = UF()
conn = sqlite3.connect(":memory:")
cur = conn.cursor()
conn.create_function("_union", 2, lambda (x,y): uf.union(x,y))
conn.create_function("_find", 1, lambda (x): uf.find(x))

cur.execute("create table add(a,b, unique fd (a,b))")
cur.execute("insert into add select _root(a), _root(b) from add on conflict fd update set rowid = union(rowid, excluded.rowid)") 
cur.execute("insert into add select a,b from add as l, add as r where _root(l.rowid) = _root(r.rowid) ON CONFLICT ")


```

## Extraction as datalog
```souffle

.decl add0(x:number, y : number, z : number)
.decl num(x:number, y : number)
.decl add(x:number, y : number, z : number)

.type AExpr = Add {x : AExpr, y : AExpr} | Num {n : number}

.input add0(filename="../subsumpt/add0.facts")

// This is because of my sloppy previous encoding
num(i, i) :- add0(i, _, _), ! add0(_,_,i).
num(i, i) :- add0(_, i, _), ! add0(_,_,i).

.decl depth(id : number, d : unsigned) 
depth(i, 0) :- num(_,i).
depth(z, max(dx,dy) + 1) :- add0(x,y,z), depth(x,dx), depth(y,dy).

// min lattice
depth(x,d) <= depth(x, d1) :- d1 <= d.

// .output depth(IO=stdout)
add(x,y,z) :- (num(_, x) ; add(_,_,x)), (num(_, y) ; add(_,_,y)),
              d = min d1 : {add0(x,y,z1), depth(z1, d1)},  depth(z,d), add0(x,y,z).

.decl tree(id: number, e : AExpr) choice-domain id
tree(j, $Num(i)) :- num(i, j).
tree(z, $Add(tx,ty)) :- tree(x,tx), tree(y,ty), add(x,y,z).

.output tree(IO=stdout)

```



# Misc

https://www.mbid.me/eqlog-algorithm/ Martin E. Bidlingmaier basically developed a system similar or identical to egglog on completely parallel lines. Maybe that means it's a good/natural idea?


## Modulo theories

Grobner bases are ~ knuth bendix method. Completion algorithm.
Modulo some a priori known equations.
Do grobner as a preprocessing step. Akin to running knuth bendix as preprocesing step.
= polynomials as objects modulo grobner. This is like datalog modulo term rewriting.


relations vs objects vs rules.
first class rules (rules as objects). first class sets (relations as objects). both blur the lines.
rules as relations?
(<=) : R -> R -> Bool
vs (<=) : R^n -> Bool
are pretty different.

first class rules ~ contexts. Kind of like sequent is first class inference rule.

Difference logic theory = theory of shortest path

galois connction between octagons and polytopes. Can we compute the relaxation of a polytope? It is a bunch of linear programming query. Can we do better?

maximize xi - xj s.t. polytyop
best objective c is then a bound. xi-xj <= c

likewise for intervals. Or any set of hyperplanes.

linear objective subject to difference constraints? probably.
Best interior octagon? Usually get a bunch of feasible points and construct convex hull. Can I build an octagon out of points? What are "best" points. Well, I could construct a polyhedra out of the points.

## Propagators
The whole database as a cell
Each relation as a cell





Context
R(x+y)
R may have arbtrary extent.
During term rewrting, we can track it. In egraphs we can't (unless I build it there)

```
let rewrite ctx t = 
```

## AC

Let's dial back to terms. What is wrong with using unordered vertices as "AC-nodes". Relational matching ought to basically work.

```
a \
b--ac - + - 
c /
```

```sql
create table plus(ac unique); -- functional to rowid
create table lit(n unique); -- functional to rowid
create table ac(in_,out_); -- a many to many relationship. A special table with special rebuild. Multiset semantics because can have terms like "a" + "a" + "a"
-- construct a + b + c as 
-- lit a  \
-- lit b -- ac - plus - 
-- lit c  /
insert into lit values ("a"), ("b"), ("c");--select * from generate_series(0,3);
insert into ac select lit.rowid,0 from lit;

--values (1,0), (2,0), (3,0);
insert into plus values (0);

select *, rowid from plus;
select *, rowid from ac;
-- This query is doing AC-matching (_ + ?x + ?y)
-- (?x + ?y) coule mean partition the AC set.
-- or (?x + ?y) could mean ony match sets of cardinality 2.
-- Depends if vars can bind to sets or
-- plus( { ?x , ?y }   ) vs  plus( { ?x , ?y, ... }) vs plus( ?x union ?y) 

select * from plus, ac as n1, ac as n2, lit as x1, lit as x2
 where n1.out_ = plus.ac and n2.out_ = plus.ac 
 and n1.rowid != n2.rowid -- multiset but don't match same term twice
 and n1.in_ = x1.rowid and n2.in_ = x2.rowid 
 and n1.in_ < n2.in_  -- break permutation symmetry
 ;
-- If I want to match (?x + ?y + ?z)... no this is impossible. Like what do you mean? Ok. Maybe in the plus case this is possible. Even a single term can be artbirarily in real valued plus.
-- Ok but AC is more dsicrete and combinatorial. There is the empty set. Maybe by vonvention you denote whether you want to allow vars to attach to the empty set.
-- I should always be allowed to bind y and z to null also.

--select * from ac 
-- groupby ac.j
```


### slog

```python
from lark import Lark, Transformer, v_args
grammar = '''
//prog : rule*
rule : head ":-" body  "."

body: body_fact ("," body_fact)*
head : NAME "{"  [ head_field ("," head_field)* ]  "}"
head_field : NAME ":" expr
body_fact :  
  | expr "=" expr -> eq
  | NAME "@" NAME -> from_

// op:
expr : NUMBER -> number
     | STRING -> string
     | NAME "." NAME -> field

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
'''

@v_args(inline=True)
class RuleTransformer(Transformer):
  froms = []
  wheres = []
  def field(self, row, field):
    return "{row}.{field}"
  def string(self,s):
    return '"' + s[1] + '"'
  def number(self,n):
    return n[1]
  def from_(self, table, row):
    self.froms.append(f"{table} AS {row}")
  def eq(self, lhs, rhs):
    wheres.append(f"{lhs} = {rhs}")
  def body(self,*args):
    wheres = " AND ".join(self.wheres)
    froms = ", ".join(self.froms)
    return f"FROM {froms} WHERE {wheres}"
  def head_field(self, key, val):
    return f"{val} AS {key}"
  def head(self,table, *fields):
    selects = ", ".join(fields)
    return f"INSERT INTO OR IGNORE {table} SELECT {selects}"
  def rule(self, head, body):
    self.froms = []
    self.wheres = []
    return  head + " " + body


parser = Lark(grammar, start="rule", parser="lalr", transformer=RuleTransformer())
print(parser.parse("path { x : e.x, y : p.y} :- edge @ e, path @ p, e.y = p.x"))
```

```python
from lark import Lark, Transformer, v_args
from dataclasses import dataclass
grammar = '''
//prog : rule*
rule : head ":-" body  "."

body: body_fact ("," body_fact)*
head : NAME "("  [ term ("," term)* ]  ")"
body_fact :  
  | term  "=" term -> eq
  | NAME "("  [ term ("," term)* ]  ")" -> rel

term : NUMBER -> number
     | STRING -> string
     | NAME -> var
     | NAME "("  [ term ("," term)* ]  ")" -> func

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
'''

#parser = Lark(grammar, start="prog")
#print(parser.parse("foo(3,4).  edge(1,2). edge(\"a\"). path(x,z) :- edge(x,y), path(y,z).").pretty())

@dataclass(frozen=True, eq=True)
class Var():
  name:str

@v_args(inline=True)
class RuleTransformer(Transformer):
  env = {} # variable env 
  froms = [] 
  wheres = []
  counter = 0
  def fresh(self, n):
    self.counter += 1
    return f"{n}{self.counter}"
  def var(self,name):
    print(name)
    return Var(name)
  def string(self,s):
    return '"' + s[1] + '"'
  def number(self,n):
    return n[1]

  def rel(self,table,*args):
    self.func(table,*args)
  def eq(self, x, y):
    if isinstance(y, Var):
      y = self.env[y]
    if isinstance(x,Var):
        if x in self.env:
          self.wheres.append(f"{self.env[x]} = {y}")
        else:
          self.env[x] = y
    else:  
      self.wheres.append(f"{x} = {y}")
  def func(self, table, *args):
    row = self.fresh(table)
    self.froms.append(f"{table} AS {row}")
    for n, arg in enumerate(args):
      if isinstance(arg,Var):
        if arg in self.env:
          self.wheres.append(f"{self.env[arg]} = {row}.x{n}")
        else:
          self.env[arg] = f"{row}.x{n}"
      else:  
        self.wheres.append(f"{arg} = {row}.x{n}")
    return f"{row}.rowid"
  def body(self,*args):
    wheres = " AND ".join(self.wheres)
    froms = ", ".join(self.froms)
    return f"FROM {froms} WHERE {wheres}"
  def head(self,table, *args):
    # delay. Is this dumb? It's gnna bite me
    def res():
      print(self.env)
      selects = []
      for arg in args:
        if isinstance(arg,Var):
          selects.append(self.env[arg])
        else:
          selects.append(arg)
      selects = ", ".join(selects)
      return f"INSERT INTO OR IGNORE {table} SELECT {selects}"
    return res
  def rule(self, head, body):
    res = head() + " " + body
    self.env = {}
    self.froms = []
    self.wheres = []
    self.counter = 0
    return res


parser = Lark(grammar, start="rule", parser="lalr", transformer=RuleTransformer())
print(parser.parse("path(x,z) :- edge(x,y), path(y,z)."))
print(parser.parse("path(x,z) :- edge(x,\"y\"), path(y,z)."))
print(parser.parse("path(x,p(z)) :- add(mul(x,y), div(y,z)), y = x."))
```
Rename columns to x0-xn.
Multiheaded rules.
Accumulating semantics for multihead is kind of easy. Weird though.
purify the wheres
add root and union everywhere.
((d :- c)  /\ b) :- a
d :- a,b,c
b :- a

```sql
create table foo(rowid INTEGER PRIMARY KEY AUTOINCREMENT, a );
insert into foo (a) values (1), (2);
create table bar(rowid INTEGER PRIMARY KEY AUTOINCREMENT, a );
insert into bar (a) values (1), (2);

select * from foo;
select * from bar;
select * from sqlite_sequence;
```


Using `default` instead of rowid
```sql
create table foo(a,b,res default -1);
--describe foo;
insert into foo (a,b) values (1 ,2);
select * from foo;
```

```python

import sqlite3
counter = 0
def fresh():
  global counter
  counter += 1
  return counter
conn = sqlite3.connect(":memory:")
cur = conn.cursor()
conn.create_function("fresh", 0, fresh)
cur.execute("create table foo(a,b,c default (fresh()), unique (a,b))")
cur.execute("insert or ignore into foo (a,b) values (2,3), (3,4), (2,3), (4,5)")
cur.execute("select * from foo")
print(cur.fetchall())
# hmm. it calls fresh even on ignore. Don't like that
```

Too many fresh isn't persay a problem but it is kind of disappointing
I guess we could use a trigger after insert

```sql
create table foo(a,b,res default -1);
--describe foo;
create trigger after insert 
insert into foo (a,b) values (1 ,2);
select * from foo;
```


```
counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def var(x):
  def res(loc):
    return {x : loc}, [] , []
  return res


def foo(a):
  def res(loc):
    row = freshrow()
    (env, froms, wheres) = a(f"{row}.a")
    return (env,  [f"foo as {row}"] + froms, [f"{loc} = {row}.rowid"] + wheres)
  return res

def merge(env1,env2):
  if len(env1) > len(env2):
    env1, env2 = env2, env1
  wheres = [ f"{v} = {env2[k]}" for k,v in env1.items() if k in env2 ] # join
  return {**env1, **env2}, wheres

def func(table):
  def res(*args):
    def res1(loc):
      row = freshrow()
      if loc != None:
        wheres = [f"{loc} = {row}.rowid"]
      else:
        wheres = []
      froms = [f"{table} as {row}"]
      env = {}
      for n, arg in enumerate(args):
        e, f, w = arg(f"{row}.x{n}")
        wheres += w
        froms += f
        env, w2 =  merge(env,e)
        wheres += w2
      return env, froms, wheres
    return res1
  return res

plus = func("plus")
x = var("x")
print(plus(x,x)(None)) # This is ugly. I should also be returning the row.
```
Ugh, so I need to pass something down the tree so the vars can do something, or I can make retvals either var or not. I could make the env have concat merge semantics and collect up at the end. That's what I did in snakelog

a.1.1 = b.1.1, a.h =

plus @ a, a.x, a.x

Ok, so I need to build a datalog first. It sucks too much to

```
      #args1 = [arg(f"{row}.x{n}") for n, arg in enumerate(args)]
      #envs, froms, wheres = map(list, zip(*args1))
      #print(froms, wheres)
      #env1 = {}
      #wheres.append(f"{loc} = {row}.rowid")
      ##froms.append(f"{f} as {row}")
      #for env in envs:
      #  env1, w = merge(env, env1)
      #  wheres += w

counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def foo(a):
  def res():
    (rid, froms, wheres) = a()
    row = freshrow()
    return (f"{row}.rowid",  [f"foo as {row}"] + froms, [f"{rid} = {row}.a"]+ wheres)
  return res

def x():
  row = freshrow()
  return (row + ".rowid" ,[f"x AS {row}"], [])

def func(f):
  def res(*args):
    def res1():
      args = [arg() for arg in args]
      rids, froms, wheres = zip(*args)
      row = freshrow()
      (f"{row}.rowid",  [f"{f} as {row}"] + froms, [f"{rid} = {row}.arg{n}" for n,rid in enumerate(rids)] + wheres)
    return res1
  return res

print(foo(foo(x))())
```

Wait, would the join form be cleaner?
JOIN foo, a on a.rowid = foo.
Meh. Kind of. 


# Partial Application
`call` is super useful
The applicative encoding
We can do it manually to see how useful it is
Lambda lifting for binders

Monads / algerbaic effects
```egglog

(function cont1/0)
(define prog
  (set_ "x" 1 cont1/0)
)

(function cont1/1)
(rewrite (apply cont1/0 x) (cont1/1 x))
(rewrite (cont1 w)

)

; the obvious thing
; what is the issue if any?
(define prog
(seq 
  (set "x" 1)
  (set "y" 2)
))

; semantics of set is state -> state function
; seq is composition. Fine.
; var "x" is state -> int
; 


```

## RVSDG
We want as much to be dataflow as possible. That is where egraph shines

An interstig design angle is to disallow varable capture.
Is this even interesting? C doesn't really have a notion of variable capture in function calls. But mutation itself is a form of let capture
Allow multi-arity. Disallow
Everything must be 



```
(datatype 1->1)
(datatype 2->1)
(datatype 2->2)

(datatype Func)
(datatype Expr)
(datatype Expr* (Cons Expr Expr*) (Nil))

(datatype Tup1)
(datatype Tup2 (Pair Expr Expr))


(function func-1-inputs-1-outputs (Expr) RVSDG)
(function func-1-inputs-2-outputs (Expr Expr) RVSDG)
(function func-2 (Expr Expr) RVSDG)
(function func (Expr*) Func)
(function call* (Func Expr*) Expr*) ; multiple input ultiple output
(function call1)
(function call2 (Func Expr Expr) Expr*)
(rewrite (call2 f e1 e2) (call f (Cons e1 (Cons e2 (Nil)))))
;(function call (Func Env) Expr)

(function get (i64) Expr)

(define neg (func-1-inputs-1-outputs (* -1 get-0)))
; specializing call to neg to get it in one shot.
(rewrite (call neg (Cons e (Nil))) (* -1 e))

(func-2-inputs-1-outputs (+ get-0 (get-0 (call ?neg get-1))))


(function call1 (RVSDG Expr) Expr)
(function subst1 (Expr Expr) Expr)

(rewrite (call1 (func-1-input1-1-output1 e) e1) (subst1 e e1))
(rewrite (subst1 (* a b) e) (* (subst1 a e) (subst1 b e)))
(rewrite (subst1 (get 0) e)) e)
(rewrite (subst1))
(rewrite (subst (call1 f x) e) (call1 f (subst1 x e))) ; we don't substitue into the function. Only explicit capture allowed

; hmm   maybe not recursing into the definition is what makes this different

; no capture is allowed. Anything body needs is explicitly passed (lambda lifting)
; But in exchance we have multi-arity as a primitive.
; slash we lift everything to work over lists? Whch is a curious form of env.
; The syntax of the language let's us restrict the context.

(function call2 (RVSDG Expr Expr) Expr)


(rewrite (= f  ... (call f)) (loop ))
```