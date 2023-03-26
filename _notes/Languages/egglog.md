
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