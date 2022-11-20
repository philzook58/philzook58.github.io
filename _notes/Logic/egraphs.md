---
layout: post
title: E-graphs
---

- [E-Graph](#e-graph)
- [My E-Graph Blog Posts](#my-e-graph-blog-posts)
- [Union Finds](#union-finds)
  - [Reference union finds](#reference-union-finds)
  - [Union find arrays and ints](#union-find-arrays-and-ints)
  - [Variations](#variations)
  - [Applications](#applications)
- [Hash Cons](#hash-cons)
- [E-matching](#e-matching)
- [Equality Saturation](#equality-saturation)
- [Proof Production](#proof-production)
- [E Graph Tactics](#e-graph-tactics)
- [Applications](#applications-1)
- [PEG Program Expression Graphs](#peg-program-expression-graphs)
  - [Tree Automata](#tree-automata)
- [Egglog](#egglog)
  - [Extraction as datalog](#extraction-as-datalog)
  - [First class sets](#first-class-sets)
  - [GATs](#gats)
- [Lambda Encoding](#lambda-encoding)
- [Contextual EGraphs](#contextual-egraphs)
- [CHR egraphs](#chr-egraphs)
- [Misc](#misc)



# E-Graph
What is an e-graph?

What is a summer's day? A rainbow?

E-graphs are a data structure that efficiently holds terms and equalities between terms.

It is useful for algebraic simplification, program transformations and proving equivalences in equational reasoning

Destructive term rewriting can be used in 



# My E-Graph Blog Posts
- [E-graphs in Julia (Part I)](https://www.philipzucker.com/egraph-1/)
- [E-Graph Pattern Matching (Part II)](https://www.philipzucker.com/egraph-2/)
- [Progress on Automated Reasoning for Catlab with Metatheory.jl Egraphs](https://www.philipzucker.com/metatheory-progress/)
- [Rewriting Monoidal Categories in the Browser with Egg](https://www.philipzucker.com/rust-category/)
- [Union Find Dicts: Dictionaries Keyed on Equivalence Classes](https://www.philipzucker.com/union-find-dict/)
- [A Simplified E-graph Implementation](https://www.philipzucker.com/a-simplified-egraph/)
- [Partial Evaluation of a Pattern Matcher for E-graphs](https://www.philipzucker.com/staging-patterns/)
- [Encoding E-graphs to Souffle Datalog](https://www.philipzucker.com/egraph-datalog/)
- [Egglog: a Prolog Syntax for Egg, Checkpoint I](https://www.philipzucker.com/egglog-checkpoint/)
- [JuliaCon 2021 Talk on Metatheory.jl and Snippets From the Cutting Room Floor](https://www.philipzucker.com/juliacon-talk/)
- [Egglog 2: Automatically Proving the Pullback of a Monic is Monic](https://www.philipzucker.com/egglog2-monic/)
- [Egglog Examples: Pullbacks, SKI, Lists, and Arithmetic](https://www.philipzucker.com/egglog-3/)
- [Naive E-graph Rewriting in Souffle Datalog](https://www.philipzucker.com/datalog-egraph-deux/)
- [A Questionable Idea: Hacking findParent into Souffle with User Defined Functors](https://www.philipzucker.com/souffle-functor-hack/)
- [Embedding E-graph Rewriting and Egglog in Constraint Handling Rules](https://www.philipzucker.com/egraph-chr/)


# Union Finds
Union finds are also called disjoint set datastructures.

You can take a set an group it into equivalence classes. One place this is useful is finding the connected components of a graph.

There are different styles of union finds and both make one thing in different and interesting ways.

At a level of fairly high abstraction, a union find is a contracting map. You iterate the map to a fixed point. Each equivalence class is the basin of a fixed point.

See coq post https://www.philipzucker.com/simple-coq-union-find/

How essential is path compression? It is the thing that gets you that inverse ackermann complexity. It requires mutation so far as I know.

Another way of constructing disjoint sets is to note that preimages of any map form disjoint sets.

Is the inverse acckerman complxity a requirement for anything I might call a union find? I don't think so.

Union finds can be fully normalized to flatness.


## Reference union finds
A chain of pointers that lead up to a root. Often the root is a pointer to itself.

```python
# no path compression
# `is` is python reference equality
class BadUF():
  def __init__(self):
    self.parent = self
  def find(self):
    x = self
    while x.parent is not x:
      x = x.parent
    return x
  def union(self,rhs):
    p = self.find()
    p2 = rhs.find()
    p.parent = p2
    return p2

x = BadUF()
y = BadUF()
z = BadUF()

x.union(y)
print(x.find() is y.find())
print(x.find() is z.find())

```

## Union find arrays and ints
What is a pointer but an index? What is an index but a pointer?
In some sense your ram is just a giant array that you hand out. And vice versa you can build the analog of pointer based algorithms by using an array as ram.

In some languages you don't have access to raw pointers easily. The array style also makes it easier/more natural to copy union finds. This style also makes it more clear how to talk about the union find in a purely functional way.

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

uf = BadUF()
x = uf.makeset()
y = uf.makeset()
z = uf.makeset()

uf.union(x,y)
assert(uf.find(x) == uf.find(y))
assert(uf.find(x) != uf.find(z))
```

## Variations
[persistent union find](https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf)

[Union Find Dicts: Dictionaries Keyed on Equivalence Classes](https://www.philipzucker.com/union-find-dict/). You can make a dict from union find to lattices. It needs to know how to merge stuff in the range. Relatedly, you could also have union find keyed on union find. 

Union find with group elements on edges. [kmett talk](https://youtu.be/KxeHGcbh-4c?t=1254). Yihong points out <http://poj.org/problem?id=2492> as a competitive programming exercise that can use this. "generalized union find" mentioned in CHR book

Scoped Union find

Colored Union find


[Data Structures and Algorithms for
Disjoint Set Union Problem](https://core.ac.uk/download/pdf/161439519.pdf) "deunions" and backtracking. hmm. 1989

[concurrent union find](https://link.springer.com/article/10.1007/s00446-020-00388-x)

## Applications
connected components of graph

reducibility of loops
[Testing Flow Graph Reducibility  - tarjan]()

https://www.cs.princeton.edu/courses/archive/spring07/cos226/lectures/01union-find.pdf
"
! Network connectivity.
! Percolation.
! Image processing.
! Least common ancestor.
! Equivalence of finite state automata.
! Hinley-Milner polymorphic type inference.
! Kruskal's minimum spanning tree algorithm.
! Games (Go, Hex)
! Compiling equivalence statements in Fortran
"
quick-find vs quick-union

percolation. estimate percolation via monte carlo. quick test of connectivity between conducting edges. That's neat.

https://en.wikipedia.org/wiki/Tarjan%27s_off-line_lowest_common_ancestors_algorithm



value numbering

# Hash Cons






# E-matching
Searching over the egraph. It is both simple and complex.
It is a brother of pattern matching. The branching factor of each eclass means that it is more nondeterministic than tree pattern matching.
It is similar to database search. Relational E-matching. 

Consider
- pattern matching at the root of a single tree
- pattern matching at ever node in a tree 
- pattern matching over a database of trees (forest)

- pattern matching over a DAG
- pattern matching over a graph (hard in principle (subgraph isomorphism), in practice maybe not that bad)

Simplify
[de Moura and Bjorner](https://leodemoura.github.io/files/ematching.pdf)
Their VM is quire similar to WAM. 


# Equality Saturation

# Proof Production
[Proof producing congruence closure](https://www.cs.upc.edu/~roberto/papers/rta05.pdf)

A union find is a data structure useful for finding connected components in a graph. The "proof" that two vertices are connected is the path between them. We need to maintain an incremental spanning tree of some kind.

We also need to record "reasons" why each edge got added. Reasons may be rewrite rules, or congruence closure.

A proof might be:
- a term rewriting sequence
- a grounded confluent terminating term rewriting system
- The ground equalities to assert to an egraph that are enough to push the proof through with no egraph rewrite rules
  
See also Z3's proof production


# E Graph Tactics

- Samuel Gruetter and Dustin Jamner - Coq. `congruence` tactic is an egraph. Too slow? [code of coq tactic](https://github.com/coq/coq/tree/master/plugins/cc). [Deciding Equality in the Constructor Theory](https://dl.acm.org/doi/10.5555/1789277.1789283)
- Lean? [lean tatic](https://pldi22.sigplan.org/details/egraphs-2022-papers/6/Equality-Saturation-as-a-Tactic-for-Proof-Assistants)

[de moura selsam](https://leanprover.github.io/papers/congr.pdf)

```coq
Axiom i64 : Type.
Axiom add : i64 -> i64 -> i64.

Axioms add_comm : forall x y, add x y = add y x.
Axioms add_assoc : forall x y z, add (add x y) z = add x (add y z).

Axioms a b c d : i64.
Axiom num : nat -> i64.

Definition add_rule_set := (add_comm , add_assoc).

Fixpoint addl (n : nat) : i64 :=
     match n with
     | O => num 0
     | S n => add (num (S n)) (addl n)
     end.
Fixpoint addr (n : nat) : i64 :=
    match n with
    | O => num 0
    | S n => add (addr n) (num (S n))
    end.

Global Hint Rewrite add_assoc : base0. (* add_comm is no good. nonterminating as a rewrite*)
Goal addl 10 = addr 10. simpl. 
(* congruence with (add_comm (num 0) (num 1)). autorewrite with base0.  *)
(* pose add_comm. pose add_assoc. *)
pose add_rule_set as rs. destruct rs.
congruence. Qed.
```

# Applications
- Denali https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf
- Herbie - improve accuracy of floating point expressions
- [Szalinksi](https://github.com/uwplse/szalinski) shrink 3d cad programs
- [Vectorization for Digital Signal Processors via Equality Saturation](https://asplos-conference.org/abstracts/asplos21-paper142-extended_abstract.pdf)
- [SPORES](https://arxiv.org/abs/2002.07951)


- [High-performance symbolic-numerics via multiple dispatch](https://arxiv.org/abs/2105.03949)
- 
# PEG Program Expression Graphs

<https://ztatlock.net/pubs/2009-popl-equality-saturation-optimizations-egraphs.pdf>
https://rosstate.org/publications/eqsat/

Control flow graph (CFG) is just like, a thing. Its denotational semantics are a bit confused. 

Egraphs like talking about functions. How to encode something cfg like into functions?

Dataflow graphs are basically just a DAG functional representation. So that intra block dataflow is not really a problem.

Being in SSA make one close to purely functional. YOu never assign to the sam name twice (although let binding shadowing could also model this purely functionally).

SSA Phi nodes are slightly bizarre. Gated Phi nodes make explicit the condition on which the merging happens. This makes them more like a purely functional if-then-else.

One can consider using streams as a functional representation of loop behavior. There are operations like tail, head, other on the stream.


PEGs have some clues on how to treat summation symbols  $\Sigma$ in an egraph. Surely you can write a sum function asa CFG. Partial Sums / indefinite integrals rather than closed sum, definite integrals.

Is there a relationship between pegs and timely dataflow?

You only Grep once by koppel - uses PEG-like representation for semantic code search.

[representing loops within egg](https://github.com/egraphs-good/egg/discussions/106)

RVSDG
https://github.com/jameysharp/optir/

Loops in egraphs and Landin's knot.

[Equality Saturation: a New Approach to Optimization](https://cseweb.ucsd.edu/~lerner/papers/popl09.pdf)

Quiche [quiche](https://github.com/riswords/quiche) python egraph for manipulating python AST
## Tree Automata

https://github.com/ondrik/libvata
[Tree Automata Techniques and Applications](https://jacquema.gitlabpages.inria.fr/files/tata.pdf)


[E-Graphs, VSAs, and Tree Automata: a Rosetta Stone](https://remy.wang/reports/dfta.pdf) [slides](https://docs.google.com/presentation/d/1oDNmzxJpsdLE51lmybcfzzzv4jRLDdrVpmMhMpFEoFk/edit?usp=sharing) [merge only rules](https://gist.github.com/remysucre/1788cf0153d7db240e751fb698f74d99)


https://en.wikipedia.org/wiki/Tree_automaton

# Egglog


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


## First class sets

## GATs


```python
# I should try souffle using subsumption UF. Maybe it'll work now?

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

uf = BadUF()
uf.set_size(5)


'''
add = {(0,1,2), (1,0,3), (0,1,4)} # x + y, y + x
while True:
  newadd = {(y,x,xy) for (x,y,xy) in add if (y,x,xy) not in add}
  if newadd.issubset(add):
    break
  add.update(newadd)
  # rebuild
  while True:
    # normalize
    add = {(uf.find(x), uf.find(y), uf.find(xy)) for (x,y,xy) in add}
    # congruence close
    fresh = { (x,y,uf.union(xy,xy1))  for (x,y,xy) in add for (x1,y1,xy1) in add if x == x1 and y == y1 and xy != xy1}
    if len(fresh) == 0:
      break
print(add)
'''

add = {(0,1,2), (1,0,3), (0,1,4)} # x + y, y + x
while True:
  newadd = {(y,x,xy) for (x,y,xy) in add if (y,x,xy) not in add}
  if newadd.issubset(add):
    break
  add.update(newadd)
  # rebuild
  while True:
    # normalize
    add = {(uf.find(x), uf.find(y), uf.find(xy)) for (x,y,xy) in add}
    addind = {(x,y) : xy for (x,y,xy) in add}
    # congruence close
    fresh = [uf.union(xy,addind[(x,y)]) for (x,y,xy) in add if addind[(x,y)] != xy]
    if len(fresh) == 0:
      break
print(add)

'''
add = {(0,1) : 2, (1,0) : 3 , (0,1) : 4} # x + y, y + x
while True:
  newadd = {(y,x,xy) for (x,y),xy in add.items() if (y,x) not in add or add[(y,x)] != xy}
  if newadd.issubset(add):
    break
  add.update(newadd)
  # rebuild
  while True:
    # normalize
    add = {(uf.find(x), uf.find(y), uf.find(xy)) for (x,y,xy) in add}
    # congruence close
    fresh = { (x,y,uf.union(xy,xy1))  for (x,y,xy) in add for (x1,y1,xy1) in add if x == x1 and y == y1 and xy != xy1}
    if len(fresh) == 0:
      break
'''
print(add)

```



# Lambda Encoding
Might work:
- Combinators. SKI or categorical. Many projects are doing something like this. Relational Algebra or matrix algebra are the same thing.
- Succ lifting. [pavel](https://pavpanchekha.com/blog/egg-bindings.html) [oleg](https://okmij.org/ftp/tagless-final/ski.pdf). Do de bruijn but let Succ float out of Var. Let's you do de bruijn index lifting as local rewrite rule. Succ has interpretation as a higher order function.

Arguable:
- Co de-bruijn. Hash Cons modulo alpha. Mcbride's Do Be doo be doo. Doesn't seem to work. Correlated rewrites required
- Graph compilation. Optimal graph reduction


# Contextual EGraphs
No one know what this means. Everyone wants it. 

[colored egraphs](https://docs.google.com/presentation/d/16fpJiVfAaNasCp3rgPusiRl7GD-18fq6aMBkDnVfsco/edit?usp=sharing)
[colored egg](https://github.com/eytans/egg)

Perhaps related to backtracking


# CHR egraphs


```prolog
:- use_module(library(chr)).
:- initialization(main,main).
% hmm are these annotations ok?
:- chr_constraint make(+int), find(+int,-), root(+int,+int), union(+int,+int), 
                  link(+int,+int), pto(+int,+int), counter(+int).

make(A), counter(N) <=> N = A, N1 is N + 1, counter(N1), root(A,0).
union(A,B) <=> find(A,X), find(B,Y), link(X,Y).
pto(A, B), find(A,X) <=> find(B,X), pto(A,X).
root(A,_) \ find(A,X) <=> X=A.
link(A,A) <=> true.
link(A,B), root(A,N), root(B,M) <=> N>=M | pto(B,A), K is max(N,M+1), root(A,K).
link(B,A), root(A,N), root(B,M) <=> N>=M | pto(B,A), K is max(N,M+1), root(A,K).

main(_) :- counter(0), make(A), make(B), make(C), union(A,B), find(B,X), find(C,Y), 
    print(X),print(Y), union(A,B), chr_show_store(true).
```

```


norm @ pto(A, A1), pto(B,B1), pto(E,E1) \ eclass(A + B, E) <=> eclass(A1 + B1, E1).

cong @ eclass(T,E1) \ eclass(T, E2) <=> E1 < E2 | pto(E2, E1).


```


```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_option(optimize,full). % Thanks Tom Schrijvers for the tip
:- chr_constraint eclass(?,-).



```

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_option(optimize,full). % Thanks Tom Schrijvers for the tip
:- chr_constraint eclass(?,-), eclass2(?,-), collect/1, kill/0, count/1.

cong @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.

% rewrite rules.
% how can we run only once?
% How can we not make a counter inc if already exists? Maybe that doesn't matter much.
comm @ eclass(X + Y, E) ==> eclass2(Y + X, E).
assocl @ eclass(X + YZ, E), eclass(Y + Z, YZ) ==> eclass2(X + Y, XY), eclass2(XY + Z, E). % if I put counter(N) in here, can refire?
assocr @ eclass(X + Y, XY), eclass(XY + Z, E) ==> eclass2(X + YZ, E), eclass2(Y + Z, YZ).

% To collect up new eclasses
collect @ eclass2(T,E), collect(L) <=> L = [eclass3(T,E) | L1], collect(L1).
done @ collect(L) <=> L = [].

% helpers to cleanup eclass2
kill @ kill \ eclass2(_,_) <=> true.
killdone @ kill <=> true.

% helper to count eclasses
count @ count(N), eclass(_,_) <=> N1 is N + 1, count(N1).

% Take rhs list and inject them as CHR constraints 
process([]).
process([eclass3(T, E)| L]) :- eclass(T,E), process(L).

% Do N rewriting runs
batch() :- collect(L), process(L).
batch(0).
batch(N) :- batch(), N1 is N -1, batch(N1).

init_add(N) :- eclass(N,E), N1 is N - 1, init_add_aux(N1,E).
init_add_aux(0,_).
init_add_aux(N,E) :-
  eclass(N, EN), eclass(EN + E, E2), N1 is N-1, init_add_aux(N1, E2).


insert( T , E) :-
 ground(T),
 var(E),
 T =.. [F | Args],
 length(Args, N), length(Es, N),
 T2 =.. [F | Es],
 eclass(T2, E),
 maplist(insert, Args, Es).


main(_) :- 
          N = 6,
          init_add(N),
          Num is 3**(N) - 2**(N+1) + 1 + N, print(Num),
          BNum is N,
          time(batch(BNum)), kill, count(0), chr_show_store(true).
/*
Output:
608
% 397,754,165 inferences, 41.712 CPU in 41.732 seconds (100% CPU, 9535677 Lips)
count(608)

N=5 is under a second. Not good scaling.
*/
```
# Misc
What would be a mvp egraph in C specialized for the comm/assoc problem look like.
Use reference based union find with tag bits?


Is ematching a wam? I suppose so. Ematching over a fixed egraph is easily expressible in prolog.
We could implement egraph as `assert`
We can't use unification vars?
Does tabling help?
```
f(1,2,3).
g(1,2,3).

-? plus(A,B,AB), plus(AB,C,ABC)
```

[Sketch-Guided Equality Saturation Scaling Equality Saturation to Complex Optimizations in Languages with Bindings](https://arxiv.org/pdf/2111.13040.pdf) de buijn indexes with extraction. Rise compiler

[denali](https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf)


[tactic lean](https://github.com/opencompl/egg-tactic-code)

[Cheli Thesis](https://arxiv.org/abs/2112.14714)

[EGRAPH 2022 workshop](https://pldi22.sigplan.org/home/egraphs-2022)
[youtube feed](https://www.youtube.com/watch?v=dbgZJyw3hnk&ab_channel=ACMSIGPLAN)


[chasing an egg](https://effect.systems/doc/pldi-2022-egraphs/abstract.pdf)

[denali](https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf)

[Yihong trick to make ematching faster](http://effect.systems/blog/ematch-trick.html)

[oliver egraph intersection](https://www.oflatt.com/egraph-union-intersect.html)

[wasm mutate - fuzzing wasm with egraphs](https://www.jacarte.me/assets/pdf/wasm_mutate.pdf)

[abstract interp for egraphs](https://arxiv.org/pdf/2203.09191.pdf) improving interval boounds



[](https://github.com/lifting-bits/eqsat)

[sketch guided equality satruation](https://arxiv.org/abs/2111.13040) Give sketches (~ patterns?) which one the ergaph reaches, transition to a new set of rewriting rules / clear the egraphs.

[beam search](https://github.com/jwtag/egg-csep590d-project)

[Caviar: an e-graph based TRS for automatic code optimization](https://dl.acm.org/doi/pdf/10.1145/3497776.3517781) halide

[Automatic Datapath Optimization using E-Graphs](https://arxiv.org/abs/2204.11478) Samuel Coward, George A. Constantinides, Theo Drane 

[Cranelift egraph rfc](https://github.com/bytecodealliance/rfcs/pull/27)

https://en.wikipedia.org/wiki/E-graph

[Equality-Based Translation Validator for LLVM](https://link.springer.com/chapter/10.1007/978-3-642-22110-1_59)

[Automatic Datapath Optimization using E-Graphs](https://arxiv.org/pdf/2204.11478.pdf) RTL optimization


[Improving MBA Deobfuscation using Equality Saturation](https://secret.club/2022/08/08/eqsat-oracle-synthesis.html)

[Fast equality saturation in Haskell](https://github.com/alt-romes/hegg)

[naive egraph](https://github.com/StrongerXi/naive-egraph)