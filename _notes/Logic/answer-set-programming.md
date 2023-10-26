---
layout: post
title: Answer Set Programming
---


- [Examples](#examples)
  - [Reachability](#reachability)
  - [Graph Coloring](#graph-coloring)
  - [Satisfiability](#satisfiability)
  - [N-Queens](#n-queens)
  - [Traveling Salesman](#traveling-salesman)
  - [Reviewer Assignment](#reviewer-assignment)
  - [Dependency Management](#dependency-management)
  - [Planning](#planning)
  - [Tower of Hanoi](#tower-of-hanoi)
  - [Rule Inference](#rule-inference)
  - [Default Reasoning](#default-reasoning)
  - [Worlds](#worlds)
  - [Compiler problems](#compiler-problems)
  - [Egraph extraction / Union Find](#egraph-extraction--union-find)
  - [Instruction Selection](#instruction-selection)
  - [Observer](#observer)
  - [Sqlite](#sqlite)
  - [Geometry](#geometry)
  - [Lambda-datalog](#lambda-datalog)
  - [Polynimal / Semirng](#polynimal--semirng)
  - [Calcium](#calcium)
  - [Types](#types)
    - [Formulog](#formulog)
  - [Sorting](#sorting)
  - [Shortest Path](#shortest-path)
  - [Spanning Tree](#spanning-tree)
  - [Metainterpreter](#metainterpreter)
  - [Subsumption / Lattices](#subsumption--lattices)
  - [Proofs](#proofs)
  - [Tree 2 Graph](#tree-2-graph)
  - [Graph Matching / Edit Distance / Homomorphism](#graph-matching--edit-distance--homomorphism)
  - [Graph Minor](#graph-minor)
  - [Finding Functors](#finding-functors)
  - [Intuitionistic Logic](#intuitionistic-logic)
  - [Rewriting](#rewriting)
  - [Well founded / Coinduction](#well-founded--coinduction)
  - [Hereditary Finite Sets](#hereditary-finite-sets)
  - [Model Checking](#model-checking)
    - [Boolean Equation Systems](#boolean-equation-systems)
  - [SMT Theories](#smt-theories)
    - [EUF Ackermanization](#euf-ackermanization)
    - [Bitvectors](#bitvectors)
    - [Theory of Arrays](#theory-of-arrays)
    - [Difference Logic](#difference-logic)
    - [EPR](#epr)
  - [Junk](#junk)
- [Constructs](#constructs)
  - [Integrity constraints](#integrity-constraints)
  - [Choice Rule](#choice-rule)
  - [Cardinality rules](#cardinality-rules)
    - [cardinality as heads](#cardinality-as-heads)
  - [Conditional](#conditional)
  - [Aggregates](#aggregates)
  - [Optimization](#optimization)
  - [Disjunction](#disjunction)
  - [Terms](#terms)
  - [Functions](#functions)
  - [Theories](#theories)
  - [Other](#other)
- [true #false](#true-false)
- [sup #inf useful for aggregates (min max of empty set)](#sup-inf-useful-for-aggregates-min-max-of-empty-set)
- [Theory](#theory)
  - [Stable Models](#stable-models)
  - [Unfounded Sets](#unfounded-sets)
  - [Non Monotonic Reasoning](#non-monotonic-reasoning)
  - [Logic of here and there](#logic-of-here-and-there)
  - [Operational](#operational)
  - [Tableau / Proof](#tableau--proof)
  - [Justification](#justification)
  - [Completion](#completion)
- [Solving](#solving)
  - [Grounding](#grounding)
  - [Solver](#solver)
- [Systems](#systems)
- [API](#api)
  - [Lua](#lua)
  - [Python](#python)
    - [nqueens](#nqueens)
- [Easy Answer Set Programming](#easy-answer-set-programming)
- [Misc](#misc)

See also notes on:

- Datalog
- Prolog
- Constraint Programming
- SAT

What is answer set programming:

- A constraint programming system like minizinc
- Super Datalog
  - Datalog with prescient negation
  - Datalog + branching
  - disjunctive datalog
- Justified SMT
- Datalog metaprogramming for SAT
- Prolog negation done right

[Potassco](https://potassco.org/) is the host of clingo, the main ASP solver (so far as I know)

The examples demonstrate some of these points.

# Examples

[potassco guide examples](https://github.com/potassco/guide/tree/master/examples)
[modeling section of course](https://teaching.potassco.org/modeling/)

[Automatic Composition of Melodic and Harmonic Music by Answer Set Programming](https://link.springer.com/chapter/10.1007/978-3-540-89982-2_21)

## Reachability

To demonstrate that it is a superset of datalog.

```clingo
edge(1,2; 2,3; 3,4).
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

```

Try `gringo  --text`. This shows that the grounder solves the entire problem.

## Graph Coloring

```clingo
edge(1,2).edge(2,3). edge(3,4). edge(1,4).
color(r). color(g). color(b).
vert(N) :- edge(N,_).
vert(N) :- edge(_, N).
{assign(N,C) : color(C) } = 1 :- vert(N).
:- edge(X,Y), assign(X,C), assign(Y,C).

```

## Satisfiability

In CNF form (a or b or c) can be see as constraint (not a /\ not b /\ not c -> false).
In this way we can translate CNF to ASP, one integrity constraint per clause.
Generate the vars via

```clingo
{a}. {b}.
:- a, not b.
:- b, not a.
:- not a, not b.
```

## N-Queens

```clingo
#const n=5.
row(1..n).
col(1..n).
{queen(I,J) : row(I), col(J)} = n.
:- queen(I,J), queen(I, J'), J != J'.
:- queen(I,J), queen(I', J), I != I'.
:- queen(I,J), queen(I',J'), I != I', I + J = I' + J'.
:- queen(I,J), queen(I',J'), I != I', I - J = I' - J'.
```

Not space effective. THere are better encodings

```clingo
{queen(I, 1..n)} = 1 :- I = 1..n.
{queen(1..n, J)} = 1 :- J = 1..n.

```

## Traveling Salesman

```clingo
{travel(X,Y)} :- road(X,Y,_).

visited(X) :- travel(X,Y), start(X). 
:- city(X), not visited(X).
:- city(X), 2 {trvale(X,Y)}.

; soft constraint
:~ travel(X,Y), road(X,Y,D) [D,X,Y]
; #minimize

; {travel(X,Y) : road(X,Y,_) } = 1 :- city(X).
; {travel(X,Y) : road(X,Y,_) } = 1 :- city(Y).

```

There are other modes than branch and bound

[clingo example](https://potassco.org/clingo/run/?example=traveling-salesperson.lp)

## Reviewer Assignment

```
{assigned(P,R) : reviewer(R)} = 3 :- paper(P).
:- assigned(P,R), coi(P,R).

:- not 6 {assigned(P,R) : paper(P)} 9, reviewer(R).
; compare to 6 {} 9 :- reviewer which makes each reviewer have between 6 and 9.
```

cardinality cnstraints are convenience features for count

## Dependency Management

[Using Answer Set Programming for HPC Dependency Solving](https://arxiv.org/abs/2210.08404)
<iframe width="560" height="315" src="https://www.youtube.com/embed/bkY9mOyUaDA" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" allowfullscreen></iframe>

## Planning

This is a cool one. It shows that ASP has an answer to the frame problem. It is finite unrolling

```
time(1..k).
fluent(p).
actions(a).
pre(a, p).
add(a,p).
init(r).

holds(P,0) :- init(P).
{occ(A,T) : action(A) } = 1 :- time(T). ; one action per time
:- occ(A,T) , pre(A, P), not holds(P, T-1). % preconditions must hold

holds(F, T):- occ(A,T), add(A,F). ; action adds property

;frame rul
holds(F,T) :- time(T), holds(F, T-1), not occ(A,T) : del(A,F).

:- query(F), not holds(F,T). ; query must hold at last time step

```

can I use this to conveniently describe transition systems? Yes.
[block world planning example](https://potassco.org/clingo/run/?example=blocksworld-planning.lp)
`#include <incmode>.` What does that do?

The frame problem is that typically when describing a system using normal boolean or predicate logic, you need to describe the entirety of the state and explicitly carry the whole thing to the next time step, even when most of it doesn't change. This is very annoying and possibly a wasteful use of reasoning resources. Nevertheless it is true and straightforward.

Temporal logic

[telingo](https://github.com/potassco/telingo)

## Tower of Hanoi

## Rule Inference

You can make variables that correspond to turning rules on or off. And making these choice variables.
You can give positive and negative examples as integrity constraints. And then optimize for a minimum number of rules. Or maybe weight by rule complicatedness.
So this infers a datalog program.
Have a pile of reasonable rules and give it a couple answers. Kind of jives for something a decompiler might like.

<https://rulemlrr19.inf.unibz.it/rw2019/downloads/RW2019-Russo-Law-p2.pdf>
Abduction

inductive logic programming
[ilasp](https://doc.ilasp.com/) [vid](https://www.youtube.com/watch?v=d3-0E-F2rks)
brave or cautius indunction

A related subproblem might be to deduce the initial fact database given the rules and some facts in and not in the output. Abduction logic programming <https://ceur-ws.org/Vol-3204/paper_9.pdf>

```clingo
vert(1..4).
{edge(X,Y)} :- vert(X), vert(Y).
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

% Hmm.
%not not path(X,Y) :- vert(X), vert(Y), X < Y.
%:- vert(X), vert(Y), X < Y, not path(X,Y).
%:- not path(4,1).
:- not path(1,4).
:- not path(2,4).

#minimize { 1,X,Y: edge(X,Y) }.
```

[Answer Set Programming for Regular Inference](https://www.mdpi.com/2076-3417/10/21/7700) inferring regular expressions from string examples

<https://github.com/stefano-bragaglia/XHAIL>

Abuduction

```clingo
{rainy; wet}.

cloudy :- rainy.
wet :- rainy.
slippery :- wet.

% it's cloudy any slippery
:- not cloudy.
:- not slippery.


```

Adbuction as loop invariant
while(C) {}
not C /\ ? => Q. get first hypothesis

- is inductive
- is invariant not inductive. strengthen loop C /\ I /\ ? => I. I is inductive realtive to I'
- is not invariant - backtrack. many abudction choices.

## Default Reasoning

ASP offers in a sense 5 truth values. True `a`, possibly true `not -a`, unknown `not a, not -a`, possibly false `not a`, false `-a`. You can add rules that collapse some of these values into the others, i.e. let's assume something possible true is in fact true `a :- not -a`.

## Worlds

You can make variables that are true in particular worlds. A version I saw was carton reasoning vs real world reasoning. This feels very modal logic-y. The branching stable models are then different worlds you can be on. I don't know that there is a way to talk about connections between worlds though in this style.

## Compiler problems

[TOAST: Applying Answer Set Programming to Superoptimisation](https://link.springer.com/chapter/10.1007/11799573_21) <http://www.cs.bath.ac.uk/tom/toast/>
[Generating Optimal Code Using Answer Set Programming 2009](https://link.springer.com/chapter/10.1007/978-3-642-04238-6_57)
[Superoptimisation: Provably Optimal Code Generation using Answer Set Programmin - crick thesis](https://purehost.bath.ac.uk/ws/portalfiles/portal/187949093/UnivBath_PhD_2009_T_Crick.pdf)

```python
import clingo

def Var(x):
  
def Add(e1,e2):

def Set(v, e):



```

```clingo

prog(plus(a, b)).

expr(E) :- prog(E).
expr(A) :- expr(plus(A,_)).
expr(B) :- expr(plus(_,B)).

isel(add(plus(A,B),A,B)) :- expr(plus(A,B)). 

{cover(E,P)} = 1 :- expr(E).

alloc(R,T)

%#show expr/1.
```

```clingo
% re
#script (python)
import clingo

def is_const(x):
    print(x)
    return x.type == clingo.SymbolType.Function and len(x.arguments) == 0
def mkid(x):
    if is_const(x):
        return x
    return clingo.Function("var", [clingo.Number(hash(x))])

#end.

% flatten
expr(E) :- prog(E).
expr(A) :- expr(plus(A,_)).
expr(B) :- expr(plus(_,B)).

% generate possible instruction outputs via pattern matching
%insn(add(V, A1, B1)) :- expr(E), E = plus(A,B), V = @mkid(E), A1 = @mkid(A), B1 = @mkid(B). 

pre_insn(add(E, A, B)) :- expr(E), E = plus(A,B).
pre_insn(mov(E,A)) :-  expr(E), E = plus(A,0).
pre_insn(mov(E,B)) :-  expr(E), E = plus(0,B).

% do the id conversion all at once.
insn(add(E1,A1,B1)) :- pre_insn(add(E,A,B)), E1 = @mkid(E), A1 = @mkid(A), B1 = @mkid(B).
insn(mov(E1,A1)) :- pre_insn(mov(E,A)), E1 = @mkid(E), A1 = @mkid(A).

% Is there really a reason to have separate insn and select?
{select(I)} :- insn(I).

defines(I,V) :- insn(I), I = add(V, A1, B1).
defines(I,V) :- insn(I), I = mov(V, A).

uses(I,A) :- insn(I), I = add(V, A, B).
uses(I,B) :- insn(I), I = add(V, A, B).
uses(I,A) :- insn(I), I = mov(V, A).

% top level output is needed.
used(P1) :- prog(P), P1 = @mkid(P). 
{select(I) : defines(I,V)} = 1 :- used(V). % if used, need to select something that defines it.

% if selected, things instruction uses are used. Again if selected 
used(A) :- select(I), uses(I,A).

%//{select(A) :- select(add(V,A,B)).
%select

%prog(plus(a, plus(b,c))).
prog(plus(a, plus(plus(0,b),c))).
defines(a,a; b,b; c,c).

%#show expr/1.
#show select/1.

% if used, must be assigned register
{assign(V, reg(0..9)) } = 1 :- used(V).

le(X,Z) :- le(X,Y), le(Y,Z). % transitive
:- le(X,Y), le(Y,X), X != Y. % antisymmettric
le(X,X) :- le(X,_). % reflexive
le(Y,Y) :- le(_,Y).

% instructions must be ordered
{le(I,J)} :- select(I), select(J).

% definitions must become before uses.
le(I,J) :- defines(I,A), used(J,A).

% var is live at instructin I if I comes after definition J, but before a use K.
% using instruction as program point is slight and therefore perhaps alarming conflation
live(I, X) :- defines(J, X), le(J, I), J!=I, le(I,K), uses(K,X).

#show assign/2.
```

```
add(0, z, x, y).
add(1, z, x, y).
add(2, )

insn(, add).
insn(, sub, ).
insn(N, mov, ).

:- insn(N), insn(M), N != M. % unique times
:- 

:- assign(Temp,R), assign(Temp2,R), live(Temp,T), live(Temp2,T) ; no register clashes.
```

```clingo
%#program myprog.
insn(x, add, y , z).
insn(w, mul, x,  y).




% identify instruction with the temp it defines. Good or bad?
%#program base.
temp(T) :- insn(T,_,_,_).
temp(T) :- insn(_,_,T,_).
temp(T) :- insn(_,_,_,T).

% scheduling
{lt(U,T); lt(T,U)} = 1 :- temp(T), temp(U), T < U.
lt(T,U) :- lt(T,V), lt(V,U). %transitive
% not lt(T,T). % irreflexive redundant
% :- lt(T,U), lt(U,T). % antisymmettric redundant

% uses
use(T,A) :- insn(T, _, A, _).
use(T,B) :- insn(T, _, _, B).

lt(A,T) :- use(T,A).

% live if U is defined before T and there is a use after T.
live(T,U) :- lt(U,T), lt(T,V), use(V,U). 

reg(r(0..9)).

{assign(T,R): reg(R)} = 1 :- temp(T).
:- assign(T,R), assign(U,R), live(U,T).

% minimize number of registers used 
#minimize { 1,R : assign(T,R)}.
% try to use lower registers as secondary objective
#minimize { 1,R : assign(T,R)}.

% sanity vs constraints. I expect none of these to be true.

binop(Op) :- insn(_, Op, _,  _).

error("assign field is not register", R) :- assign(_,R), not reg(R).
error("assign field is not temp", T) :- assign(T,_), not temp(T).


```

```clingo
#script (python)
import clingo

def is_const(x):
    return isinstance(x, clingo.Symbol) and len(x.arguments) == 0
def mkid(x):
    if is_const(x):
        return x
    return clingo.Function("v" + str(hash(x)), [])

#end.

prog(plus(a,plus(b,c))).
expr(E) :- prog(E).
expr(A) :- expr(plus(A,_)).
expr(B) :- expr(plus(_,B)).

% It's almost silly, but also not.
insn(@mkid(E), add, @mkid(A), @mkid(B)) :- expr(E), E = plus(A,B).
id(@mkid(E),E) :- expr(E).



```

```clingo
#script(python)
import clingo
def my_add(a,b):
  return clingo.Number(a.number + b.number)

#end.

test_fact(@my_add(1,2)).
```

```clingo
biz.
{foo; bar} = 2 :- biz.
```

Could use python parser to create code. That's kind of intriguing.

Free floating and assign to blocks?
The graph like structure is nice for sea of nodes perhaps.
clingo-dl might be nice for scheduling constraints.

Using clingraph would be cool here.

```clingo

prog(E).
expr(E) :- prog(E).

% block(B,X,E) % variable X should have expression E in it. This summarizes the block.

% demand.  ( dead code elimination kind of actually. )
expr(A;B) :- expr(add(A,B)). 

reg(rax;rdi;rsi;r10;r11).


insn(E, x86add(I1,I2)) :- expr(add(A,B)), insn(A,I1), insn(B,I2). 

{ insn(E, x86add(R1,R2)) } :- expr(E), E = add(A,B), insn(A,I1), insn(B,I2), reg(R1), reg(R2). 

% how to factor representing intructions

{ insn(E, x86add) } :- expr(add(A,B)).

% really its a pattern identifier.



sched(E,I,N) :- insn(E,I), ninsn(N), 0...N.
{ dst(E,x86add,0,R) } :- reg(R), not live(R).
src(E,I,R) :- insn(add(A,B, x86add), dst(A,_,R), dst(B,_,R).

% must schedule value needed before computation
:- sched(add(A,B), I, N), sched(A,I1,M), M >= N.
:- sched(add(A,B), I, N), sched(B,I1,M), M >= N.

% We could schedule at multiple times. That's rematerialization.


% copy packing?
{insn(E, cp)} :- expr(E).


read(src) :- insn(x86add(Dst, Src)).
clobber(Dst;zf;cf) :- insn(x86add(Dst, Src)).

% initial values / calling conventions
value(rdi,x0,0; rsi,x1,0; rcx,x2,0).
value(rax, E, N) :- prog(E), ninsn(N).

live(R,N-1) :- live(R,N), not clobber(R,I,N). 
live(R,N-1) :- read(R,N). 



ninsn(N) :- N = #count { I : active(E,I) }.



```

```clingo
#script (python)
import clingo

def to_asm(t):
  if t.name == "add":

  return clingo.String("todo")

#end.


prog(E).
expr(E) :- prog(E).
expr(A;B) :- expr(add(A,B)).

child(E,A; E,B):- expr(E), E = add(A,B).

reg(rax;rdi;rsi;r10;r11).
ecount(N) :- N = #count { E : expr(E) }.
{ where(R,E)   } = 1 :- reg(R), expr(E).
{ when(1..N,E) } = 1 :- ecount(N), expr(E).

% subexpressions must come earlier
:- when(I, E), when(I2, C), child(E,C), I2 > I.

% time is unique
:- when(I,E1), when(I,E2), E1 != E.

% There can't exist a clobber E1 that occurs
:- child(E,C), where(R,C), where(R, E1), E1 != C, 
   when(T,E), when(Tc,C), when(T1,E1), Tc < T1, T1 < T. 

write(R,T) :- when(T,E), where(R,E).
read(R,T)  :-  when(T,E), child(E,C), where(R,C).

liver(R,T) :- read(R,T).
liver(R,T-1) :- liver(R,T), not write(R,T).

live(T, C)   :-  when(T, E), child(E,C).
live(T-1, E) :-  live(T,E), not when(T,E), T >= 0. 

avail(T,E) :- when(T,E).
avail(T+1,E) :- avail(T,E), where(R,E), not write(R,T), T <= End.

% where = assign ? alloc ?

#minimize { 10, : where(R,E), reg(R)  } + { 50, : where(R,E), stack(R)  }.

```

## Egraph extraction / Union Find

<https://www.philipzucker.com/asp-for-egraph-extraction/>

```clingo
%re
eq(Y,X) :- eq(X,Y).
eq(X,Z) :- eq(X,Y), eq(Y,Z).

term(X) :- eq(X,_).
term(X;Y) :- term(add(X,Y)).

eq(add(X,Y), add(Y,X)) :- term(add(X,Y)).
eq(add(X,add(Y,Z)), add(add(X,Y),Z)) :- term(add(X,add(Y,Z))).
eq(add(X,add(Y,Z)), add(add(X,Y),Z)) :- term(add(add(X,Y),Z)).

term(add(1,add(2,add(3,4)))).
```

```clingo
%re
#script(python)

uf = {}
def find(x):
  while x in uf:
    x = uf[x]
  return x

def union(x,y):
  x = find(x)
  y = find(y)
  if x != y:
    uf[x] = y
  return y

#end.


% :- term(add(X,Y)), rw(X,X1), rw(Y,Y1), 

% add( @find(Y) , @find(X) ,@find(XY) ):- add(X,Y,XY).

%rw(T, @union(T,add(@find(X), @find(Y)))) :- term(T), T = add(X,Y). % congruence?
%rw(T, @union(T,add(@find(Y), @find(X)))) :- term(T), T = add(X,Y). % commutativity.
%rw(T, @find(T)) :- term(T).
%rw(X, @find(X); Y, @find(Y)) :- term(add(X,Y)).

%term(T) :- rw(_,T).

term(@union(T, add(@find(X), @find(Y)))) :- term(T), T = add(X,Y).
term(@union(T, add(@find(Y), @find(X)))) :- term(T), T = add(X,Y).

term(@find(X); @find(Y)) :- term(add(X,Y)).

bterm(1,0).
bterm(N+1, add(N,X)):- bterm(N,X), N < 5. 
term(X) :-  bterm(5,X).
%term(add(1,2)).

#show term/1.
```

Explicit strata control. Does this work? Does it semi-naive? But I want to add strata for term producing rules

```
#script(python)
def main(ctl):
  for i in range(10):
    ctl.ground(["cong", [])]) # aka rebuild
    ctl.ground(["rewrite",[])])
  ctl.solve()

#prog(rebuild)
add(@find(X),@find(Y),@find(Z)) :- add(X,Y,Z).
add(X,Y,@union(Z,Z1)) :- add(X,Y,Z), add(X,Y,Z1), Z != Z1.
#end.

#prog(rewrite)
add(Y,X,Z) :- add(X,Y,Z).
add()

@end.

#end.
```

```clingo
%re
#script(python)

uf = {}
def find(x):
  while x in uf:
    x = uf[x]
  return x

def union(x,y):
  x = find(x)
  y = find(y)
  if x != y:
    uf[x] = y
  #print(uf)
  return y

#end.

add(X,Y,XY) :- term(XY), XY = add(X,Y).
term(X;Y) :- term(add(X,Y)).
term(add(add(add(add(1,2),3),4),5)).

add(@find(Y),@find(X),@find(Z)) :- add(X,Y,Z).
add(@find(X),@find(YZ),@find(XYZ);@find(Y),@find(Z),@find(YZ)) :- add(X,Y,XY), add(XY,Z,XYZ), YZ = @find(add(Y,Z)).

add(@find(X),@find(Y),@find(Z)) :- add(X,Y,Z).
add(@find(X),@find(Y),@union(Z,Z1)) :- add(X,Y,Z), add(X,Y,Z1), Z != Z1.

enode(N) :- N = #count { X,Y,XY : add(X,Y,XY) }.
enode2(N) :- N = #count { X,Y,XY : fadd(X,Y,XY) }.

fadd(@find(X),@find(Y),@find(Z)) :- add(X,Y,Z).

#show enode/1.
#show enode2/1.
```

## Instruction Selection

[Complete and Practical Universal Instruction Selection](https://dl.acm.org/doi/10.1145/3126528)

```clingo
prog((
  set(p2,plus(p1,4)),
  set((st,q1), p2),
  set(q2, plus(q1,4)),
  set((st,p1), q2)
)).

plus(p1,4,p2).
plus(p1,4,p1).

```

This is doing dag tiling. Graph matching probably doesn't look that much different.

```clingo
% demand
expr(X;Y) :- expr(add(X,Y)).
expr(X;Y) :- expr(mul(X,Y)).

{ sel( add, E) } :- expr(E),    E = add(X,Y),        sel(P1,X), sel(P2,Y).
{ sel( mul, E) } :- expr(E),    E = mul(X,Y),        sel(P1,X), sel(P2,Y).
{ sel( fma, E) } :- expr(E),    E = add(mul(X,Y),Z), sel(P1,X), sel(P2,Y), sel(P3,Z).
@
offset(0;1;2;4;8;16).
{ sel( load, E) } :- expr(E),    E = load(add(Addr,N)), sel(P1,Addr), offset(N).

{ sel(reg, E) } :- expr(E), E = var(X). % we don't _have_ to "use" register if something dumb is using it.


{ sel(nop, E) }:- expr(E), E = add(X,0), sel(P,X).

prog(mul(var(x), var(y))).
expr(E) :- prog(E).

pat(P) :- sel(P,_).

%:- #count { sel(P,E) : expr(E),pat(P) } > 1. % only select at most one pattern
:- #count {sel(P, E) : pat(P), prog(E)} = 0.
%#minimize { 1,X,Y : sel(X,Y) }.

#show expr.


```

## Observer

```clingo
%re
#script(python)

class Observer():
  def output_atom(sym, atom):
    print(f"output_atom {sym} {atom}")
  def rule(self, choice, head=[] , body=[]):
    print(f"rule {choice} {head} :- {body}")


def main(ctl):
  ctl.register_observer(Observer)
  ctl.ground([("base",[])])
  print(dir(ctl))
  ctl.solve()

#end.

edge(1,2;3,4).
path(X,Y) :- edge(X,Y).

```

## Sqlite

```python
import sqlite
import clingo

prog = """
edge(1,2;3,4).
path(X,Y) :- edge(X,Y).
"""

sqlite.connect(":memory:")
# could either register observer callback to insert into sqlite
# or just flip the entire model in

ctl = Control()
ctl.ground([("base",[])])


```

## Geometry

Deductive database

```clingo
#script(python)
import clingo
def sort(*s):
  return clingo.Tuple(sorted(s))

#end.

test(@sort(4,5,3)).

point(y,x).
line(A,B) :- point(X), point(Y), (A,B) = @sort(X,Y). % seems a little silly here.
```

Storing sorted canonical versions is easy, joining (efficiently) modulo permutations is tougher.

Using smart constructors. Is this better?

```
#script(python)

def line(*args):
  return clingo.Function("line", sorted(args))

#end.

```

Mixing in grobner?

```clingo
#script(python)
import sympy

#end.


```

## Lambda-datalog

All the herculean effort I went to on souffle is easy because clingo has nice pyton integration

varargs is easy.
Sets can be represented as sorted deduped lists.
We can return multiple results so this is also easy to get the elements out of a set.
certainly I can define

```clingo
%re
#script(python)
import clingo
nil = clingo.Function("nil",[])
def cons(x,xs):
  return clingo.Function("cons", [x,xs])

def elem(l):
  res = []
  while l.name == "cons":
    assert len(l.arguments) == 2
    res.append(l.arguments[0])
    l = l.arguments[1]
  assert l.name == "nil" and len(l.arguments) == 0
  return res

def clist(*args):
  if len(args) == 0:
    return nil
  return cons(args[0], clist(*args[1:]))

# sort and duplicate a list. Could also do a whole patricia tree thing, but whetev.
def cset(*args):
  s = set(args)
  return clist(*sorted(list(s)))

def append(*ls):
  return clist(*sum(map(elem,ls), []))

def union(*ls):
  return cset(*sum(map(elem,ls), []))

# maps as assoc lists
'''
def put(d,k,v):
  d = { k : v for (k,v) in elem(d) }
  d[k] = v
  clist( d.items())
'''

# introspection
def arguments(x):
  return clist(*x.arguments)
def name(x):
  return clingo.String(x.name)
def apply(name,args):
  return clingo.Function(name.string, elem(args))


# locally nameless
def open(t):
  pass
def close(x,t):
  pass
def subst():
  pass
def lam(x,e):
  pass
def norm(t):
  pass


def error(e):
  print(e)
  assert False

#end.

test(@clist(1,2,3,4,5)).
test(@append(@clist(a,b,c), @clist(d))).
test(@cset(1,1,2,28,3,4,4)).
foo(@elem(X)) :- test(X).

err(@error("this is a custom error")). 
```

## Polynimal / Semirng

Similar to lattices in some respects.

```clingo
#script(python)
import sympy


#end.




```

```python
from sympy import *
x, y, z = symbols('x,y,z')
init_printing(use_unicode=False, wrap_line=False)
e = (3*x/2 + y)*(z - 1)
print(e.as_poly())
f = Function("f")
e = f(x) + 1 + f(f(x))
print(e)
print(e.as_poly())
p = e.as_poly()
d = {p : 7}
e = f(x) + 1 + f(f(x))
p2 = e.as_poly()
d[p] =  8
print(p == p2)
print(hash(p), hash(p2))
print(p is p2)
print(d)
```

A problem with foreign relatons is there is no way to communicate an update back to asp.

```python
import clingo

ctl = clingo.Control()
print(dir(ctl))
#print(help(ctl.add))
_biz = [42]
def biz(x):
  yield from _biz

ctl.add("""
foo(7).
bar(Y) :- foo(X), X = Y. %, @biz(X) = Y.
""")
ctl.ground()
_biz.append(76)
ctl.ground()

```

Hmm. Ok, clingo does both

```clingo
#script(python)
import clingo
def test1():
  print("hello world")
  return clingo.String("hiel")
#end.

#script(python)
def test2():
  print("he world")
  return clingo.String("foo")
#end.
foo(@test1()).
foo(@test2()).

```

## Calcium

```clingo
#script(python)

from calcium import *

#end.

```

## Types

<https://www.cl.cam.ac.uk/~nk480/bidir-survey.pdf>

```clingo

#script(python)

def lookup(env,k):
  assert env.name == "cons"
  print(env)
  car = env.arguments[0]
  if car.arguments[0] == k:
    return car.arguments[1]
  else:
    return lookup(env.arguments[1], k)

#end.

%-of(cons(X,A,G), E, B) :- -of(G, lam(X,E), arr(A,B)) 
% demand
%do_check(G, lam) :- 
%check() :- check(lamI),
%synth() :- -check(lamI),


check(G, E, T) :- do_check(G,E,T), E = var(X), T = @lookup(G,X).
check(G, E, T) :- do_check(G,E,T), E = ann(E1,T), check(G,E1,T).
check(G, E, T) :- do_check(G,E,T), E = tt, T = unit.
check(G, E, T) :- do_check(G,E,T), E = lam(X,E1), T = arr(A,B), check(cons((X,A),G),E1,B).
check(G, E, T) :- do_check(G,E,T), E = app(E1,E2), T = B, check(G,E1,arr(A,B)), check(G,E2,A).


check(G,E,T) :- synth(G,E,T). 
do_synth(G,E) :- do_check(G,E,T). % we can derive a synth query from check query

synth(G,E,T) :- do_synth(G,E), E = var(T), T = @lookup(G,X).
synth(G,E,T) :- do_synth(G,)

do_check(G, E1, T1) :- do_check(G, ann(E1,T1), T).
do_check(cons((X,A),G),E1,B) :- do_check(G, lam(X,E1), arr(A,B)).

do_synth(G, E1) :- do_check(G, app(E1,E2), B).
do_check(G, )


do_check(nil, lam(x,var(x)), arr(a,a)).
```

Hmm. This actually kind of is the rule selection problem.

Proof search. How to put the search into choice and not do full datalog expansion
p(n, )   add n parameter to judgement. no, this still expands too much... hmm. Maybe like the isel example, we need to abstract the state and put more in the derivation tree.

```

```

### Formulog

Z3 is available in python. ASP is a datalog. Badabing bada boom

```clingo
%re
#script(python)
from z3 import *
import clingo

exprs = {}

def z3ref(e):
  id_ = e.get_id()
  res =  clingo.Function("z3", [clingo.Number(id_),clingo.String(repr(e))])
  exprs[res] = e
  return res

def toz3(s):
  assert s.name == "z3"
  return exprs[s]

def bool(x):
  return z3ref(Bool(x.string))

def is_sat(e):
  s = Solver()
  s.add(toz3(e))
  res = s.check()
  if res == sat:
    return clingo.Function("sat")
  elif res == unsat:
    return clingo.Function("unsat")

#end.

test(@bool("x")).
foo(X) :- test(Y), X = @is_sat(Y).

```

Could Z3 be used as a theory?
ASP as z3 theory?

## Sorting

<https://www.aaai.org/ocs/index.php/KR/KR14/paper/viewFile/7966/7912>

```clingo
order(X,Y) :- p(X), p(Y), X < Y, not p(Z) : p(Z), X < Z, Z < Y.
p(3).
p(7).
p(19).
```

## Shortest Path

Fishy as hell. It's complaining about something. And it's outputting all paths. Hmm.

```clingo
edge(1,2;2,3;3,4;1,4).
vert(V) :- edge(V,_).
vert(V) :- edge(_, V).
path(X,Y,1) :- edge(X,Y).
path(X,Z,1 + N) :- edge(X,Y), vert(Z), N = #min { N1 : path(Y,Z,N1) }. 
```

Between two particular nodes this could be an optimization problem

```clingo
edge(1,2;2,3;3,4;1,4).
vert(V) :- edge(V,_).
vert(V) :- edge(_,V).
start(1). end(4).
{on_path(X,Y)} :- edge(X,Y).
{on_path(X,Y) : edge(X,Y)} = 1 :- start(X). 
{on_path(X,Y) : edge(X,Y)} = 1 :- end(Y).
{on_path(Y,Z) : edge(Y,Z)} = 1 :- on_path(X,Y), not end(Y). % every entry must leave
#minimize {1,X,Y : on_path(X,Y)}.
```

## Spanning Tree

```clingo
%edge(1..3,1..6).
%edge(4,2).
edge(1,2;2,3;3,4;1,4).
vert(V) :- edge(V,_).
vert(V) :- edge(_,V).
%root(1).
%{tree(X,Y)} :- edge(X,Y).
%{tree(X,Y) : edge(X,Y)} = 1 :- vert(Y), not root(Y). % one incoming node.


% 0 {tree(X,Y)} :- vert(X).

% every vertex has a tree edge
1 {tree(V,U) : edge(V,U); tree(U,V): edge(U,V)} :- vert(V).

% every vertex has at most on incoming tree edge
{tree(U,V): edge(U,V)} 1 :- vert(V).

%Y = Z :- tree(Z,X), tree(Y,X). % functional dependency

tpath(X,Y) :- tree(X,Y).
tpath(X,Z) :- tree(X,Y), tpath(Y,Z).

path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

% if connected in edge graph, tree connected in tree graph
% {path(X,Z) : tpath(X,Y), tpath(Y,Z)}.


```

## Metainterpreter

[slides](https://teaching.potassco.org/meta/)
`clingo --output=reify`

```
conjunction(B) :- literal_tuple(B),
        hold(L) : literal_tuple(B, L), L > 0;
    not hold(L) : literal_tuple(B,-L), L > 0.

body(normal(B)) :- rule(_,normal(B)), conjunction(B).
body(sum(B,G))  :- rule(_,sum(B,G)),
    #sum { W,L :     hold(L), weighted_literal_tuple(B, L,W), L > 0 ;
           W,L : not hold(L), weighted_literal_tuple(B,-L,W), L > 0 } >= G.

  hold(A) : atom_tuple(H,A)   :- rule(disjunction(H),B), body(B).
{ hold(A) : atom_tuple(H,A) } :- rule(     choice(H),B), body(B).

#show.
#show T : output(T,B), conjunction(B).
```

Hmm. Maybe I need to ground the metaprogram itself? Then I can avoid

## Subsumption / Lattices

It is unlikely the grounder gets the boost that subsumption or lattices gives datalog. In which point it is not clear there is a point. Lattices and subsumption can be modelled by just ignoring the deletion. But if I wanted to model having exactly only the unsubumed terms could I do it?

Question: Can ASP and Lattice Datalog be reconciled? Does this model in terms of pure ASP show yes? That we could push the solving in principle into the grounder. Yes, I think that's right. Then the remaining uncertain pre-foo can be used.

```clingo
num(1..3).
{foo(none); foo(some(X)) : num(X)} = 1.

-foo(none) :- foo(some(X)).
% :- foo(some(X)), foo(none). % but this already loses.


% bar(n) <= bar(m) :- n <= m.


%{bar(1..3)}.
-bar(N) :- bar(M), N <= M.
% hmm. no? THen any rule that produces has to be replaced with choice?
% - vs not?

% maybe two separate predicates. pre-foo and foo.
% pre-foo(X) :-   pre-foo is produced
% pre-foo(join(X,Y)) :- pre-foo(X), pre-foo(X).
% {foo(X) : pre-foo(X)} = 1.
% -foo(Y) :- pre-foo(X), pre-foo(Y), X > Y.
% although maybe we just want #maximize { X : foo(X) }




```

When the pinnacle of the lattice is selected, does that imply everything underneath is selected? That feels right.

The power set lattice does not present an issue? But it doesn't in datalog either.
We have greater powers of negation and aggregation in ASP.
"booleanization" seems like a useful technique.

Lattice via python.

```clingo
%re
#script(python)
import clingo
path_ = {}

def path(x,y):
  return path_[(x,y)]

tt = clingo.Function("tt", [])

def set_path(x,y,c):
  if (x,y) in path_:
    c1 = path_[(x,y)]
    c =  min(c1,c)
    path_[(x,y)] = c
  else:
    path_[(x,y)] = c
  return c
#end.

path(X,Y,C1) :- edge(X,Y,C), C1 = @set_path(X,Y,C).
path(X,Z,C2) :- edge(X,Y,C), path(Y,Z,C1), C2 = @set_path(X,Y,C + C1).


edge(a,b,1).
edge(b,c,1).
edge(a,c,4).
edge(a,c,5).
edge(a,c,3).


conn(X,Y) :- path(X,Y,_).
final_path(X,Y,C1) :- conn(X,Y), C1 =  #min { C : path(X,Y,C)  }.

```

Hmm. Doesn't work because how do we inform clingo something has changed?
Ok yes, this works. We have some lighter amounts of redundancy + improved termination.
Ordering of atoms matters.

## Proofs

In many cases, a "proof" is some artifact containing enough breadcrumbs to figure out the relevant bits of a trace of some proof search. If a system does not support this, it can be added sometimes as a tracing parameter.

Every rule can store the appropriate bindings in an extra parameter. Then you can know what rules fired

The "proof" of a connectivity query is the path.

You often need some kind of lattice action to make this converge since there are infinitely many paths in any grph with cycles.

A timestamp can be sufficnet breadcrumb. Timestamp is similar to proof depth. Take the min lattice.

Optimization over datalog provenances?

Set of support provenance. This doesn't work in datalog, because we can't detect loops. But we could use ASP negation.

```
{support(path(A,B), edge(X,Y))} :- path(A,B), edge(X,Y), path(Y,Z), not support(edge(X,Y), path(Y,Z))
```

Does the search aspect of ASP add anything to this datalog provenance story? Hmm.
In SAT, the "proof" object is the unsat certificate, a resolution chain. I don't know if stock ASP solvers output something like this for UNSAT. The extra twist is that it may be unsat for justification issues.

```clingo



```

Using gringo.
Gringo grounds datalog programs, but it does so online. Actually since it requires

```bash
echo "
edge(X,X+1) :- X = 1..5.
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

 " | gringo --text
```

Outputting the datalog derivations in order actually does help a lot in terms of reonctructing proofs. Facts can only have been derived by facts appearing above. A prolog process can now reconstruct proofs without getting nto loops

These are essentially timestamps.

If we make everything conditional on a nondetermisitc variable, the grounder will actually display the entire rule derivation body. Cute huh?

```bash
echo "
{c}.
edge(X,X+1) :- X = 1..5, c.
path(X,Y) :- edge(X,Y), c.
path(X,Z) :- edge(X,Y), path(Y,Z), c.
 " | gringo --text
```

```prolog
{c}.
edge(1,2):-c.
edge(2,3):-c.
edge(3,4):-c.
edge(4,5):-c.
edge(5,6):-c.
path(1,2):-c,edge(1,2).
path(2,3):-c,edge(2,3).
path(3,4):-c,edge(3,4).
path(4,5):-c,edge(4,5).
path(5,6):-c,edge(5,6).
path(4,6):-c,path(5,6),edge(4,5).
path(3,5):-c,path(4,5),edge(3,4).
path(2,4):-c,path(3,4),edge(2,3).
path(1,3):-c,path(2,3),edge(1,2).
path(1,4):-c,path(2,4),edge(1,2).
path(2,5):-c,path(3,5),edge(2,3).
path(3,6):-c,path(4,6),edge(3,4).
path(2,6):-c,path(3,6),edge(2,3).
path(1,5):-c,path(2,5),edge(1,2).
path(1,6):-c,path(2,6),edge(1,2).
```

You could use such a trace to do differential datalog. You can delete facts. Then delete any rule that depends on that fact. If that is the last rule with that head, recursively delete derivations using that rule.
You can also delete or add rules similarly. Just delete any instantiations with the rule tag.

 You can also name rules if you like

```bash
echo "
{rule(base_path;fact;trans_path)}.
edge(X,X+1) :- X = 1..3, rule(fact).
path(X,Y) :- edge(X,Y), rule(base_path).
path(X,Z) :- edge(X,Y), path(Y,Z), rule(trans_path).


%edge(1,5) :- rule(fact). % just to see what multiple proof pathways looks like
 " | gringo --text
```

This is the same sort of program you would write for conditionaly turning rules on an off (selecting datalog rules under some criteria).

```
#script(python)

path_ = {}
def path(x,y):
  if (x,y) in path_:
    return False
  else:
    return clingo.Const("true")

#end.

% a "lattice" like effect of only recording first derivation
path(X,Y) :- edge(X,Y), path(X,Y), @path(X,Z) = true.
```

## Tree 2 Graph

In a sense this is doing very little, but perhaps that is only because the tree and graph reprsentations are so close to each other. In most other languages this would stink.

Really this is DAGs not trees. The set semantics and probable underlying hash consing of clingo do that

```clingo
expr(plus(plus(var(a),var(b)),var(c))).

%vert(a,var;b,var;c,var).

expr(A) :- expr(plus(A,_)).
expr(B) :- expr(plus(_,B)).

% asts are an attributed ported multi graph.
% so we need to attribute the vertices with data, and say which port edges are attached to
% If we don't add these labels, we lose info and can't reconstruct the trees

edge(T, left, A) :- expr(T), T = plus(A,B).
edge(T, right, B) :- expr(T), T = plus(A,B).
vert(T, plus) :- expr(T), T = plus(A,B).
vert(T, var) :- expr(T), T = var(A).

% back to a tree
expr'(T, plus'(EA,EB)) :- edge(T,left, A), expr'(A,EA), expr'(B,EB), edge(T,right,B), vert(T,plus).
expr'(A, var'(A)) :- vert(A,var).

%#show expr'/1.

```

## Graph Matching / Edit Distance / Homomorphism

[Flexible graph matching and graph edit distance using answer set programming](https://arxiv.org/abs/1911.11584)

Instead of encoding subgraph patterns as rules (good for small patterns), they encode is by explicitly representing grpah homomoprhisms

```clingo
% h is functiona mapping from X to Y
{h(X,Y) : n2(Y,L)} = 1 :- n1(X,L).
% X and Y are edge identifiers now. Map edge X to edge Y such that source and tagret are mapped
{h(X,Y) : e2(Y,S2,T2,L), h(S1,S2), h(T1,T2)} = 1 :- e1(X,S1,T1,L).
% properties must also be preserved
:- p1(X,K,D), h(X,Y), not p2(Y,K,D).
```

Flip it around to get an isomorphism

```clingo
{h2(X,Y) : n1(X,L)} = 1 :- n2(Y,L).
{h2(X,Y) : e1(X,S1,T1,L), h2(S1,S2), h(T1,T2)} = 1 :- e2(Y,S2,T2,L).
:- p2(Y,K,D), h2(X,Y), not p1(X,K,D).
```

Hmm h and h2 aren't necessarily inverse. They probably compose to an automorphism. Would adding the inverse condition help or hurt?

Or alternatively get a subgraph isomorphism

```clingo
{h(X,Y) : n1(X,L)} <= 1 :- n2(Y,L).
{h(X,Y) : e1(X,S1,T1,L), h(S1,S2), h(T1,T2)} <= 1 :- e2(Y,S2,T2,L).
```

Interesting maybe for query homomorphisms. Queries can be represented as graph.

## Graph Minor

## Finding Functors

```clingo
% tabulate a finite category
compose1(f, g , h).
hom1(f, a, b). % or cod(f,a), dom(f,b)

cod(F,A) :- hom(F,A,_).
dom(F,B) :- hom(F,_,B).

% maybe check associativity and such
% maybe generate id(a) laws.

% tabulate a second cat
compose2(f, g , h).
hom2(f, a2, b2).

% functor is analog of h in graph homomorphism
{functorOb(A,B) : ob2(B)} = 1 :- ob1(A).
{functormorph(F,G) : }

% plays consisntently with objects and morphisms
% should this be generating facts? ... maaaaaybe.
functorObj(A,B) :- functorHom(F,G), hom1(F,A,_), hom2(G,B,_). 

% plays nice with compose
funHom(H1,H2) :- compose1(F1,G1,H1), compose2(F2,G2,H2), funHom(F1,F2), funHom(G1,G2). 


```

Is finding a functor easier or harder than graph homomorphism?
Enumerating them?
Is finding functors part of any interesting proof method?

Next level up, finding natural transformations

## Intuitionistic Logic

In what sense, if any, is clingo an intuitionistic theorem prover [applications of intuionistic logic to answer set programming](https://nokyotsu.com/me/papers/tplp04.pdf) [Answer set programming in intuitionistic logic](https://www.sciencedirect.com/science/article/pii/S001935771730054X).
Refutations. State axioms as rules, state therem to prove as constraint. Look for unsat.
asp does not immediately admit every intuitionistic formula. That's ok.
The relationship of asp negation to intuitionistics negation is confusing.
Intuitionistic logic is one with pretty few assumptions about how the logic works. A proof in there probably transfers over to a notion of proof in ASP. It's the other direction that is more worrying.

I mean, forgetting (explicit) negation, what about just using choice to model intuitionistic disjunction? A -> B \/ C ~ 1{b;c} :- a. I don't see a reason to use  disjunction?
Using conditionals to simulate higher order axioms?
Datalog + Case analysis. Cyclic proofs?

[On Equivalent Transformations of Infinitary Formulas under the Stable Model Semantics](https://www.cs.utexas.edu/users/vl/papers/etinf.pdf) "From the results of Pearce [7] and Ferraris
[1] we know that in the case of grounded logic programs in the sense of Gelfond
and Lifschitz [2] and, more generally, finite propositional formulas it is sufficient
to check that the equivalence F ↔ G is provable intuitionistically" So intuitionsitc reasoning is sufficient for proving equivalence of ASP programs. But perhaps not the other way. Yes, that is often what I'm doing. Translating datalog programs into intionistic logic to see if it's ok. But if the connection is complete, I may miss valid transformations.

## Rewriting

It all comes back to edge-path.
Rewriting systems have directed edges between terms.

```clingo

rw(fact(0), 1, S).
rw(T, N*fact(N-1), S+1) :- rw(_, T, S), T = fact(N), N > 0.

start(fact(7)).
reach(A) :- start(A).
reach(B) :- reach(A), rw(A,B).

% or a tagged version that maintains te starting point.
reach(A,A) :- start(A).
reach(S, B) :- reach(S,A), rw(A,B).

% may want to demand based on reach
%
rw(T, 1) :- reach(_,T), T = fact(0).
rw(T, N*fact(N-1), S+1) :- rw(_, T, S), T = fact(N), N > 0.


% could also inline rw into the recursivr reach call. 
rw(Start, fact(0), 1, S).
rw(Start, N*fact(N-1), S+1) :- rw(Start, T, S), T = fact(N), N > 0.

% get most simplified one.
% assuming terminating/confluent rewrite system.
% can either do that by tracking most steps, or by uing termination metric on term itself.
#maximum { S : rw(fact(3), T, S)}

```

A graph without cycles can talk about longest path.

```clingo

size_ = {}
def size(l):
  if l in size_:
    return size_[l]
  res = sum(map(size,l.arguments)) + 1
  size_[l] = res
  return res

# subsumptn pattern
simp_ = {}
def simp(l):

def set_simp(l,l1):


```

Modular grounding?

Datalog modulo term rewriting. I mean, I guess this is ASP modulo term rewriting.
The idea is that you can normalize datalog terms before they go in. What is unsatisfying is you may want guarded rewriting, for which the guards depend on datalog analyses. Then we need something subsumptive or lattice-like, which clingo doesn't offer?

```clingo
#script (python)
import clingo

import maude

test_mod = """
fmod TESTMOD is
  sort Term .
  op foo : Term -> Term .
  ops x bar : -> Term .
  eq foo(x) = bar .
endfm

"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('TESTMOD')


def to_maude(x):
    print(str(x))
    return mod.parseTerm(str(x))

def from_maude(t):
    return clingo.parse_term(str(t))
    #return clingo.Function(str(t.symbol()), map(from_maude,t.arguments()))

def reduce(x):
    t = to_maude(x)
    print(t.reduce())
    return from_maude(t)

#end.

test(@reduce(foo(x))).

```clingo
#script (python)
import clingo
import maude

test_mod = """
  fmod TESTMOD is
    sort Term .
    op foo : Term -> Term .
    ops x bar : -> Term .
    eq foo(x) = bar .
  endfm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('TESTMOD')

def reduce(x):
    t = mod.parseTerm(str(x))
    t.reduce()
    return clingo.parse_term(str(t))
#end.

test(@reduce(foo(x))).
% Result: test(bar)
```

```python
# https://github.com/fadoss/maude-bindings/blob/master/tests/python/buildTerm.py
import maude

maude.init(advise=False)

mod = maude.getModule('NAT')
natk = mod.findSort('Nat').kind()

splus  = mod.findSymbol('_+_', [natk, natk], natk)
stimes = mod.findSymbol('_*_', [natk, natk], natk)

onetwo = [mod.parseTerm('1'), mod.parseTerm('2')]
three  = mod.parseTerm('3')

# Constructs 4 + (3 * (1 + 2))
#expr = splus.makeTerm((mod.parseTerm('4'),
t = mod.parseTerm("4 + (3 * (1 + 2))")
print(list(t.arguments()))
print(dir(t))
print(t.symbol())
```

```python
from dataclasses import dataclass
# https://en.wikipedia.org/wiki/Normalisation_by_evaluation

# Hmm. I should just be using clingo terms if that is what I want this for.
# Can clingo terms hold lambdas (even briefy?) ?
class Term():
  pass
class Sem(Term): # Hmmm.
  pass

@dataclass
class TLam(Term):
  x:str
  body:Term
@dataclass
class TApp(Term):
  f:Term
  x:Term
@dataclass
class TVar(Term):
  x:Term

@dataclass
class SLam(Sem):
  f:Callable[Sem,Sem]


counter = 0
def fresh():
  global counter
  counter += 1
  return counter

def reify(sem):
  if isinstance(sem, SLam):
    x = fresh()
    return TLam(x, sem.f(x))
  else:
    #traverse children    



def meaning(ctx, tm):
  if isinstance(tm, TVar):
    return ctx[tm.x]
  elif isinstance(tm, TLam):
    def res(y):
      ctx2 = copy(ctx)
      ctx2[tm.x] = y
      interp(ctx2, tm.body)
    return SLam(res)
  elif isinstance(tm,TApp):
    f1 = meaning(ctx, tm.f)
    assert isinstance(f1, SLam)
    return meaning(ctx,f1.f(x))


  


```

## Well founded / Coinduction

Coq Accessibility [chlipala](http://adam.chlipala.net/cpdt/html/GeneralRec.html#:~:text=Well%2DFounded%20Recursion,Coq%20is%20well%2Dfounded%20recursion)
[coq library for wf](https://coq.inria.fr/library/Coq.Init.Wf.html)
<https://proofassistants.stackexchange.com/questions/1077/well-foundedness-classical-equivalence-of-no-infinite-descent-and-accessibility>

Accessible seems like a bad name to me. "acc(x) = Terminating at x"
Wait. Does acc stand for ascending chain condition?

```clingo
r(1,2;2,3;3,4).
r(2,1). 
node(X;Y) :- r(X,Y).
acc(X) :- node(X), acc(Y) : r(X,Y).
wf :-  acc(X) : node(X).
```

Encode well-foundedness. Put choice in. Solve for termination order?

Coinductive. Greatest Fixed point. Least fixed point of negative works.
Take each coinductive rule and if any of hypotheses are _known_ false, it isn't true.

Has inifintie path is coinductive property

See coinduction in datalog notes

```clingo
-inf_trace(X) :- vert(X), -inf_trace(Y) : edge(X,Y).
inf_trace(X) :- vert(X), not -inf_trace(X). %If it's not disprovable, it's true.
```

Nontermination = presence of loop in finite case. In a sense finite makes us classical.

```clingo

path(X,Z) :- edge(X,Y), path(Y,Z).
loop(X) :- path(X,X). % loop = inf_trace

```

## Hereditary Finite Sets

Set theory has this notion of sets of sets. This is not how I typically model things, but it is interesting and fun.

Atomic set labels.
Extensionality
elem relation

Wellfoundedness is optional, becomes nonwellfounded set theory which is neat.

```clingo
set(empty).
:- elem(X,empty).
wf(empty).

subset(A,B) :- set(A), set(B), elem(X,B) : elem(X,A). 
eq(A,B) :- subset(A,B), subset(B,A).

wf(A) :- set(A), wf(X) : elem(X,A).

elem(X, sing(X)) :- set(sing(X)).
:- elem(Y,sing(X)), X != Y.

elem(X, union(A,B)) :- set(union(A,B)), elem(X,A).
elem(X, union(A,B)) :- set(union(A,B)), elem(X,B).
:- elem(X,union(A,B)), not elem(X,A), not elem(X,B). % is this necessary?


elem(X, inter(A,B)) :- set(inter(A,B)), elem(X,A), elem(X,B).
:- elem(X,inter(A,B)), not elem(X,A).
:- elem(X,inter(A,B)), not elem(X,B).


elem(X, trans(A)) :- elem(X,A).
elem(Y, trans(A)) :- set(X), elem(X,A), elem(Y,trans(X))

% demand
set(trans(X)) :- set(trans(A)), elem(X,A), set(X).





```

## Model Checking

Modal logic. Satisfaction is set of states
modal mu calculus

```
% labelled transition system
trans(1,a,2).
states(s) :- trans(s,_,_).
states(s) :- trans(_,_,s).
act(a) :- trans(_,a,_).
prop(p, 1). % state property p holds at 1.

reachable(S,S) :- state(S).
reachable(S,S2) :- trans(S,_,S1), reachable(S1,S2).


form(A;B) :- form(and(A,B)). 
form(A;B) :- form(or(A,B)). 
sat(S,P) :- prop(P,S).
sat(S,) :- form(box(a, F)), sat(S1,F) : reachable(S,S1).

```

### Boolean Equation Systems

<http://www.tcs.hut.fi/Publications/bibdb/HUT-TCS-A99.pdf>. See also mcrl2 groot book
An intermediate problem for model checking modal u-calculus. Boolean equations with least and greatest fixed point operaors.
`(sx=a)*`

Dependency graph, edge if x_i appears in a_j
Standard form. binary operations on rhs.

If everything is using least fixed point, no prob. Direct translation.

"Blocks" correspond to strata

```clingo
p1 :- p3. % u.x1=x3
p2.  %  u.x2 = 1 
p3 :- p4. p3 :- p5. % u.x3 = x4 \/ x5
p4 :- p2,p1. %u.x4 = x2 /\ x1

```

If everythign is greatest fixed point, complement the system

```clingo
-p1 :- -p2. -p1 :- -p3. % v.x1 = x2 /\ x3
-p2 :- -p3,-p4. % v.x2 = x3 \/ x4
-p3 :- -p2,-p4. % v.x3 = x2 \/ x4
-p4. %v.x4 = 0
```

Conjunctive and disjunctive systems allow alternation but only contain /\ or only contain \/

Hmm. It might be possible to directly express the modal formula + transition systemcompilation in ASP

```clingo
trans(1,a,2; 1,a,4; 2,a,3; 3,a,2).


```

General translaion. Feels like they are building a parametrized system with rules turnining on and off. We're inferring some kind of graph.

My first inclination was to use direct encoding + ASP priority. That seems like it ought to work?
Add min p and max p as optimization objectives. Put them in the priority that the equations appear. Can I encode games in this way?
I'm like mixing my metaphors. A max sat solver can probably do this also

## SMT Theories

How many SMT theories (euf, arrays, sets) are encodable?

ASP is kind of datalog metaprgramming for SAT.
Many (quantifier free?) SMT problems can be bit blasted.

### EUF Ackermanization

Ackermanization in clingo?

```clingo
% congruence
% generate using python probably.
eq(f(X,Y), f(X1,Y1)) :- term(f(X,Y)), term(f(X1,Y1)), % demand to avoid infinity
     eq(X,X1), eq(Y,Y1). 


eq(A,A) :- term(A). % reflexivity

%eq(f(A1,B), f(A,B)) :- term(f(A,B)), term(f(A1,B)), eq(A,A1). % subst
%tygfeq(f(A,B1), f(A,B)) :- term(f(A,B)), term(f(A,B1)), eq(B,B1).

eq(X,Y) :- eq(Y,X).
eq(X,Z) :- eq(X,Y), eq(Y,Z).

eq(f(a,a),a).
eq(a,b).
% convenience 
term(A) :- eq(A,_).

% however is there a non quadratic encoding?
% how to do everything modulo equality?
% foreign union find? Too fishy. The UF needs to be backtracked.

```

The information in a union find is not that big. There just aren't as many partitions as there are binary relations (2^(n^2)) power set of pairs. The number of partitions isn't that much bigger than 2^n
But can one find a fixed parametrization of partitions that embeds into asp?

root(a,b) doesn't work.

at most n partitions. Could order them by partition size. But that's still quadratic
How to identifty partitions? in a factored way?

### Bitvectors

Named bitvectors + extract function is good approach.
Sum of product form can be literall translated to rules.
`z = ab + ~cd`

```clingo
{a;b;c;d}.
z :- a,b.
z :- not c, d.
```

```clingo
%cnf no. something isn't right.  z <-> ab + ~cd 
{a;b;c;d;z}.
% {-a;-b;-c;-d;-z}.
e :- a,b.
e :- not c, d.
:- not z, e.
:- not e, z.
```

```clingo
{a;b}. %inputs
and(a,b) :- a,b.
or(a,b) :- a,b.
-a :- not a.
nand(a,b) :- not and(a,b).
nand1(a,b) :- not a.
nand1(a,b) :- not b.
xor :- a, not b.
xor :- not a, b.
eq :- a,b.
eq :- not a, not b.

% demand driven calculation of boolean expressions
bit(X;Y) :- bit(and(X,Y)).
and(X,Y) :- bit(and(X,Y)), X, Y.  
{X} :- input(X).

bit(X) :- bitvec(X,1).
bit(sel(X,I)) :- bitvec(X,N), I = 0..N. % bitblast
bitvec(X,N;Y,N) :- bitvec(and(X,Y), N).



```

Sat sweeping internal to asp?

```clingo

bitvec(a).
size(a,3).

bitvec(A) :- size(A,_).

bit(b1, 0).
:- bit(b0,0).

b11 = concat(b1, b1).
x0 = concat(b0,b0,b0,b0).

size(concat(A,B), N + M) :- size(A,N), size(B,M), bitvec(concat(A,B)).
%size(extract()) :- 

% equation on extract/concat

% bit blast. 
% { bit(A,0..N) } :- size(A,N).

% equal means bits are equal
bit(B,N) :- bit(A,N), eq(A,B).

% bit(bvadd(a,b), N) <-> bit(a)
% size(a,N)
% carry(a,b)


```

```clingo
{foo(0..3)}.
{bar(0..3)}.

foo(N) :- N = 0..3. %, (7 / (2 ** N)) mod 2 = 0.
-bar(N) :- N = 1..3.
bar(0).

% An adder circuit
carry(0).
add(N) :- foo(N), not bar(N), not carry(N).
add(N) :- not foo(N), bar(N), not carry(N).
add(N) :- not foo(N), not bar(N), carry(N).
add(N) :- foo(N), bar(N), carry(N).
carry(N+1) :- foo(N), bar(N), carry(N).

```

```


% bitwise operations are easy
and(N) :- foo(N), bar(N).

or(N) :- foo(N).
or(N) :- bar(N).

-neg(N) :- foo(N).

% hmmm.
{neg(0..4)}.
-neg(N) :- foo(N).
:- neg(N), foo(N)

% shifting
shift(N+1) :- foo(N), N < 4.

% 


```

### Theory of Arrays

Theory of arrays in clingo? Hmm.

```clingo
select(store(X,A,V), X, V).
```

A theory of sets is pretty cool

```clingo

elem(S, X) :- set(S), S = add(X,S1).
elem(S, X) :- set(S), S = union(S1,S2), elem(S1, X).
elem(S, X) :- set(S), S = union(S1,S2), elem(S2, X).
elem(S, X) :- set(S), S = inter(S1,S2), elem(S2, X), elem(S1,X).
elem(S, X) :- set(S), S = diff(S1,S2), elem(S1, X), neg elem(S2,X). %??? neg?

sub(S1 ,S2) :- elem(S1, X) : elem(S2, X).
eq(S1,S2) :- sub(S1,S2), sub(S2,S1).
```

### Difference Logic

In the datalog notes, I talk about how difference logic propagator is th same as shortest path.

### EPR

What about this one huh. Kind of interesting.
EPR and datalog are kind of related in that they both rely on something like finite herband universes for their termination/decidability.
The eager encoding of epr can be very bad though.

a(V) and e(V) for variables.

```clingo

; relation enumrating existential variables
e(x;y;z).

{rel(R, X, Y, Z)} :- rel(R,3), e(X), e(Y), e(Z).

{ Query_expr  }.

% hmm.
A :- and(A,B).
B :- and(A,B).
and(A,B) :- A,B.
rel(R, a)






```

## Junk

Questions:

- First class sets and reflecltion
- Lattice stuff. External union find? subsumption. Use aggregates? They can be recursive?
- parsing
- dominators and other forall. Bicycle problem
- context + zippers
- observational equality
- spanning tree and other choice domain problems
- topological sort
- shortest path
- rewriting
- program verificaion? well, planning is already bounded model checking.

```clingo
child(X,Y) :- parent(Y,X).
parent(ann,bob). parent(bob,carol). parent(bob,dan).
```

constants are larger than integers

```clingo
% p in model
p :- abracadabra > 7.
```

```clingo
% p not in model
p :- abracadabra < 7.
```

unsafe variable. Clingo throws error

```clingo
p(X) :- X > 7.
```

shorthand for multiple tuples

```clingo
p(1,2; 2,4; 4,8; 8,16).
```

Pick which to show and which to not

```clingo
p. p(a). p(a,b).
#show p/0. #show p/2.
```

`#const n=4` can also be done as `-c n 4` on command line
`#include` directives

Ranges are inclusive

```clingo
p(1..5). % analog of p(0). p(1). ... p(5).
```

remainder operator `\`

```clingo
#const n=10.
composite(N) :- N = 1..n, I = 2..N-1, N\I = 0.
prime(N) :- N=2..n, not composite(N).

```

Choice rules. pieces from the set. Cardniality constraints.

```clingo
#const n=4.
{p(X); q(X)} = 1 :- X = 1..n.
:- p(1). % model can't have p(1)
% :- not p(1). % model has to have p(1). Combo gives unsat
```

```clingo

{p(a);q(b)} = 1. ; p or q
```

`{p(a); p(b)} 1` is the same as `{p(a); p(b)}. :- p(a), q(b).` We could enumerate every subset that can't be and exclude them with constraint.
`1 {p(a); p(b)}` is the same as `{p(a); p(b)}. :- p(X), q(X).`

`:- f(X,Y1), f(X,Y2), Y1 != Y2.` expresses functional constraint. Same thing as `Y1 = Y2 :- f(X,Y1), f(X,Y2).`

Clingo makes auxiliary predicates instead of dummy variables for `_` interesting.

grounding time and solving time.
For slow ground: try enumerating better. symettry breaking. Rules with fewer variables.

Disjunction
Conditional Literals.
p :- q(X) : r(X).

# Constructs

There are a bunch of extra constructs that compile to extra variables and such. Many are in essence syntactic sugar.

## Integrity constraints

`:- a,b,c.`
gets translated to
`x :- a,b,c, not x.`

odd loop destroys model.

Negation in the head Is the same thing a flipped integrity constraint. Makes sense from a currying perspective
In intuitionistic logic `not a = (a -> void)`.
`not a :- b = (void :- a) :- b = void :- a,b.`

## Choice Rule

`{a}`
`{buy(corn); buy(chips)} :- at(grocery).`
even loop
`{a,b,c} :- foo`
give a name to body, but then also give a name to the things that can or can't be in the model (neg a basically).

```
body :- foo.
a :- body, not nega.
nega :- body, not a.
```

## Cardinality rules

introduce counter. This is the datalog method for summation. You don't need lattice / summation because you just need to check for the presence of the trigger
The greatest sum

upper bounds
`a :- {} u`
becomes

```
y :- u {}
a :- not y
```

### cardinality as heads

`l {stuff} u :- body`
becomes

```
x :- body
{stuff} :- x
y :- l {stuff} u
:- x, not y
```

A general trick is to name your bodies.

Weighted cardinality rules.
Having the counter go up by a weight isn't hard

```clingo
{foo(1..3)}.
bar(N) :- N = #count { N1: foo(N1)}.
```

This is amusingly conjunction in the head. Gringo doesn't really recognizes it as such though. So you're probably paying a lot of cost

```clingo
d.
{a;b;c} = 3 :- d.
```

## Conditional

{l : l1,l2,l3}
Could be seen as {l | l1, l2, l3}
Expansion is context dependent.
In head: disjunction (exists?)
In body: conjuction of elements.

Conditionals are related to `:-`

```clingo
bar.
foo : bar.
% foo :- bar. this is the same
{biz : bar}.
%{biz} :- bar. This is the same
```

Also relatedly a bounded forall quantification in the body.
It's more like a bounded existential quantification in the head.

Condition in the `{}` brackets vs not.

```clingo
bar(1..3).
biz(X) : bar(X). % this is a disjunctive rule
{foo(X) : bar(X)}.
baz :- X < 4 : bar(X).

```

is `#false : foo` the same thing as `neg foo`?

```clingo
foo.
% #false : foo.
% not foo.
```

How are conditionals expanded? I don't see them saying
q :- a(X) : l(X)
could possible be expanded to

```clingo
c(x1) :- not l(x1). % Is this okay? Yes.
c(x1) :- a(x1).
q :- c(x1).  % ... c(x2),c(x3),...
```

q :- c(x1),c(x1),c(x3),...

Stratified conditionals are not really a problem.

Maybe it's negation. forall X, l(X) -> a(X) ~ not exists X, l(X) /\ not a(X). classcially. But this has negation on a.
`q :- not (l(X), not a(X)).` Is monotonic for fixed l.

```clingo
l(x1).
-q :- l(X), not a(X). % q doesn't  
q :- not -q.
```

```clingo
{l(1..3)}.
{a(1..2)}.
q :- a(X) : l(X).
%q :- {a(X) : l(X)}.
:- not q.
```

Hmm. So adding brackets makes it do nothing with that rule. Is this an empty cardinality constraint?
No brackets is the conjunction of the rules.

`#false : p(X)` is an interesting construction. If there is any p(X), then the rule can't apply,

```
% gringo --text
{l(1)}.
{l(2)}.
{l(3)}.
{a(1)}.
{a(2)}.
q:-a(1):l(1);a(2):l(2);#false:l(3).
:-not q.
```

Ok, so this looks like it reduces it to an expansion. a(1):l(1) could be called c(1).

`#count {a(X), l(X)} = #count l(X)`

## Aggregates

`#count #sum #sum+ #min #max`

## Optimization

Directive
weights and priorities

## Disjunction

Disjunction is a weirdo.

```clingo
c.
a;b;d :- c.

% a,b,d :- c. same thing
% b. try this. Kills all the other models
```

Note that only models with exactly one of these are returned.

```clingo
c.
{a;b;d} :- c.
```

This program has all choices

```clingo
c.
1 {a;b;d} :- c.
```

This program has what I might consider the classical disjunction where at least one of them is true.

## Terms

```clingo
list(cons(a,cons(b,cons(c,cons(d,nil))))).
list(Xs) :- list(cons(X,Xs)).
```

In my experience, terms are _extremely_ useful for modelling.
Clingo also supports tuples.
That clingo has structured data is huge compared to minizinc.

## Functions

Clingo can call extrnal functins defined in python or lua using `@`

```clingo


```

```clingo
#script (python).
import clingo

def inspect(a):
    print(dir(a))
    return a

def concat(a, b):
    return clingo.String(a.string + b.string)

# convenient method to build cons lists
# in other words, using python we can support varargs
def mylist(*args):
    if len(args) == 0:
        return clingo.Function("nil",[])
    else:
        return clingo.Function("cons", [args[0], mylist(*args[1:])])
#end.

foo(@concat("bar", "biz")).
foo(@inspect(bar(biz,2))).
foo(@mylist(1,2,3,4,5,6)).
```

Another interesting thing. Extralogical generic functions like prolog `=..` or `functor` <https://www.swi-prolog.org/pldoc/man?predicate=functor/3>

```clingo
#script (python).
def functor(x):
  assert isinstance(x, clingo.Function)
  return clingo.Function(self.?, [])

def arity(x):
  assert isinstance(x, clingo.Function)
  return clingo.Number(len(self.args))

def arg(x,n):
  assert isinstance(x, clingo.Function)
  return x.args[n]

def subst(t,x,y):
  pass

def maplist(f,*ls):
  pass # hmm. Can I do this?
#end.




```

## Theories

There are external theories available. In particular for difference logic and linear programming.
Also you can make your own
[theory solving slides](https://teaching.potassco.org/tsolving/)

<https://github.com/potassco/clingoLP> linear programming
<https://github.com/potassco/clingo-dl> difference logic

```clingo
{a}.
&diff {x-y} <= -3 :- a.
```

```clingo

#theory mytheory {
    &flum/0 : any,
}.
```

- clingcon
- aspartame
- adsolver
- aspmt, dlvhex, ezcsp, gasp, inca

## Other

`%* *%` multiline comments
asp-core-2 languague
aspif intermdiate language

# true #false

# sup #inf useful for aggregates (min max of empty set)

double negation - doesn't have to vbe proven

`#external` atom

# Theory

## Stable Models

Stable models = well-founded model + branching

## Unfounded Sets

[Using Unfounded Sets for Computing Answer Sets of Programs with Recursive Aggregates](https://www.mat.unical.it/~alviano/archives/publications/2007/cilc07-recAggr.pdf)

Is there a relation with non-well-founded sets (aczel)? A nested set-like model. Maybe each atom is a set?

## Non Monotonic Reasoning

<https://en.wikipedia.org/wiki/Negation_as_failure>
<https://en.wikipedia.org/wiki/Autoepistemic_logic>
<https://en.wikipedia.org/wiki/Default_logic>
<https://en.wikipedia.org/wiki/Stable_model_semantics>
<https://en.wikipedia.org/wiki/Nonmonotonic_logic>
<https://en.wikipedia.org/wiki/Circumscription_(logic)>

Monotonic means that adding a fact or axioms only increases the theorems derived.
Non-monotonic means this is not true. Negation as failure means

<https://en.wikipedia.org/wiki/Closed-world_assumption> Closed world assumption. It's something like there are no rules we don't know of. Our set of rules is complete. Hence if we fail to derive something via the rules we have, it is false.
Other interesting assumptions: unique name assumption (things with distinct names are not equal). closed domain assumption (only elements that are named exist).

stable models are not unique
in prolog multiple model program do not terminate

wellfounded semantics - true,false, unkown. If atom in wellfounded model it is true in every stable model. upper bound on union and lower bound on interesection. Unique well founded model?

classical interpretation of prolog rules has way too many models.
completion of logic program - :- becoms if and only if <->
This still has too many models.
There are things there that are only self proving like `e :- e`
Loop formula block these out

True false prpagation
Known true atom set and known false atom set

## Logic of here and there

A two world kripke model. One of possibly true and one definitely true.

Satisfaction relationship.

Equilibrium logic

## Operational

The consequence operator is famiiar from datalog. We make an expanding databas of known facts by applying the rules.
We can also however note when facts cannot be possible be derived.
The Fitting operator does this.
Phi(T,F) = using rules who fit known true and known false
F(<t,f>) = {a | }
You know a fact can't be derived when no rule which has it as a head is fireable anymore.

The well-founded operator adds the extra derivations that circular proofs are disallowed. If the only rules that could derive facts are circular and all their support is known false, then these circular facts are also false.

Can I make an asp system automatically produce well-founded or fitting fixed points instead of stable models? I think this might be what the brave and cautious modes do. They converge the the known true and the compement of known true for the well-founded operator.

The fixed point of the operators typically does not converge such that the known true and known false sets cover the whole space.

foo() :- pos(), pos(), neg(), neg()
// all atoms from program. one generator for eac argument of foo.
notfoo() :- atom(x), atom(y), atom(z), { notpos() ; notpos() ; neg(); neg() }
The result of this datalog program is an underapproximation of foo and notfoo. Stable models do not include any atoms of notfoo and must have all atoms in foo.
If you then branch on one of the remaining choices, you can allow propagation to proceed. I guess until notfoo U foo cover all possible atoms.

Upper bounding operator keep foo rule above. replace notfoo where you just ignore negs of rule. This results in a smaller notfoo. In fact this doesn't fepend on the true set at all?
notfoo() :-  atom(x), atom(y), atom(z), { notpos() ; notpos() }
So this will make a large foo. foo overapproximates, notfoo underapproximates.

What about base facts, and then do completion modulo basefacts
basefoo()
foo :- basefoo().
foo() :- bar, biz, foo, yada
bar,biz,foo  :- foo, !basefoo()

nogood is a set of entries expressing that any solution containing is inadmissble

## Tableau / Proof

<https://teaching.potassco.org/pcharacterization/>

## Justification

## Completion

Completion is methology to translate logic programs into more traditional logic. This is useful if you want to reuse other systems or metatheory.
We know that `:-` is implication in some sense. The thing is, if you directly translate your rules to classical logic using this correpondence, the resulting axioms are too loose. A classical solver is free to _overapproximate_. For example, a positive logic program interpreted this way always has a model where everything is true. This isn't what we want.
This is related to the confusing notion that the transitive closure of a relation is not shallowly embeddable in first order logic with finite axioms, despite the path axioms sure looking like they do it.

Logic programming is usually about the _least_ model.
It also is a closed world. This means that if something is true, it must be the head of at least one true body.

To axiomatize this, collect up every rule with the same head by or-ing the possible bodies. Turn the implication into a bi-implication.

There is still a problem though in regards to loops.
Loop-formula require that every loop is supported from the outside.

# Solving

## Grounding

take every rule
Naive grounding, just expand every varable with every possible value in the program.
bottom up grounding
arithemtic predicates X < X' is good for reducing redudnant grounds. All ground terms are totally ordered.

Dependncy if head unfifies with fact in body. Hmm. Interesting.
seminaive grounding
simplification
straitfied programs are solved by the grounder
top down grounding?

atoms are found to be true, possible, and false

gringo --text mode shows grounded program

[On the Semantics of Gringo](https://www.cs.utexas.edu/~vl/papers/gringo.pdf) Some propsitional rewrites of some of the rules

Grounding is a compelling idea. There are two pieces to an ASP system, the grounder and solver. The grounder is a datalog that takes ordinary quantified rules `foo(X) :- bar(X)`  and produces an overapproximation of their possible ground instances `foo(a) :- bar(a). foo(b) :- bar(b) ...` . For every new rule that applies (and possibly produces something new I think), it outputs one line into a file. I think this aspif file is a very natural proof format for datalog. You can basically build provenance by traversing the file upwards. Building a checker that such a file is a valid datalog run is much simpler than building a performant datalog.

In other words, a grounder converts a datalog program into much bigger one that only has grounded rules. And it produces these grounded rules in the order they can be derived. Hence the heads of the ground rules are the facts in the database and the bodies are information about which rule and facts produced that head.

And that is basically the information that provenance needs. It is also basically a trace of the datalog execution, short circuiting out the difficulties of actually performing the body queries.

## Solver

Branching
Conflict directed No good learning
Conequence operator
X = Cn(P^X)

SAT solving liek
Constraint processing

Propagate upper and lower bound.
Branch if they don't meet.
smodels
Each node in search tree is a 3 valued intepretation

Checking a stable model is easy
Finding oone is hard.
Interesint
disjunctive logic programs are harder. They bump up the complexity. Hmm

Completion. One of the rules must have applied
sufficient and necessary
Closed world is that
every stable model is model of compketion. supported models
e :- e is a problem
cycles are the problem (well founded prof trees)
Fages theorem - compltion of loop free formulas are stable models
loops and loop formulas

external support of loops.
if atom is true, loop must be supported
Lin-Zhao theorem - loop formula + completion is stable formula

Fitting operator puts stuff in false when no rules could possibl produce it anymore
Partial interpretations
unfoundd set - a set is unfounded with respect to current T,F pair. If there is no rule that can produce it without using something in the set
sacca-zaniola theorem - model of rules, no unfounded subsets of model
Lee's theorem. Model of compltetion and no unfounded loops
Greatest unfounded set
well founded operator - fitting oprtsyot + things that are not supported fo into the false set
Well founded is stronger than fitting.
partial interpretations and well founded models
backward propagation

Solving
Nogoods - an assignmnt that cannot be extended to a model
bodies and atoms are (partially) assigned truth values

ASP is so powerful.
I could possibly write a version of contextual datalog here?
Map into Z3 using explicit justification
Non-sautrating ASP. Is this ok? Kind of feels like it isn't

Open vs Closed world - what does this mean really.

# Systems

Clingo
smodels - original. Branching + propagation?
ASSAT - encoding to sat

# API

Pyhton and Lua can be done inline

```clingo
#script (python).
print("hello world")
#end.

```

## Lua

There is inline lua for writing propagators and control. That's pretty neat.
<https://potassco.org/clingo/run/?example=pigeonator-propagator.lp>

## Python

<https://potassco.org/clingo/python-api/5.6/>

```python
import clingo
print(clingo.__version__)
from clingo import *
ctl = clingo.Control()

one = clingo.Number(1)
clingo.String("foo")
print(parse_term("q(1,2,3)"))
parse_program("q(X) :- p(X).", lambda prg: print(prg))
p = clingo.Function("p", [one], positive=True)
print(p)

```

```python
import clingo
ctl = clingo.Control()
ctl.add("p", ["t"], "q(t).")
parts = []
parts.append(("p", [clingo.Number(1)]))
parts.append(("p", [clingo.Number(2)]))
ctl.ground(parts)
ctl.solve(on_model=lambda m: print("Answer: {}".format(m)))
```

### nqueens

```clingo
#const n=4.
{q(1..n,1..n)} = n.
% These are all possible atoms. "generation"

```

Clingo options --help:

- enum-mode
- projective solution enumeration
- `--models 10` compute at most 10 models
- opt-mode, find opt, enumate optimal, enum below bound, set known initial bound
- paralel mode `-t` number of threads. compete and split mode
- --const replace const with whatever
- print simplified program
- verbose
- help=3 gives more options
- --warn

nogoods
loops

gringo is the grounder
clasp is the solver - very SAT solver sounding. The options in help=3 talk about random restarts, glucose,

Is ASP an ackermannization stage kind of followed by SAT/CSP? Datalog followed by SAT/CSP? How intertwined are the stages?

Hmm. All constraints are encodable to

Grounding with datalog?
Ackermanizing in clingo?

# Easy Answer Set Programming

[easy answer set programming](https://www.youtube.com/watch?v=kDjmqycSy_o&list=PL7DBaibuDD9O4I05DiQfilqPUgpClMKYu&index=2&ab_channel=Potassco) [https://arxiv.org/abs/2111.06366](https://arxiv.org/abs/2111.06366)
While ASP is usually introduced by talking about negation, negation is a complicated topic. If instead we take choice `{q}` as primitive, you can talk about a lot of stuff in a more easily understood style. It is a world branching datalog execution then.

```clingo
{a}.
b :- a.
:- not b.
```

"In order". Non recursive answer set programs are _still_ interesting. They are a set description language.
You can run right down them. Go in topological order of appearance in heads / bodies

```clingo
{a}.
b :- a.
{c} :- not a.
```

Hmm. So backtracking search is still necessary for non recusrive?

```clingo
n(1).
{a(X)}:- n(X).
b(X) :- a(X).
:- n(X), not b(X).

```

Generate and test. Describe the space first. Then add implications, Then constraints.

For positive recursive rules, it is nondeterministic guessing of choice rules, and then running datalog to execution

```clingo
{a}.
b :- c.
c :- a.
a :- b.

```

```clingo
{a}.
{b} :- c.
{c} :- a.
{a} :- b.

```

Circumspection, autoepistemic
Stable Models = Well-founded + branch

No goods- constraints that can't hold. Leanred clauses?
set of true atoms as the model

The oracle guess Y. evaluate `not` with respect to this guess. The rest of the rules evaluate

Reduct, removes the guess from the rules,
fix(P^X) = X. Stable mdels are olutions to this equation
Datalog can be used to confirm a guess, or propagate a partial guess. The P time check of a guess makes it NP
Each atom in model has justificagion in _reduct_
It is stabe model of reduct

```clingo
a.
b :- a, not c.
c :- b.
```

ASP is datalog with a prophetic negation
ASP is datalog + branching (to deal with ) into multiple universes

non monotnic. Adding a c fact doesn't just increase the model. It makes a totally incomparable model

```clingo
a :- not c.
%c. 

```

Only 1 is possible

```clingo
b :- not a.
a :- not b.
```

One of these possibilities.

```clingo
b :- not a, not c.
a :- not b, not c.
c :- not a, not b.
```

So you can compile {x} into

```clingo
x :- not notx.
notx :- not x.
```

# Misc

[Stable model semantics mnikanren](http://minikanren.org/workshop/2023/minikanren23-final3.pdf)

[clinguin](https://github.com/potassco/clinguin) specify a gui in asp

```clingo
talk(X) :- people(X). % people talk in both worlds
-talk(X) :- non_human_animal(X), rw. % non human animals do not talk in rw
talk(X) :- human_like_cc(X), cw. % human-like cartoon char can talk in cw
swim(X) :- fish(X). % fish swim in both worlds
non_human_animal(X) :- fish(X), rw. % fish is a non-human-animal in rw
human_like_cc(nemo) :- cw. % Nemo is a human-like cartoon char in cw
fish(nemo). % Nemo is a fish in both worlds
cw :- not rw. % cw and rw are two separate worlds
rw :- not cw.

```

Facts, rules, disjuntion, integrity, conditions, choice, aggregate, multiobjective optimization, weak integrity constraints

Safety - a rule is safe if all variables occur in positive body
Grounding outputs rules and possibly true atoms.
An overapproximation of atoms

elaboration tolerance

Union, Intersevtion, projection of models

<https://arxiv.org/html/2208.02685v1/#rprlif19> iclp 2022
[Transforming Gringo Rules into Formulas in a Natural Way](https://arxiv.org/html/2208.02685v1/#EPTCS364.13) translating gringo into First order logic

[Verifying Tight Logic Programs with anthem and vampire](https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/verifying-tight-logic-programs-with-anthem-and-vampire/F8EDF1CABBEC7B5AC369B51D8BF90F7D) - using vampire to solveasp problems?

[Transforming Gringo Rules into Formulas in a Natural Way](https://link.springer.com/chapter/10.1007/978-3-030-75775-5_28)

[How to build your own ASP-based system ?!](https://arxiv.org/pdf/2008.06692.pdf)

[Arntzenius disccision](https://twitter.com/arntzenius/status/1264570390849949696?s=20&t=5y91-I1SPrIGomAWSqs69w) "How are Datalog, SAT/SMT, and answer set programming related? Is ASP basically the generalisation of SAT to first order logic, plus recursion? And Datalog restricts ASP to Horn clauses and stratified recursion?

<https://en.wikipedia.org/wiki/Answer_set_programming>

[transpiling PCF to ASP](https://arxiv.org/pdf/1808.07770.pdf)
[temporal answer set programming](https://deepai.org/publication/temporal-answer-set-programming) TELINGO
[Potassco, the Potsdam Answer Set Solving Collection](https://potassco.org/)

[Possivbe worlds explorer](https://github.com/idaks/PW-explorer) demos <https://github.com/idaks/PWE-demos> . Qlearning? Sure. <https://ischool.illinois.edu/people/bertram-ludascher> datalog debugging. Prevoenance.
[martens Generating Explorable Narrative Spaces with Answer Set Programming](https://drive.google.com/file/d/1CKDOsT9FIGW3SNyW5u5heIxbx_ZLCAP5/view)

[Alviano, M., Faber, W., Greco, G., and Leone, N. 2012. Magic Sets for Disjunctive Datalog Programs](https://arxiv.org/abs/1204.6346)
Clingo
dlv2 maybe <https://dlv.demacs.unical.it/>
[wasp](https://github.com/alviano/wasp)
[embasp](https://embasp.readthedocs.io/en/latest/index.html) <https://github.com/DeMaCS-UNICAL/EmbASP>
dlvhex <http://www.kr.tuwien.ac.at/research/systems/dlvhex/>

[seventh answer set competition](https://arxiv.org/pdf/1904.09134.pdf)
[lifschitz prgraming with clingo short 35 page](https://www.cs.utexas.edu/~vl/teaching/378/pwc.pdf)
[liftshift asp book 198pg](https://www.cs.utexas.edu/users/vl/teaching/378/ASP.pdf)
Disjunctive logic programming

Grounding - Figure out the term universe?
semi naive grounding.
So answer set programming runs datalog, and then ?

Hmm. This is datalog + csp. This is what i wanted to build a compiler end to end.

stable models - smallest of models?
[13 definitions of a stable model](https://www.cs.utexas.edu/users/vl/papers/13defs.pdf)
well founded
stable = well-founded + branch

[what is answer set programming](https://www.cs.utexas.edu/users/vl/papers/wiasp.pdf)
[answer set programming in a nutshell](https://www.youtube.com/watch?v=m_YuE2E_bck&ab_channel=SimonsInstitute)
loop formulas
`p :- q(X) : r(X)` conditional literals
stronger than sat?
`:- q(X), p(X).` integrity constraints.
`p(x); q(X):- r(X)` disjunction
smt infrastructure, but theory is asp specific?
modeling + grounding + solving

metaprogramming - intriguing

[applications of answer set programming](https://www.youtube.com/watch?v=i5dARGZmuIU&ab_channel=AutumnSchoolonLogicandConstraintProgramming)

huh clingo supports lua programs. That's intriuging. I was considerig doing that to souffle

Alviano, M., Faber, W., Greco, G., & Leone, N. (2012). Magic sets for disjunctive Datalog programs

[ASP-core2 standard](https://www.mat.unical.it/aspcomp2013/files/ASP-CORE-2.03c.pdf)

```clingo
innocent(Suspect) :- motive(Suspect), not guilty(Suspect).
motive(harry).
motive(sally).
guilty(harry).
```

There is "constructive character". negation as failure. not guilty is assumed to hold unless is has to . This is innocent until proven guilty? Hmm. That's a fun constructive example. In the eyes of the law innocent = unknown and known guilty.
This example is also valid stratified datalog.

```clingo
% instance
eagle(eddy).
penguin(tux).

% encoding
 fly(X) :- bird(X), not -fly(X).
-fly(X) :- penguin(X).
bird(X) :- penguin(X).
bird(X) :- eagle(X).
```

Hmm. Explicit negation predicate.

```clingo
% This is unsat. :- p, -p. is there by default
-p.
p.
```

brave vs cautious modes? What the hell is that. <https://stackoverflow.com/questions/55675488/brave-cautious-reasoning-in-clingo> enumration modes. Non total. They converge towards minimal or maximal model?

[Beyond version solving: implementing general package solvers w Answer Set Programming Todd Gamblin](https://www.youtube.com/watch?v=bkY9mOyUaDA&ab_channel=PackagingCon)

[Answer set programming (ASP) is the powerhouse technology you’ve never heard of](https://twitter.com/mgrnbrg/status/1589652522180153344?s=20&t=JfnzTQG-SeFdO1qYUwKkrw) <http://www.weaselhat.com/2022/11/07/asp/>
Datalog provenance is explanations. Can be used as a monotonic theory in SMT search.

[Potassco Guide](https://github.com/potassco/guide/releases/)

[Comments on ASP](https://news.ycombinator.com/item?id=34071325)
[Automating Commonsense Reasoning with ASP and s(CASP)*](https://personal.utdallas.edu/~gupta/csr-scasp.pdf)
Constraints. Default rules. 5 truth values for p, not -p, not p not -p, not p, -p

[Potsdam publication list](https://www.cs.uni-potsdam.de/wv/publications/#DBLP:journals/ai/GebserKS12)

[answer set planning a survey](https://www.cs.uni-potsdam.de/wv/publications/DBLP_journals/corr/abs-2202-05793.pdf)

[clingraph](https://github.com/potassco/clingraph) generate graphics from clingo problem. Brilliant

[anthem](https://github.com/potassco/anthem) translates clingo files to first order provers. What encoding? [Verifying Tight Logic Programs with anthem and vampire](https://arxiv.org/pdf/2008.02025.pdf)

[embasp](https://www.mat.unical.it/calimeri/projects/embasp/)
[idlv](https://github.com/DeMaCS-UNICAL/I-DLV)
[dlv](https://dlv.demacs.unical.it/)

[asp-core 2](https://www.mat.unical.it/aspcomp2013/files/ASP-CORE-2.03c.pdf)

[eclingo](https://www.cs.uni-potsdam.de/wv/publications/DBLP_journals/corr/abs-2008-02018.pdf) modal operators for all worlds reasoning

[asp tools](https://research.ics.aalto.fi/software/asp/)

- [lp2normal](https://research.ics.aalto.fi/software/asp/lp2normal/) This tool transforms an smodels program into a normal logic program by translating away extended rule types (choice rules, cardinality rules, and weight rules).
- [lp2sat](http://www.tcs.hut.fi/Software/lp2sat/)

CIRC2LP: Translating circumscription to disjunctive logic programming
DINGO: Extending ASP with difference constraints
GnT: A solver for disjunctive logic programs
LP2ACYC: Implementing ASP via SAT modulo acyclicity
LP2BV: Translating normal/smodels programs for SMT (bit vector) solvers
LP2DIFF: Translating normal/smodels programs for SMT (difference logic) solvers
LP2NORMAL: Translating smodels programs into normal programs
LP2SAT: Translating normal/smodels programs for SAT solvers
LPEQ: Verifying the equivalence of logic programs
MINGO: Extending ASP with linear constraints over integers
MINGOR: Extending ASP with linear constraints over reals
Miscellaneous tools for ASP
Modularity support for answer set programming
SATEQ: Verifying the equivalence of sets of clauses
SMODELS: A solver for normal logic programs extended by cardinality/weight constraints and Boolean optimization

LP2mip

[lp2pb](https://github.com/wulfdewolf/lp2pb) translate grounded rules to opb pseudoboolean models

[hakank's asp](http://www.hakank.org/answer_set_programming/)

[interesting discussion](https://swi-prolog.discourse.group/t/non-monotonicity-defeasibility-strategies-and-other-stuff/6038/15)

[hard string problems encoded to answer set programming](https://drops.dagstuhl.de/opus/volltexte/2023/17953/pdf/lipics-vol259-cpm2023-complete.pdf#page=309)
