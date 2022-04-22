---
author: philzook58
comments: true
date: 2020-09-22 15:37:08+00:00
layout: post
slug: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution
title: Prolog
wordpress_id: 1865
---

- [Systems](#systems)
- [History](#history)
  - [Ciao](#ciao)
- [Examples](#examples)
  - [Things that are prolog](#things-that-are-prolog)
    - [Hello World](#hello-world)
  - [Lists](#lists)
  - [Difference Lists](#difference-lists)
  - [Rewriting in prolog](#rewriting-in-prolog)
- [Topics](#topics)
  - [SLD resolution](#sld-resolution)
  - [Interesting predicates](#interesting-predicates)
  - [Imperative analogies](#imperative-analogies)
  - [Abstract Machines / Implementation](#abstract-machines--implementation)
  - [Modes](#modes)
  - [Verification](#verification)
  - [Modules](#modules)
  - [meta circular interpreters](#meta-circular-interpreters)
  - [Delimitted Continuations](#delimitted-continuations)
  - [Tabling](#tabling)
  - [Attributed Variables](#attributed-variables)
  - [Constraint Logic Programming (CLP)](#constraint-logic-programming-clp)
    - [Prolog II, III IV.](#prolog-ii-iii-iv)
  - [Parallel](#parallel)
  - [Coroutines](#coroutines)
  - [DCG - Definite Clauses Grammars (DCG)](#dcg---definite-clauses-grammars-dcg)
  - [CHR](#chr)
      - [Basics](#basics)
      - [Pairing](#pairing)
      - [Paths from edges](#paths-from-edges)
      - [Minimum](#minimum)
      - [GCD](#gcd)
      - [Sort](#sort)
      - [Get foo](#get-foo)
      - [Fibonacci](#fibonacci)
      - [Boolean Propagators](#boolean-propagators)
      - [Lattice](#lattice)
      - [Assignment](#assignment)
      - [EGraphs](#egraphs)
    - [Compiling](#compiling)
    - [Embedding into CHR](#embedding-into-chr)
  - [Answer Set Programming s(CASP)](#answer-set-programming-scasp)
  - [Extral(ogical features](#extralogical-features)
  - [Lambda](#lambda)
- [Semantics](#semantics)
- [Expert Systems](#expert-systems)
- [Lambda Prolog](#lambda-prolog)
    - [HO Unification](#ho-unification)
  - [LF](#lf)
    - [Twelf](#twelf)
  - [Rust Chalk Harrop](#rust-chalk-harrop)
- [LogTalk](#logtalk)
- [Linear Logic Programming](#linear-logic-programming)
- [Coinductive Logic Programming](#coinductive-logic-programming)
- [inductive logic programmingh](#inductive-logic-programmingh)
- [Theorem Proving](#theorem-proving)
    - [Stuff](#stuff)
  - [2019](#2019)
  - [Notes from 2017 -Resolution and unification](#notes-from-2017--resolution-and-unification)

See also:
- Datalog
- Constrained Horn Clauses
- Constraint Programming (Answer Set programming in particular)

# Systems
[50 years of prolog](https://arxiv.org/pdf/2201.10816.pdf)

- Swi prolog - I think this is a good default choice.
- [ciao](http://ciao-lang.org/)
- [sicstus](https://sicstus.sics.se/) requires commercial license [manual](https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/index.html)
- gnu prolog
- [scryrer](https://github.com/mthom/scryer-prolog)
- tau prolog - javascript web enabled
- hprolog
- binprolog
- XSB - fancy tabling. 
- YAP
- B-prolog
- ECLiPSe - can talk to minizinc
- Qu-prolog


Relatives:
- Minikanren
- minizinc
- picat
- Mercury - mode declarations and type declarations. Allows reordering, but deals with IO using lionear types?
- Curry - Haskell syntax like language.
- Lambda prolog - teyjus, elpi, makam
- Hilog
- Godel
- Hyprolog - abduction
- ergo AI, flora2
- guan https://github.com/microsoft/Guan c# prolog?


## Ciao
[ciao manual](http://ciao-lang.org/ciao/build/doc/ciao.html/ciaofulltoc.html)

```ciao
main(_) :- format("hellow world").
```

```ciao
main(_) :- print([1,2,3]),
  append(A,A,A), print(A)
.
```

[assertions and auto documetation](http://ciao-lang.org/ciao/build/doc/ciao.html/AssrtLang.html)
[ciao and design philosphy](http://cliplab.org/papers/hermenegildo11:ciao-design-tplp.pdf)
ciaopp - preprocessor and veirfier? PLAI

# Examples
## Hello World

```prolog
:- initialization(main,main).
main(_) :- format("hello world ~p\n", [foo(8)]).
```

## Things that are prolog
- Typeclasses
- Inductive data types
- Inference rules
- CSS?


## Lists
```prolog
append([], X, X).
append([H | X], Y, [H | Z]) :- append(X, Y, Z).
```
## Difference Lists
## Rewriting in prolog



# Topics
## SLD resolution


## Interesting predicates
[comparson and unification of terms](https://www.swi-prolog.org/pldoc/man?section=compare)
`=@=`
`==`
`=`
`/=` a weaker version of dif. Uses negation as fialure in kind of unsatisfactory way

`=..` destructures a term

## Imperative analogies
Unification variables are pointers. Unifying them is aliasing them.
Unification is bidirectional pattern matching





## Abstract Machines / Implementation
[Warren's Abstract Machine: A Tutorial Reconstruction.](http://wambook.sourceforge.net/wambook.pdf)


Paul Tarau showing an interesting compilation strategy. <https://popl21.sigplan.org/details/PADL-2021-papers/5/A-Family-of-Unification-oblivious-Program-Transformations-and-Their-Applications>
<https://github.com/ptarau/LogicTransformers>

binprolog. Translate to binary relations

structure copying vs structure sharing

Term indexing

Original Dec-10 prolog paper


## Modes
In some ideal world, it's great if every predicate is reversible, but it isn't the case. Different variable positions can be used in different ways, input, output, both. They can also have total functional character (exactly one answer), partial functional character (one or zero), of nondeterminisitc (many answers). 
Modes are required to use predicates correctly. Annotating them may allow the compiler to be more efficient. The compiler may infer them. They are conceptually interesting also in theorem proving contexts. See bidirectional typing.


mercury
ciao prolog

## Verification

## Modules



## meta circular interpreters

[power of prolog - A Couple of Meta-interpreters in Prolog](https://www.metalevel.at/acomip/)


[metapredicates](https://www.metalevel.at/prolog/metapredicates#call)
`call/N` in principle could be implemented in prolog itself.

```prolog
:- initialization(main,main).
foo(7).
main(_) :- call(foo(X)), print(X).
```

## Delimitted Continuations
Continuations are a reification of a call stack. The call stack in prolog is a goal stack.
When you 

[swipl manual entry](https://www.swi-prolog.org/pldoc/man?section=delcont)
[schrivers et al](https://www.swi-prolog.org/download/publications/iclp2013.pdf)

- effect handlers - implicit state
- definite clause grammars
- coroutines

## Tabling
[Tabling as a Library with Delimited Control](https://biblio.ugent.be/publication/6880648/file/6885145.pdf)
[Swi prolog manual](https://www.swi-prolog.org/pldoc/man?section=tabling)

```prolog
:- table path/2.
edge(1,2).
edge(2,3).
edge(3,1).
edge(3,4).

path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).

:- initialization(main,main).
main(_) :- path(1,4).
```

```prolog
:- use_module(library(tabling)).
:- table a/0.

a :- a.
```

Hmm. Tabling comes _from_ earley parsing historically. That's interesting.

tabling and packrat parsing [DCGs + Memoing = Packrat Parsing But is it worth it?](https://mercurylang.org/documentation/papers/packrat.pdf)
tabling vs memoing

## Attributed Variables
Attaching extra info to variables. This can be be used to implement CLP as a library

## Constraint Logic Programming (CLP)
- CLP(B) - constraint over boolean variables. Sometimes bdd based
- CLP(FD)
- CLP(Z)

[Anne Ogborn's tutorial](https://github.com/Anniepoo/swiplclpfd)

[Indexing dif/2](https://arxiv.org/abs/1607.01590)
`reif` `if_/` `tfilter/3`


eclipse talks to minizinc?
[clp examples](https://swish.swi-prolog.org/example/examples.swinb)

### Prolog II, III IV.
Cyclic terms. Rational terms. See Condicutive logic programming
[swi prolog comments on rational trees](https://www.swi-prolog.org/pldoc/man?section=cyclic)

[introduction to prolog III](https://www.researchgate.net/publication/220427862_Introduction_to_prolog_III)
[prolog and infinite trees](http://www.softwarepreservation.org/projects/prolog/marseille/doc/Colmerauer-InfTree-1982.pdf)

## Parallel 
https://en.wikipedia.org/wiki/Parlog
50 years of datalog talks about stuff.


## Coroutines
[swi manual](https://www.swi-prolog.org/pldoc/man?section=coroutining)
- `dif/2` ? Test is delyed until terms are sfufcient different or have become identical
- `freeze/2` - equivalent to call is Var is bound
frozen
when
call_residue_vars

delay
[block](https://www.swi-prolog.org/pldoc/doc_for?object=block_directive%3A(block)/1)

## DCG - Definite Clauses Grammars (DCG)

[Anne Ogborn tutorial](https://github.com/Anniepoo/swipldcgtut)
[hakank picat](https://twitter.com/hakankj/status/1508321812261871616?s=20&t=-ertSPtY87GogVCFq4f-Rw)

## CHR
[forward chaining, chr comes up](https://swi-prolog.discourse.group/t/forward-chaining-like-rete-algorithm-in-rule-engine/5137/28)

[swipl manual section](https://www.swi-prolog.org/pldoc/man?section=chr)
[Anne Ogborn's tutorial](https://github.com/Anniepoo/swiplchrtut)
[Schrijver's ICLP tutorial](https://dtai.cs.kuleuven.be/CHR/files/tutorial_iclp2008.pdf)

Constraint handling rules
A question I never had an answer for https://twitter.com/notjfmc/status/1422215450675535877?s=20&t=RyHMtBS3ySaALLC9MuGmUA . CHR afaik are a way of integrating eager rewriting into prolog https://en.wikipedia.org/wiki/Constraint_Handling_Rules 

I'm not sure this is even persay a prolog topic. But the prolog community is the most engaged

http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html
[chr.js](https://github.com/fnogatz/CHR.js/)
[chr what else](https://arxiv.org/pdf/1701.02668.pdf)



[Where is the CHR constraint store?](https://stackoverflow.com/questions/59234770/constraint-handling-rules-in-swi-prolog-does-the-constraint-store-exists-only?rq=1)

[Some cool examples](https://dtai.cs.kuleuven.be/CHR/examples.shtml). Gaussian, fourier, rational trees, equation solvers

https://github.com/brog45/chrplay


compiler to sql statements. Makes sense.
Multiset rewriting?

[sql](https://github.com/awto/chr2sql)
Man what hope is there of compiling a 7 year old haskell project?

[cchr](https://github.com/nickmain/cchr) efficient implementation in C

[yihong's egraph in chr. awesome](https://github.com/yihozhang/cchr/blob/master/experiment/egraph.cchr)

[chr parsing](https://stackoverflow.com/questions/65647409/parsing-with-chr-constraint-handling-rules)

[parallel chr](https://github.com/KaiSta/Parallel_CHR)

CHR parsing
“Analysing graph transformation systems through Constraint Handling Rules” by Frank Raiser and Thom Frühwirth
“As time goes by: Constraint Handling Rules — A survey of CHR research from 1998 to 2007” by Jon Sneyers, Peter Van Weert, Tom Schrijvers and Leslie De Koninck


https://stackoverflow.com/questions/67771845/prolog-get-a-list-of-all-the-rules-an-entity-verifies
```prolog
:- use_module(library(chr)).

:- chr_constraint snore/1, sleep/1, breathe/1.
:- chr_constraint eat/1, live/1, rest/1, collect/2, pull/2.

snore(X) ==> breathe(X).
snore(X) ==> sleep(X).
sleep(X) ==> rest(X).

breathe(X) ==> live(X).
eat(X)     ==> live(X).
sleep(X)   ==> live(X).

live(X) \ live(X) <=> true.  % eliminates duplicates

collect(Who,L),snore(Who)   <=> collect(Who,[snore|L]).
collect(Who,L),sleep(Who)   <=> collect(Who,[sleep|L]).
collect(Who,L),breathe(Who) <=> collect(Who,[breathe|L]).
collect(Who,L),eat(Who)     <=> collect(Who,[eat|L]).
collect(Who,L),live(Who)    <=> collect(Who,[live|L]).
collect(Who,L),rest(Who)    <=> collect(Who,[rest|L]).

pull(Who,L) \ collect(Who2,L2) <=> Who = Who2, L = L2.
```

[sicstus examples](https://sicstus.sics.se/sicstus/docs/4.2.0/html/sicstus/CHR-Examples.html#CHR-Examples)
[swi examples](https://www.swi-prolog.org/pldoc/man?section=chr-examples)
```prolog

:- module(leq,[leq/2]).
:- use_module(library(chr)).

:- chr_constraint leq/2.
reflexivity  @ leq(X,X) <=> true.
antisymmetry @ leq(X,Y), leq(Y,X) <=> X = Y.
idempotence  @ leq(X,Y) \ leq(X,Y) <=> true.
transitivity @ leq(X,Y), leq(Y,Z) ==> leq(X,Z).
/*
?- leq(X,Y), leq(Y,Z).
leq(X, Z),
leq(Y, Z),
leq(X, Y).
*/
```

finite domain solver. 
```prolog
:- module(dom,[dom/2]).
:- use_module(library(chr)).

:- chr_constraint dom(?int,+list(int)).
:- chr_type list(T) ---> [] ; [T|list(T)].

dom(X,[]) <=> fail.
dom(X,[Y]) <=> X = Y.
dom(X,L) <=> nonvar(X) | memberchk(X,L).
dom(X,L1), dom(X,L2) <=> intersection(L1,L2,L3), dom(X,L3).
% ?- dom(A,[1,2,3]), dom(A,[3,4,5]).
% A = 3.
```

[CHR debugging](https://www.swi-prolog.org/pldoc/man?section=chr-debugging)
chr tracing
chr_show_store

https://www.swi-prolog.org/pldoc/man?section=chr-guidelines
Don't bind rules in head
mode declarations of chr affect performance. Huh
c \ c <=> true is often desirable. Set semantics instead of multiset.

You can ignore the 
```
:- initialization(main,main).
main(_) :- whatever
```
as noise that I do to make my prolog programs run from the command line instead of interactively.

#### Basics

```prolog
:- use_module(library(chr)).
:- chr_constraint rain/0, wet/0, umbrella/0.

rain ==> wet.
rain ==> umbrella.

:- initialization(main,main).
main(_) :- rain, chr_show_store(true).
```

```prolog
:- use_module(library(chr)).
:- chr_constraint rain/0, wet/0, umbrella/0.

rain <=> wet.
rain <=> umbrella.

:- initialization(main,main).
main(_) :- rain, chr_show_store(true).
% just wet
```

```prolog
:- use_module(library(chr)).
:- chr_constraint left/0, right/0, forward/0, backward/0.

left,right  <=> true.
forward, backward <=> true.

:- initialization(main,main).
main(_) :- forward, left, right, backward, left, chr_show_store(true).
% just left
```

#### Pairing
```prolog
:- use_module(library(chr)).
:- chr_constraint male/1, female/1, pair/2.

% <=> makes a pairing
% this makes all pairs
% male(X),female(Y)  ==> pair(X,Y).
male(X) \ female(Y)  <=> pair(X,Y).
% hmm cransto gets farbus.

:- initialization(main,main).
main(_) :- male(gary), female(zirkin),  male(cransto), female(farbus), chr_show_store(true).
```


#### Paths from edges
```prolog
:- use_module(library(chr)).
:- chr_constraint edge/2, path/2.

base  @ edge(X,Y) ==> path(X,Y).
trans @ edge(X,Y), path(Y,Z) ==> path(X,Z).
pset  @ path(X,Y) \ path(X,Y) <=> true.

:- initialization(main,main).
main(_) :- edge(1,2), edge(3,4), edge(3,2), edge(1,3), chr_show_store(true).
```

#### Minimum
```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint min/1, findmin/1.

findmin(_), min(N) \ min(M) <=> N < M | true.
findmin(Min), min(N) <=> Min = N.
main(_) :- min(7), min(14), min(13), findmin(Min), print(Min), chr_show_store(true).
```
#### GCD
```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint gcd/1.

gcd(N) \ gcd(M) <=> 0 < N, M>=N | Z is M - N, gcd(Z).
% hmm not working
main(_) :- gcd(15), gcd(5), chr_show_store(true).
```


#### Sort

bubble sort
```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint a/2.

a(I,V), a(J,W) <=> I>J, V<W | a(I,W), a(J,V).
main(_) :- a(1,6), a(2,4), a(3,14), chr_show_store(true).
```

merge sort
```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint next/2.

next(A,B) \ next(A,C) <=> A < B, B < C | next(B,C).
main(_) :- next(0,7), next(0,2), next(0,5), chr_show_store(true).
```

#### Get foo

#### Fibonacci
merge sort
```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint fib/2.

fib(0,M) <=> M = 1.
fib(1,M) <=> M = 1.
%fib(N,M) <=> N >= 2, ground(N) | fib(N-1, M1), fib(N-2, M2), when((ground(M1),ground(M2)), M is M1 + M2).
fib(N,M) <=> N >= 2, ground(N) | N1 is N - 1, N2 is N - 2, fib(N1, M1), fib(N2, M2), M is M1 + M2.

main(_) :- fib(5,M), print(M), chr_show_store(true).
```

```prolog
:- use_module(library(chr)).
:- use_module(library(clpfd)).
:- initialization(main,main).
:- chr_constraint fib/2.

fib(0,M) <=> M #= 1.
fib(1,M) <=> M #= 1.
fib(N,M) <=> ground(N), N #>= 2 | N1 #= N - 1, N2 #= N - 2, fib(N1, M1), fib(N2, M2), M #= M1 + M2.

main(_) :- fib(5,M), print(M), chr_show_store(true).
```

top down memo
```prolog
:- use_module(library(chr)).
:- use_module(library(clpfd)).
:- initialization(main,main).
:- chr_constraint fib/2.

cong @ fib(N,M1) \ fib(N,M1) <=> M1 #= M2.
fib(0,M) ==> M #= 1.
fib(1,M) ==> M #= 1.
fib(N,M) ==> ground(N), N #>= 2 | N1 #= N - 1, N2 #= N - 2, fib(N1, M1), fib(N2, M2), M #= M1 + M2.

main(_) :- fib(5,M), print(M), chr_show_store(true).
% store is not empty. Contains memoized fib entries.
```

#### Boolean Propagators


#### Lattice
```
lat(A), lat(B) <=> lat(join(A,B))
```

Propagators are monotonic functions between lattices. CHR was built for propagation
BitSet CHRs?
Other fast propagators?

#### Assignment

#### EGraphs

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass/2.
fcong @ eclass(f(X), E1) \ eclass(f(X), E2) <=> E1 = E2.
acong @ eclass(a, E1) \ eclass(a, E2) <=> E1 = E2.

main(_) :- eclass(a, A), eclass(f(A), FA), eclass(f(FA), FFA), FA=A, chr_show_store(true).
```

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass/2, gas/2.
pcong @ eclass(X + Y, E1) \ eclass(X + Y, E2) <=> E1 = E2.
% nothing should produce this? Well...
% ncong @ eclass(num(X), E1) \ eclass(num(X), E2) <=> E1 = E2.
% pcong @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.

gas(_, 0) <=> true.
comm @ eclass(X + Y, E) \ gas(comm, N) <=> N > 0 | N1 is N - 1, gas(assocl, N1), eclass(Y + X, E).
assocl @ eclass(X + YZ, E), eclass(Y + Z, YZ) \ gas(assocl, N) <=> N > 0 | N1 is N - 1, gas(assocr, N1), eclass(X + Y, XY), eclass(XY + Z, E).
assocr @ eclass(X + Y, XY), eclass(XY + Z, E) \ gas(assocr, N) <=> N > 0 | N1 is N - 1, gas(comm, N1), eclass(X + YZ, E), eclass(Y + Z, YZ).


main(_) :- eclass(1, E1), eclass(2,E2), eclass(3,E3), eclass(E1 + E2, E12), eclass(E12 + E3, E123), gas(comm,5), chr_show_store(true).
% hmm we're only getting to the first rule... I see. We can of course get around this. but not elegantly.
% hmm we're also not runnign fairly on deeper facts. Cripes.
```

pcong is only one step away from structure sharin? No. it really is just structure sharing... Hmm.

Hmm. gas is yet another form of demand based pulling. but only in CHR

A list of all things to retain in gas. Delete anything that fires. No we don't have to delete.
ok ok ok. This isn't so bad.
We just need to batch.
reassert when done.
Difference list useful?
gas(L) <=> L = [X | L1], gas(L1),
But now is there a fair chance for the rules?
Maybe if we scramble the list. it's a mess.

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass(?,-), eclass2(?,-), col/1, kill/0, count/1.

cong @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2.


% rewrite rules.
comm @ eclass(X + Y, E) ==> eclass2(Y + X, E).
assocl @ eclass(X + YZ, E), eclass(Y + Z, YZ) ==> eclass2(X + Y, XY), eclass2(XY + Z, E).
assocr @ eclass(X + Y, XY), eclass(XY + Z, E) ==> eclass2(X + YZ, E), eclass2(Y + Z, YZ).

% made it way worse
% eclass(T,E) \ eclass2(T,E) <=> true.
% eclass2(T,E) \ eclass2(T,E) <=> true.

% To collect up new eclasses
collect @ eclass2(T,E), col(L) <=> L = [eclass3(T,E) | L1], col(L1).
done @ col(L) <=> L = [].

% helpers to cleanup eclass2
kill @ kill \ eclass2(_,_) <=> true.
killdone @ kill <=> true.

% helper to count eclasses
count @ count(N), eclass(_,_) <=> N1 is N + 1, count(N1).

% Take rhs list and inject them as CHR constraints 
process([]).
process([eclass3(T, E)| L]) :- eclass(T,E), process(L).


% Do N rewriting runs
batch() :- col(L), process(L). % print(L)
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

        %  insert(f(a), Fa), insert(a, A), Fa = A, insert(f(f(a)), FFa),
        %   chr_show_store(true).
         % eclass(1, E1), eclass(2,E2), eclass(3,E3), eclass(E1 + E2, E12), eclass(E12 + E3, E123),
       
          N = 5,
          init_add(N),
          Num is 3**(N) - 2**(N+1) + 1 + N, print(Num),
          BNum is N,
          time(batch(BNum)), kill, count(0), chr_show_store(true).
          
          
```


```prolog
%rhs([]).
%rhs([T | L]) :- flatten(T), rhs(L).
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass(?,-), eclass2(?,-), col/1, kill/0, count/1.


insert( T , E) :-
 ground(T),
 var(E),
 T =.. [F | Args],
 length(Args, N), length(Es, N),
 T2 =.. [F | Es],
 eclass(T2, E),
 maplist(insert, Args, Es).

main(_) :- insert(1 + 2 + 3 + 4, E), chr_show_store(true).


```

We can also perform rules like
find(t1), find(t2) ==> E1 = E2.
These will always finish since they only compress egraph.

It is quite possible that translating to integers and using CHR union find is faster.
#### Semi naive?

eclass2 is somewhat like new_eclass
We could perhaps find delta_eclass

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint eclass(?,-), declass/2, eclass2(?,-), col/1, kill/0, count/1.

% Take rhs list and inject them as CHR constraints 
process([]).
process([eclass3(T, E)| L]) :- declass(T,E), process(L).

% Do N rewriting runs
batch() :- col(L), process(L). % print(L)
batch(0).
batch(N) :- batch(), N1 is N -1, batch(N1).

init_add(N) :- eclass(N,E), declass(N,E), N1 is N - 1, init_add_aux(N1,E).
init_add_aux(0,_).
init_add_aux(N,E) :- eclass(N, EN), eclass(EN + E, E2), declass(N, EN), declass(EN + E, E2), N1 is N-1, init_add_aux(N1, E2).

insert( T , E) :- ground(T), var(E), T =.. [F | Args], length(Args, N), length(Es, N),  T2 =.. [F | Es],
 eclass(T2, E),  maplist(insert, Args, Es).


cong @ declass(T, E1), eclass(T, E2) ==> E1 = E2.
cong2 @ eclass(T, E1) \ eclass(T, E2) <=> E1 = E2, declass(T,E1).

% rewrite rules.
comm @ declass(X + Y, E) ==> eclass2(Y + X, E).
assocl1 @ declass(X + YZ, E), eclass(Y + Z, YZ) ==> eclass2(X + Y, XY), eclass2(XY + Z, E).
assocl2 @ declass(Y + Z, YZ), eclass(X + YZ, E) ==> eclass2(X + Y, XY), eclass2(XY + Z, E).
assocr1 @ declass(X + Y, XY), eclass(XY + Z, E) ==> eclass2(X + YZ, E), eclass2(Y + Z, YZ).
assocr2 @ declass(XY + Z, E), eclass(X + Y, XY)  ==> eclass2(X + YZ, E), eclass2(Y + Z, YZ).

% made it way worse
% eclass(T,E) \ eclass2(T,E) <=> true.
% eclass2(T,E) \ eclass2(T,E) <=> true.

% To collect up new eclasses
collect @ eclass2(T,E), col(L) <=> L = [eclass3(T,E) | L1], col(L1).
collect @  col(_) \ declass(_,_) <=> true.
done @ col(L) <=> L = [].

% helpers to cleanup eclass2
kill @ kill \ eclass2(_,_) <=> true.
kill2 @ kill \ declass(_,_) <=> true.
killdone @ kill <=> true.

% helper to count eclasses
count @ count(N), eclass(_,_) <=> N1 is N + 1, count(N1).




main(_) :- 
          N = 2,
          init_add(N),
          Num is 3**(N) - 2**(N+1) + 1 + N, print(Num),
          BNum is N,
          time(batch(BNum)), % kill(), count(0),
           chr_show_store(true).
          
          
```

### Compiling
[KU leuven system : implementation and application](https://lirias.kuleuven.be/retrieve/33588). Hmm. Is CHR compiled into prolog code?
[CCHR: the fastest CHR Implementation, in C](https://lirias.kuleuven.be/retrieve/22123)  
Idle thoughts, what about time dataflow.

### Embedding into CHR
- TRS
- Prolog and CLP
- Graph trasnfomation 
- Petri nets

GAMMA general abstract mnodel for multiset manipulation

## Answer Set Programming s(CASP)
https://swish.swi-prolog.org/example/scasp.swinb
"Tabling and s(CASP) are quite different beasts. They both address reasoning in cyclic domains including negation. Tabling provides Well Founded Semantics where s(CASP) provides Stable Model Semantics. s(CASP) stresses creating an explanation. Tabling does not. Tabling scales a lot better than s(CASP). It all depends …"

https://gitlab.software.imdea.org/ciao-lang/sCASP
[Constraint Answer Set Programming without Grounding](https://arxiv.org/abs/1804.11162)
[Justifications for Goal-Directed Constraint Answer Set Programming](http://www.cliplab.org/papers/sCASP-ICLP2020/TC-explainCASP.pdf) ERGO AI uses justification trees  https://coherentknowledge.com/ using XSB

s(ASP) was just ASP https://personal.utdallas.edu/~gupta/ . S(CASP) includes constraints
[tutorial slides](http://platon.etsii.urjc.es/~jarias/slides/gde21-tutorial.pdf)
[tutorail paper](http://ceur-ws.org/Vol-2970/gdepaper1.pdf)

[event calculus](https://swi-prolog.discourse.group/t/event-calculus-in-swi-prolog/5233)
## Extralogical features
### Database manipulation
[swi](https://www.swi-prolog.org/pldoc/man?section=db)
[sicstus database manip](https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/ref_002dmdb.html#ref_002dmdb)
retract - take out of database
assert - put into database/
set_prolog_falg
dynamic predicates. 
recorded database

`A = A, assert(foo(A)), A = x` what does this do. Does it make a clause `foo(A).` or does it make `foo(x).` Ah ok. The term is copied. So it makes the first on
### Cuts and Such

cut
green cut




findall bagor setof are aggregation of solutions. They are reifying predicates kind of.


[ Finding all Solutions to a Goal](https://www.swi-prolog.org/pldoc/man?section=allsolutions)




## Lambda
Oh sweet mysterious lambda

The minikanren `evalo`

[Oleg's lambda interpreter](https://okmij.org/ftp/Prolog/index.html#lambda-calc)

One is tempted to attempt to use prolog variables for lambda variables. Requires extralogical copying primitives
`copy_term`

[swipl](https://www.swi-prolog.org/pldoc/man?section=yall) lambda expressions.

[lambda is iso prolog](http://www.complang.tuwien.ac.at/ulrich/Prolog-inedit/ISO-Hiord.html)

HiLog - My impression is this is a bit like "first order functional" programming. All predicates need names. You can achieve this via defunctionalization, lambda lifting, etc.

# Semantics
Completion semantics
Well-founded
Completion semantics

# History
Resolution in automatc theorem provers came earlier.
Kowalski and Colmerauer

Flotd nondeterminstic algorithms 9167
PLANNER Hewitt

Prolog 0
Prolog 1

metamorphisis grammars -> DCG
Dec-10 prolog
Ediburgh prolog

structure copying vs structure sharing

fifth generation computing

Extensions to unification
prolog II
Prolog III

CLP Jaffar Lassez 1987

# Expert Systems
See Also:
- Databases
Knowledge Representation
https://en.wikipedia.org/wiki/Rete_algorithm


# Lambda Prolog
[lambda prolog page](https://www.lix.polytechnique.fr/~dale/lProlog/)
Implementations
- Teyjus - seems to maybe not be developed anymore
- elpi - alive and well. Coq metaprogamming
- Makam - a variant on lambda prolog with some cooll paper tutorials


Install as `opam install elpi`. Run as `elpi -test` to run with main query

```elpi
main :- print "hello world".
```

```elpi

type rain prop.
type wet prop.
type umbrella prop.
%mode (rain i).
%mode (wet i).
%mode (umbrella i).
rain :- !, declare_constraint rain [_].
wet :- !, declare_constraint wet [_].
umbrella :- !, declare_constraint umbrella [_].

main :- std.append [] [] X, print X,
        std.length [1,3,4] L, print L,
        std.take 2 [1,2,3,4] L1, print L1,
        std.map [1,2,3] (x\ y\ y is 2 * x) L2, print L2,
        std.iota 10 L3, print L3, % range of numbers
        true,
        Z is 1 i+ 2, print Z,
        Z1 is (cos 3.0) + (int_to_real ((rhc "a") + (size "hello"))), print Z1,
        fst (pr 1 2) One, print One,
        dprint (pr (some 3)),
        var V, var (V1 3) A B, print A, print B, % so it destructures a vairable application
        some T == some T,
        trace.counter "foo" I, print I, trace.counter "foo" I1, print I1,
        %print app [lam (x \ const "a"), const "b"],
        declare_constraint wet [W],
        declare_constraint rain [R],
        declare_constraint umbrella [U],
        R = 7,
        print "ok"
.

constraint rain wet {
  rule rain <=> wet.
}
```

Some built in elpi files
- [builtin](https://github.com/LPCIC/elpi/blob/master/src/builtin.elpi) surprising that even very basic stuff is defined in here.
  - i+ i- r+ mod div infix operations. + is overloaded it looks le
  - regular expresions rex. Like Str module
  - print dprint raw terms?
  - quotation? https://github.com/LPCIC/elpi/blob/master/src/elpi-quoted_syntax.elpi lam, app, const, clause, arg
  - same_term same_var var name - geiventbaraibe, ground_term, closed_term, constant, 
  - if/3
  - random.int
  - int.map, std.string.map, std.string.set, std.map takes in a comp function, 
  - gc functions. trace,counter
- [stdlib](https://github.com/LPCIC/elpi/blob/master/src/builtin_stdlib.elpi)
  - mem, exsits, map2, filter, fold, zip, unzip, intersperse, max, findall 

[examples in test](https://github.com/LPCIC/elpi/tree/master/tests/sources)
- named clauses `:clausename`
- namespaces
- typeabbrev
- seperate compilation?
- w.elpi algorithm W?
- ndprover

`external` fields. Interesting

[a tutorial on lambda prolog and is applications to theorem provin - Amy Felty](https://www.site.uottawa.ca/~afelty/dist/lprolog97.pdf)
[thesis implementing lambda prolog in ciao prolog](https://www.yumpu.com/en/document/view/39502786/university-of-minnesota-this-is-to-certify-that-i-employers)

[Implementing Type Theory in Higher Order Constraint Logic Programming](https://hal.inria.fr/hal-01410567v2/document) longer elpi paper. describes chr.
- macro directives
- delay directives
### HO Unification
forall exists forall problems
Raising vs Skolemization


## LF
LF is of some relation to lambda prolog (being a prologish system with lambdas in it) although with some different aims. It is dependently typed (pi 2 I think?) in a way different from coq etc.

Twelf.
dedukti. lambda - pi
[beluga](http://complogic.cs.mcgill.ca/beluga/) is this kind of twelf? [beluga paper](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.188.3950&rep=rep1&type=pdf)
abella.
These are all related I guess? abella might not be LF

Logical frameworks is a general vague concept I think. It is a system in which it is easy to model logical language nad inference rules.
but ELF the edburgh logical fraemwork is more specific.
Related to Pi2 a corner of the lambda cube.

[The Next 700 Challenge Problems for Reasoning with Higher-Order Abstract Syntax Representations](https://link.springer.com/article/10.1007/s10817-015-9327-3)
### Twelf
http://twelf.plparty.org/live/
http://twelf.org/wiki/About_The_Twelf_Project 

Twelf is a depnedelty typed landguage that is also a logic programming langfuage. Because it has a totality checker and termination checker, prolog clauses can be considered proofs.

https://core.ac.uk/download/pdf/82649367.pdf Normalization for the Simply-Typed Lambda-Calculus in Twelf

## Rust Chalk Harrop
https://github.com/rust-lang/chalk
https://rust-lang.github.io/chalk/book/

http://smallcultfollowing.com/babysteps/blog/2017/01/26/lowering-rust-traits-to-logic/#type-checking-generic-functions-beyond-horn-clauses
https://internals.rust-lang.org/t/blog-series-lowering-rust-traits-to-logic/4673/12 internals thread

http://smallcultfollowing.com/babysteps/blog/2017/04/23/unification-in-chalk-part-2/ how chalk handles type normalization




# LogTalk

[logtalk](https://logtalk.org/) is it's own curious kind of universe.
[github repo](https://github.com/LogtalkDotOrg/logtalk3)
It adds object oriented programming to prolog.
<https://logtalk.org/2009/12/08/lambda-expressions-in-logtalk.html> lambdas

# Linear Logic Programming
See linear logic
prolog rules destroy the body. Good for modeling state
Chris martens
[ceptre](https://github.com/chrisamaphone/interactive-lp)

The interaction of linear logic and logic programming was very inlfluential on the concept of focusing

# Coinductive Logic Programming
Actually fairly unrelated to inductive logic programming.
Dealing with infinite terms and streams.


# inductive logic programmingh
popper https://arxiv.org/abs/2005.02259
https://github.com/metagol/metagol metagol 
http://andrewcropper.com/
https://arxiv.org/pdf/2102.10556.pdf inductive logic programming at 30

# Theorem Proving
[Leantap](https://formal.iti.kit.edu/beckert/leantap/)
Jens Otten
[How to Build an Automated Theorem Prover. Invited Tutorial at TABLEAUX in London/UK](http://www.jens-otten.de/tutorial_tableaux19/)

[A simple version of this implemented in tau prolog](https://www.philipzucker.com/javascript-automated-proving/) Prdocues proofs translated to bussproofs latex

### Stuff

.type Lifted = Lit {x : symbol} | Y {x : Lifted, y : Lifted}

.decl r(x : Lifted, y : Lifted)
.decl a(x : Lifted)
r(x1, $Y(x1,x2)), a($Y(x1,x2)) :- r(x1,x2).



defeasible logic programming

[O-keefe - An Elementary Prolog Library](http://www.cs.otago.ac.nz/staffpriv/ok/pllib.htm) some suggestions about unicode and other test stuff. Higher order operators

[50 years of prolog and beyond](https://arxiv.org/pdf/2201.10816.pdf)

<https://github.com/Anniepoo> - Annie ogborn has some cool seeming tutorials

<https://github.com/philzook58/lips-minikanren> trying to use lips sccheme for minikanren in browser

<https://github.com/aprolog-lang/aprolog> alpha prolog. Nominal logic. What the heck is that again?

old title: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution




BAP universal valures
OCaml typeclasss system
Oleg modellign typeclasses as prolog
<https://inbox.ocaml.org/caml-list/20190904152517.GA2014@Melchior.localnet/>
<http://okmij.org/ftp/ML/index.html#trep>

canonical structures and unification hints. Can we make a metaintepreter for this?


Hmm. Gauntlet thrown.
Byrd is not sure how prolog can? do this stuff.
<https://www.youtube.com/watch?v=aS8oj2GXras&feature=youtu.be&ab_channel=LecturesbyProf.EadesatAU>
XSB prolog
"complicated
tabling and abstract interpretation
tabling has a notion of subsumption? when are two calls the same?
conductive logic over streams
tree automata
lvars. fixpoint over lattices

meta interpeter, sure. That's one way to get com,plketeness
What if one defunctionalizes the minikanren pause mechanism. What does it look like?
Oh there's a first order kanren paper that does this



Hmm. Could one do barliman style in lambda prolog?
F, ex1, ex2, ex3.
2012 quine ppaper
2017 barliman paper

Tree automa, lvar, language for fixpoints.
Not depth first, not breadth first,
coniductive logic programming UT Dallas
Abstract Interpretation ~ tabling. What does that mean?

nada Amin
lambda kanren
defeasible logic

proof checker running backwards



Scheme workshop



https://git.sr.ht/~sforman/Prolog-Junkyard/tree/master/miscellaneous/itc.pl interval tree clocks in prolog
https://www.metalevel.at/trs/ knuth bendix completion
https://arxiv.org/abs/1706.00231 auto differentiating using constraint handling rules

<http://adam.chlipala.net/papers/MakamICFP18/MakamICFP18.pdf> prototpying functional language using higher order logic programing makam
chlipala
<https://www.tweag.io/blog/2019-11-28-PCF-makam-spec/>

Egraphs in prolog
Unification variables give native union find data strcuture
Hash consing - ??
equal( (t, E1), (t2,E2) :- E1 = E2. % union find joining

Great. But then we need to possibly union find parents

t(x,y) ====> t(E1,E2)

equal(  t1, t2  ) :- lookup( t1 )

file:///home/philip/Downloads/ODonnell1987_Chapter_Term-rewritingImplementationOf.pdf

https://core.ac.uk/download/pdf/81972151.pdf Logic programming with equations.

Eqlog - goguen and mesegaer?

assert_equal(EGraph,   ,EGraph') :- lookup(t1, E1), lookup(t2, E2), E1 = E2, EGraph' = EGraph
assert_eqyal(  ) :- lookup(t1, E1), lookup(t2, E2)

rebuild(EGraph, EGraph' ) :- 

rebuild(EGraph) :- EGraph = (  , Map )

To miss a parent inference isn't wrong, it's just wasteful

If we do no hash consing, we do have to store every known term.
We also need a map from Eclasses back to terms don't we?

What if we broke apart. are association lists so bad?
f(g(y)) ===> [  f(G) => F , g(Y) => G, y => Y ]

Or we could use the HEADS as keys in assoc. and then assoc list the leftovers.
This isunder the assumptyiong that variables

== for search
[ == , ]

We may want to prune duplicates occasionally
If we interweave 

Can we even achieve apttern matching without an index from ENodes => terms?
Yessss.....?
Given a pattern ( EClass, g(f(A)) )
We can look in g/1 for Eclass on the right hand side.
For those matches, we build a subproblem of matching the pieces of the left hand size ENodes.





With tabling?
Tabling gives us some kind of memoization

equal?(Egraph, t1,t2) :- lookup(EGraph, t1, E1), lookup(EGraph, t2, E2).
equal?(arg1(  ) :- eqwal?(args1, args2), assert_equal(EGraph, t1, t2)

Stratified prolog predciates. This euqation paper mentions this 
and this tabling thing mentions it https://www.swi-prolog.org/pldoc/man?section=tabling-non-termination


Datalog and program analysis
https://www2.cs.sfu.ca/CourseCentral/721/jim/DatalogPaper.pdf - What you always wanted to know about datalog
http://rightingcode.org/tutorials/popl20/ popl 2020 - reasoning tools using llvm and z3
Z3 has a datalog style reasoning engine in it

First you need to get a program as a mapping


The Chase - get existentials in the head. Wisnesky says somethign to do with jkabn extensions and lawvere theory
What was up with the notion of quantifiers as adjoints anyway?
Maybe also some kind of completion?
Datalog +-
Formulog
Bap KB as datalog
What 

Typeclasses vs Canonical Structures. I don't get it.
Could I make a model? Maybe in prolog?
Diamond problem
Inheritance.
What are typeclasses? "Kind of like prolog"
Things are incompatible for some reason?
Canonical structures add unification hints?
https://hal.inria.fr/hal-00816703v1/document canonical structures ofr the working coq user


So what is the synctatic condition that precludes search?
1. nonoverlapping 

Would it be more interesting to just 
What am I understanding here?

Canonical structures was suggesting that some kind of inconstency would manifest.
Maybe lambda prolog gets us closer. We can have existential variables and such.

extensible unification


nat === (carrier nat_abGrp) :- 
A === A.


nat == carrier(Eq) :- Eq == natEq.
carrier(Eq,nat).



nonunifiable(L) :- all( /= , L ).


% haskell has no backtracking
% every case has a cut.
eq(tup()) :- !.
eq(tup(A,B)) :- !, eq(A), eq(B)

% 

eq(int, prim__equal_int).
eq(tup(A,B), lambda( x, case( x, tup(a,b) => bool_and( apply(EqualA, a) , apply(EqualB, b )  )    )  )  ) :- 
      eq(A, EqualA), eq(B, EqualB).
eq(tup(A,B), comp(and, par(EqualA,EqualB)))


eq(int).
eq()
eq(tup(A,B)) :- eq(A), eq(B).


ord(bool).
ord().

functor( maybe )
functor(compose(F,G)) := functor(F), functor(G)

traversable :-

% superclass
class(ord(A)) :- call(ord, A), class(eq(A))



"diamonds appear evertwhere. See pullbacks" ~ Hale


Transcribing rules to prolog and coq.
In Coq the cookbook is that you make an inductive. One constrctor per rule.
If you call eauto, coq will perform prolog style backchaining search. See Chlipala
You could write these as functions rather than as 
The data type is the proof structure.

Prolog is the same thing. It's less imposing than coq though.
You make predicates and :- for each condition.
Prolog has built in nondtermisnion and unification.


Tying rules in prolog.
I did the point-free simply typed lambda calculus
type(fst, tup(A,B), A).


type(Gamma |- plus(A,B) : nat ) :- 
          type(Gamma |- A : nat), type(Gamma |- B : nat)
type(Gamma, lam(X, Body) |- fun(A,B )) :- type() , type( [X | Gamma]


http://www.coli.uni-saarland.de/projects/milca/esslli/comsem.pdf computational semantics. some interesting material here
https://samples.jbpub.com/9780763772062/PrologLabBook09.pdf - prolog experiment in discretem mathemtiacs logic and computatilbitly



They start with defining a set of atoms like

var(x).
var(y).

forall(x, stupid(x)).


https://www.youtube.com/watch?v=RwBiHLoQ3E4&ab_channel=PapersWeLove niko matsakis - lambda prolog

https://rust-lang.github.io/chalk/book/recursive.html chalk. harrop formula


The Otten sequent calculus prover is very similar to a meta circular intepreter for prolog

Horn clauses (or harrop formula) 



Lambda-mu calculus and prolog. Focusing is relevant.
Prolog has an imperative reading


Executing the Algebra of Programming

type(fst, prod(A,B) -> A ).
type(snd, prod(A,B) -> B ).
type(id, A -> A).

interp(fst, tup(A,B), A ).
interp(snd,  tup(A,B), B).
interp(id, A , A).
interp(fan(F,G), A, tup(B,C)) := interp( F, A, B) , interp(G, B, C).  
interp(comp(F,G), A, C ) :- interp( F, A, B ), interp(G, B, C).
interp(conv(F), A, B) :- interp(F, B, A).
interp(cata(F) , fix(A) , C )  :-  interp(map(cata(F)), A, B) ,  interp(F, B, C)

% map instance for ListF
interp(map(F), cons(A,B) , cons(A,B2) ) :- interp(F, B, B2).
interp(map(F), nil, nil).

% in constrast to map instance for list
interp(map(F), [], []).
interp(map(F), [X | XS], [Y | YS]  ) :- interp(F, X, Y), interp(map(F), XS, YS).





% convert to listf form
listf([], nil).
listf([A | XS ], cons(A,fix(L))  ) :- listf(XS, L).


Different style


cata(F, fix(A), C) :- map(cata(F), A, B), call(F, B, C).
fst(pair(A,B), A).

comp(F, G, A, B) :- call() , call()


% define what it means to be a functional relation
functional( fst, fst).
functional( snd, snd).
function(  )

% prolog is database stuff ~ relation algebra. It makes perfect sense.


interp( map )

Converting prolog to abstract machine form
step( Stack Result ) :-


oprolog veriffication

Warrne and Maier 1988 textboook
proplog - propsitional goals only. 
datalog - constants only
prolog - functional symbols

% tail recursive formulations
factorial(N,F) :- factorial(0, N,1,F)
factorial(I,N,T,F) :- I < N, I1 is I+1, T1 is T * I1, factorial(I1, N, T1,F)
factorial(N,N,F,F).

hitchikers guide to prolog machine
https://drops.dagstuhl.de/opus/volltexte/2018/8453/pdf/OASIcs-ICLP-2017-10.pdf


ref a
ref b

https://formal.iti.kit.edu/beckert/leantap/leantap.html Beckert posegga leantap
https://link.springer.com/chapter/10.1007%2F3-540-36377-7_6 metacircular abstarct interpretation in prolog
https://www.metalevel.at/acomip/

Pfenning constructive logic course http://www.cs.cmu.edu/~fp/courses/15317-f17/schedule.html
Programs as proof search
He considers the prolog predictaes as the judgements themeselves
As compared to considering the pile of predicates as entedcedents of a sequent
Bottom up search ius forward reasoning, top down is backward reasonining
bidrectional type checking - https://arxiv.org/pdf/1908.05839.pdf



Prolog semantics -
Since prolog can not terminate you can take that denotational semantics perspective.
https://www.swi-prolog.org/pldoc/man?section=WFS well founded semantics. - True/False/unknown
https://en.wikipedia.org/wiki/Well-founded_semantics
http://www.cse.unsw.edu.au/~cs4415/2010/resources/gelder91wellfounded.pdf
http://dai.fmph.uniba.sk/~sefranek/links/FixPointSurvey.pdf  fixpoitn semantics for logic programming a survey. melvin fitting
Melvin fitting has a number of interesting bokos http://melvinfitting.org/

So prolog already has belnap bools in it. 


What does it look like to mix prolog with exact reals?



Modes and determinism annotations.

Kowalski - hgistory of prolog https://www.researchgate.net/publication/277670164_History_of_Logic_Programming



tabling - 
Tabling is some kind of memoization.
It is connected to bottom up strategies
swi prolog https://www.swi-prolog.org/pldoc/man?section=tabling
https://www.metalevel.at/prolog/memoization
https://biblio.ugent.be/publication/6880648/file/6885145.pdf tabling as a library with delimited control
https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/delimited-continuations-for-prolog/DD08147828169E26212DFAF743C8A9EB delimitted continuations for prolog
https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.294.9440&rep=rep1&type=pdf XSB extending prolog with tabled logic programming. XSB prolog is the most advanced tabling implementation (still? maybe that is old information)
https://github.com/SWI-Prolog/tabled-prolog-book warren wrote a book draft
https://www3.cs.stonybrook.edu/~warren/xsbbook/book.html ok This may not be being finished anytime soon
Tabled typeclass resolution


http://www.covingtoninnovations.com/mc/plcoding.pdf - coding guidelines for prolog

https://swi-prolog.discourse.group/t/algebra-in-prolog/1849 - algerba in prolog
https://github.com/maths/PRESS prolog equation solving system


scryer prolog - a rust based implemnentation . https://github.com/mthom/scryer-prolog
Interesting links
Precise garbage collection in Prolog 
"Can Logic Programming Execute as Fast as Imperative Programming?" - Peter van Roy
indexing dif/2 https://arxiv.org/abs/1607.01590 calls for if_ predicate
debray allocator

https://wiki.nikitavoloboev.xyz/programming-languages/prolog notes

https://mercurylang.org/documentation/documentation.html mercury

Names:
Kowalski
schrijver
Nuemerekl
Markus triska
Wielemaker
Warren
Miller
Nadathur
melivn fitting

https://www.metalevel.at/prolog/theoremproving 
presburger and resolution
https://www.youtube.com/watch?v=b2Px7cu2a68&feature=youtu.be&ab_channel=ThePowerofProlog term rewriting in prolog

https://dl.acm.org/doi/book/10.1145/3191315
Declarative Logic Programming: Theory, Systems, and ApplicationsSeptember 2018
Has another WAM tutorial in it

So


prolog modes

https://www.metalevel.at/prolog/attributedvariables attributed variables

https://sicstus.sics.se/sicstus/docs/latest4/pdf/sicstus.pdf sicstus prolog manual


Exact reals. The semantics already has this three valued logic flavor

```
partition([X,Y]).
partition([X,Y]) :- partition([[X, X+Y / 2]]).
partition([[X,Y]) :- partition( [X+Y/2 , Y  ]).

interval(X), stuff.


sqrt()

```

Using prolog multiple answer streams is kind of like relying on haskell laziness.
It's this intrinsic lANGUAGE construct being used as a streaming datatpe
Unclear if wise. Fast but inflexible and unclear. Too clever for own good.

clpq
clpr

delmittied dontinuation. The contiuation is a goal stack.
But is the continuation also catching choice point stack?


homoiconic. Term syntax is identical to 


Maier and Warren 

T_p, the immediate conseqeunce operator. Applying one round of prolog/datalog/ etc rules

Proplog


SMT-log
Datafun - a fiunctional datalog https://www.cl.cam.ac.uk/~nk480/datafun.pdf https://www.youtube.com/watch?v=gC295d3V9gE
datalog - stephenel diehl https://www.stephendiehl.com/posts/exotic04.html
uZ - datalog in Z3
souffle
doup


What are appli8cations of datalog
program analysis. That points to analysis tutorial

Datalog ~ polynomial time in some sense. 
 So application wise, it can be fixed point computations
 Or we can encode

 send more money
 num(0) num(1)
 num(2)
 adder(  )

 https://sites.google.com/site/pydatalog/Online-datalog-tutorial
 nqueens - they unroll it significantly.

Some examples
http://cse.unl.edu/~riedesel/pub/cse413/des/doc/manualDES.pdf

 ok farmer goat. As a path search basicaly

state(goat, foxm, chienbk, ) :- 



Parsing a grammar. This is an odd one. Encode positions of string in database.
t(1,a,2).
t(2,b,3).
t(3,a,4).
t(4,b,5).
t(5,a,6).
a(F,L) :- t(F,a,L).
a(F,L) :- a(F,M), t(M,b,L).
a(F,L) :- a(F,M), t(M,a,L).
DES> a(1,6)
{
 a(1,6)
}
Info: 1 tuple computed.

Games? 

Domain modeling with datalog
https://www.youtube.com/watch?v=oo-7mN9WXTw&ab_channel=%23pivorakLvivRubyMeetUp

https://github.com/ptarau/TypesAndProofs
More theorem provers

binprolog - analog of CPS. Add a new parameter to every predicate

LD resolution

monoid of clauses - unfolding
bin(A :- BBBB) = (A>C :- BBBB>C)


2020/9
Propagators.

Kmett. The Art of the Propagator https://dspace.mit.edu/bitstream/handle/1721.1/44215/MIT-CSAIL-TR-2009-002.pdf?sequence=1&isAllowed=y 

The gecode manual [https://www.gecode.org/doc-latest/MPG.pdf](https://www.gecode.org/doc-latest/MPG.pdf)

Adding constraints or smt. I have a seperate store for them (in the state)? explicit probe annotations to check still satisfiable.

9/1/20

I was looking at prolog again. Jesus nothing changes.

What are the good programs. The art of prolog has an open access link

Difference lists are cool. They really are similar ot hughes lists. Or al ist that keeps a pointer to it's end

Using it for theorem proving is cool. Where are those examples? The lambda prolog book has some exmaples. There is a propsitional satisfiabilioty prover in art of prolog. Propositional solver in powr of prolog [https://www.metalevel.at/prolog/theoremproving](https://www.metalevel.at/prolog/theoremproving) [http://vidal-rosset.net/g4i_prover.html](http://vidal-rosset.net/g4i_prover.html)   http://jens-otten.de/tutorial_cade19/slides/prover_tutorial_CADE19_2.pdf

[http://tca.github.io/veneer/examples/editor.html](http://tca.github.io/veneer/examples/editor.html) minikanren examples. 

[http://io.livecode.ch/](http://io.livecode.ch/) more minikanren examples [https://www.youtube.com/watch?v=0FwIwewHC3o](https://www.youtube.com/watch?v=0FwIwewHC3o) implementing microkanren 

https://www.youtube.com/watch?v=0FwIwewHC3o

nomial logic programming [https://arxiv.org/pdf/cs/0609062.pdf](https://arxiv.org/pdf/cs/0609062.pdf) alphaprolog. Chris mentioned this nominal thing as nother way of dealing with binders

Datalog - souffle.  Reading gorup paper [https://arxiv.org/pdf/1207.5384.pdf](https://arxiv.org/pdf/1207.5384.pdf). Sttratification. relations indexed on program point/ abstract state of program point. Interval analysis encoded in binary to datalog?

425/20 I was playing with prolog recently. Pretty cool 

What is the deal with scheme and racket? i just don't have the  revelation.

[http://home.pipeline.com/~hbaker1/CheneyMTA.html](http://home.pipeline.com/~hbaker1/CheneyMTA.html)

Lisp in easy pieces

[http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/](http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/)

[https://schemers.org/](https://schemers.org/)

I was looking at disjoint set data structures again [https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9](https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9)

Kmett's latest propgator talk was mentioning using group actions somehow in unification? [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ)

george wilson - https://www.youtube.com/watch?v=nY1BCv3xn24 intutition for propagators.

[http://hackage.haskell.org/package/discrimination-0.3](http://hackage.haskell.org/package/discrimination-0.3) What the hell is this? Fritz Henglein. 

[http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/](http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/)

https://www.reddit.com/r/haskell/comments/a9yze4/is_there_an_arraylike_data_structure_which_gives/

interesting comments  

[https://www.lri.fr/~filliatr/puf/](https://www.lri.fr/~filliatr/puf/) a coq formalization of a persistent union find data structure.  They use persistent arrays, which do some kind of rebalancing operation. 

Persistent data structures. Wassup with them?

## 2019

Combine LogicT with an OSQP monad for branch and bound

[http://overtond.blogspot.com/2008/07/pre.html](http://overtond.blogspot.com/2008/07/pre.html)

[https://github.com/dmoverton/finite-domain](https://github.com/dmoverton/finite-domain)

[https://blog.plover.com/prog/haskell/monad-search.html](https://blog.plover.com/prog/haskell/monad-search.html)

[https://www.schoolofhaskell.com/user/chowells79/even-more-money](https://www.schoolofhaskell.com/user/chowells79/even-more-money)

[https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet](https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet)

Select Monad

Branch and Bound

Ed kmett is up to funny business

[https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s](https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s)

Propagators

[https://www.sciencedirect.com/science/article/pii/S1571066105805444](https://www.sciencedirect.com/science/article/pii/S1571066105805444)

Typed logical variables in haskell by Claesson and Ljundogjgklds

[https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf](https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf)

Also by claesson, the key monad paper. 

[http://www.cse.chalmers.se/~koen/](http://www.cse.chalmers.se/~koen/)

Interesting guy. He is coqauthor with hughes on quickcheck.

Atze van der Ploeg is both Key monad paper and reflection without remorse. They have an FRP paper that sounds interesting

He metnioend a number of interesting things. He's doing very reference heavy code? Kanren. 

He mentoins intension vs extensional equality. Judgemental eqaulity is the one inside the type checker. Is it ~ ? And intwnsional equality is the one within the language itself, that is :~: . Extensional. nuPRL starts with an untyped lambda calculus and then you teahc the system typing derivations? What is nuPRL's deal

Union-find algortihm - as part of unification?

nerualkanren, synquid. Two program synthetsis projects. Synquid uses liquid typing

Oleg Shen paper using efficient charing for logic programming

[https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf](https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf)

[http://sebfisch.github.io/explicit-sharing/](http://sebfisch.github.io/explicit-sharing/)

Maybe sebastein fischer is the name I should assicuate more storngly?

[https://sebfisch.github.io/research/](https://sebfisch.github.io/research/)

The Curry language. Haskell + logic. Egison has weirdo patterns too. Multiple patterns can match? Non-linear pattern require. Realted to view patterns? view patterns are a weirod syntax. realted to guard patterns. DOn't need to introduce intermediate names

[https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf](https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf)

View patterns might be a way of getting something like the Agda .x syntax, where something is forced to be something by unification?

[https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork](https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork)

Kmett mentions a "octagonal" domain. What the hell is he talkiing about. He also moentions interval and polyhedral which makes more sense

https://www-apr.lip6.fr/~mine/publi/article-mine-HOSC06.pdf

Huh. Interesting. It is in between power of polyhedral and interval. allows sums/differences of two variables. I think I've heard this called difference logic. This paper also mentions galois connections. Galois connections are studied in the context of abstract interpetation?

https://arxiv.org/pdf/1807.08711.pdf 

Using Agda and galois connections. Interestign example of sets of even and odd numbers.

This other paper does an interesting thing of defining division in terms of a glaois connection. Might we also get a good definition of fractions that way? a fraction t ~ m/n is a "number" such that forall z. x <= y   -> x * t * n <= y * m?  There is an notion of negative numbers, fractions, etc as reified weirdo operations that can't be solved yet. Hmm. Yeah, This jives with galois theory doesn't it. That book I was reading was talking about field extensions. Or number systems being invented to make more equations solvable. The reals make ? solvable. fractions make division solvable. Complex makes roots solvable. finite field extensions make simple algerbaic equations solvable. 

[https://www.sciencedirect.com/science/article/pii/S1567832612000525](https://www.sciencedirect.com/science/article/pii/S1567832612000525)

% -----------------------------------------------------------------
% leanseq.pl - A sequent calculus prover implemented in Prolog
% -----------------------------------------------------------------

% operator definitions (TPTP syntax)

:- op( 500, fy, ~).     % negation
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication
:- op( 500, fy, !).     % universal quantifier:  ![X]:
:- op( 500, fy, ?).     % existential quantifier:  ?[X]:
:- op( 500,xfy, :).

% -----------------------------------------------------------------
prove0(F) :- prove([] > [F]).
% -----------------------------------------------------------------

Oliveira, that same guy as the Search monad and some other thingds

I suppose perhaps there is something similar happening in functional programming. to make recrsuively defined functions solvable, you need to extemnd the language with a Y-combinator or some of fixed point operator.

Interval airthemteic in a theorem prover. That is a way of getting sets. Min and Max. Interesting

This is also a pleasant by Backhouse

http://www.cs.nott.ac.uk/~psarb2/G53PAL/FPandGC.pdf

indirect equality

m=n ===  forall k. k <= m <=> k <= n

Galois connection between convex hulls of integer points? There is a sequence of abstractions for integer programming. You can turn dimension by dimension into integer so there are 2^D different domains to talk about. And there is this grid of connections that forms a lattice itself? Like the top is the completely R^D, and the bottom is Z^D. Using these connections is the branch and bound procedure. 

Floor and Ceil are also galois connections. Maybe also round? I had been thinking in terms of ibjects being individual numbers, not convex sets of numbers. Convex sets does tie in much better to categorical thinking

http://www.cs.tau.ac.il/~msagiv/courses/asv/absint-1.pdf

An interesting paper tutorial on galois connections. V cool.

monotone functions between are like natural tranfromations?

One place used dup as the adjunction to max.

There may be more to galois connections than adjunctions, since they are assuming a meet and join operation. Some interesting doncturctions like the porduct of galois connections.

[https://www.youtube.com/watch?v=KxeHGcbh-4c](https://www.youtube.com/watch?v=KxeHGcbh-4c)  

minikanren is strongly unification based. it is using search for the unification map. In simplest form [UniMap]

[https://github.com/JeffreyBenjaminBrown/learn-logict](https://github.com/JeffreyBenjaminBrown/learn-logict)

https://www.msully.net/blog/2015/02/26/microkanren-%CE%BCkanren-in-haskell/

[https://gup.ub.gu.se/file/207634](https://gup.ub.gu.se/file/207634) logic typed variable claesson

[http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification](http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification) unification.

[http://webyrd.net/arithm/arithm.pdf](http://webyrd.net/arithm/arithm.pdf)

[https://ro-che.info/articles/2017-06-17-generic-unification](https://ro-che.info/articles/2017-06-17-generic-unification) unification-fd . 

[https://winterkoninkje.dreamwidth.org/100478.html](https://winterkoninkje.dreamwidth.org/100478.html)

unification-fd inserts itself in the same position Fix does.

Lattices. Subsumption lattice for unufication. More and less general partial order. meet and join. top and bottom

## Notes from 2017 -Resolution and unification

So I was learning about about minikanren. There are some videos online. Minikanren is a logic programming language (like Prolog) that embeds easily into other languages because it has a small core.

Logic programming is weird mainly (partially) because you define relations rather than functions. Relations do not have a input output relationship like functions do. In a sense they are like functions where you get to choose which thing is output and which things are input. Pretty crazy.

The most obvious way to do this to me is to make every function a bag of functions. Just write one function for every possible choice of output variable. These functions may need to be non-deterministic, outputting multiple possibilities, for example for y = x^2 gives x = +sqrt(y) or -sqrt(y). However, this isn't really how logic programs are written. Instead they deduce how to use a relation as a function.

I find most intro to prolog stuff off putting, talking about socrates(man), when that is not a problem I have ever given a crap about.

Resolution is the classical logic version of function composition.

a-> b and b->c can be combined easily into a function a-> c.

Implication in classical logic is weird. It translates to

a->b  ====> (not a)  or b

When a is true, b has to be true. When a is false, b can be true or false.

For the statement a implies b to be true then it needs to evaluate to false only when a is true and b is false

not  (a and (not b))

using De Morgan's law you can distribute nots turning ands into ors.

Then that becomes

(not a) or b.

If you have

((not a) or b) and ((not b) or c)

it does not matter what b is really because either b or not b will be false

so this is equivalent to

(not a) or c

since at least one has to be true to make the whole expression true

Unification

Predicate logic allows propositions to depend on variables. Think Prolog.

A simple question given two expressions is whether there are values of the variables that make the expressions equal.

I do this in my head sometimes when I'm looking a a parametric haskell type.

The type variables need to be matched up with two different expressions.

Sometimes this can be too hard to do in my head, especially when the type variables end up being functions.  So there is need for an algorithmic procedure. I mean, also because you want a computer to do it.

First off, let's suppose we have the two expressions in tree form.

Nodes can be Or, And, Predicates, Not.

We'll want them in some canonical form too so that we don't get tripped up by the commutativity or distributivity of Boolean operators

We need to collect up a bucket of deduced equivalences as we go down the trees of the two expressions. Whenever we hit a variable, we check if we have a substitution in our bucket. If so, replace it. If not, we put into our equivalences that variable is equal to whatever the other expression has in that place. When we hit something that trips us up, we announce failure and the expressions couldn't be unified.

The prolog algorithm is roughly guess a pair of terms in the goal (the executing state) and knowledge base (the code base) that will unify. Try to unify them. If they do, then use resolution to get rid of those terms.

Like what if we reflected into Eisenberg's Stitch? Or what was Weirich's thing? People have been talking about intrinsically typed system-F lately.
