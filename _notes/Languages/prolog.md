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

- [Examples](#examples)
  - [Hello World](#hello-world)
  - [Things that are prolog](#things-that-are-prolog)
  - [Lists](#lists)
  - [Difference Lists](#difference-lists)
  - [Copy Term and Structural Matching](#copy-term-and-structural-matching)
  - [Term rewriting](#term-rewriting)
  - [Small Step Semantics](#small-step-semantics)
  - [Hoare Logic](#hoare-logic)
  - [Bunched Logic / Separation](#bunched-logic--separation)
  - [Modal Logic](#modal-logic)
  - [Model Checking](#model-checking)
  - [Typeclass](#typeclass)
  - [Type checking / inference](#type-checking--inference)
  - [Refinement Types](#refinement-types)
    - [Bussproofs printing](#bussproofs-printing)
      - [Categorical Prover](#categorical-prover)
    - [Instruction selection](#instruction-selection)
  - [Lambda](#lambda)
  - [Unification](#unification)
  - [Theorem Proving](#theorem-proving)
    - [Interactive](#interactive)
- [Topics](#topics)
  - [Systems](#systems)
    - [Ciao](#ciao)
  - [SLD resolution](#sld-resolution)
  - [Interesting predicates](#interesting-predicates)
  - [Imperative analogies](#imperative-analogies)
    - [Manual Prolog](#manual-prolog)
  - [Abstract Machines / Implementation](#abstract-machines--implementation)
  - [Modes](#modes)
  - [Single Sided Unifivcation](#single-sided-unifivcation)
    - [DIY Prolog](#diy-prolog)
  - [Verification](#verification)
  - [Modules](#modules)
  - [meta interpreters](#meta-interpreters)
  - [Delimitted Continuations](#delimitted-continuations)
  - [Tabling](#tabling)
    - [XSB](#xsb)
  - [Python](#python)
  - [Prolog II, III IV](#prolog-ii-iii-iv)
  - [Parallel](#parallel)
  - [Macros](#macros)
  - [Coroutines](#coroutines)
  - [Indexing](#indexing)
  - [DCG - Definite Clauses Grammars (DCG)](#dcg---definite-clauses-grammars-dcg)
  - [Constraint Logic Programming (CLP)](#constraint-logic-programming-clp)
    - [clpb](#clpb)
    - [clp(euf)](#clpeuf)
    - [Attributed Variables](#attributed-variables)
    - [Coroutining](#coroutining)
    - [CLP(Set)](#clpset)
  - [CHR](#chr)
    - [Compiling](#compiling)
    - [Examples](#examples-1)
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
      - [Union Find](#union-find)
      - [EGraphs](#egraphs)
      - [Semi naive?](#semi-naive)
    - [Embedding into CHR](#embedding-into-chr)
    - [SQL](#sql)
  - [Answer Set Programming s(CASP)](#answer-set-programming-scasp)
  - [Extralogical features](#extralogical-features)
    - [Database manipulation](#database-manipulation)
    - [Cuts and Such](#cuts-and-such)
- [Functions](#functions)
  - [Lambda](#lambda-1)
    - [HiLog](#hilog)
    - [Alpha prolog](#alpha-prolog)
- [Semantics](#semantics)
- [History](#history)
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
- [Probablistic Logic Programming](#probablistic-logic-programming)
- [Abductive logic programming](#abductive-logic-programming)
- [Equational Logic Programming](#equational-logic-programming)
- [Functional Logic Programming](#functional-logic-programming)
- [Misc](#misc)
  - [2019](#2019)
  - [Notes from 2017 -Resolution and unification](#notes-from-2017--resolution-and-unification)

See also:

- Datalog
- Constrained Horn Clauses
- Constraint Programming (Answer Set programming in particular)
- Scheme (Minikanren)

# Examples

## Hello World

For a SWI prolog program, I need the `initiaization(main,main).` thing to say where to start running.

```prolog
:- initialization(main,main).
main(_) :- 
  writeln("hello world"),
  print("hello world"),
  format("hello world ~p\n", [foo(8)]).
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

Differece lists are related to singly-linked that maintain a pointer to the last element.

```
// something like this.
struct diff_list {
  list * head;
  list * end;  
};
```

You have fast append because you don't have to traverse the list to find the end.

```
append(X-Y,Y-Z,X-Z).
```

## Copy Term and Structural Matching

copy_term is super useful, but questionable from a purist perspective.
<https://www.swi-prolog.org/pldoc/man?predicate=copy_term/2>

I think the issue is moding? copy_term only works in one mode. "proper" prolog works in all modes, or at least has termination issues in some modes. <https://www.metalevel.at/prolog/purity>

copy_term can in principle be define by cases however...? No wait. it can't. We can copy ground terms, which is almost meaningless.
It's an equality predicate also.

copy_term1([],[]).
copy_term1([X|Xs], [X|Ys]) :- copy_term(Xs,Ys).

eq([],[]).
eq([X|Xs], [Y|Ys]) :- X=Y, eq(Xs,Ys).

## Term rewriting

<https://www.youtube.com/watch?v=b2Px7cu2a68>
The context technique is nice. It's a generic representation of context.
This is showing a generic approach where rewrite rules are repreented as a data structure.
But a specialization/partial evaluation is writing them directly in

```prolog
step(fact(0), 1).
step(fact(N), N * fact(N')) :- N #> 0, N' #= N + 1.

normal_form(T,T1) :- 
  map(normal_form, Args),
  step()


conc(F,Ls,Rs)  is f(l3,l2,l1, _, r1, r2, r3)
```

Functional programs using infix equality notation. Slightly different than `fact/2` predicate style.

```prolog
:- initialization(main,main).
:- op(900, xfx, user:(==>)).

fact(0) ==> 1.
fact(N) ==> M :- N1 is N - 1, fact(N1) ==> M1, M is N * M1.

main(_) :- fact(6) ==> N, writeln(N).
```

What is demand driven egglog? It may have a relation to provenance.
Naive equality proof search.

Expect lots of loops and overlap. memoization is useful.

DCG stye proof for depth control? But then
Ah answer subsumption tabling can keep just first answer. Yes.

The rewrite proof reconstruction and this process are related.

```
--> [], .
A == A --> !, [refl].

add(X,Y) == add(Y,X) --> [add_comm].
add(X,add(Y,Z) == add(Y,X) --> [add_assoc].

% generic form
A == B --> {rule(name, A ==> A1)}, [ruleL(name)], A1 == B.
A == B --> {rule(name, B ==> B1)}, [ruleR(name)], A == B1.
X == Y --> [eq_comm], Y == X.
f(X) == f(A) --> [cong].
T1 == T2 --> {T1 ..= [F | Args1], T2 ..= [F | Args2]}, [cong], map(==, Args1, Args2). 
% If I used explicit context, this could be tail recursive?
```

```prolog

:- initialization(main,main).
:- op(900, xfx, user:(===)).

rule(fact(N), fact(N-1)).

```

```prolog

:- initialization(main,main).
:- op(900, xfx, user:(===)).

rule(A + B,  B + A, add_comm).

birule(A + (B + C), (A + B) + C, add_assoc).

A === A --> [refl].
A === B --> {rule(A ,A1, R)}, [left(R)], A1 === B.
% it is slightly simpler to just rewrite one side and leave the other as a stopping condition.

%A === B --> {rule(A ,A1, R)}, [right(R)], A === B1.
% A === B --> [eq_symm], B === A.

println(X) :- format("~w\n", [X]).

main(_) :- phrase(1 === 1, Pf), format("~w\n",Pf),
           phrase(1 + 2 === 2 + 1, Pf2), println(Pf2),
           length(Pf3, 0), phrase(1 + 2 === 3 + 1, Pf3), println(Pf3).

```

```prolog
:- initialization(main,main).
:- op(900, xfx, user:(==>)).
:- op(900, xfx, user:(===)).

:- table _ ==> po('@<'/2). % accumulate smallest term according to "standard order"

A === B :- A ==> C, B ==> C1, C = C1.


%A ==> C :- A ==> B, B ==> C. % trans

A ==> A. % refl first or last?

% congruence before rewriting to memoize subpieces
A + B ==> A1 + B1 :- A ==> A1, B ==> B1.

% This is not ematching.
A ==> C :- rw(A, B), B ==> C.

% rw(A1,B), A1 ==> C, B ==> C. 
% This kind of specs to ematching...?
% we might need to freeze the pattern when it gets too big. unfailing completion.



%A ==> B :- B ==> A. % sym? No.

%A + B ==> A + B1 :- A ==> A1.

rw(A,B) :- birw(A,B).
rw(A,B) :- birw(B,A).
rw(A + B, B + A).
birw(A + (B + C), (A + B) + C).

% generic congruence
% A ==> B :- A =.. [F | Args], length(Args,N), length(Args1,N), map('==>', Args, Args1), B =.. [F | Args1].



%f(A) ==> f(B) :- A ==> B. % cong
%foo(A) ==> foo(B) :- A ==> B. % cong
%foo(foo(a)) ==> a.
%a ==> b.
%b ==> c.



main(_) :- writeln(hi), 
  ((9 + 4) + 3) ==> A, writeln(A),
  ((9 + 4) + 3 + 10 + 12) === (12 + 10 + 3 + 4 + 9), writeln(success).
  
  
  %foo(foo(a)) ==> E, writeln(E),
  %b ==> C, writeln(C).

% Any ground ordering is fine.

% https://www.swi-prolog.org/pldoc/man?predicate=term_size/2 includes sharing. interesting
% term_order(T,T2) :- term_size(T,S), term_size(T2,S2), 
%      S < S2 -> 
%        true 
%      ;  T =.. Tl, T1 =.. Tl2, lex(term_order, Tl1, Tl2) 
```

A cure possibly for non confluence.

evaluation relations

```prolog
eval()


```

It is more useful to track by final position rather than by initial query term.
Knuth bendix completion. With respect to a data type of ground rewrite rules, instantiate a pattern

```
match(foo(A), [foo(foo(a)) -> a]) :- 

match(Pat, Pat, _).
match(foo(Pat), foo(T), [ -> foo(T)]) :- match(Pat, []

```

## Small Step Semantics

```prolog
:- initialization(main,main).

value(true).
value(false).
value(zero).
value(succ(V)) :- value(V).

eval(A,A) :- value(A). % not step(A,B). Or put cut here.
eval(A,C) :- step(A,B), eval(B,C).
      % step(A,B) -> eval(B,C) ; done.
step(pred(zero),zero).
step(pred(succ(T)),T).
step(succ(T), succ(T1)) :- step(T,T1).
step(pred(T), pred(T1)) :- step(T,T1).
step(iszero(zero), true).
step(iszero(succ(_)), false).
step(ite(true,T,_), T).
step(ite(false,_,E), E).
step(ite(C,T,E), ite(C1,T,E)) :- step(C,C1).

hastype(zero, nat).
hastype(succ(T), nat) :- hastype(T,nat).
hastype(pred(T), nat) :- hastype(T,nat).
hastype(iszero(T), bool) :- hastype(T,nat).
hastype(ite(C,T,E), Ty) :- hastype(T,Ty), hastype(E,Ty), hastype(C,bool).

main(_) :- eval(pred(pred(succ(succ(succ(zero))))), V), writeln(V).

```

If we go metainterpreter on this, we can evaluate with respect to a list or set of rewrite rules.

```
step(apply(F,X), )

```

## Hoare Logic

<https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html>

```prolog

hoare(P, skip, P).
hoare(P, seq(C1,C2), Q) :- hoare(P, c1, R), hoare(R, c2, Q).
% hoare(P, set(X,V), Q) :- subst(P,X,V,Q). something like this. Not declarative.
% hoare(P, while(C,Inv,B), Q) , a good place for inductive logic programming? 
hoare(P, ite(C,T,E), Q) :- hoare(and(C,P), T, Q), hoare(and(not(C), P), E, Q).

% consequence, We may weaken the post, or strengthen the pre
% a use case for subsumption?
% hoare(P, S, Q) :- hoare(P1, S, Q), P => P1.
% hoare(P, S, Q) :- hoare(P, S, Q1), Q1 => Q.
% or make it same rule.

% weakest precondition is reasonable use of -++ mode. Or maybe +++ mode.

```

## Bunched Logic / Separation

<https://softwarefoundations.cis.upenn.edu/slf-current/toc.html>

## Modal Logic

## Model Checking

[Set Graphs VI Logic Programming and Bisimulation](https://users.dimi.uniud.it/~agostino.dovier/DID/LNC/CONVEGNI/DOVIER_TORINO.pdf)
Bisimulation
co-LP

## Typeclass

```
implements(clone,life(A,T))

impl(tostring, life(A,i64)).
impl(tostring, vec(T)) :- impl(tostring, T).

% associate what trait owns fields
traitfield(tostring, tostring).

dotcall( foo, tostring ) :- type(foo, T), traitfield(Trait, tostring), impl(Trant, T). 
% dotcall(TEnv, foo, tostring)




% annotate everything with lifetimes?

% https://stevedonovan.github.io/rustifications/2018/09/08/common-rust-traits.html
% display, default, format, clone,

% sized
% borrow


% from to

% iterator
```

Typeclass are "functions" from types to instances. Functions in prolog are represented as relations. This is proof threading.

```prolog

eq(bool,
  [ eq(bool,true,true) = true, 
    eq(bool,false,false) = true,  
    eq(bool,true,false) = false,
    eq(bool, false,true) = false ]).

eq(pair(A,B), [eq((A,B),(XA,XB),(YA,YB)) = and(eq(A,XA,YA), eq(B,XB,YB))]) :- eq(A,IA), eq(B,IB).

```

The equational represntation is a separate issue.

Use dicts <https://www.swi-prolog.org/pldoc/man?section=bidicts> for instance dictionaries?

```
instance(eq(bool),  { equal: [X,Y] >> X = Y ->  } ).

```

## Type checking / inference

I probably have something like this somewhere else in my notes
This has something of the flsvor of a declarative statement of the typing rules, readin `:-` as horizontal line.
I'm not being careful about moding.
Not that de bruijn isn't really necessary in the type checking process. Explicit names works ok because I'm not doing any substitution.

```prolog
type(Env, nat(X), int).
type(Env, tt, unit).
type(Env, var(X), TX) :- lookup(Env, X, TX).
type(Env, lam(X, B), TA -> TB ) :- type([X - TA |Env], B, TB ).
type(Env, app(F,X), TB ) :- type(Env, F, TA -> TB ), type(Env, X, TA).

```

3-fix notation can be 2 2-fix operators

```
:- op(|-, fxx).
:- op(:, fxx).

G |- E : T :- .
```

Hmm. in the lambda prolog encdoing of this, thye use implication for var(X).
So env is more of the form [ forall Env, type(E,X,TA) | Env]
but actuall maybe we want to encode that only refining environments.

type(Env-E, lam(X,B), TX -> TB) :- type( [forall E1, type(Env-E1, X, TX) | Env] - E,  )

type(E,X,Tx) :- var(E), forallE_type(X,Tx).
forallE_type(X,Tx) :- lookup(Env, forallE_type(X,Tx))
forallE_type(X,Tx) :- type(E,X,Tx).

fvar(X) onto the assertion environment list.

strcturally recursive copy_term is pure and can produce fresh vars. Kindo f it builds new vars by refining a fhresness source
var(X)

[]

instead of putting it in the type(var(X)) rule.

Relationship to Hindley-Milner. We are using prolog uvars as type variables. This is tricky though.

<https://github.com/bertas/hm_prolog/blob/master/src/type.pl> This is not right to my eye for example.
Using var(A) is cheating.
<https://www.swi-prolog.org/pack/list?p=type_check> a package for typechecking prolog itself with HM
<http://kyagrd.github.io/tiper/>
[Executable Relational Specifications of Polymorphic Type Systems Using Prolog](https://link.springer.com/chapter/10.1007/978-3-319-29604-3_8)
Let generalization
Is generalize even good prolog?

```
type(Env, let(X,E,B), TB) :- type(Env, E, T1), generalize(T1,T2), type([X - T2 | Env], B, TB).

generalize(tVar(A), )
generalize(A -> B)
```

## Refinement Types

Use CLP to build a refinement type system.
<https://arxiv.org/abs/2010.07763>

```prolog



```

### Bussproofs printing

```prolog

proof(bin(G, Rule, PX,PY)) --> proof(PX), proof(PY),
              ,"\RightLabel{", rule(Rule) ,"}", "\BinaryInfC{", sequent(G), "}".
proof(un(G, Rule, PX)) --> proof(PX),
              ,"\RightLabel{", rule(Rule) ,"}", "\UnaryInfC{", sequent(G), "}".
proof(ax(G, Rule)) --> 
              ,"\RightLabel{", rule(Rule) ,"}", "\AxiomC{", sequent(G), "}".


height(ax(_,_), 0).
height(un(_,_,PX), N) :- N := NX+1, height(PX,NX).
height(bin(_,_,PX,PY), N) :- N := max(NX,NY)+1, height(PX,NX), height(PY,NY).




```

#### Categorical Prover

```prolog

%sequent( Hyp, Conc, Var )

:- use_module(library(clpfd)).
%:- table prove/2.
:- use_module(library(solution_sequences)).
%:- op(600, xfy, i- ).

prove(S, ax(S, id)) :- S = (A > A).
prove(S, ax(S, fst)) :- S = (A /\ _B > A).
prove( A /\ B > B, ax(A /\ B > B, snd)).
prove( S, ax(S, inj1 )) :- S = (A > A \/ _B).
prove( S, ax(S, inj2 )) :- S = (B > _A \/ B).
prove( false > _ , initial ).
prove( _ > true  , terminal ).
prove( A > B /\ C, bin(A > B /\ C, pair, P1, P2)) :- prove(A > B, P1), prove(A > C, P2).
prove( A \/ B > C , bin(A \/ B > C, case, P1, P2)) :- prove( A > B, P1), prove( A > C, P2).
prove( A > C, bin(A > C, comp, P1, P2)) :- prove(A > B, P1), prove(B > C, P2).


height(ax(_,_), 1).
height(un(_,_,PX), N) :- N #> 1, N #= NX+1, height(PX,NX).
height(bin(_,_,PX,PY), N) :- N #> 1, N #= max(NX , NY) + 1, height(PX,NX), height(PY,NY).

% maybe explicilty taking proof steps off of a list. using length.
% use dcg for proof recording?


prove(A > A)       --> [id].
prove(A /\ _ > A)  --> [fst].
prove(_ /\ B > B)  --> [snd].
prove(A > A \/ _)  --> [inj1].
prove(B > _ \/ B)  --> [inj2].
prove(false > _)   --> [initial].
prove( _ > true)   --> [terminal].
prove(A > B /\ C)  --> [pair], prove(A > B),  prove(A > C).
prove(A \/ B > C)  --> [case], prove(A > C),  prove(B > C).
prove(A > C)       --> [comp], prove(A > B),  prove(B > C).

:- initialization(main).
%main :- format("hello world", []).
%main :- between(1, 10, N), height(Pf, N), writeln(Pf), prove( w /\ x /\ y /\ z > w, Pf ), print(Pf), halt.
main :- length(Pf, _), phrase(prove(w /\ x /\ y /\ z > w \/ y),Pf), print(Pf), halt.
main :- halt.
```

Yes, the dcg form is very pretty. It's a writer monad of sorts. It is recording a minimal proof certificate that is reconstructable to the full thing pretty easily.

`G --> [tag], D1, D2`
Should be read as

```
  D1        D2
------------------ tag
       G
```

```

prove(Sig , A > B) --> { insert(A,Sig,Sig1) }, [weaken(A)], prove(Sig1, A > B).
prove(A > forall(X,B)) --> , prove(weak(X, A) > B).
prove(A > forall(X,B)) --> {insert(X,Sig,Sig2) }, prove(Sig1, A > B).
prove(Sig, forall(X,A) > ) --> , prove(weak(X, A) > B)

```

Maybe start with implication
prove((A > (B > C)  ) --> [curry], prove( A /\ B > C).
prove((A /\ (A > B) > B ) --> [eval].

Catlog

### Instruction selection

A model of Instruction selection can be viewed as related to a parsing problem. A parse is building a tree out of a linearized sequence. Instruction selection is finding a linear sequence of machine instructions to represent an expression or sequence of high level statements.

```prolog
% isel(R0, select( ,A + B)) --> {B := }

isel(R0, lit(A))    --> [mov(R0, A)]. % {integer(A)},
isel(R0, A + A)     --> [lsl(R0, R1)], isel(R1, A).
isel(R0, A + B * C) --> [fma(R0, RA,RB, RC)], isel(), sel().
isel(R0, A + B)     --> [add(R0, R1, R2)], isel(R1, A), isel(R2, B).
isel(R0, A * B)     --> [mul(R0, R1, R2)], isel(R1, A), isel(R2, B).
%isel(R0, binop(Op, A, B))     --> [mul(R0, R1, R2)], isel(R1, A), isel(R2, B).

% note storage restrictions.
% isel(reg(R0), A + B)     --> [add(reg(R0), reg(R1), reg(R2))], isel(reg(R1), A), isel(reg(R2), B).
% spill?
% isel(R0, A) --> [mv(R0, R1)], isel(R1, A). %optional copy. Bad rule


% liveness.
% isel(LiveSet, ) --> [add(R0,R1,R2)], { Live1 = Live \ R0 + R1 + R2 } , isel(LiveSet)
% maybe use bitvector?
% No give varoables unique identifiers, skolem style? id(1, Expr), id(2, Expr), 

:- initialization(main,main).
main(_) :- phrase(isel(R0, lit(2) + lit(7)), Asm), print(Asm), halt.
```

## Lambda

Higher Order Unification
Embeddable nonimal unification
Unification

```
unify(A,B) :- var(A), var(B)
```

```
subst(X,V,E,E1) :- 
```

maps from ground variables to prolog vars for interpreters

```
[x - X, y - Y, z - Z]
```

```prolog
:- initialization(main,main).
main(_) :- T = [append([],A,A), append([X|Xs], Y, [X|Zs]) :- append(Xs,Y,Zs)],
      numbervars(T,0,End),
      length(Vs, End),
      writeln(Vs).




```

Can you make pure data structures that respect monotonicity.
They ought to defer or freeze rather than make judgements on variables.

## Unification

```prolog
find(Env,K,) :- 
  lookup(Env,K,V),
  (V == $'var'(N) ->
   find(Env, V, )
   ; 
   
   )




union(Uf, X, Y) :- 
  lookup(Uf, X, Xv), lookup(Uf, Y, Yv), Xv = Yv.

find(Uf,X,V) :- lookup(Uf,X,Xv).

unify(Env,'T1,T2) :- 
  eval(T1,T11), eval(T1,T22),
unify(Env, term(F,Arg), term(F,Arg1)) :-
 maplist(unify(Env, Arg, Arg1)).
unify(Env, $VAR(N), T) :-
    eval(T,T1), lookup(Env, $VAR(N), T1).


```

```prolog


%macro(ex(X,E)) :- 
  


```

[set unification](https://arxiv.org/pdf/cs/0110023.pdf)
list based vs union based reps
Set constraints
{log}
boolean unification

## Theorem Proving

Last chapter of bratko. Building a resolution prover using asserta. PyRes?

```prolog
% unify with occurs check? No. We don't need occurs check
theorem(Poslist,Neglist).
resolve(A-B,C-D) :- remove(Form, B,B1), remove(Form, C,C1), Q=A+C1, P=B1+D. % sort of a hash join

```

[Leantap](https://formal.iti.kit.edu/beckert/leantap/)
Jens Otten
[How to Build an Automated Theorem Prover. Invited Tutorial at TABLEAUX in London/UK](http://www.jens-otten.de/tutorial_tableaux19/)

[A simple version of this implemented in tau prolog](https://www.philipzucker.com/javascript-automated-proving/) Prdocues proofs translated to bussproofs latex

[a pearl on SAT and SMT solving in prolog](https://www.sciencedirect.com/science/article/pii/S030439751200165X) [code](http://www.staff.city.ac.uk/~jacob/solver/index.html)

[Backjumping is Exception Handling](https://arxiv.org/abs/2008.04720) throw and catch implement backjumping for a sat solver

[PRESS: PRolog Equation Solving System](https://github.com/maths/PRESS) as described in the art of prolog book. also has an lp solver?
Pretty interesting tehcniques. If a variable is in a single position, you can unfold the expression. 2. you can apply quadratic equations and stuff 3.
Is it kind of a zipper to isolate a variable?

[tarau Formula Transformers and Combinatorial Test Generators for Propositional Intuitionistic Theorem Provers](https://arxiv.org/abs/1910.01775)

Dyckhoff g4ip

### Interactive

Teyjus
ACL2 analogy. ACL2 is modelling a pure lisp.

```prolog
axiom(P) :- asserta(P).
qed(F,Prf) :- check(F, Prf), asserta(F).

main(_) :- 
  axiom(a),
  axiom(b),
  lemma(a(X) :- b(X))

```

```
% lexical scope. We could do this as a macro?
let(X, e, let(X, e,  X).

```

isabelle style

```prolog
:- dynamic proven.


% "difference list" form of a proof fragment
[A] > (A | foo(x) )  

proven(edge12,  [] > edge(1,2)).
proven(edge23,  [] > edge(2,3)).
proven(trans, [A] > path(X,Z) :- edge(X,Y) :- A).
proven(trans, [A,B] > path(X,Z) :- edge(X,Y) :- A, path(Y,Z) :- B)

asserta(proven(myname, tree)).

```

Using asserta let's us refresh the schematic variable in an axiom

# Topics

## Systems

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
- [trealla](https://github.com/trealla-prolog/trealla) prolog interpreter in C. Not WAM based. tree-walking, structure-sharing, deep binding whatever that means

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
- guan <https://github.com/microsoft/Guan> c# prolog?

### Ciao

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

## SLD resolution

## Interesting predicates

[comparson and unification of terms](https://www.swi-prolog.org/pldoc/man?section=compare)

- `=@=`, variant
- `?=`
- `==`
- `=`
- `/=` a weaker version of dif. Uses negation as fialure in kind of unsatisfactory way

- `=..` destructures a term

- `numbervar` [vanumber](https://www.swi-prolog.org/pldoc/man?section=varnumbers) concretize terms.
- [gensym](https://www.swi-prolog.org/pldoc/man?section=gensym) suggests using content based identifiers
- [termhash](https://www.swi-prolog.org/pldoc/man?predicate=term_hash/2)
- `variant_sha1` a cyrptographic hash? This is acceptable?

[concurrent_forall](https://www.swi-prolog.org/pldoc/man?section=thread)

[`call_with_inference_limit`](https://www.swi-prolog.org/pldoc/doc_for?object=call_with_inference_limit/3)

- <https://www.swi-prolog.org/pldoc/doc_for?object=once/1> once make nondet semidet

## Imperative analogies

Unification variables are pointers. Unifying them is aliasing them.
Unification is bidirectional pattern matching

Prolog predicates are like function calls. The fact that fields can be both input and output is like using output pointers in C. These pointers come in as arguments often.

[Prolog as a Procedural Programming Language](https://www3.cs.stonybrook.edu/~warren/xsbbook/node4.html)

- Assign Once variables - because of this assignment can be symmetrical
-

We can abuse the precedure calls of a host languages. This is related to minikanren, but minkanren doesn't use depth first search

### Manual Prolog

Proplog is even weaker than datalog. Pure propositional variables with no arguments.

```python
# We use sequencing as , and function calls as heads.
# We could envelope in try catch blocks for calls that don't work out

# a :- b, c.
def a():
  b()
  c()
# b :- c.
def b():
  c()
# c.
def c():
  pass

a() # succeeds.
```

For nondeterminism python generators are a decent guess.
Need to undo unifications.
Can do Cells without persay doing generic unification.
Use python case statements or if then else.

```python
# no path compression
# `is` is python reference equality
class BadUF(): # Cell
  def __init__(self): # *args
    self.parent = self
  def find(self):
    x = self
    while x.parent is not x: #  or x is not instance(Cell)
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

```
# a(Stuff) :- b(Stuff), c(Stuff).
# a(Stuff) :- c(Stuff)
def a(s):
  for s in b(s.copy()):
    for s in c(s.copy()):
      yield s
  for s in c(s.copy()):
    yield s

class Env(dict):
  def find():
  def __set__(self):
    #calls find
    #does unification.
  def __get__(self):
    #calls find.
  def fresh(self):
    self[len(self)] = len(self) 
    return len(self)

def append(x,y,z,s):
  s1 = s.copy()
  s1[x] = []
  s1[y] = s1[z]
  yield s1
  a, b, c = freshes(s, 3)
  s[x] = (a,b)
  s[z] = (a,c)
  yield from append(b,y,c,s)


```

Yeah. This amounts to a goofy minikanren where I've inlined combinators.

```ocaml
type goal = string (* Propsoitional *)
type goalstack = goal list
type state = goalstack list

type clause = goal * (goals list) (*  (goal list) list String.Map.t  *)



let rec sld_step prog = function
  | [] -> failwith "fail" (* nothing more to try *)
  | [] :: totry -> failwith "succeed" (* all goals cleared *)
  | ( (g :: gs) :: todo) -> 
            let bodies = lookup prog g (* Lookup also does unfication in real version *)
            let newgoals = List.map bodies ~f:(fun body -> body :: gs)
            sld_step prog (newgoals :: todo)

type table = 

let rec slg_step prog table resume_stack gen_stack
 = match resume_stack with
 | [] -> failwith "fail"
 | (cnode, solution) :: rs -> 


```

SLD resolution in stack form. You have a stack of goal sets. It isn't that bad because you're actually sharing a lot of repeated goals.

SLD in tree search form? The stack is some kind of manifestation of the tree. We could perhaps store the tree as a zipper instead

## Abstract Machines / Implementation

[Warren's Abstract Machine: A Tutorial Reconstruction.](http://wambook.sourceforge.net/wambook.pdf)

Paul Tarau showing an interesting compilation strategy. <https://popl21.sigplan.org/details/PADL-2021-papers/5/A-Family-of-Unification-oblivious-Program-Transformations-and-Their-Applications>
<https://github.com/ptarau/LogicTransformers>

binprolog. Translate to binary relations

structure copying vs structure sharing

Term indexing

Original Dec-10 prolog paper

[discussion on scryer forum](https://github.com/mthom/scryer-prolog/discussions/1457)

BAM - berkeley abstract machine [Can Logic Programming Execute as Fast as Imperative Programming?](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.68.9970&rep=rep1&type=pdf)
[Peter Van Yoy's thesis](https://www.info.ucl.ac.be/~pvr/Peter.thesis/Peter.thesis.html)
<http://lambda-the-ultimate.org/classic/message1618.html#11082>
[Andrew Taylor's thesis  - high performance prolog implementation](http://www.info.ucl.ac.be/people/PVR/Taylor.thesis.ps)

[comparsion of WAM and ZIP](https://stackoverflow.com/questions/4478615/alternatives-to-the-wam/4504325#4504325)

VAM

TOAM - tree oriented abstract machine

[global optimization in a prolog compiler for TOAM](https://core.ac.uk/download/pdf/82489071.pdf)

## Modes

In some ideal world, it's great if every predicate is reversible, but it isn't the case. Different variable positions can be used in different ways, input, output, both. They can also have total functional character (exactly one answer), partial functional character (one or zero), of nondeterminisitc (many answers).
Modes are required to use predicates correctly. Annotating them may allow the compiler to be more efficient. The compiler may infer them. They are conceptually interesting also in theorem proving contexts. See bidirectional typing.

mercury
ciao prolog

## Single Sided Unifivcation

picat pattern matching

<https://www.swi-prolog.org/pldoc/man?section=ssu>

Maybe not even that complicated? Claims it a fairly simple macro. Use `==`

```prolog


```

### DIY Prolog

[a python interpreter](https://github.com/photonlines/Python-Prolog-Interpreter)

<https://curiosity-driven.org/prolog-interpreter>

Prolog and es6 generators <https://curiosity-driven.org/prolog-interpreter>

<https://news.ycombinator.com/item?id=2152570>

<https://cs.stackexchange.com/questions/6618/how-to-implement-a-prolog-interpreter-in-a-purely-functional-language>

[andrej bauer's pl zoo prolog](http://plzoo.andrej.com/language/miniprolog.html)

[1985 pascal design and implementation of prolog interpreter](https://core.ac.uk/download/pdf/228674394.pdf)

## Verification

## Modules

## meta interpreters

[power of prolog - A Couple of Meta-interpreters in Prolog](https://www.metalevel.at/acomip/) [video](https://www.youtube.com/watch?v=nmBkU-l1zyc&feature=youtu.be&ab_channel=ThePowerofProlog)

[metapredicates](https://www.metalevel.at/prolog/metapredicates#call)
`call/N` in principle could be implemented in prolog itself.

```prolog
:- initialization(main,main).
foo(7).
main(_) :- call(foo(X)), print(X).
```

Things you can do:

- tracing parameter "proof"
- Change evaluation order of goals or clauses
- Change unification - occurs check, attributed vars
- continuations
- fair interleaving
- abstract interpetation
- partial evaluation

absorption and reification

```prolog
:- initialization(main,main).
% surprisingly raw Goal is implicit call/1
mi0(Goal) :- Goal.

main(_) :- mi0(mi0(append([12],[42],X))), print(X).
```

Advantages to _not_ using prolog syntax.

metacircular interpeter - interpreter can interpret self
<https://news.ycombinator.com/item?id=19283803>

```prolog
:- initialization(main,main).
mi([]). % empty goal stack
mi([G,Gs]) :- clause_(G,Body), mi(Body), mi(Gs).

% define rules of metainterpreter itself
clause_(mi([]), []).
clause_(mi([G | Gs]), [clause_(G,Body), mi(Body), mi(Gs)]).

% what does this mean? This is a weird one.
clause_(clause_(G,Body), []) :- clause_(G,Body).

```

[Prolog meta-interpreter with difference lists](http://lambda-the-ultimate.org/node/2984#comment-43853)

```prolog
:- initialization(main,main).
mi([]).
mi([G|Gs]) :-
        mi_clause(G, Rest, Gs),
        mi(Rest).


```

Same idea but the body of a clause is represented as a difference list in clause_

`clause/2` is a way to get the rules of a clause.

```prolog

:- initialization(main,main).
clause_(append([],Y,Y), []).
clause_([X | Xs],Ys, [X | Zs]), [append(Xs, Ys, Zs)]).

%mi(Sig, all(X, Body)) :- X = fvar(Sig), Sig1 is Sig + 1, mi(Sig1, Body). 
%mi(all(X, Body)) :- gensym(Sig), X = fvar(Sig), mi(Sig1, Body).
%mi(P, S, A => Body) :- assertz(A), mi(Body), retract(A).
%mi(Sig, ex(X, Body)) :- X = fvar(Sig), Sig1 is Sig + 1, mi(Sig1, Body).  

mi(P,S,pi(X, Body)) :- gensym(fvar, Y), X = fvar(Y), mi(P, [X|S], Body). % could use numbering.
mi(P,S,D => G) :- mi([D|P],S,G).
mi(P,S,sigma(X,G)) :- mi(P,S,G), forall( subterm(X,fvar(Y)), member(fvar(Y),S)  ) 
mi(P,S,+G) :- copy_term(E,P,E1,P1), do_goal(P,S,P1, G) % no this copy term isn't right. copy term hurts. Ah copy_term/4

do_goal(P,S, [G :- B|Gs], G) :- mi(P,S,B).
do_goal(P,S, [_|Gs], G) :- do_goal(P,S,Gs,G).

```

This is wrong.

```prolog

:- initialization(main,main).
:- use_module(library(occurs)).
:- op(1200, xfx, \).
:- op(900, xfy, =>).
% copy_term?
pi(X \ Body) :- gensym(fvar,Y), X = fvar(Y), fvar(Y) => Body.
A => Body :- asserta(A), Body, retract(A).
% https://www.swi-prolog.org/pldoc/man?section=occurs
% https://www.swi-prolog.org/pldoc/man?section=forall2
ex(X \ Body) :- Body, forall(fvar(Y), free_of_var(fvar(Y), X)). % this is checking the wrong thing right?
A /\ B :- A, B.
A \/ B :- A; B.

% seperate the notions?
goal_and().
prog_and().

sterile(J) :- pi(X \ (bug(X) => (in(X,J) => dead(X)))).
dead(B) :- ex(J \ (heated(J) /\ in(B,J) /\ bug(B))).
heated(j).

main(_) :- sterile(j), \+ bug(_B), \+ fvar(_X).
```

Hmm. when I asserta with a variable, I'm asserting the universal thing, not something tied to the variables in scope. That seems really bad.

Oh wow. Also asserta doesn't cleanup on fail. asserta(bar(7)), fail. still leaves bar(7) asserted

chr as the store of new facts.

foo_q(X,Y,Z) \ foo(X,Y,Z) <=> true.
foo_q(X,Y,Z) <=> { foo(x,y,z)}.
foo_q(X,Y,Z) <=> {fail}.

or turn it around

foo(X) :- foo_q_chr(X). % see if chr query succeeds
% else regular other clauses.

CHR +

How can I automatically associate chr with

assert_chr(foo, Args)
retract_chr(foo, Args), assert(foo, Args) <=> true.
assert_chr(T,Args) \ query_chr(T, Args) <=> true. % hmm. does this unify the stuff in the assert, destroying it's universal quantification?
% <https://www.swi-prolog.org/pldoc/man?section=compare>
assert(T) \ query(T1) <=> { unifiable(T1, T), copy_term(T, Tc), Tc = T1 }.
This might fix that problem. Very ugly.

Does this have proper backtracking semantics though? No. Probably not. I don't think chr makes choice points.
If unificable fails, great it continutes, but if something _later_ fails it won't backtrack.
We could try and control which rule applies via some kind of number, a choice point placed _before_ we call chr_query.
Getting quite arcane.
assert(T) \ query(T1) <=> { unifiable(T1, T), copy_term(T, Tc), Tc = T1 ; fail}.

This is insanity.
Wow, shallowly embedding harrop clauses in prolog is hard/impossible.

Naw, why even seaprate out the args? Maybe better indexing, but screw it for now.
assert_chr(foo(Args)).
I might be building a prolog (meta?) interpreter in chr.

locally nameless encoding of exists. do opening with X. no copy_term of program clauses.

```
open(evar(N),N,X,X).
open(evar(M),N,X,evar(M)) :- dif(N,M).

close(). Hmm. Maybe we never need to close.

mi(S, P, all(B)) :- gensym(X), open(B,0,fvar(X), B1), mi([fvar(X)|S], P, B1).
mi(S, P, ex(B)) :- open(B,0,X,B1), mi(S,P,B1), extrude_check(S,X).
mi(S, P, D => G) :- mi(S,[D|P], G).
mi(S, P, +G) :- 
mi(S, P, +G) :- call(G). %native call

% de bruijn the named rep. This is close I guess.
bruijn(T,T1) :- number_var(T, T2), bruijn([], T2,T1)
bruijn(Vars, var(N), var(I)) :- index(Vars, N, I).
bruijn(Vars, ex(X,B), ex(T1)) :- bruijn([X|Vars], B, T1). 

mi(Sig, Env, Prog, all(B)) :- gensym(X), mi([X | Sig], [X | Env], Prog, B).
% if I distinguish avar(N) from evar(N), Sig is already an Env

mi(Sig, Env, Prog, var(N)) :- lookup(N,Env,V). % and V goes where?
mi(Sig, Env, Prog, +G ) :- subst(G,Env,Sig).

% do subsitution lazily instead of eagerly.


```

normalization by evaluation.
Hmm. What if I did use the lambda library
<https://www.swi-prolog.org/pldoc/man?section=yall>

```
all(L) :- gensym(X), call(L, fvar(X)).
ex(L) :- call(L, Y), extrude_check(Y).
impl(D,G) :-  call(asserta(D), G) -> retract(D) ; retract(D), fail. 
% ok but asserta loses track of current unification variables.
% also problem if G produces multiple answers?
% label_vars(D,D1). asserta(D :- subst(D1, )
% pack it, then unpack it on other side.
% number_vars, term_variables
% https://www.cs.cmu.edu/~fp/papers/ilps91.pdf mentions the assert retract encoding. Mentions that variables are nasty.
```

```prolog
right(_,_,true).
right(S,P,and(B1,B2)) :- right(S,P,B1), right(S,P,B2).
right(S,P,or(B1,_B2)) :- right(S,P,B1).
right(S,P,or(_B1,B2)) :- right(S,P,B2).
right(S,P,impl(B1,B2)) :- right(S,[B1|P], B2).
right(S,P,ex(_X,B)) :- right(S,P,B). % maybe
right(S,P,all(X,B)) :- gensym(X), right([X|S],P,B). % maybe
right(S,P,+A) :- member(D,P), left(S,P,D,A). %decide

% alternate name: clause deonstruct, focused.
left(_,_,A,A).
left(S,P,impl(G,D), A) :- left(S,P,D,A), right(S,P,G).
left(S,P,and(D1,_D2), A) :- left(S,P,D1,A).
left(S,P,and(_D1,D2), A) :- left(S,P,D2,A).
left(S,P,all(_X,D), A) :- left(S,P,D,A). % maybe



```

Before unify throw signal (attrbuted var).
WHy this is wrong:
Generally, trying to use the wrong kind of variable is a road strife with peril.

- When we use P, we destroy the universal quantifications within. If we copy, we destroy the connection to the existential variables. This is also one of the problems of using `asserta`. `copy_term` allows you to add variables to be renamed, but not the ones to be shared. This is the opposite of he behavior we want

It is somewhat natural to expect that lambda terms might be useful. <https://www.swi-prolog.org/pldoc/man?section=yall>
<https://www.swi-prolog.org/pack/list?p=lambda>
<https://swi-prolog.discourse.group/t/yall-lambda-arguments-visibility/5112/2> This example is evidence that the implementation of yall may not scope as lambdas should.

Let us go under the (quite possibly faulty) assumption that the story on lambdas is clear in prolog.
One can manually lambda lift, defunctionalize, closure convert if you want to.

Lambda's in `yall` only produce goals, so far as I can tell. So if you want them to produce terms, that needs to come in as another paramter by convention. This feels a bit like continuation passing or output parameter passing.

```prolog
:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- initialization(main,main).
:- use_module(library(occurs)).

extrude_check(S,T) :- writeln([ex_check, S, T]), forall((sub_term(X, T), ground(X), X = fvar(Y)), member(Y,S)). 

right(_,_,true).
right(S,P,and(B1,B2)) :- right(S,P,B1), right(S,P,B2).
right(S,P,or(B1,_B2)) :- right(S,P,B1).
right(S,P,or(_B1,B2)) :- right(S,P,B2).
right(S,P,impl(B1,B2)) :- right(S,[B1|P],B2).
right(S,P,ex(L)) :- call(L,X,G), right(S,P,G), writeln([ex,X]), extrude_check(S,X).
right(S,P,all(L)) :- writeln(all), gensym(v,X), call(L,fvar(X),G), right([X|S],P,G), writeln([exit_all, G]).
right(S,P,+A) :- member(D,P), writeln([pick,P, D,A]), left(S,P,D,A), writeln([D,A]). %decide

% alternate name: clause deonstruct, focused.
left(_,_,+A,A).
left(S,P,impl(G,D), A) :- left(S,P,D,A), right(S,P,G).
left(S,P,and(D1,_D2), A) :- left(S,P,D1,A).
left(S,P,and(_D1,D2), A) :- left(S,P,D2,A).
left(S,P,all(L), A) :- call(L,X,D), left(S,P,D,A). % maybe


%main(_) :- P = [
%  all( [J, T] >> T = impl(all([X,T1] >> T1 = impl(and(bug(x), in(x,J)), dead(x)), sterile(J))),
%  all( [B, T] >> T = impl(ex([J,T1] >> T1 = and(headed(J), and(in(B,J), bug(B)) ) , dead(B))),
%  heated(j) ]


foo(E,G) :- G = all(bar(E)).
bar(E,X,G) :- G = impl(+foo(X), +foo(E)). 
% ;re
query(Q) :- Q = ex([H2,J2] >> (J2 = all({H2} / [Q2,G2] >> (G2 = impl(+foo(Q2),+foo(H2)))))).

main(_) :- 
  P = [
  all([L,T] >> (T = +append([], L, L))),
  all([H,T] >> (T = all([L1, T1] >> 
               (T1 = all([L2,T2] >> 
               (T2 = all([L3, T3] >> 
               (T3 = 
        impl(+append(L1,L2,L3),
             +append( [ H | L1], L2, [H | L3]))))))))))
  ], right([], P, +append([a,D], [c], Z)), writeln(Z),
  right([],[],true), writeln(pass),
  right([],[+a], +a), writeln(pass2),
  right([],[+a,+b], +b), writeln(pass3),
  right([],[all([X,T] >> (T = +foo(X)))],+foo(a)), writeln(pass4)
  , right([], [+append(nil, nil, nil)], +append(nil, nil, nil)) , writeln(pass5)
  , right([], P, +append([], [], X)) , writeln(X), writeln(pass6),

  right([], [], impl(+a,+A)), writeln(A),
  right([], [], impl(and(+a,+b),+b)),
  right([], [], impl(and(+a,+b),+b)),
  right([], [], all([Q,G] >> (G = impl(+foo(Q),+foo(Q))))),
  %\+ right([], [], all([Q,G] >> (G = impl(+foo(Q),+foo(a))))),
  right([], [], all({F}/[Q1,G1] >> (G1 = impl(+foo(Q1),+foo(F))))), writeln(F),

  %right([], [], ex([H1,J1] >> (J1 = impl(+foo(H1),+foo(H1))))),
  writeln(pass7),!,
  %right([], [], ex([H2,J2] >> (J2 = all({H2} / [Q2,G2] >> (G2 = impl(+foo(Q2),+foo(H2))))))),
  writeln(pass8),
  %right([],[],ex(foo)),
  writeln(pass9),
  %query(Q7),
  %right([],[],Q7),
  right([],[],ex([X,Q]>>(Q=all([Y,P]>>(P=impl(+d(X),+d(Y))))))).





  %right([],[],[], append(nil,nil,nil)), print(passed)
.


```

Drinker's paradox example. This shouldn't pass

```prolog

:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- initialization(main,main).
:- use_module(library(occurs)).

extrude_check(S,T) :- writeln([ex_check, S, T]), forall((sub_term(X, T), ground(X), X = fvar(Y)), member(Y,S)). 

right(_,_,true).
right(S,P,and(B1,B2)) :- right(S,P,B1), right(S,P,B2).
right(S,P,or(B1,_B2)) :- right(S,P,B1).
right(S,P,or(_B1,B2)) :- right(S,P,B2).
right(S,P,impl(B1,B2)) :- right(S,[B1|P],B2).
right(S,P,ex(L)) :- call(L,X,G), right(S,P,G), writeln([ex,X]), extrude_check(S,X).
right(S,P,all(L)) :- writeln(all), gensym(v,X), call(L,fvar(X),G), right([X|S],P,G), writeln([exit_all, G]).
right(S,P,+A) :- member(D,P), writeln([pick,P, D,A]), left(S,P,D,A), writeln([D,A]). %decide

% alternate name: clause deonstruct, focused.
left(_,_,+A,A).
left(S,P,impl(G,D), A) :- left(S,P,D,A), right(S,P,G).
left(S,P,and(D1,_D2), A) :- left(S,P,D1,A).
left(S,P,and(_D1,D2), A) :- left(S,P,D2,A).
left(S,P,all(L), A) :- call(L,X,D), left(S,P,D,A). % maybe


main(_) :- right([],[],ex([X,Q]>>(Q=all({X} / [Y,P]>>(P=impl(+d(X),+d(Y))))))).
```

<https://github.com/SWI-Prolog/swipl-devel/blob/master/library/yall.pl> yall implementation
copy_term_nat(Free+Lambda, Free+LambdaCopy), is a way to copy_term but also share variables in the Free list. We copy and then unify. Nice.

```
lambda_functor(Term, Functor) :-
    copy_term_nat(Term, Copy),
    variant_sha1(Copy, Functor0),
    atom_concat('__aux_yall_', Functor0, Functor).
```

This is interesting. Determinsitically creating a functor name based on the sha1 of the context

We could also implement scoping the usual way, not trying to pull a fast one by reusing prolog mechanisms.
de bruijn indices or locally nameless
This brings it's own peril. We are treated prolog as a functional or imperative language here.
Oleg has an example where he uses pure constructs.
If we want to make this generic
[ndexing dif/2](https://arxiv.org/pdf/1607.01590.pdf)

```prolog
:- use_module(library(reif)).
:- use_module(library(terms)).
:- use_module(library(clpfd)).
:- initialization(main,main).
open_(X,N,T,T1) :- if_(T = lam(B), 
                      (N1 #= N + 1, T1=lam(T2), open_(X,N1,B, T2)) ,
                   if_( T = var(N), 
                       T1 = X,
                   mapargs(open_(X,N), T, T1) % https://www.swi-prolog.org/pldoc/doc_for?object=mapargs/3
                   )).
%close() maybe unecesaary?
main(_) :- writeln(hi), open_(a, 0, lam(var(1)), T), writeln(T).

```

We don't need to open persay, since we mostly/entirely just need evaluation?
It's the same as open except doing it eagerly vs lazily / batching the traversal.

```prolog
right(T1 = T2) --> {unify(T1,T2)}.
eval(S,E,evar(N), V) :- lookup(E,N,V).
eval(S,E,avar(N), V) :- lookup(S,N,V).
eval(S, E, F, R) :- 
unify(S,E,T1,T2) :-
unify(S,E,apply(F,Args), )

% hmm. keeeping E and S vars on same stack is useful because that says what is in scope

```

We still have a scope extrusion check.
An exmample:
????
Existentials should really be being filled in with terms that exist at the time that binder is being opened. The unfication variable is a standin, delaying picking a term so that we can deduce at it should have been, but it is not protected from unifying with forall quantified variables that didn't exist at the time of it's creation. These would not have been legitimate concrete terms

By analogy with the occurs_check, we might choose to just not worry about this and hope for some kind of systems magic flag to come along later.
Attributed variables might also enable pushing unifiation
The interpreter could also insist on treating `=` specially. It is difficult to avoid accidentally using native prolog unfication both in the interpreter, but also in the interpretted programs.

```
term_lam(X \ B) :- [G|X] \ (G = B). % does this make sense? Fishy. term_lam = \\ notation

```

So a natural question is how can we make this interpreter shallower? We are reusing prolog's search mechanisms and unification mechanisms. So that's nice.

Implication is sticky though. One might be tempted to use `asserta` which make dynamic databases. Naive use of this is not right

- asserta considers all unification variables to be universals. It breaks the correlation of the program database with the goal
- retracting the implication once you leave the scope of it is tricky. Yes `retract` exists. But it is not clear to me

assert and retract are manipulating a global database store. This is a leaky abstraction and somewhat doomed to failure IMO. Imagine trying to implement function calls using a global memory. Ok I guess you could do it by maintaining your own stack.

By analogy with file handles, we may think some kind of bracketing expression may help. `setup_call_cleanup(asserta(D), G, retract(D))` <https://www.swi-prolog.org/pldoc/doc_for?object=setup_call_cleanup/3> No. This doesn't retract at the right point. The search may exit the implication but then return to it on backtracking. This doesn't retract until G won't be called anymore.

Ok, well perhaps we never call retract, but instead key on an identifier of what branch we are in.
And to deal with the sharing problem, we could replace all E vars in the program clause with keys that access them from a store.
It really feels like we're plugging up hole after hole on a leaky ship.

DCGs can be used to clean up the state carrying a bit, since so may rules do not involve state.
<https://www.swi-prolog.org/pack/list?p=edcg>
<https://www.metalevel.at/prolog/dcg>

```prolog
:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).

right(true).
right(and(B1,B2)) --> right(B1), right(B2).
right(or(B1,_B2)) --> right(B1).
right(or(_B1,B2)) --> right(B2).
right(impl(B1,B2)), [s(_,_,P)] --> [s(_,_,[B1|P])], right(B2).
right(ex(L)), [s(_,E,_)] --> [s(_,[X|E],_)], {call(L,X,G)}, right(S,P,[X|E],G).
right(all(L)), [s(S,_,_)] --> [s([X|S],_,_)], {gensym(X), call(L,X,G)}, right([X|S],P,E,G).
right(+A) --> member(D,P), left(D,A). %decide

left(A,A).
left(impl(G,D), A) --> left(D,A), right(G).
left(and(D1,_D2), A) --> left(D1,A).
left(and(_D1,D2), A) --> left(D2,A).
left(all(L), A) --> {call(L,X,D)}, left(D,A).

```

Higher order unification is a separate issue. If we are already overloading unification, it is probably not that hard to treat.
Miller pattern unification is a subcase of higher order unification that is easy. The idea is to restrict higher order unification to it's bones.

```prolog
:- use_module(library(intercept)).
:- initialization(main,main).

%https://www.swi-prolog.org/pldoc/man?section=intercept

%right(+A) :- send_signal(goal(A)).
% hmm, so that send signal is still in scope of the current intercept it seems like?
%right(impl(D,G)) :- intercept(right(G),goal(A), (writeln(A), D=A;send_signal(goal(A)))).

% implicit contxt being parlayed.
left(D,A) :- D = A.
right(+A) :- send_signal(prog(P)), member(D,P), left(D,A). 
right(impl(D,G)) :- send_signal(prog(P)), intercept(right(G), prog(P1), P1 = [D | P]).

run(G) :-  intercept(right(G), prog([]), true).
 % intercept(right(G),goal(A), (writeln(A), D=A)).
main(_) :-  intercept(send_signal(x), X, writeln(X)),
            %intercept((right(impl(foo(c), impl(foo(b), +foo(A)))), writeln(A)), prog([]), true).
            run(right(impl(foo(c), impl(foo(b), +foo(A))))), writeln(A).
```

So these techniques enable implicit context in different ways. Could receive database per head symbol

```prolog
:- use_module(library(intercept)).
:- use_module(library(yall)).
:- use_module(library(apply)).
:- initialization(main,main).

biz(X) :- get_ctx(facts(P)), member(D,P), D = biz(X). % for non unversal facts this works. call(D,bar(X))
%biz(X) :- X = foo.

% hmm. I want to reenter the continuation mutiple times though? Is that ok?
% ok, so if I just send back the 


bar(X) :- get_ctx(facts(P)), member(D,P), D = bar(X). % for non unversal facts this works. call(D,bar(X))

bar(X) :- get_ctx(clauses(P)), writeln(P), writeln(X), member(D,P), call(D,bar(X)). % for non unversal facts this works. call(D,bar(X))


% bar(a).


% essentially, reader monad

foo(X) :- send_signal(clauses(P)), member(D,P), call(D,foo(X)).

% mayb send_silent_signal is useful here
% or perhaps catch the error of a missing prog(P).
% use intercept/4 just to make sure variables in P don't get screwed up?
%impl(D,G) :- get_ctx(facts(P)), intercept(G, facts(P1), P1=[D|P]).

impl(D,G) :- get_ctx(facts(P)), intercept(G, facts(P1), =(P1), [D|P]).

climpl(D,G) :- get_ctx(clauses(P)), intercept(G, clauses(P1), =(P1), [D|P]).


get_ctx(facts(P)) :- catch(send_signal(facts(P)), error(unintercepted_signal(facts(_4104)),_4096), P = []).
get_ctx(clauses(P)) :- catch(send_signal(clauses(P)), error(unintercepted_signal(clauses(_4104)),_4096), P = []).

% could maintan seprate lists per functor, but what's the point?
setup_db(G) :- intercept(G,prog(P),P=[]).

buz :- writeln(ap), bar(a), send_signal(facts(P)), writeln([facts,P]), bar(b), writeln(succed_b).

bar_clause(X, G) :- G = bar(X).
biz_clause(G) :- G = bar(X), writeln(X), biz(X).
main(_) :- 
  % yes it traverses to the outer intercept
 %intercept(intercept(send_signal(foo), bar, writeln(bar)), foo, writeln(foo)),
% setup_db((
  %impl(bar(b), impl(bar(c), bar(A))), A \= c, writeln(A), bar(a),

  % \+ impl(bar(_F), (bar(a), bar(b))) % should fail because F needs to be a and b
  %, climpl([G] >> G = bar(a), bar(a))
  %, climpl([G] >> G = bar(a), bar(a))
  %, climpl(=(bar(a)), bar(a)) % this is nice. What if I wanted a body though?
  %, climpl([G] >> (G = bar(X), biz(X)), impl(biz(a), bar(a)))
   climpl(biz_clause, bar(a)) % impl blocks climpl. Hmm. So non interferencing signals don't bubble.
   % Do I need to do  if_( = facts(), P1 = P(),  send_signal()) explicit signal repropgation?
   % intercept(G, Signal, Signal = fact(P) -> doit ; send_signal(Signal))
   % seems very non compostional to require this. Can this be right?
   % Also could use [fact(), clause(), fact()] rep of P
   % or implement impl(D,G) :- climpl(=(D), G). 


  .
% )).
 %intercept((biz(X), send_signal(bar)), bar, X=bar), writeln(X).

% exists is uninterestnig except for scope check.
%pi(L) :- gensym(fvar,X), call(L,X).
pi(L) :- send_signal(fvar(N)), N1 #= N + 1, intercept(call(L, fvar(N1)), fvar(N1), true).

% This seems kind of useful for abductive logic programming. Maybe they have soome tricks?

% more point free combinator tricks rather than using []
% That will be less error prone.
```

```prolog
:- use_module(library(intercept)).
:- initialization(main,main).

% add this clause to mark bar/1 as "scoped dynamic predicate"
bar(X) :- get_ctx(facts(P)), member(D,P), D = bar(X).
% also can have regular global clauses
bar(X) :- biz(X).
bar(c). 

impl(D,G) :- get_ctx(facts(P)), intercept(G, facts(P1), =(P1), [D|P]).
get_ctx(facts(P)) :- catch(send_signal(facts(P)), error(unintercepted_signal(facts(_)),_), P = []).

main(_) :- impl(bar(a), (bar(X), impl(bar(b), bar(Y)))), writeln(X), writeln(Y).


% no it does pass signals through.

%main(_) :- intercept(intercept(send_signal(foo(X)), bar(X), writeln(bar)), foo(X), writeln(foo)).

```

They don't cover (maybe) the problem of keeping universal variables universal but existentials linked

```prolog
%:- initialization(main,main).

right(+A) :- shift(goal(A)).
right(impl(D,G)) :- reset(right(G), goal(A), Cont), 
  (Cont == 0 ->
  true;
  (A=D ; shift(goal(A))), call(Cont)).

main(_) :-  reset(right(impl(foo(c), impl(foo(b), +foo(A)))), goal(_), Cont), 
(Cont == 0 -> writeln(A) ; fail).
```

## Delimitted Continuations

Continuations are a reification of a call stack. The call stack in prolog is a goal stack.
When you

[swipl manual entry](https://www.swi-prolog.org/pldoc/man?section=delcont)
[schrivers et al](https://www.swi-prolog.org/download/publications/iclp2013.pdf)
[disjunctive delimited control](https://arxiv.org/pdf/2108.02972.pdf)
[Tabling as a Library with Delimited Control](https://biblio.ugent.be/publication/6880648/file/6885145.pdf) <https://arxiv.org/pdf/1507.08087.pdf>
[intercept library](https://www.swi-prolog.org/pldoc/man?section=intercept)preferred because it plays nicer with cuts and things. I don't even understand what the difference is in contract between this and reset/shift.

- effect handlers - implicit state
- definite clause grammars
- coroutines

[DCGs implemented with delimited continuations](https://swi-prolog.discourse.group/t/dcgs-implemented-with-delimited-continuations/1921)
[Conitnuations in prolog](https://occasionallycogent.com/continuations_in_prolog/index.html)
[exmaple usage in prolog](https://github.com/kamahen/nerdle/blob/main/cw631.pl)

## Tabling

Tabling is a kind of auto-memoization. It can make queries terminate that no longer did, and the caching can speed others up.

[Tabling as a Library with Delimited Control](https://biblio.ugent.be/publication/6880648/file/6885145.pdf) <https://arxiv.org/pdf/1507.08087.pdf>
[Swi prolog manual](https://www.swi-prolog.org/pldoc/man?section=tabling)
[Programming in Tabled Prolog - Warren](https://www3.cs.stonybrook.edu/~warren/xsbbook/book.html)
[Tabling as Concurrent Machines](https://www3.cs.stonybrook.edu/~warren/xsbbook/node15.html)

[Tabling with Answer Subsumption: Implementation, Applications and Performance](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.294.9893&rep=rep1&type=pdf)

[Tabling with Sound Answer Subsumption](https://arxiv.org/pdf/1608.00787.pdf)
[Fixing non-determinsim](https://lirias.kuleuven.be/retrieve/383155)

[Linear Tabling Strategies and Optimizations](https://arxiv.org/abs/0705.3468) - kind of a combo of iterative deepening and tabling. Iterate top level goal and memoize true solutions. Just kill it on looping. Eventually, you'll stabilize

```
:-table p/2.
p(X,Y):-p(X,Z),e(Z,Y).
p(X,Y):-e(X,Y).
The transformed predicate is as follows:
p(X,Y):-p(X,Z),e(Z,Y),memo(p(X,Y)).
p(X,Y):-e(X,Y),memo(p(X,Y)).
p(X,Y):-check_completion(p(X,Y)).
```

calls memo on success. This is probably not how tabling is implemented in SWI, but it's interestign. Hmm. I don't really see how al this state tracking is possible/easy as user prolog.

[A simple scheme for implementing tabled logic programming systems based on dynamic reordering of alternatives.](https://www.cs.nmsu.edu/~gupta/tabling/tab.pdf) DRA.
 Simplifying dynamic programming via mode-directed tabling
 Mode-directed tabling for dynamic programming, machine learning, and constraint solving

OLDT vs SLG

Memoization of prolog is two different issues: Dealing with metavariables and dealing with search
WHat is the search space of prolog? Nodes are goal stacks, edges are rules. Using DFS to traverse a graph goes out of control, even a DAG does lots of retraversal.
Memoizatin of prolog goals is differet to purely functional moemization. The metavariables matter and are in a sense return parameters a la C. So you have to memoize different metavairable paramters as different things, because they are in a sense different functions.

Fib and Fact are terminating even if exponentially slow. It's hard to think of a simple high school math example that might be defined in a potentially non terminating way. THe edge-path query is an easy prolog example.

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

<https://www.swi-prolog.org/pldoc/man?section=tabling-mode-directed>. Mode difreced tabling. Can take minimum answer, first answer, etc. Good for dynamic programming

Longest common subsequence

```prolog
%:- use_module(library(tabling)).
:- table lcs(_,_,lattice(longest/3)).


lcs([], _Ys, []).
lcs(_Xs, [], []).
lcs([X|XS], [X|YS], [X|Zs]) :- lcs(XS,YS,Zs).
lcs([X|XS], [Y|YS], Zs) :- dif(X,Y), (lcs([X|XS],YS, Zs); lcs(XS,[Y|YS],Zs)).

longest(P1, P2, P):-
    length(P1, L1),
    length(P2, L2),
    (   L1 > L2
    ->  P = P1
    ;   P = P2
    ).

:- initialization(main,main).
main(_) :- lcs([1,2,3], [2,7,1,4,2,3,6,5], LCS), print(LCS).
           %lcs([1,2,3], Ys, LCS1), print(LCS1).

```

Hmm. Tabling comes _from_ earley parsing historically. That's interesting.
"Earley deduction"

tabling and packrat parsing [DCGs + Memoing = Packrat Parsing But is it worth it?](https://mercurylang.org/documentation/papers/packrat.pdf)
tabling vs memoing

[Memoisation: Purely, Left-recursively, and with (Continuation Passing) Style](https://arxiv.org/abs/1707.04724)
[More declarative tabling in Prolog using multi-prompt delimited control](https://arxiv.org/abs/1708.07081)

Queries and Answers as separate concepts.

- Variant Tabling - lookup in the table only allows for renaming of variables in the query
- Subsumptive tabling - lookup can also succeed on anything that is

Call similarity vs answer similarity. User defined subsumption

Variant storage and query seems relevant to harrop datalog

Tabling makes an entry in the table when it encounters a goal. When it encounters this goal again it reads from the table

Eddie modelled prolog as a "memoized" (Pred -> Bool). Maybe really (Pred -> Maybe Bool) where the table contains lattice values. (Pred -> Set). SUbsumptive tabling makes Pred ordered too (slash a lattice?). The arrow has to be monotonic.

tnot. Stratified negation. Is this what all the continuations are about? Suspend this goal until the table is complete.
Tabling as a server. The table can store continuations of who is expecting answers next?

Tabling needs to record continuations in order to know who to tell when it discovers a new answer for that query.

```python

edges = [(1,2), (2,3), (3,4), (4,1), (2,1), (14,24)]
ptable = {}

# assert ans as possibility in response to question q
def add_ptable(q, ans):
  answers, conts = ptable[q] 
  if ans not in answers: # don't repeat answers already seen. Inductively, consumers already informed
    answers.add(ans) # add to answer set
    # inform consumers of this question of new answer
    for k in conts:
      k(ans)

# request information about paths starting at x.
def path(k, x): # y unknown aka path(x,Y) with continuation k
  if x in ptable:
    answers, conts = ptable[x]
    conts.append(k)
    for a in answers:
      k(a)
  else:
      ptable[x] = (set(),[k])
      # path(X,Y) :- edge(X1,Y), X1 = X.
      for (x1,y) in edges:
        if x1 == x:
          add_ptable(x, (x,y))
      # path(X,Z) :- edge(X1, Y), X1 = X, path(Y,Z)
      for (x1,y) in edges:
        if x1 == x:
          path(lambda ans: add_ptable(x, (x, ans[1])), y)

# query paths starting from 1
path(lambda ans : print("starts from 1", ans), 1)
#path(lambda ans : print(ans), 1)

add_ptable(1, (1,8))

print(ptable) # note 14,24 data not in there. Not bottom up
path(lambda ans : print("starts from 3", ans), 3)
print(ptable)

path(lambda ans : print("starts from 3", ans), 14)
print(ptable)
```

This somehow didn't have a problem with the recursive answer.
A failing computation may later succeed.
Is it not a problem that we are filling the continuation table excessively?

To make it less spooky, the continuation could be defunctionalized maybe? This would allow us to deduplicate the continuations as we can make a set of the

Very coroutiney. Memoized coroutines?

bounded term depth property. all terms have bounded depth. tabling is guaranteed to terminate
definite programs - no negation
normal programs

[]()
[A Term-Based Global Trie for Tabled Logic Programs](https://www.dcc.fc.up.pt/~ricroc/homepage/publications/2009-ICLP.pdf)
[give reasoning a trie](https://www.en.pms.ifi.lmu.de/publications/PMS-FB/PMS-FB-2020-2/PMS-FB-2020-2-paper.pdf) cool summary of indexing structures

consumers vs generators. First time goal is reached it is egenerator. subsequent are consumers

To what degree can the parts of magic set be seen as analogs of tabling

variant tabling - the magic predicates may be storage of tabling keys / queries

Tabling is "memoized coroutines"
Memoing

There is more variation available in memoizing than I realized.

```python

fib_table = {0:1, 1:1}
def fib(n):
  if n in fib_table:
    return fib_table[n]
  res = fib(n-1) + fib(n-2)
  fib_table[n] = res
  return res

print(fib(3))
```

There are _two_ very distinct sites of interaction with the table. Checking if a query is in the table, vs filling in the table once you know.

If you're worried about a non terminating computation because you end up callign yourself in a loop, you can mark a question as already asked in the table. We lift a nonterminating query to and Option[int] returning query that for some examples of nontermination instead returns `None`.

```python
fib_table = {0:1, 1:1}
def fob(n):
  if n in fib_table:
    #if fib_table[n] == None:
    #  return None
    return fib_table[n]
  else:
    fib_table[n] = None # mark question as asked
  x = fob(n) # now this is an infinite loop
  if x == None: # error handling
    return None
  y = fob(n-1)
  if y == None:
    return y
  res = x + y
  fib_table[n] = res
  return res

print(fob(3))
```

What about memoizing coroutines

Above was tabling/memoizing a determinstic computation
Tabling semideterminstic is easier than full nondeterminism.

path query in semideterministic mode. Either fails or succeeds. Not multiple values.

```python
edge = {0:1, 1:2, 2:0}
path_table = {(x,y) for i,j in edge.items()}
def path(x,z):
  if (x,z) in path_table:
    return True
  for y in edge[x]:
    p = path(y,z)
    if p == True:
      return True
  return False

print(path(0,0))
```

### XSB

XSB prolog has some unsusual features and supposedly the most advanced implementation of tabling.

The manual is quite nice.[manual vol 1](http://xsb.sourceforge.net/manual1/manual1.pdf)

<http://xsb.sourceforge.net/research.html>

```
john[spouse->mary, child->>{bob,bill}]

translates to

fd(john,spouse,mary)
mvd(john,child,bob)
mvd(john,child,bill)
```

model checking
[model checking using tabled logic programming](https://cs.uwaterloo.ca/~jmatlee/Teaching/CS745/PaperPres/XMC.pdf)

term-sets {Var:Goal} let's you talk about the set that corresponds to Goal.
`{X : member(X,[a,b,c])}`
This is related to "first class sets" in datalog
Prolog has `setof`
termsets - save space if factorable in this way compared to "extensionalizing"
egraph equality infects everywhere. equals is equals. termsets aren't saying terms are equal.
egraphs for parse trees?
a(a(a(b(b(b))))) as a string Or maybe symmetric comp form?
S -> aSb
S -> eps

There are different mechanisms for table size restrictions / improve terminating.
radial,

incrmenetal table mainatence. Has a dependency graph. Something like seminaive? Trie based vs not?

Weaker semantics and choosing semantics.

## Python

[easy to call into python now](https://swi-prolog.discourse.group/t/a-bundled-python-interface/6735)
 <https://www.swi-prolog.org/pldoc/doc_for?object=section(%27packages/janus.html%27)>

<https://www.swi-prolog.org/pldoc/man?section=janus-python-package>
`pip install git+https://github.com/SWI-Prolog/packages-swipy.git#egg=janus_swi`

<https://www.swi-prolog.org/pldoc/man?section=janus-call-prolog>
<https://swi-prolog.discourse.group/t/installing-janus-linking-error/6954> note neede same versin of janus a swipl --version installed python3 -m pip install git+<https://github.com/SWI-Prolog/packages-swipy.git@V9.1.18#egg=janus_swi>

```python
from janus_swi import *
print(query_once("writeln('Hello world!')"))
print(apply_once("user", "plus", 1, 2))
print([a["D"] for a in query("between(1,6,D)")])

import janus_swi as janus

janus.consult("trains", """
    train('Amsterdam', 'Haarlem').
    train('Amsterdam', 'Schiphol').
    """)
print([d['Tuple'] for d in
           janus.query("train(_From,_To),Tuple=_From-_To")])
#prolog() # go into repl

janus.consult("stlctype", """
typeof(_,int(N), int) :- integer(N).
typeof(G,plus(X,Y), int) :- typeof(G,X,int), typeof(G,Y,int).
typeof(G,var(X),T) :- member(X-T,G).
typeof(G,lam(X,B),T1-T2) :- typeof([X-T1|G],B,T2).
""")
print(list(janus.query("typeof([],plus(int(1),int(2)),T)")))
print(janus.query_once("typeof([],lam(x,var(x)),T)"))
```

```prolog
```

swi

```prolog
:- initialization(main,main).

main(_) :- 
  py_version,
  py_call(print("Hello World!\n")),
  py_call(sys:getsizeof([1,2,3]), Size), writeln(Size),
  py_call(sys:path, Path), writeln(Path),
  py_iter(range(1,3), X), writeln(X)
  %,py_call(eval("1"), X)
   .

```

## Prolog II, III IV

Cyclic terms. Rational terms. See Condicutive logic programming
[swi prolog comments on rational trees](https://www.swi-prolog.org/pldoc/man?section=cyclic)

[introduction to prolog III](https://www.researchgate.net/publication/220427862_Introduction_to_prolog_III)
[prolog and infinite trees](http://www.softwarepreservation.org/projects/prolog/marseille/doc/Colmerauer-InfTree-1982.pdf)

## Parallel

<https://en.wikipedia.org/wiki/Parlog>
50 years of datalog talks about stuff.

## Macros

<https://swi-prolog.discourse.group/t/new-library-macros/6571> macro library. Seems nice
[triska on macros](https://www.metalevel.at/prolog/macros)

```prolog
:- use_module(library(macros)).
#define(max_size, 100).

```

<https://www.swi-prolog.org/pldoc/man?section=progtransform>
`goal_expansion`
`term_expansion`

Can I use macros to make better scoping?

```prolog
:- initialization(main,main).

%term_expansion(Term,X) :- write(term), nl, write_canonical(Term), nl, fail.
term_expansion(bar(foo(X)), biz :- baz) :- writeln(hit_other).

%goal_expansion(Term,X) :- write(goal), nl, write_canonical(Term), nl, fail.

bar(foo(X)).

%goal_expansion(ex(X,T), )

main(_) :- 
  %write_canonical(foo(a))
  %write(hi).
  writeln(foo),
  listing(biz),
  true.

```

## Coroutines

[swi manual](https://www.swi-prolog.org/pldoc/man?section=coroutining)

- `dif/2` ? Test is delyed until terms are sfufcient different or have become identical
- `freeze/2` - equivalent to call is Var is bound
frozen
when
call_residue_vars

delay
[block](https://www.swi-prolog.org/pldoc/doc_for?object=block_directive%3A(block)/1)

## Indexing

<https://www.youtube.com/watch?v=FZLofckPu4A&ab_channel=ThePowerofProlog>

- first argument indexing
- deep indexing
- multi argument indexing
- JIT

- exchange arguments
- use specific functor not default ones - <https://www.metalevel.at/prolog/data#clean> [clean vs dirty reps](https://www.youtube.com/watch?v=KJ8uZiWpomg&ab_channel=ThePowerofProlog). For example reprrsent integer by lit(N) rather than raw N. default args + nonlogical preds are nodet. not good. "defaulty" representation. We can't symbolically express lit(X) + lit(Y). monotonic mode of clp(z)
- pull unifications into head (should happen by default)
- decompose arguments - use auxiliary predicates if system doesn't offer deep indexing
- lagged arguments - one case is subsumed by another. list_last convert to auxliary that remebed what you've seen. Check if foldl is applicable
- reification. zcompare, if_. library(reif), tfilter

redundant choice points are an indication of lost performance or poor indexing

[Indexing dif/2](https://arxiv.org/abs/1607.01590) Consider a removal predicate on a list. it involves dif.

[first zargument indexing](https://stackoverflow.com/questions/29605132/first-argument-indexing)
[eclipse: from LP to CLP](https://arxiv.org/abs/1012.4240)
[demand driven indexing of prolog clauses](https://user.it.uu.se/~kostis/Papers/iclp07.pdf)
[preindexed terms for prolog](https://cliplab.org/papers/indexed-terms-lopstr-2014-postproc-2015.pdf)
See also tabling

## DCG - Definite Clauses Grammars (DCG)

<https://www.youtube.com/watch?v=CvLsVfq6cks&t=3811&ab_channel=ThePowerofProlog>

[Anne Ogborn tutorial](https://github.com/Anniepoo/swipldcgtut)
[hakank picat](https://twitter.com/hakankj/status/1508321812261871616?s=20&t=-ertSPtY87GogVCFq4f-Rw)
[triska dcg primer](https://www.metalevel.at/prolog/dcg)
[swi manual - comments are good too](https://www.swi-prolog.org/pldoc/man?section=DCG)

DCGs look a bit like CFG grammars. They make threading an input and remainder list implicit. The input and remainder are considered a difference list.

DCGs describe sequences.
They can be used to serialize and deserialize, parse and pretty print.

You call a DCG via `phrase/2`. `phrase/3` gives you access to the remainder. phrase/2 specializes phrase/3 with a [] terminator.  DCGs are annotated as double slashes `as//0`.

```prolog
as --> [].
as --> [a], as.

:- initialization(main,main).
main(_) :- phrase(as, [a,a,a]), print("passed"), 
          phrase(as, [a,b,a]), print("doesn't pass").

```

`{ mygoal }` is a way to lift a prolog goal that doesn't touch the input lists.

Triska suggests turning on double quoted strings becomes lists. It appears swi has some behavior like this by default.

```prolog
:- set_prolog_flag(double_quotes, chars).
% even number of as
as --> "".
as --> "aa", as.

:- initialization(main,main).
main(_) :- phrase(as, "aaaa"), print("passed").

```

seqq describes concatenating a sequence of lists.

- `seq`
- semicontext
- DCGs are useful also for implicilty carrying state.
- State trasnformation is a _sequence_ of states when considered purely functionally.

```
state(S), [S] --> [S].
state(S0, S), [S] --> [S0].
```

Being able to implicilty pass state makes DCGs reminscent of monads. I've not seen a proof of equivalence however. State _is_ a very powerful construct. Me dunno. Maybe you could even pass around continuations in there.

This is showing context notation. Lists on the left hand sides of rules are pushed onto the stream after the rule works (I guess that means it unifies the head of the remained with this quantity). It looks very much like a form of lookahead.

library [dcg/basics](https://www.swi-prolog.org/pldoc/man?section=basics), [dcg/high_order](https://www.swi-prolog.org/pldoc/man?section=highorder)

library [pio](https://www.swi-prolog.org/pldoc/man?section=pio) - pure io. phrase_from_file phrase_to_stream

Triska shows an interesting trick to improve nontermination. You can parametrize your dcg such that it knows it is
consuming the input stream. The recursion depth should be bounded by the stream size itself. Very reasonable. The decreasing argument is the stream itself.

expr([_ | Rs], Rs) --> "1". shows that expr consumes one character
Called via
phrase(expr(Rs, _),Rs).

Or more easily, use tabling.

Reporting errors - add error streat arguments to dcg

regexp interpreter. dcg rexp//1

Longest match firsat behavior - order rules for longest match

## Constraint Logic Programming (CLP)

- CLP(B) - constraint over boolean variables. Sometimes bdd based
- CLP(FD)
- CLP(Z)
- CLP(H)

[Anne Ogborn's tutorial](https://github.com/Anniepoo/swiplclpfd)

[Indexing dif/2](https://arxiv.org/abs/1607.01590)
`reif` `if_/` `tfilter/3`

eclipse talks to minizinc?
[clp examples](https://swish.swi-prolog.org/example/examples.swinb)

CHR is a language for eaiser custom clp theories

[Constraint Logic Programming : A Survey](https://www.sciencedirect.com/science/article/pii/0743106694900337)

Constrained Horn Clauses are not that much different from CLP.

Bottom up execution. "facts" allows logically constrained variables. `foo(X) :- x > 7, X < 11.`. I wonder how resolutin provers deal with theory specific stuff.

Execution model: A goal stack + constraint store. Minikanren?
[A Framework for Extending microKanren with Constraints](https://arxiv.org/pdf/1701.00633.pdf)

### clpb

[swi manual clpb](https://www.swi-prolog.org/pldoc/man?section=clpb)
[The Boolean Constraint Solver of SWI-Prolog: System Description](https://www.metalevel.at/swiclpb.pdf)
[Boolean Constraints in SWI-Prolog: A Comprehensive System Description](https://www.metalevel.at/boolean.pdf)
[clpb triska](https://www.metalevel.at/clpb/)
[github repo with examples](https://github.com/triska/clpb)

```prolog
:- include(module(clpb)).

% a finite set is a mapping / assoc-list to bool
% a multiset is a mapping to int
union()

main(_) :- [x - X. y - Y, z - Z]

```

bdd, indexical, or external sat.
[robdd.pl](http://www.cs.otago.ac.nz/cosc410/ok/index.htm)

bdd using chr?

```

bdd(Var, L,R , Id), bdd( ,L,R, Id) ==>
bdd(Var,L,R,)
```

independent set example

```prolog
independent_set(*(NBs)) :−
  findall(U−V, edge(U, V), Edges),
  setof(U, V^(member(U−V, Edges);member(V−U, Edges)), Nodes),
  pairs_keys_values(Pairs, Nodes, _),
  list_to_assoc(Pairs, Assoc),
   maplist(not_both(Assoc), Edges, NBs).

 not_both(Assoc, U−V, ~BU + ~BV) :−
  get_assoc(U, Assoc, BU),
  get_assoc(V, Assoc, BV).
```

- domino tilings

<https://stackoverflow.com/questions/63505466/prolog-implementation-of-quines-algorithm-for-classical-propositional-logic-in?noredirect=1&lq=1>
<https://stackoverflow.com/questions/64835191/boolean-unification-in-prolog>

### clp(euf)

`union(+T1,+T2)` `T1 =:= T2` delay until ground? Not quite right. foo(x,X) foo(y,X) still has congruence power if we learn x = y. `union(eid(), eid())`. Support union of terms and eid
`find(+T,-Eid)`
`ematch(+Pat,-Match)`
`extract(+Eid, -Term)`

attrbitued var style ([z3](https://z3prover.github.io/papers/z3internals.html#sec-equality-and-uninterpreted-functions) style?). `put_attr( ,euf_parents,)` `put_attr( , euf_sibling, )` `put_attr( , term, )`
vs chr style
There was also in that prolog smt paper a congruence closure routine.

### Attributed Variables

Attaching extra info to variables. This can be be used to implement CLP as a library

<https://www.metalevel.at/prolog/attributedvariables>
<https://sicstus.sics.se/sicstus/docs/3.7.1/html/sicstus_17.html>
<https://www.swi-prolog.org/pldoc/man?section=attvar>

Attributed variables are a union find dict?

Atributed variables are also reminscent of nelson oppen, theories are informed

```prolog
:- initialization(main,main).


attr_unify_hook(Domain, Y) :-  % it's odd this is not tagged by the event type. 
 % Since we don't super get the key, perhaps it is wisest to wrap the attribute foo(Domaindata)
  writeln(union_event),
  writeln(Domain), % larry (data held in "Y")
  writeln(Y). % variable id of "X"

main(_) :- put_attr(X, mykey, fred), 
           put_attr(Y, mykey, larry), 
           put_attr(Y, mykey2, farry),  % with ths union_event is triggered twice, once per attribute
           get_attr(X,mykey,F), writeln(F),
           writeln(X), writeln(Y),
           X = Y,  % triggers union_event
           get_attr(X,mykey,FX), writeln(FX), % fred 
           get_attr(Y,mykey,FY), writeln(Y), writeln(FY)  % fred. Y is literally X now anyway.

          .

```

### Coroutining

Sometimes is makes sense to be lazy doing something until a variable is filled in more.
This is basically what `dif/2` does. It wakes up when either thing gets more filled in

`freeze` is a delayed `call`

### CLP(Set)

<https://www.clpset.unipr.it/>
`{log}` "setlog"
JSetL

[set unification](https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/set-unification/2B789EB32DCF9F77021DBE26FC691032)
[Sets and constraint logic programming](https://dl.acm.org/doi/10.1145/365151.365169)

G Rossi
A Dovier
E Pontelli

herditraryl hybrid finite sets. Finite sets of finite sets + terms

[Set Constraints in Logic Programming](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=ea756dcfc1db14307899a5b7d33b82fefbdc74c0)
[Set constraints and logic programming - kozen](https://www.cs.cornell.edu/~kozen/Papers/sclp.pdf) CLP(SC)
Herbrand atom ~ singleton set
Aiken

Relation to boolean equation systems?

Kuper - Logic programming with sets

## CHR

[forward chaining, chr comes up](https://swi-prolog.discourse.group/t/forward-chaining-like-rete-algorithm-in-rule-engine/5137/28)

[swipl manual section](https://www.swi-prolog.org/pldoc/man?section=chr)
[Anne Ogborn's tutorial](https://github.com/Anniepoo/swiplchrtut)
[Schrijver's ICLP tutorial](https://dtai.cs.kuleuven.be/CHR/files/tutorial_iclp2008.pdf)

Constraint handling rules
A question I never had an answer for <https://twitter.com/notjfmc/status/1422215450675535877?s=20&t=RyHMtBS3ySaALLC9MuGmUA> . CHR afaik are a way of integrating eager rewriting into prolog <https://en.wikipedia.org/wiki/Constraint_Handling_Rules>

I'm not sure this is even persay a prolog topic. But the prolog community is the most engaged

<http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html>
[chr.js](https://github.com/fnogatz/CHR.js/)
[chr what else](https://arxiv.org/pdf/1701.02668.pdf)

[Where is the CHR constraint store?](https://stackoverflow.com/questions/59234770/constraint-handling-rules-in-swi-prolog-does-the-constraint-store-exists-only?rq=1)

[Some cool examples](https://dtai.cs.kuleuven.be/CHR/examples.shtml). Gaussian, fourier, rational trees, equation solvers

<https://github.com/brog45/chrplay>

Multiset rewriting?

[cchr](https://github.com/nickmain/cchr) efficient implementation in C

[yihong's egraph in chr. awesome](https://github.com/yihozhang/cchr/blob/master/experiment/egraph.cchr)

[chr parsing](https://stackoverflow.com/questions/65647409/parsing-with-chr-constraint-handling-rules)

[parallel chr](https://github.com/KaiSta/Parallel_CHR)

[Automatic Differentiation using Constraint Handling Rules in Prolog](https://arxiv.org/abs/1706.00231)
Build up dataflow graph. Huh.

[Pros and Cons of Using CHR for Type Inference](https://dtai.cs.kuleuven.be/CHR/papers/chr2012/02-Csorba-chr12.pdf) <https://twitter.com/flippac/status/1567622246025383938?s=20&t=7jEZ-QlMkI3Jdw1l-LGSjg>

[Toward a First-Order Extension of Prolog’s Unification          using CHR](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.112.1661&rep=rep1&type=pdf)

[satisfiability modulo chr](https://www.comp.nus.edu.sg/~gregory/papers/smchr.pdf)

[Extending Arbitrary Solvers with Constraint Handling Rules](https://www.comp.nus.edu.sg/~gregory/papers/ppdp03.pdf)

### Compiling

[KU leuven system : implementation and application](https://lirias.kuleuven.be/retrieve/33588). Hmm. Is CHR compiled into prolog code?
[CCHR: the fastest CHR Implementation, in C](https://lirias.kuleuven.be/retrieve/22123)  
Idle thoughts, what about time dataflow.

[attributed data for chr indexing](https://lirias.kuleuven.be/retrieve/61662)

### Examples

CHR parsing
“Analysing graph transformation systems through Constraint Handling Rules” by Frank Raiser and Thom Frühwirth
“As time goes by: Constraint Handling Rules — A survey of CHR research from 1998 to 2007” by Jon Sneyers, Peter Van Weert, Tom Schrijvers and Leslie De Koninck

<https://stackoverflow.com/questions/67771845/prolog-get-a-list-of-all-the-rules-an-entity-verifies>

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

<https://www.swi-prolog.org/pldoc/man?section=chr-guidelines>
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

#### Union Find

From furhwith book. Generalized union find is also interesting.

```prolog
:- use_module(library(chr)).
:- initialization(main,main).
% hmm are these annotations ok?
:- chr_constraint make(+int), find(+int,-), root(+int,+int), union(+int,+int), link(+int,+int), pto(+int,+int).

make(A) <=> root(A,0).
union(A,B) <=> find(A,X), find(B,Y), link(X,Y).
pto(A, B), find(A,X) <=> find(B,X), pto(A,X).
root(A,_) \ find(A,X) <=> X=A.
link(A,A) <=> true.
link(A,B), root(A,N), root(B,M) <=> N>=M | pto(B,A), K is max(N,M+1), root(A,K).
link(B,A), root(A,N), root(B,M) <=> N>=M | pto(B,A), K is max(N,M+1), root(A,K).

main(_) :- make(1), make(2), make(3), union(1,2), find(2,X), find(3,Y), 
    print(X),print(Y), union(1,3), chr_show_store(true).
```

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

Is there a way to encode seminaive eval maybe? Even for datalog this is not clear you can. The folding of delta back into the main relationseems problematic.

leansmt
egraph + clp(R) + clp(FD) + clp(B). How far from SMT is that?

### Embedding into CHR

- TRS
- Prolog and CLP
- Graph trasnfomation - See term rewriting notes
- Petri nets

GAMMA general abstract mnodel for multiset manipulation

### SQL

[sql](https://github.com/awto/chr2sql)
Man what hope is there of compiling a 7 year old haskell project?
compiler to sql statements. Makes sense.

```prolog
:- use_module(library(chr)).
:- chr_constraint left/0, right/0, forward/0, backward/0.

left,right  <=> true.
forward, backward <=> true.

:- initialization(main,main).
main(_) :- forward, left, right, backward, left, chr_show_store(true).
```

```sql
CREATE TABLE left(a);
CREATE TABLE right(a);
CREATE TABLE backward(a);
CREATE TABLE forward(a);

INSERT INTO left VALUES (NULL);
INSERT INTO right VALUES (NULL), (NULL);
INSERT INTO backward VALUES (NULL), (NULL);
INSERT INTO forward VALUES (NULL);

select *, right.rowid from right;
create table env(left,right, UNIQUE(left), UNIQUE (right)); -- Use CTE? But then multiple statements?
-- INSERT INTO env SELECT left.rowid, right.rowid FROM left,right LIMIT 1; -- hmm we're overselecting. LIMIT BY 1? Yuck
INSERT OR IGNORE INTO env SELECT left.rowid, right.rowid FROM left,right;
-- only update timestamp if env is empty.
-- we could push env into the metalayer. Slow? Also the uniqueness filtering.
select * from env;

-- do rhs here if there was one. 
-- INSERT INTO rhs FROM env, left, right WHERE left.rowid = env.left AND right.rowid = env.right
DELETE FROM left where left.rowid IN (select env.left from env);
DELETE FROM right where right.rowid IN (select env.right from env);
DELETE FROM env;
select *, rowid from right;
select *, rowid from left;

```

Compred with datalog, sql multiset semantics is good match.
Hmm. Can't make nullary tables?

Hmm. The semantics of CHR are a problem. It seems unlikely I can do bulk matching. I'd have to just take the first match. That's putting a lot of control flow in the metalayer / not amoriziting well over sql statements.

ooh, what about env(left,right, UNIQUE left, UNIQUE right). Yes. This seems safe enough and yet bulk. Nice.

I can compromise on the sequential nature of chr, but th resource matching feels important.
Explicit multiset semantics with a count field? That's a bummer. Feels complicated. ON CONFLICT UPDATE
left -> 1, right -> 2 ---> left --> left -> 1 - min(1,2)), right -> 2 - min(1,2)
Naw, not even this fixes it.
The limit by 1 might be the best solution.

The issue here that really requires an env is that we have multi-headed rules.

```python
left = {None : 1} # multisets as maps to integers
right = {None : 2}

for l, n in left.items():
  if n > 0:
    for r, m in right.items():
      if m > 0:
        if l == r:
          left[l] -= min(n,m)
          right[r] -= min(n,m) # Is this mutation ok?
          #break or double break?
print(left)
print(right)

# list as multiset
left = [(,)]
right = [(,), (,)]

# mutating the collecton while iterating over it is irritating again
```

If my advice is to just use SWI for CHR, why is tabled SWI not my advice for datalog. No. That _is_ reasonable advice probably.
Not unless you're doing something weird

What would be better is to store the build values in env and not the keep ids. I don't know persay how bad that join is. Maybe using a left join or something so that sql knows it doesn't have to even loop up stuff it doesn't need.

This is not that elegant.

```python

class Rule():
  def __init__(self, name, kill, keep, guard, build):
    cols = ", ".join([f"{row})" for table, row in kill + keep])
    constraints = ", ".join([f"UNIQUE ({row})" for table, row in kill]) # To avoid double counting kills
    fields = ", ".join(cols, constraints)
    create_env = f"CREATE TEMP TABLE env({fields})" # put name on the env?

    selects = ", ".join([f"{row}.rowid" for table, row in kill + keep])
    wheres = " AND ".join(guards)
    find = f"INSERT OR IGNORE INTO env SELECT DISTINCT {selects} FROM {froms} WHERE {wheres}"
    
    deletes = [f"DELETE FROM {table} INNER JOIN env ON {table}.rowid = env.{row}" for table,row in kill]

    #rowenv  = ", " [ "  for table,row in kill + keep]
    where = " AND ".join([f"{table}.rowid = env.{row}" for table,row in kill + keep])
    inserts = [f"INSERT INTO {table} SELECT {val} FROM env, {selects} WHERE " for table, val in build]

    "DROP TABLE env"
```

Could imagine a syntax with an explicit binding part that puts these things in the env.
And that the built expsressions may not refer to the bound varaibles. Annoying restriction. And obviously we could

```
l @ left, r @ right <=> guard | p = l.x, z = r.y |  {r,a}
```

Keep a bunch of rules synchronized is annoying

## Answer Set Programming s(CASP)

<https://swish.swi-prolog.org/example/scasp.swinb>
"Tabling and s(CASP) are quite different beasts. They both address reasoning in cyclic domains including negation. Tabling provides Well Founded Semantics where s(CASP) provides Stable Model Semantics. s(CASP) stresses creating an explanation. Tabling does not. Tabling scales a lot better than s(CASP). It all depends …"

<https://gitlab.software.imdea.org/ciao-lang/sCASP>
[Constraint Answer Set Programming without Grounding](https://arxiv.org/abs/1804.11162)
[Justifications for Goal-Directed Constraint Answer Set Programming](http://www.cliplab.org/papers/sCASP-ICLP2020/TC-explainCASP.pdf) ERGO AI uses justification trees  <https://coherentknowledge.com/> using XSB

s(ASP) was just ASP <https://personal.utdallas.edu/~gupta/> . S(CASP) includes constraints
[tutorial slides](http://platon.etsii.urjc.es/~jarias/slides/gde21-tutorial.pdf)
[tutorail paper](http://ceur-ws.org/Vol-2970/gdepaper1.pdf)

[event calculus](https://swi-prolog.discourse.group/t/event-calculus-in-swi-prolog/5233)

## Extralogical features

### Database manipulation

[Persistent predicates based on RocksDB](https://swi-prolog.discourse.group/t/persistent-predicates-based-on-rocksdb/5501)
<https://github.com/JanWielemaker/rocks-predicates>

[swi](https://www.swi-prolog.org/pldoc/man?section=db)
[sicstus database manip](https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/ref_002dmdb.html#ref_002dmdb)
retract - take out of database
assert - put into database/
set_prolog_falg
dynamic predicates.
recorded database

`A = A, assert(foo(A)), A = x` what does this do. Does it make a clause `foo(A).` or does it make `foo(x).` Ah ok. The term is copied. So it makes the first on

[a declarative alternative to assert in logic programming](https://www.cs.cmu.edu/~fp/papers/ilps91.pdf)

```prolog
fib(0,1).
fib(1,1).
fib(M,N) :- M > 1, M1 is M - 1, M2 is M - 2, fib(M2, N2), asserta(fib(M2,N2)), 
            fib(M1, N1), asserta(fib(M1,N1)), N is N1 + N2.
% hmm. Infinite answers...

```

Program reflection. Partial evaluation.

### Cuts and Such

cut
green cut

findall bagor setof are aggregation of solutions. They are reifying predicates kind of.

[Finding all Solutions to a Goal](https://www.swi-prolog.org/pldoc/man?section=allsolutions)

# Functions

<https://www.swi-prolog.org/pack/list?p=function_expansion> a macro for function expansion

## Lambda

Oh sweet mysterious lambda

The minikanren `evalo`

[Oleg's lambda interpreter](https://okmij.org/ftp/Prolog/index.html#lambda-calc)

```
eval(E1*E2, R) :- eval(E1, E1R), eval(E2,E2R), copy_term(E1R,(E2R->Body)),
                       eval(Body,R).
eval(E,E).
```

One is tempted to attempt to use prolog variables for lambda variables. Requires extralogical copying primitives
`copy_term`

[swipl](https://www.swi-prolog.org/pldoc/man?section=yall) lambda expressions.
`[X] >> B` as `lam(X,B)`.

[lambda is iso prolog](http://www.complang.tuwien.ac.at/ulrich/Prolog-inedit/ISO-Hiord.html)

the elpi paper argues for de bruijn levels?

```prolog
% locally nameless

term(lam(X,X)).
% convert lam(X,X) form to gensym lam(fvar(x123),fvar(x123)) form
% I should just use numbervar/1
concrete( lam(X,B) , lam(X, B2)  ) :-  gensym(x, X), debruijn(B, B2). % copy term maybe

% Turn X into bvar(N).

close(N, X, X, bvar(N)).
close(N, X, lam(Y, B), lam(Y,B2) ) :- Y /= X, N2 is N + 1, close(N2, B,B2).
close(N, X, T, T2) :- T /= lam(), T /= X, 
  T ..= [F | Args],
  maplist(close(N,X), Args, Args2), 
  T2 .== [F | Args2].

abstract(X, T, blam(T2)) :- close(0,X,T,T2).

instantiate(N, V, bvar(N), V).
instantiate(X)

% norm(T,T2)
% miller(T,T2). % :=: or some other special equals.

% miller(X,X).
% miller(blam(T1), blam(T2)) :- miller(T1,T2)
% miller(app(F, Args), T) :- var(F), reabstract(T, Args, F). % maybe throw a norm in there?
% miller(X,Y) :- X ..= [F | Args1], Y ..= [F | Args2],  maplist(miller, Args1, Args2).

% F @ [X,Y,Z] infix application
% norm(lam(X,X) @ 3, 3).



```

The question is, can lambda prolog be implemented as a library?

### HiLog

My impression is this is a bit like "first order functional" programming. All predicates need names. You can achieve this via defunctionalization, lambda lifting, etc.

[From HiLog to Prolog](https://www3.cs.stonybrook.edu/~sbprolog/manual1/node44.html)

"`X(a, b)` is just an (external) shorthand for the Prolog compound term: `apply(X, a, b)` "

### Alpha prolog

<https://homepages.inf.ed.ac.uk/jcheney/programs/aprolog/>

Nominal logic
<https://arxiv.org/pdf/1012.4890.pdf> nominal unification revsitied Urban

<https://johnwickerson.github.io/dissertation.pdf>
"atoms" are a thing that are less free than unification vars but more free than ground terms. They are alpha renamable

freshness constraint a # t says that a appears in no subterm in t.
a # X when X is a variable can't be concluded.

freshness judgement
equational judgements

nominal unification returns substitution and new freshness constrains

A relative of miller pattern. They can be encoded into each other it says and gives references

J. Cheney. Relating Nominal and Higher-Order Pattern Unification.
J. Levy and M. Villaret. Nominal Unification from a Higher-Order Perspective

==(A \ X, B \ Y) :- dif(A,B), X == swap(A,B,Y), A # Y.

A # A \ Y.

<https://easychair.org/publications/preprint/DLVk> Efficiency of a good but not linear nominal unification algorithm

# Semantics

Completion semantics

Well-founded
[Well founed semantcis 1991](http://www.cse.unsw.edu.au/~cs4415/2010/resources/gelder91wellfounded.pdf)
[Well-Founded Semantics, Generalized](http://www.melvinfitting.org/bookspapers/pdf/papers/WFGen.pdf) two different ordering realtions, truth and knowledge. We always move from unknown to more known.
[well founded tutorial](https://users.soe.ucsc.edu/~avg/Papers/wftut.pdf)

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
<https://en.wikipedia.org/wiki/Rete_algorithm>

# Lambda Prolog

[tabling in higher order logic programming](http://reports-archive.adm.cs.cmu.edu/anon/2003/CMU-CS-03-185.pdf)

<https://userpages.uni-koblenz.de/~laemmel/paradigms1011/resources/pdf/lambda-prolog.pdf> ralf lammel slides

[lambda prolog page](https://www.lix.polytechnique.fr/~dale/lProlog/)
Implementations

- Teyjus - seems to maybe not be developed anymore
- elpi - alive and well. Coq metaprogamming
- Makam - a variant on lambda prolog with some cooll paper tutorials

[elpi: fast embeddable lmabda prolog interpreter](https://hal.inria.fr/hal-01176856/document)

- using de bruijn _levels_ means pattern matching doesn't need to do anything?
[elpi vs code extension](https://github.com/LPCIC/elpi-lang)

Install as `opam install elpi`. Run as `elpi -test` to run with main query

```elpi
main :- print "hello world".
```

A little bit of an odd encoding. Why `fact`? Oh I see. Because they have an outer loop that is inserting facts.

```elpi
kind entry type.
type fact entry -> o.
%type false o.

kind person type.
type kim,dana person.
type finished person -> int -> entry.
type cs_major, graduates person -> entry.

fact (finished kim 102) & fact (finished dana 101).
fact (finished kim 210) & fact (finished dana 250).

fact (cs_major X) :- (fact (finished X 101); fact (finished X 102)),
        fact (finished (X 250)), fact (finished X 301).

false :- fact (finished X 210), fact (finished X 250).

```

```elpi
kind jar, bug type.
type j jar.
type sterile, heated jar -> o.
type dead, bugs bug -> o.
type in bug -> jar -> o.

sterile J :- pi x\ bugs x => in x J => dead x.
dead B :- heated J, in B J, bugs B.
heated j.

main :- sterile J, print J.
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

```elpi
kind unit type.
type tt unit.
type lam  (unit -> unit) -> unit.

main :- (x\ x) = (y\ F y), print F,
     (x\ x) = (y\ y),
     % fails (x\ x) = (y\ F), % this is exists F, \x x = y\ F. Which is not solvable
     % pi (y\ X = y) % fails
      (x\ tt) = (y\ F2), print F2
. 
```

```elpi
main :- (x \ x) = (x \ F_ x),
        (x \ y \ x y) = (z \ G z), print G.

```

```elpi
% church encoding
kind i type.
type zero, one, two ((i -> i) -> i -> i) -> o.
type add ((i -> i) -> i -> i) -> ((i -> i) -> i -> i) -> ((i -> i) -> i -> i) -> o.

zero F :- F = f\ x\ x.
one F :- F = f\ x\ f x.
two F :- F = f\ x\ f (f x).
add X Y Z :- Z = f\ x\ (X f (Y f x)).

main :- two(T), one(O), add T T Z, print Z,
        % add Q T T, print Q. % unification problem outside patern fragment. Flex-flex?
        add T Q T, print Q. % no prob

```

Some built in elpi files

- [builtin](https://github.com/LPCIC/elpi/blob/master/src/builtin.elpi) surprising that even very basic stuff is defined in here.
  - i+ i- r+ mod div infix operations. + is overloaded it looks le
  - regular expresions rex. Like Str module
  - print dprint raw terms?
  - quotation? <https://github.com/LPCIC/elpi/blob/master/src/elpi-quoted_syntax.elpi> lam, app, const, clause, arg
  - same_term same_var var name - geiventbaraibe, ground_term, closed_term, constant,
  - if/3
  - random.int
  - int.map, std.string.map, std.string.set, std.map takes in a comp function,
  - gc functions. trace,counter
- [stdlib](https://github.com/LPCIC/elpi/blob/master/src/builtin_stdlib.elpi)
  - mem, exsits, map2, filter, fold, zip, unzip, intersperse, max, findall

std.do notation?

[Intro slides](https://github.com/gares/mlws18/blob/master/slides.pdf)

```elpi
kind term type.
kind ty type.
type app term -> term -> term.
type lam (term -> term) -> term.
type arr ty -> ty -> ty.

pred of i:term o:ty.

of (app H A) T :- of H (arr S T), of A S. 
of (lam F) (arr S T) :- pi x \ of x S => of (F x) T. 

cbn (lam F) (lam F).
cbn (app (lam F) N) M :- cbn (F N) M.

```

[examples in test](https://github.com/LPCIC/elpi/tree/master/tests/sources)

- named clauses `:clausename`
- namespaces
- typeabbrev
- seperate compilation?
- w.elpi algorithm W?
- ndprover

look at teyjus test folders?

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
<https://www.youtube.com/watch?v=XnZTADrsiHQ&list=PL2IiUBbPiuoY22PjECQscRQ81LaR0lgdh&index=2&ab_channel=TYPES2022>
dedukti workshop
Intermidate "assembly" for interchange between proof formats.
Logical framework
lambda pi - has dependent types. But not types that depend on types. Pi only quantifies over terms.
kocheck - fast rust

[beluga](http://complogic.cs.mcgill.ca/beluga/) is this kind of twelf? [beluga paper](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.188.3950&rep=rep1&type=pdf)
abella.
These are all related I guess? abella might not be LF

Logical frameworks is a general vague concept I think. It is a system in which it is easy to model logical language nad inference rules.
but ELF the edburgh logical fraemwork is more specific.
Related to Pi2 a corner of the lambda cube.

[The Next 700 Challenge Problems for Reasoning with Higher-Order Abstract Syntax Representations](https://link.springer.com/article/10.1007/s10817-015-9327-3)

### Twelf

<http://twelf.plparty.org/live/>
<http://twelf.org/wiki/About_The_Twelf_Project>

Twelf is a depnedelty typed landguage that is also a logic programming langfuage. Because it has a totality checker and termination checker, prolog clauses can be considered proofs.

<https://core.ac.uk/download/pdf/82649367.pdf> Normalization for the Simply-Typed Lambda-Calculus in Twelf

## Rust Chalk Harrop

<https://github.com/rust-lang/chalk>
<https://rust-lang.github.io/chalk/book/>

<http://smallcultfollowing.com/babysteps/blog/2017/01/26/lowering-rust-traits-to-logic/#type-checking-generic-functions-beyond-horn-clauses>
<https://internals.rust-lang.org/t/blog-series-lowering-rust-traits-to-logic/4673/12> internals thread

<http://smallcultfollowing.com/babysteps/blog/2017/04/23/unification-in-chalk-part-2/> how chalk handles type normalization

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

[LTL Model Checking using Coinductive Answer Set programming](http://platon.etsii.urjc.es/~jarias/GDE-2022/GDE-13.pdf)
Completion + loop formula (external support) gives lfp.
completion + ? give gfp?

[Co-Logic Programming: Extending Logic Programming with Coinduction](https://personal.utdallas.edu/~gupta/ppdp06.pdf)

[COnductive logic programming and it's applications](https://personal.utdallas.edu/~gupta/iclp07paper.pdf)

```prolog
:- use_module(library(coinduction)).

:- coinductive p/1.

p([1|T]) :- p(T).

```

```prolog
:- use_module(library(coinduction)).

:- coinductive p/0, q/0.
p :- q.
q :- p.

```

```prolog
mi(Gs, G) :- member(Gs,G1), subsumes_term(G1,G), 

```

# inductive logic programmingh

Hyper in bratko

[Inductive Logic Programming: From Machine Learning to Software Engineering](https://direct.mit.edu/books/book/4900/Inductive-Logic-ProgrammingFrom-Machine-Learning)

popper <https://arxiv.org/abs/2005.02259>
<https://github.com/metagol/metagol> metagol
<http://andrewcropper.com/> muggleton
<https://arxiv.org/pdf/2102.10556.pdf> inductive logic programming at 30
[hakank examples](https://swi-prolog.discourse.group/t/popper-inductive-logic-programming-ilp-and-my-popper-page/3929)

[Abductive Reasoning in Intuitionistic Propositional Logic via Theorem Synthesis](https://arxiv.org/abs/2205.05728v1). Includes a g4ip

[Hakank symbolic function induction picat](https://twitter.com/hakankj/status/1556344141994508288?s=20&t=yqv3psiW3ByDbnVTBLr_GA)

[Louise](https://github.com/stassa/louise)
<https://github.com/stassa/louise/blob/09a06e081b8933bbdb999424bf1a62673e88a3d6/src/louise.pl> line 465 for metainterpreter prove. multi clause inductive learning. "inductive"

Metarules
`P(A,B) :- Q(A,C), R(C,B)`. second order qauntified variables

metainterpretive learning (MIL) - a prolgo metainterpreter

# Probablistic Logic Programming

<https://swi-prolog.discourse.group/t/new-book-second-edition-of-foundations-of-probabilistic-logic-programming/6228>

# Abductive logic programming

<https://en.wikipedia.org/wiki/Abductive_logic_programming>

Infer ground facts given results

<https://stackoverflow.com/questions/41274692/discussion-about-abductive-logic-programming-vs-answer-set-programming>
"Any logic programing that supports hypothetical reasoning can support ALP"

```
assumez(P) :- assertz(P).
assumez(P) :- retract(P), fail.
abducible :- (assumez(amount(glucose,low));assumez(amount(glucose,medium))),
         (assumez(amount(lactose,medium));assumez(amount(lactose,hi))).

feed(lactose) :- amount(glucose,low), amount(lactose,hi).
feed(lactose) :- amount(glucose,medium), amount(lactose,medium).

% ?- abducible, feed(lactose), listing(amount/2).
```

[Abduction in Logic Programming - Denecker Kakas](https://web.stanford.edu/class/cs227/Readings/Abudction%20in%20LP.pdf)

A different variation <https://swi-prolog.discourse.group/t/non-monotonicity-defeasibility-strategies-and-other-stuff/6038/23>

```
/* SWI-Prolog 9.1.0 */
solve(true) --> !.
solve((A,B)) --> !, solve(A), solve(B).
solve(A) --> {abducible(A)}, !, [A].
solve(H) --> {clause(H, B)}, solve(B).
```

# Equational Logic Programming

<https://www.cs.ox.ac.uk/files/3444/PRG116.pdf>

<https://cseweb.ucsd.edu/~goguen/sys/eqlog.html> eqlog

See Maude in term rewriting
[INDUCTIVE EQUATIONAL LOGIC PROGRAMMING](https://digitalcommons.uri.edu/oa_diss/791/)
[higher order equationa logic programming](https://dl.acm.org/doi/pdf/10.1145/174675.177889)

[
Logic programming, functional programming, and inductive definitions](https://link.springer.com/chapter/10.1007/BFb0038699) Another argument in favor of inductive definitions, not first order logic. paulson

# Functional Logic Programming

See Curry

# Misc

[tar parsing in prolog](https://news.ycombinator.com/item?id=34427081)
[rethinking prolog - oleg](https://okmij.org/ftp/kakuritu/rethinking.pdf) unification variables are an optimization

[An interactive semantics of logic programming](https://arxiv.org/abs/cs/0107022) <https://twitter.com/davidad/status/1567780900284387329?s=20&t=jW6J2ukuizpdkb11CCe3bQ>

[ICLP proceedings](https://arxiv.org/abs/2208.02685) - lots of ASP stuff

[pyswip](https://github.com/yuce/pyswip)

<https://github.com/mthom/scryer-prolog/pull/838> scryer as a library?

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

<https://git.sr.ht/~sforman/Prolog-Junkyard/tree/master/miscellaneous/itc.pl> interval tree clocks in prolog
<https://www.metalevel.at/trs/> knuth bendix completion
<https://arxiv.org/abs/1706.00231> auto differentiating using constraint handling rules

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

<https://core.ac.uk/download/pdf/81972151.pdf> Logic programming with equations.

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
and this tabling thing mentions it <https://www.swi-prolog.org/pldoc/man?section=tabling-non-termination>

Datalog and program analysis
<https://www2.cs.sfu.ca/CourseCentral/721/jim/DatalogPaper.pdf> - What you always wanted to know about datalog
<http://rightingcode.org/tutorials/popl20/> popl 2020 - reasoning tools using llvm and z3
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
<https://hal.inria.fr/hal-00816703v1/document> canonical structures ofr the working coq user

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

<http://www.coli.uni-saarland.de/projects/milca/esslli/comsem.pdf> computational semantics. some interesting material here
<https://samples.jbpub.com/9780763772062/PrologLabBook09.pdf> - prolog experiment in discretem mathemtiacs logic and computatilbitly

They start with defining a set of atoms like

var(x).
var(y).

forall(x, stupid(x)).

<https://www.youtube.com/watch?v=RwBiHLoQ3E4&ab_channel=PapersWeLove> niko matsakis - lambda prolog

<https://rust-lang.github.io/chalk/book/recursive.html> chalk. harrop formula

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
<https://drops.dagstuhl.de/opus/volltexte/2018/8453/pdf/OASIcs-ICLP-2017-10.pdf>

ref a
ref b

<https://formal.iti.kit.edu/beckert/leantap/leantap.html> Beckert posegga leantap
<https://link.springer.com/chapter/10.1007%2F3-540-36377-7_6> metacircular abstarct interpretation in prolog
<https://www.metalevel.at/acomip/>

Pfenning constructive logic course <http://www.cs.cmu.edu/~fp/courses/15317-f17/schedule.html>
Programs as proof search
He considers the prolog predictaes as the judgements themeselves
As compared to considering the pile of predicates as entedcedents of a sequent
Bottom up search ius forward reasoning, top down is backward reasonining
bidrectional type checking - <https://arxiv.org/pdf/1908.05839.pdf>

Prolog semantics -
Since prolog can not terminate you can take that denotational semantics perspective.
<https://www.swi-prolog.org/pldoc/man?section=WFS> well founded semantics. - True/False/unknown
<https://en.wikipedia.org/wiki/Well-founded_semantics>
<http://www.cse.unsw.edu.au/~cs4415/2010/resources/gelder91wellfounded.pdf>
<http://dai.fmph.uniba.sk/~sefranek/links/FixPointSurvey.pdf>  fixpoitn semantics for logic programming a survey. melvin fitting
Melvin fitting has a number of interesting bokos <http://melvinfitting.org/>

So prolog already has belnap bools in it.

What does it look like to mix prolog with exact reals?

Modes and determinism annotations.

Kowalski - hgistory of prolog <https://www.researchgate.net/publication/277670164_History_of_Logic_Programming>

tabling -
Tabling is some kind of memoization.
It is connected to bottom up strategies
swi prolog <https://www.swi-prolog.org/pldoc/man?section=tabling>
<https://www.metalevel.at/prolog/memoization>
<https://biblio.ugent.be/publication/6880648/file/6885145.pdf> tabling as a library with delimited control
<https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/delimited-continuations-for-prolog/DD08147828169E26212DFAF743C8A9EB> delimitted continuations for prolog
<https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.294.9440&rep=rep1&type=pdf> XSB extending prolog with tabled logic programming. XSB prolog is the most advanced tabling implementation (still? maybe that is old information)
<https://github.com/SWI-Prolog/tabled-prolog-book> warren wrote a book draft
<https://www3.cs.stonybrook.edu/~warren/xsbbook/book.html> ok This may not be being finished anytime soon
Tabled typeclass resolution

<http://www.covingtoninnovations.com/mc/plcoding.pdf> - coding guidelines for prolog

<https://swi-prolog.discourse.group/t/algebra-in-prolog/1849> - algerba in prolog
<https://github.com/maths/PRESS> prolog equation solving system

scryer prolog - a rust based implemnentation . <https://github.com/mthom/scryer-prolog>
Interesting links
Precise garbage collection in Prolog
"Can Logic Programming Execute as Fast as Imperative Programming?" - Peter van Roy
indexing dif/2 <https://arxiv.org/abs/1607.01590> calls for if_ predicate
debray allocator

<https://wiki.nikitavoloboev.xyz/programming-languages/prolog> notes

<https://mercurylang.org/documentation/documentation.html> mercury

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

<https://www.metalevel.at/prolog/theoremproving>
presburger and resolution
<https://www.youtube.com/watch?v=b2Px7cu2a68&feature=youtu.be&ab_channel=ThePowerofProlog> term rewriting in prolog

<https://dl.acm.org/doi/book/10.1145/3191315>
Declarative Logic Programming: Theory, Systems, and ApplicationsSeptember 2018
Has another WAM tutorial in it

So

prolog modes

<https://www.metalevel.at/prolog/attributedvariables> attributed variables

<https://sicstus.sics.se/sicstus/docs/latest4/pdf/sicstus.pdf> sicstus prolog manual

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
Datafun - a fiunctional datalog <https://www.cl.cam.ac.uk/~nk480/datafun.pdf> <https://www.youtube.com/watch?v=gC295d3V9gE>
datalog - stephenel diehl <https://www.stephendiehl.com/posts/exotic04.html>
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

 <https://sites.google.com/site/pydatalog/Online-datalog-tutorial>
 nqueens - they unroll it significantly.

Some examples
<http://cse.unl.edu/~riedesel/pub/cse413/des/doc/manualDES.pdf>

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
<https://www.youtube.com/watch?v=oo-7mN9WXTw&ab_channel=%23pivorakLvivRubyMeetUp>

<https://github.com/ptarau/TypesAndProofs>
More theorem provers

binprolog - analog of CPS. Add a new parameter to every predicate

LD resolution

monoid of clauses - unfolding
bin(A :- BBBB) = (A>C :- BBBB>C)

2020/9
Propagators.

Kmett. The Art of the Propagator <https://dspace.mit.edu/bitstream/handle/1721.1/44215/MIT-CSAIL-TR-2009-002.pdf?sequence=1&isAllowed=y>

The gecode manual [https://www.gecode.org/doc-latest/MPG.pdf](https://www.gecode.org/doc-latest/MPG.pdf)

Adding constraints or smt. I have a seperate store for them (in the state)? explicit probe annotations to check still satisfiable.

9/1/20

I was looking at prolog again. Jesus nothing changes.

What are the good programs. The art of prolog has an open access link

Difference lists are cool. They really are similar ot hughes lists. Or al ist that keeps a pointer to it's end

Using it for theorem proving is cool. Where are those examples? The lambda prolog book has some exmaples. There is a propsitional satisfiabilioty prover in art of prolog. Propositional solver in powr of prolog [https://www.metalevel.at/prolog/theoremproving](https://www.metalevel.at/prolog/theoremproving) [http://vidal-rosset.net/g4i_prover.html](http://vidal-rosset.net/g4i_prover.html)   <http://jens-otten.de/tutorial_cade19/slides/prover_tutorial_CADE19_2.pdf>

nomial logic programming [https://arxiv.org/pdf/cs/0609062.pdf](https://arxiv.org/pdf/cs/0609062.pdf) alphaprolog. Chris mentioned this nominal thing as nother way of dealing with binders

Datalog - souffle.  Reading gorup paper [https://arxiv.org/pdf/1207.5384.pdf](https://arxiv.org/pdf/1207.5384.pdf). Sttratification. relations indexed on program point/ abstract state of program point. Interval analysis encoded in binary to datalog?

425/20 I was playing with prolog recently. Pretty cool

What is the deal with scheme and racket? i just don't have the  revelation.

I was looking at disjoint set data structures again [https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9](https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9)

Kmett's latest propgator talk was mentioning using group actions somehow in unification? [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ)

george wilson - <https://www.youtube.com/watch?v=nY1BCv3xn24> intutition for propagators.

[http://hackage.haskell.org/package/discrimination-0.3](http://hackage.haskell.org/package/discrimination-0.3) What the hell is this? Fritz Henglein.

[http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/](http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/)

<https://www.reddit.com/r/haskell/comments/a9yze4/is_there_an_arraylike_data_structure_which_gives/>

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

<https://www-apr.lip6.fr/~mine/publi/article-mine-HOSC06.pdf>

Huh. Interesting. It is in between power of polyhedral and interval. allows sums/differences of two variables. I think I've heard this called difference logic. This paper also mentions galois connections. Galois connections are studied in the context of abstract interpetation?

<https://arxiv.org/pdf/1807.08711.pdf>

Using Agda and galois connections. Interestign example of sets of even and odd numbers.

This other paper does an interesting thing of defining division in terms of a glaois connection. Might we also get a good definition of fractions that way? a fraction t ~ m/n is a "number" such that forall z. x <= y   -> x _t_ n <= y * m?  There is an notion of negative numbers, fractions, etc as reified weirdo operations that can't be solved yet. Hmm. Yeah, This jives with galois theory doesn't it. That book I was reading was talking about field extensions. Or number systems being invented to make more equations solvable. The reals make ? solvable. fractions make division solvable. Complex makes roots solvable. finite field extensions make simple algerbaic equations solvable.

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

<http://www.cs.nott.ac.uk/~psarb2/G53PAL/FPandGC.pdf>

indirect equality

m=n ===  forall k. k <= m <=> k <= n

Galois connection between convex hulls of integer points? There is a sequence of abstractions for integer programming. You can turn dimension by dimension into integer so there are 2^D different domains to talk about. And there is this grid of connections that forms a lattice itself? Like the top is the completely R^D, and the bottom is Z^D. Using these connections is the branch and bound procedure.

Floor and Ceil are also galois connections. Maybe also round? I had been thinking in terms of ibjects being individual numbers, not convex sets of numbers. Convex sets does tie in much better to categorical thinking

<http://www.cs.tau.ac.il/~msagiv/courses/asv/absint-1.pdf>

An interesting paper tutorial on galois connections. V cool.

monotone functions between are like natural tranfromations?

One place used dup as the adjunction to max.

There may be more to galois connections than adjunctions, since they are assuming a meet and join operation. Some interesting doncturctions like the porduct of galois connections.

[- Edward Kmett - Logic Programming à la Carte](https://www.youtube.com/watch?v=KxeHGcbh-4c)  

minikanren is strongly unification based. it is using search for the unification map. In simplest form [UniMap]

[https://github.com/JeffreyBenjaminBrown/learn-logict](https://github.com/JeffreyBenjaminBrown/learn-logict)

<https://www.msully.net/blog/2015/02/26/microkanren-%CE%BCkanren-in-haskell/>

[https://gup.ub.gu.se/file/207634](https://gup.ub.gu.se/file/207634) logic typed variable claesson

[http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification](http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification) unification.

[Pure, Declarative, and Constructive Arithmetic Relations (Declarative Pearl)](http://webyrd.net/arithm/arithm.pdf)

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
