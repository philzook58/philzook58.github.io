---
layout: post
title: Constraint Programming
---

- [What is it for?](#what-is-it-for)
- [Minizinc](#minizinc)
    - [Embedding datalog into minizinc](#embedding-datalog-into-minizinc)
- [Picat](#picat)
- [Answer Set Programming](#answer-set-programming)
  - [negation](#negation)
  - [Frame Problem Default Logic](#frame-problem-default-logic)
    - [nqueens](#nqueens)
- [Topics](#topics)
  - [Branch and Bound](#branch-and-bound)
  - [Local Search](#local-search)
  - [Lattices](#lattices)
  - [Propagators](#propagators)
  - [Heuristics](#heuristics)
- [Misc](#misc)

# What is it for?
Puzzle solving
- n-queens
- sudoku

Compiler problems

Routing Problems
Allocation problems

Plannning
Reachability
Verification
# Minizinc
[tutorial](https://www.minizinc.org/doc-2.6.2/en/part_2_tutorial.html)
[202 autumn school](https://www.youtube.com/watch?v=lQi3b-sxt1s&ab_channel=AutumnSchoolonLogicandConstraintProgramming)

[Exploring a shipping puzzle, part 3](https://kevinlynagh.com/notes/shipping-puzzle/part-3/)

```minizinc
var int : x;
solve satisfy;
```

How to make DSLs. Look for macros. Look for function call. Look for gensyms


```minizinc

mov("a","b");


```


var vs par is compile vs runtime distinction in type system
it would be cool if minizinc could support adts or records.

### Embedding datalog into minizinc

```minizinc
set of int : verts = 1..3;
array[verts,verts] of bool : edge;
%array[int,int] of verts : edge0;
array[verts,verts] of var bool : path;

%edge0 = [|1,2 | 2,3];
% check if in edges list
function bool: edge0(int : i, int : j) = 
    i = 1 /\ j = 2 \/
    i = 2 /\ j = 3;
edge = array2d(verts,verts, [ edge0(i,j) | i,j in verts]);

constraint forall(i,k in verts)(
    path[i,k] <-     % <-> ? 
    edge[i,k] \/ exists(j in verts)(edge[i,j] /\ path[j,k])
);

%output ["\(edge)"];

solve satisfy;
```

Note that `-a` or `--all-solutions` will show all solutions. 

Non negated datalog should have a unique solution. Datalog with negation is a different ballgame.

# Picat
[website](http://www.picat-lang.org/)

index mode annotations
table annotions include lattice type stuff "mode-directed tabling"

action rules
loops
# Answer Set Programming
[Arntzenius disccision](https://twitter.com/arntzenius/status/1264570390849949696?s=20&t=5y91-I1SPrIGomAWSqs69w) "How are Datalog, SAT/SMT, and answer set programming related? Is ASP basically the generalisation of SAT to first order logic, plus recursion? And Datalog restricts ASP to Horn clauses and stratified recursion?

<https://en.wikipedia.org/wiki/Answer_set_programming>

[transpiling PCF to ASP](https://arxiv.org/pdf/1808.07770.pdf)
[temporal answer set programming](https://deepai.org/publication/temporal-answer-set-programming) TELINGO
[Potassco, the Potsdam Answer Set Solving Collection](https://potassco.org/)

[Possivbe worlds explorer](https://github.com/idaks/PW-explorer) demos https://github.com/idaks/PWE-demos . Qlearning? Sure. https://ischool.illinois.edu/people/bertram-ludascher datalog debugging. Prevoenance. 
[martens Generating Explorable Narrative Spaces with Answer Set Programming](https://drive.google.com/file/d/1CKDOsT9FIGW3SNyW5u5heIxbx_ZLCAP5/view)

Clingo
dlv2 maybe https://dlv.demacs.unical.it/
[wasp](https://github.com/alviano/wasp)
[embasp](https://embasp.readthedocs.io/en/latest/index.html) https://github.com/DeMaCS-UNICAL/EmbASP
dlvhex http://www.kr.tuwien.ac.at/research/systems/dlvhex/

[seventh answer set competition](https://arxiv.org/pdf/1904.09134.pdf)
[lifschitz prgraming with clingo](https://www.cs.utexas.edu/~vl/teaching/378/pwc.pdf)

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

## negation
<https://en.wikipedia.org/wiki/Negation_as_failure>
<https://en.wikipedia.org/wiki/Autoepistemic_logic>
<https://en.wikipedia.org/wiki/Default_logic>
<https://en.wikipedia.org/wiki/Stable_model_semantics>
<https://en.wikipedia.org/wiki/Nonmonotonic_logic>

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

Fitting operator
Phi(T,F) = using rules who fit known true and know false
F(<t,f>) = {a | }

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


## Frame Problem Default Logic
can I use this to conveniently describe transtion systems?



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

`{p(a); p(b)} 1` is the same as `{p(a); p(b)}. :- p(a), q(b).` We could enumerate every subset that can't be and exclude them with constraint.
`1 {p(a); p(b)} ` is the same as `{p(a); p(b)}. :- p(X), q(X).`

`:- f(X,Y1), f(X,Y2), Y1 != Y2.` expresses functional constraint. Same thing as `Y1 = Y2 :- f(X,Y1), f(X,Y2).`

Clingo makes auxiliary predicates instead of dummy variables for `_` interesting.


grounding time and solving time.
For slow ground: try enumerating better. symettry breaking. Rules with fewer variables.

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


# Topics
## Branch and Bound

## Local Search
## Lattices

## Propagators

## Heuristics

# Misc
- google or-tools
- eclipse https://www.eclipseclp.org/


[Hakan's site](http://www.hakank.org/) an insane number fo examples in systems

Coursera Course

[ORTools](https://developers.google.com/optimization) is apprently killer according to [Minizinc Challenge](https://www.minizinc.org/challenge.html)

GeCode

[CPMpy](https://www.youtube.com/watch?v=A4mmmDAdusQ&ab_channel=Int%27lConferenceonPrinciplesandPracticeofCP)

[constraint programming for robotics](http://www.codac.io/)
 Also see interval constraint programming [interval mooc](https://www.ensta-bretagne.fr/jaulin/iamooc.html)  http://www.codac.io/tutorial/index.html 

[csplib](https://www.csplib.org//) a library of constrains

[art of propagators](https://dspace.mit.edu/handle/1721.1/54635) 
[geocode manual on propagators](https://www.gecode.org/doc-latest/MPG.pdf) (appendix P) 
Propagators have been described as "just" monotonic functions between lattices. <https://www.youtube.com/watch?v=s2dknG7KryQ&ab_channel=ConfEngine>


[constraint acquisition](https://twitter.com/grmenguy/status/1531879717376184320?s=20&t=-IHVNfpCMKlhva0T8ctWXA) inferring predoncitions for code?
