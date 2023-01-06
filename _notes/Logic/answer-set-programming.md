---
layout: post
title: Answer Set Programming
---


- [Non Monotonic Reasoning](#non-monotonic-reasoning)
- [Justification](#justification)
- [Completion](#completion)
- [](#)
- [Examples](#examples)
  - [Reachability](#reachability)
  - [Graph Coloring](#graph-coloring)
  - [Satisfiablity](#satisfiablity)
  - [n queens](#n-queens)
  - [Travelling Salesman](#travelling-salesman)
  - [Reviewer Assignment](#reviewer-assignment)
  - [Planning](#planning)
  - [Rule Inference](#rule-inference)
  - [Junk](#junk)
- [Constructs](#constructs)
  - [Integrity constrains](#integrity-constrains)
  - [Choice Rule](#choice-rule)
  - [Cardinality rules](#cardinality-rules)
  - [Conditional](#conditional)
  - [Optimization](#optimization)
- [Grounding](#grounding)
- [Solving](#solving)
- [Systems](#systems)
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

- Super Datalog
  - Datalog with prescient negation
  - Datalog + branching
  - disjunctive datalog
- Justified SMT
- Prolog negation done right

[Potassco](https://potassco.org/) is the host of clingo, the main ASP solver (so far as I know)


# Non Monotonic Reasoning
<https://en.wikipedia.org/wiki/Negation_as_failure>
<https://en.wikipedia.org/wiki/Autoepistemic_logic>
<https://en.wikipedia.org/wiki/Default_logic>
<https://en.wikipedia.org/wiki/Stable_model_semantics>
<https://en.wikipedia.org/wiki/Nonmonotonic_logic>

Logic of here and there
Equilibrium logic

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
You know a fact can't be derived when no rule which has it as a head is fireable anymore.


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

# Justification
# Completion
Completion is methology to translate logic programs into more traditional logic. This is useful if you want to reuse other systems or metatheory.
We know that `:-` is implication in some sense. The thing is, if you directly translate your rules to classical logic using this correpondence, the resulting axioms are too loose. A classical solver is free to _overapproximate_. For example, a positive logic program interpreted this way always has a model where everything is true. This isn't what we want.
This is related to the confusing notion that the transitive closure of a relation is not shallowly embeddable in first order logic with finite axioms, despite the path axioms sure looking like they do it.

Logic programming is usually about the _least_ model.
It also is a closed world. This means that if something is true, it must be the head of at least one true body.

To axiomatize this, collect up every rule with the same head by or-ing the possible bodies. Turn the implication into a bi-implication.

There is still a problem though in regards to loops.


# 


# Examples
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
## Satisfiablity
In CNF form (a or b or c) can be see as constraint (not a /\ not b /\ not c -> false).
In this way we can translate CNF to ASP, one integrity constraint per clause.
Generate the vars via
```clingo
{a}. {b}.
:- a, not b.
:- b, not a.
:- not a, not b.
```

## n queens
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
## Travelling Salesman
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

## Reviewer Assignment
```
{assigned(P,R) : reviewer(R)} = 3 :- paper(P).
:- assigned(P,R), coi(P,R).

:- not 6 {assigned(P,R) : paper(P)} 9, reviewer(R).
; compare to 6 {} 9 :- reviewer which makes each reviewer have between 6 and 9.
```

cardinality cnstraints are convenience features for count

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


can I use this to conveniently describe transtion systems? Yes.

## Rule Inference

You can make variables that correspond to turning rules on or off. And making these choice variables.
You can give positive and negative examples as integrity constraints. And then optimize for a minimum number of rules. Or maybe weight by rule complicatedness.
So this infers a datalog program.

https://github.com/stefano-bragaglia/XHAIL
## Junk

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
`1 {p(a); p(b)} ` is the same as `{p(a); p(b)}. :- p(X), q(X).`

`:- f(X,Y1), f(X,Y2), Y1 != Y2.` expresses functional constraint. Same thing as `Y1 = Y2 :- f(X,Y1), f(X,Y2).`

Clingo makes auxiliary predicates instead of dummy variables for `_` interesting.


grounding time and solving time.
For slow ground: try enumerating better. symettry breaking. Rules with fewer variables.

Disjunction
Conditional Literals.
p :- q(X) : r(X).

# Constructs
There are a bunch of extra constructs that compile to extra variables and such. Many are in essence syntactic sugar.

## Integrity constrains
`:- a,b,c.`
gets translated to
`x :- a,b,c, not x.`

odd loop destroys model.


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

cardniality as heads
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


## Conditional
{l : l1,l2,l3}
Could be seen as {l | l1, l2, l3}
Expansion is context dependent.
In head: disjunction (exists?)
In body: conjuction of elements


## Optimization
Directive
weights and priorities



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

asp-core-2 languague
aspif intermdiate language
#true #false
double negation - doesn't have to vbe proven

# Grounding
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


# Solving
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




# Python
https://potassco.org/clingo/python-api/5.6/

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

https://arxiv.org/html/2208.02685v1/#rprlif19 iclp 2022
[Transforming Gringo Rules into Formulas in a Natural Way](https://arxiv.org/html/2208.02685v1/#EPTCS364.13) translating gringo into First order logic

[Verifying Tight Logic Programs with anthem and vampire](https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/verifying-tight-logic-programs-with-anthem-and-vampire/F8EDF1CABBEC7B5AC369B51D8BF90F7D) - using vampire to solveasp problems?

[Transforming Gringo Rules into Formulas in a Natural Way](https://link.springer.com/chapter/10.1007/978-3-030-75775-5_28)

[How to build your own ASP-based system ?! ](https://arxiv.org/pdf/2008.06692.pdf)

[Arntzenius disccision](https://twitter.com/arntzenius/status/1264570390849949696?s=20&t=5y91-I1SPrIGomAWSqs69w) "How are Datalog, SAT/SMT, and answer set programming related? Is ASP basically the generalisation of SAT to first order logic, plus recursion? And Datalog restricts ASP to Horn clauses and stratified recursion?

<https://en.wikipedia.org/wiki/Answer_set_programming>

[transpiling PCF to ASP](https://arxiv.org/pdf/1808.07770.pdf)
[temporal answer set programming](https://deepai.org/publication/temporal-answer-set-programming) TELINGO
[Potassco, the Potsdam Answer Set Solving Collection](https://potassco.org/)

[Possivbe worlds explorer](https://github.com/idaks/PW-explorer) demos https://github.com/idaks/PWE-demos . Qlearning? Sure. https://ischool.illinois.edu/people/bertram-ludascher datalog debugging. Prevoenance. 
[martens Generating Explorable Narrative Spaces with Answer Set Programming](https://drive.google.com/file/d/1CKDOsT9FIGW3SNyW5u5heIxbx_ZLCAP5/view)

[Alviano, M., Faber, W., Greco, G., and Leone, N. 2012. Magic Sets for Disjunctive Datalog Programs](https://arxiv.org/abs/1204.6346)
Clingo
dlv2 maybe https://dlv.demacs.unical.it/
[wasp](https://github.com/alviano/wasp)
[embasp](https://embasp.readthedocs.io/en/latest/index.html) https://github.com/DeMaCS-UNICAL/EmbASP
dlvhex http://www.kr.tuwien.ac.at/research/systems/dlvhex/

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

brave vs cautious modes? What the hell is that. https://stackoverflow.com/questions/55675488/brave-cautious-reasoning-in-clingo enumration modes. Non total. They converge towards minimal or maximal model?


[Beyond version solving: implementing general package solvers w Answer Set Programming Todd Gamblin](https://www.youtube.com/watch?v=bkY9mOyUaDA&ab_channel=PackagingCon)


[Answer set programming (ASP) is the powerhouse technology you’ve never heard of](https://twitter.com/mgrnbrg/status/1589652522180153344?s=20&t=JfnzTQG-SeFdO1qYUwKkrw) http://www.weaselhat.com/2022/11/07/asp/
Datalog provenance is explanations. Can be used as a monotonic theory in SMT search.

[Potassco Guide](https://github.com/potassco/guide/releases/)


[Comments on ASP](https://news.ycombinator.com/item?id=34071325)
[Automating Commonsense Reasoning with ASP and s(CASP)*](https://personal.utdallas.edu/~gupta/csr-scasp.pdf)
Constraints. Default rules. 5 truth values for p, not -p, not p not -p, not p, -p

[Potsdam publication list](https://www.cs.uni-potsdam.de/wv/publications/#DBLP:journals/ai/GebserKS12)

[answer set planning a survey](https://www.cs.uni-potsdam.de/wv/publications/DBLP_journals/corr/abs-2202-05793.pdf)