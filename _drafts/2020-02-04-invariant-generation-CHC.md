

https://arxiv.org/abs/2002.09002 rusthorn. Trick involving old new values to model borrowing from creusot talk

https://arieg.bitbucket.io/pdf/gurfinkel_ssft15.pdf
IC3/PDR

deadlock empire using CHC? Well deadlock empire has counterexamples.

Recursion and Loops are where it comes handy. We can reduce the straight line behavior (and branching) with ordinary wp. But the loops are tougher.
Function calls may not be recursive of course. If we previously establidshed


Keeping overapproximations of Reachable sets.
Generalize counterexamnple and push them backwards

Z3 imlementation.
https://github.com/pddenhar/Z3-IC3-PDR

really nice description
http://www.cs.tau.ac.il/~msagiv/courses/asv/IC3.pdf

ic3/pdr vs interpolation based
use unsat cores

https://github.com/Z3Prover/z3/blob/master/examples/python/mini_ic3.py

There is some interpolation happening in SPACER

The SAT version
Maintain cnf fomrulas (sets of clauses)for each time step
A cube = an assignment = a conjunction of literals.
We manitain a queue of counterexamples
If the counterexample is in F0, then we found a bad trace
NewLemma - take negation of counterexample.. This is candidate clauses (possibly we may delete some literals). We want to exclude an errant counterexample. 



Push - pick a clauses in Fi. split it into two pieces. if a subpiece is not in Fi+1 
unfold - we initialize a new Fi to have no clauses (no constraints). Candidate will pick any bad state now.
Predecessor- m0 and m1 is a combined state picked. m1 -> m means we may add literals to m. We need to find a state that ends up in m. We pushed the counterexample backwards. That makes sense. And we might find multiple.
Requeue - if this counterexample can't be reached from previous guy, push it forward.
```python
init = And(p, q, r, yada)
sets = [init]

def check_unreachable():
  for F, Fn in zip(sets, sets[1:]):
    if check(Implies(Fn,F)):
      retrun True
  return False



queue = []
while true:
  check_reachable()
  check_unreachable
```

So if I used spacer naively with a predicate per programs point, each would be solved in the PDR manner.


Hmm. So the horn clauses don't give you anything in regards to wp itself. They are useful for interprcoedural and invaraints?

Interesting stuff in here.
Locking examples.
Concurrency
In raw smtlib but also using tool
https://github.com/seahorn/seahorn-tutorial

Hmm. The tutorial shows the block-like CHC form
But then takes macro steps using wp to fuse out?

Hmm. So the horn clauses aren't because they are a natural modelling framework, but because they have a natural solution method.

CHC and CLP are the same thing, different communities

init -> inv
inv /\ 

https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-yurifest.pdf

Maybe there is some connection to the datalog stuff?
One predicate per line of program?
Or you could have program point as varaible?


Lifting blocks to clauses. How would one model a control flow diagram in prolog?
block1in(x') :- blockout(x) /\ blocktransition(x,x')

blockin(x) :- (blockout( wp()  ))

block1in :- block7out

which direction should be in/out? depends on wp vs sp?

Alternatively an explciit variable for control point block(n, )

Or should entire block be a predicate?
block(invars, outvars) :- blocka(outvars, invars')

https://www.youtube.com/watch?v=bTPSCVzp1m8&ab_channel=WorkshoponSoftwareCorrectnessandReliability2013

The expnasion / unrolling operator.

https://arxiv.org/abs/2104.04224 - A theory of heap[s for cxonstrained horn clauses

Houdini dillig
daikon - random execution traces infer stuf
"invasraint inference"
Aiken - https://ti.arc.nasa.gov/m/events/nfm2013/pubs/AikenNFM13.pdf "sounds like daikon"
Notes on z3 codebase
muz = muZ. fixedpoint solvers.
There are a vairety

PDR / IC3 always come up.
I should try to know what those are

Meta foregin code base techniques
- checkout build files - Gives a hierarchy of the structure of the project. Dependency sorted.
- checkout tests


Folders:
- cmake, not that interesting
- contrib - qprofdiff tool. axiom profiler diff tool?
- doc - not that ijnterest
- examples 
  * tptp
  * maxsat solver using C bindings
## src - most of the goodies are here.



- CmakeLists.txt - ineresting actually. Gives a more full listing of everything
  header files.
  subdirectories to scan. util comes first.
  util, math, ast, params, model, tactic, parsers, sat,
- utils 
  * approx_nat. uses UINTMAX to represent "huge". That's cool.
  * bitvector - arrau for storing bit vbectors
  * hash - custom hash stuff http://burtleburtle.net/bob/hash/doobs.html
  * inf_int_rational - rationals with infinitesimals
  * memory_manager? 
  * min_cut
  * mpbq - binary rationals. multi precision binary Q, q meaing rational
  * mpff - mulitprecision fast floats?
  * sexp
  * stack - low level stack allocator?
  * state_graph - tracking "live" and "dead" states 
- math
  * polynomial - upolonymial - uvariate. some facotrizxations, algerbaic numbers
  * dd - decision diagrams
  * hilbert - computes hilbert basis. A thing from inequalities o https://en.wikipedia.org/wiki/Hilbert_basis_(linear_programming)
  * simplex - bit matrix, network flow, simplex algo
  * automata
  * interval - interval arithemtic
  * realclosure - closing the rationals, computale reals, infinitesimals, Huh. This idea of infinitesimals is odd but intriguing. What is that for?
  * subpaving
  * greobner
  * lp
- ast
 * euf - has an egraph implementation -referencing egg?! etable - one entry per function symbol
 * fpa - conversion between bitvector and floating point
 * macro - z3 macros. universally quantified that can be used as macros. Macros are universally quantified formulas of the form:
     (forall X  (= (f X) T[X]))
     (forall X  (iff (f X) T[X]))
   where T[X] does not contain X. macro_finder=True flag?
 * normal - normal forms. skolemaizaytion. negation normals form. Pull quantifiers
 * pattern - pattern ordering, can one be instantiated to the other?
 * proof - proof checker and traversal
 * rewriter - huge. der destructive equality resoltion. rewrite.h common infratsture
 * More I got tired
- params - stuff
- model


You know, it's a lot, but it isn't quite as overwhelming as I have felt in the past
- shell - z3 executable
 * main.cpp - hmm trace and debug builds.
 * smtlib_frontend.cpp - parse_smt2_commands
 * src/smt2/smt23parser - oh wow. the parser is pretty complex. Is this really the runtime in some sense? This file is best read bottom to top. Well, it's loading evertythning up into the context. That makes sense. asserts. parse_cmd. declarations, consts, asserrs,  eventually you run check_sat
 * src/solver/solver.h check_sat, combined_solver.cpp. check_sat is like an overloadable class function though? Where does the solver get built?

 * cmd_context? This is where commands are defined. Might be secret ones.

paramaters, tactics, and commands
z3 -in  interactive mode
(help) - gives commands?
model based projection
(query predicate) horn rules. there are an insane number of options to this
(include)
(help-tactic)
(get-value expr) in current model. Crazy
(get-proof-graph) whaaaaat
(eval term) options - completion. arrays as stores? array_equalities
(eufi) model based interpolation
(euf-project) congurence propjection
(declare-rel) declare new relation? takes a representation*. This is a datalog thing right?
(rule (=> ))
(declare-map) new array map operator
(dbg- stuff) - wow a lot here
(check-sat-assuming)
(check-sat-using tactic)
(declare-tactic)
(apply tactic)
(simplfiy) has a print-proofs option?

muz has: datalog, bmc, and spacer mode, and xform?
:print-certificatie fives "inductive invataint" even in datalog?



data driven horn clause solver. They use decision trees?
That's interesting. What about a scikit-learn loop,
Or polynomial fitting?
Good invariants candidates over bit vectors? That cbat thing sounds kind of good.
One of those domains. There was also that thing. That paper for comparative whatever that was guessing useful conditions inside.
https://www.cs.purdue.edu/homes/suresh/papers/pldi18.pdf

https://www.cs.utexas.edu/~isil/cs389L/houdini-6up.pdf

Constrained horn clauses

https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf

https://chc-comp.github.io/

https://spacer.bitbucket.io/

https://seahorn.github.io/

https://theory.stanford.edu/~arbrad/papers/Understanding_IC3.pdf 


Programming Z3 tutorial
Spacer jupyter tutorial https://github.com/agurfinkel/spacer-on-jupyter/blob/master/Dagstuhl2019.ipynb
https://arieg.bitbucket.io/pdf/synasc2019.pdf

IC3 / PDR unbounded model checking

This is somehow more than a prolog. It's inferring _predicates_

https://people.eecs.berkeley.edu/~sseshia/219c/#books modelchecking course.


Subgoal induction. ??? Seems tailor fitted to CHC. From Mitchel Wand paper refernces to Morris paper
"inductionless induction / narrowing" are the things cody seemed to find this reminsent of 


Wait, so SAT is solving the problem, but unsat is a counterexample trace?

```python
from z3 import *
x = BitVec("x",16)
x1 = BitVec("x'",16)
s = SolverFor("HORN")
i16 = BitVecSort(16)
Inv = Function('mc', i16, BoolSort())

'''
x = 0
while(x < 10)
  x++
assert(x < 11)
'''
init = ForAll(x, Implies(x == 0, Inv(x)))
loop = ForAll([x,x1], Implies( And(x < 10, Inv(x), x1 == x + 1), Inv(x1) ) )
post = ForAll(x, Implies(Inv(x), x < 11)) #ForAll(x, Implies(And( x < 11 , Inv(x)), False)) 

s.add(init, loop, post)
s.check()
s.model().eval( Inv(x) )
```

You can use horn clauses to perform craig interpolation.
A => I
I /\ B => False
Hmmmmmm. But what do you use craig interpolation for?
IC3 I think. You can build over approximations of intermiedate sets.



Running a prolog query:

forall(x, plus(s(x), ) )
plus(x,y,z) => False
Or 
True => plus(x,y,z) ? with no quantification?



https://www.youtube.com/watch?v=-eH2t8G1ZkI&t=3413s
syntax guided synthesis
sygus-if https://sygus.org/
CVC4 supports it.
LoopInvGen, OASES, DryadSynth, CVC4

rahul sharma
polikarpova, peleg, isil dillig

https://www.youtube.com/watch?v=h2ZsstWit9E&ab_channel=SimonsInstitute - 
automated formal program reapir
"fault localization" 
https://github.com/eionblanc/mini-sygus