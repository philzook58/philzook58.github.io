
Notes on z3 codebase
muz = muZ. fixedpoint solvers.
There are a vairety

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