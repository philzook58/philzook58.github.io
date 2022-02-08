---
layout: post
title: SMT Solvers
---

https://yices.csl.sri.com/papers/manual.pdf yices has a `ef-solve` mode that synesthesia used for synthesis. Is this the analog of PBR solving?

Idea: Convert Z3 DRAT to tactic script <https://github.com/Z3Prover/z3/discussions/5000> <https://github.com/Z3Prover/z3/discussions/4881>

Idea: Analgous to intervals or complex numbers, do extended reals <https://en.wikipedia.org/wiki/Extended_real_number_line> Using Reals + ADTs. Interesting because algerbaic operations become partial. Do as smt macro?


User propagated theories

delta debugging  - https://ddsmt.readthedocs.io/en/master/

https://twitter.com/RanjitJhala/status/1391074098441187328 - jhala asks for 

running `perf`
`perf record -F 99  --call-graph dwarf ./z3 /tmp/review.smt2;  perf report |  c++filt | less`

z3 -st

The axiom profiler and quantifier instantiations

Differences between solvers is important

Check regression on same solver - much better if true.

LLogic debugging - https://www.metalevel.at/prolog/debugging

"Try Smt.arith.solver=2"
"All automatic Z3 bot sometimes uses git bisect."
"rewriter.flat=false"
-v:10


WWDD - what would dafny do


https://arxiv.org/pdf/2010.07763.pdf refinement types tutorial

fascinating that this paper internalizes the partial evaluation prcoess into the smt formula

Amin Leino Rompf, Computing with an SMT Solver” https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml237.pdf
They translate functions to versions that have fuel. They don't give them much fuel
Lit marking. 
Lit(x) + Lit(y) => Lit(x + y). This is another wya to encode constant propagation into egglog 

Trigger whispering. Can I use Z3 as an egglog? Completely using the trigger system I can't trigger on equality can I?

Michal Moskal's thesis - interesting

Claire Dross, Sylvain Conchon, Johannes Kanig, and Andrei Paskevich. Reasoning with
triggers. In Pascal Fontaine and Amit Goel, editors, 10th International Workshop on Satisfiability Modulo Theories, SMT 2012, EasyChair 2013 EPiC Series, pages 22–31, 2012. - a logical semantics of triggers

http://www.rosemarymonahan.com/specsharp/papers/SAC_Final.pdf Reasoning about Comprehensions with
First-Order SMT Solvers
Duplicate functions. Trigger on only one version. Avoids things going off the rails.


https://github.com/Z3Prover/z3/pull/5625/commits/ec792f64205a6aea5ab21d2859a632676726bedf user propagation of theories example






How to get Z3 to return models with quantified statements.
mbqi needs to saturate? epr
Can I do it by explicitly gassing?

Axiom schema



# EPR
"Bernays Schonfinkel"
A decidable fragment of first order logic.
It relies on there being no function symbols, it's similar to datalog in this sense.
Also the only quantifiers allowed are exists, forall.
Quantifier alternation also leads to a form of function symbols thanks for skolemization.
There are more sophisticated variants which can have function symbols satisfying certain straitifcation conditions.


The finite model property.

<http://microsoft.github.io/ivy/decidability.html>
<https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-model-based-quantifier-instantiation>
<https://arxiv.org/pdf/1710.07191.pdf>


Can be turned into equisatisfiable propositional formula by:
1. Turn outer existential to free variable
2. Turn inner forall into conjunction over all existential variable possibilities.

<https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Courses/SS2017/Program%20Verification/04-Quantifiers.pdf>

Herbrand universe saturation is sort of key. Can I achieve this with gas? I could artificially macroize sorts to do so.


[interestting tidbit](https://stackoverflow.com/questions/24062292/most-efficient-way-to-represent-memory-buffers-in-z3) suggests not using array initialization using stores. Instead element by element. Also extensionality axiom for arrays can be turned off

https://stackoverflow.com/questions/28149863/why-is-e-matching-for-conjunctions-sensitive-to-order-case-splitting-strategy

# Z3 source spelunking

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