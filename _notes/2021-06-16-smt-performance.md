---
layout: post
title: SMT Solvers
---


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
