---
layout: post
title: SMT Solvers
---

- [Solvers](#solvers)
- [CVC5](#cvc5)
  - [Proofs](#proofs)
  - [interpolation](#interpolation)
  - [abduction](#abduction)
  - [Higher Order](#higher-order)
  - [Sep logic](#sep-logic)
  - [datatypes](#datatypes)
  - [Transcendentals](#transcendentals)
  - [Float](#float)
  - [test/regress](#testregress)
  - [options](#options)
- [EPR](#epr)
- [Z3 source spelunking](#z3-source-spelunking)
  - [src - most of the goodies are here.](#src---most-of-the-goodies-are-here)

See also:
- SAT solvers
- Synthesis
- automated theorem proving
- Imperative Verification

[datalog based systems can us incremental smt solving ](https://cs.pomona.edu/~michael/papers/iclp2020_extabs.pdf) Nice trick to use (=> label clause). This trick also comes up in unsat cores. (check-sat-assuming label label) then. ALso consider doing minimal number of push pops or keep pool of solver contexts to find miniaml push pop
# Solvers
W: What options are actualy worth fiddling with
It is interesting to note what unusual characteristics solvers have.

z3
bitwuzla
boolector
cvc4
cvc5
yices2
[smtinterpol](https://github.com/ultimate-pa/smtinterpol)
alt-ergo
veriT
colibri
mathsat (ultimate eliminator https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/?ui=tool&tool=eliminator)
smt-rat
stp


vampire
aprove


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

# CVC5
[Paper](https://homepages.dcc.ufmg.br/~hbarbosa/papers/tacas2022.pdf)
- abduction
- inteprolation
- sygus
- Proofs, alethe lfsc lean4 maybe others?
- coinductive types
- separation logic

[kinds files](https://github.com/cvc5/cvc5/blob/a8623b22f6f8d28191f090f8f5456540d9cb0a18/src/theory/builtin/kinds)
This is a [parsers listing](https://github.com/cvc5/cvc5/blob/a8623b22f6f8d28191f090f8f5456540d9cb0a18/src/parser/smt2/smt2.cpp). You can find all (exposed) built in functions here 

- `eqrange`? So set equality over a range? Seems useful. Rewriter expands to obvious quantified fromula
- `iand`
- `int.pow2`
- `real.pi`
- `@` is HO apply
- bags
- lots of strings functions

## Proofs
```cvc5
(set-logic ALL)
(set-option :produce-proofs true)
(declare-const x Int)
(assert (= x 1))
(assert (= x 2))
(check-sat)
(get-proof)
```

## interpolation
[interpolation slide](https://userpages.uni-koblenz.de/~sofronie/vtsa-2015/slides-griggio2.pdf)
For unsatisifable formula `A => B`, produces a C such that `A => C`, `C => B` whihc only uses shared variables. Considered as sets, B is a subset of A.

For finite unrolling of transition relation, we can use it to produce an abstraction of the initial state that is sufficient to prove the property. Maybe this gets us a full inductive invariant.

For pure sat interpolation can be found from resolution proof / unsat certificate

Theory specific interpolation.

## abduction
- get-abduct --produce-abducts https://github.com/cvc5/cvc5/blob/master/test/regress/regress1/abduction/abduct-dt.smt2 get-abduct-next (set-option :produce-abducts true)
(set-option :incremental true)
```cvc5
(set-logic QF_LIA)
(set-option :produce-abducts true)
(set-option :incremental true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0))
(get-abduct A (>= (+ x y) 2))
(get-abduct-next)
(get-abduct-next)
```

```cvc5
(set-logic QF_LRA)
(set-option :produce-abducts true)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (and (>= x 0) (< y 7)))
(get-abduct A (>= y 5))
```
## Higher Order
```cvc5
(set-logic HO_ALL) ; HO_UF; HO_LIA
(declare-const f (-> Int Int))
(assert (= (f 1) 2))
(assert (= f (lambda ((x Int)) 2)))
(assert (= f f))
(check-sat)
(get-model)
```


## Sep logic
<https://cvc5.github.io/docs/cvc5-0.0.7/theories/separation-logic.html>

`sep.nil` a nil pointer value. Not sure this has any semantics. Maybe it is one extra value out of domain?
`sep.emp`
`sep` seperating conjunction
`pto`
`wand`

```cvc5
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (sep (pto 1 1) (pto (as sep.nil Int) 2)))
(check-sat)
;(get-model)
```
## datatypes
`Tuple`
`dt.size`
`tuple_select` `tuple_update`

## Transcendentals
<https://cvc5.github.io/docs/cvc5-0.0.7/theories/transcendentals.html>

`exp` `sin` `cos` `arccos` `sqrt` and so on
```cvc5
(set-logic QF_NRAT)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (> x real.pi))
(assert (< x (* 2 real.pi)))
(assert (< (* y y) (sin x)))
(check-sat)
```
## Float
[Good real to float?](https://github.com/cvc5/cvc5/discussions/8024)
`+oo` `+zero` `-zero` `NaN` 
`fp` What is this? `fq.eq` `fp.abs` `fp.neg` `fp.fma` `fp.sqrt` `fp.roundtoIntegral`
`fp.isNormal` `fp.isSubnormal` `fp.izZero` `fp.isInfinitr` `fp.isNaN` `fp.isNegative` `fp.isPositive` `fp.to_real`
Indexed operators
`to_fp` `to_fp_unsigned` `fp.to_ubv` `fp.tosbv` `to_fp_real`

```cvc5
(set-logic ALL)
(declare-const x Float64)
(define-const onef Float64 ((_ to_fp 11 53) RNE 1))
(assert (= x (fp.add RNE x x)))
(assert (fp.lt onef (fp.add RNE x x)))
(check-sat)
(get-model)
```
## test/regress
Looking at the test/regress folder, what sort of odd looking stuff is there?
- (_ iand 4) what is this
- sygus
- (! :named foo)
- (-> Event$ Bool) higher order sorts
- --product-proofs finite-model-find fmf-bound
- (set-info :status sat) . Hmm does it use this?

So it looks like theory specific stuff can be accesed namespaces
- str.prefixof str.substr str.len str.to_int
- set.subset set.insert set.singleton
- fp.is_zero fp.to_real

## options
<https://cvc5.github.io/docs/cvc5-0.0.7/binary/options.html#most-commonly-used-cvc5-options>
cvc --help
--dump-intsantiations
--dump-proofs
--dump-unsat-cores
--proof-dot-dag
--proof-format-mode


--conjecture-gen candidate fo inductive proof
--dt-stc-ind strengthening based on structural induction
--finite-model-find
--e-matching

<https://cvc5.github.io/docs/cvc5-0.0.7/binary/output-tags.html>
-o inst
-o sygus
-o trigger - print selected triggers
-o learned-lits
-o subs

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