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
  - [Z3 Add Commutative Benchmark](#z3-add-commutative-benchmark)
  - [Interactive Proof](#interactive-proof)
    - [Hilbert Proof](#hilbert-proof)
    - [Backwards Proof](#backwards-proof)
    - [Manual Proof System](#manual-proof-system)

See also:
- SAT solvers
- Synthesis
- automated theorem proving
- Imperative Verification

[datalog based systems can us incremental smt solving ](https://cs.pomona.edu/~michael/papers/iclp2020_extabs.pdf) Nice trick to use (=> label clause). This trick also comes up in unsat cores. (check-sat-assuming label label) then. ALso consider doing minimal number of push pops or keep pool of solver contexts to find miniaml push pop

[Fuzzy-sat](https://arxiv.org/pdf/2102.06580.pdf) running smt queries through a fuzzer

natural domain smt

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

[check sat assuming for many quefries](https://cs.pomona.edu/~michael/papers/iclp2020_sub.pdf)

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


## Z3 Add Commutative Benchmark

```python
from z3 import *
Num = DeclareSort("Num")
add = Function("add", Num, Num, Num)
num = Function("num", IntSort(), Num)

from functools import reduce
import random
print(reduce(add, [num(n) for n in range(10)]))

x,y,z = Consts("x y z", Num)
axioms = [
  ForAll([x,y], add(x,y) == add(y,x)),
  ForAll([x,y,z], add(add(x,y),z) == add(x,add(y,z)))
]


import timeit
for N in range(5,17):
  s = Solver()
  s.add(axioms)
  e1 = reduce(add, [num(n) for n in range(N)])
  perm = list(range(N))
  random.shuffle(perm)
  e2 = reduce(add, [num(n) for n in perm])

  s.add(e1 != e2)
  print(N, timeit.timeit(lambda: s.check(), number = 1))

```

## Interactive Proof

### Hilbert Proof
Hilbert style proofs where the only inference rule is Z3_check.
Register known theorems to central repository. Refer to them later.
There are some basic theorems with quantifiers I couldn't get Z3 to do even the most basic step of, so this idea feels sunk.
I guess I could also admit vampire.

```python
from z3 import *
class Kernel():
    def __init__(self):
        self._formula = {}
        self._schema = {}
        self._explanations = {}
    def axiom(self, name, formula):
        assert name not in self._formula
        self._formula[name] = (formula, None)
        return name
    def add_schema(self, name, schema):
        assert name not in self._schema
        self._schema[name] = schema
        return name
    def instan_schema(self, schema, name, *args):
        #name = self.fresh(name)
        self._formula[name] = (self._schema[schema](*args), ("schema", schema))
        return name
    def theorem(self, name, formula, *reasons, timeout=1):
        assert name not in self._formula
        s = Solver()
        #s.set("timeout", timeout)

        s.add([ self._formula[reason][0] for reason in reasons])
        # snity check here. s.check(). should return unknown. If returns unsat, we have an incosisitency
        # Even if we have inconsistency but z3 isn't finding it, that is a small comfort. 
        s.add(Not(formula))
        status = s.check()
        if status == unsat:
            self._formula[name] = (formula, reasons)
            print(f"Accepted {name}")
        elif status == sat:
            print(f"Counterexample : {s.model()}")
        elif status == unknown:
            print("Failed: reason unknown")
        else:
            print(f"unexpected status {status}")
    #def calc(self):
    #    pass
    #def definition: # is definition distinct from axiom?

t = Kernel()
p = Real("p")
t.axiom("p_def", p*p == 2)
m,n = [ToReal(x) for x in Ints("m n")]

#t.theorem("p irrational", p != m / n)
#(m / n == p)
def even(x):
    y = FreshInt()
    return Exists([y], 2 * y == x)
def odd(x):
    y = FreshInt()
    return Exists([y], 2 * y + 1 == x)
r,w = Ints("r w")
t.theorem("even odd", ForAll([r], even(r) != odd(r)))
def rational(p):
    m = FreshInt("m")
    n = FreshInt("n")
    return Exists([m,n], And(n != 0, p == ToReal(m) / ToReal(n) ))
rational(p)

#t.theorem("mndef", Implies(rational(p), p == m / n) )

#t.theorem( Implies( p == m / n, Exists([r,w], And(p == r / w,  Or(And(even(r), odd(w)), And(odd(r), even(w)) ) ))))
# how do you use this exists?

#t.theorem(   )
def evenodd(n,m):
    return even(n) != even(m)

t.theorem(0, Implies(  And(p == m / n, n != 0) , p * n == m  ))
t.theorem(1, Implies(  And(p == m / n, n != 0, evenodd(m,n)) , p * n == m  ))
#t.theorem(2, Implies(  And(p == m / n, n != 0, evenodd(m,n)) , 2 * n * n == m * m , "p_def"))
t.theorem(3, even(r) != odd(r))
#t.theorem(4, even(r * r) != odd(r * r))
t.theorem(5, Implies(r == 2 * w, even(r*r) ))
t.theorem(6, Implies(r == 2 * w, r*r == 4 * w * w ))

#t.theorem(7, Implies(r == 2 * w, even(r) ))
#t.theorem(8, Implies(even(r), even(r*r)), 5, 6, 7)
t.theorem("even or odd", Or(even(r), odd(r)))
#t.theorem("even or odd r*r", Or(even(r*r), odd(r*r)))
t.theorem(8, ForAll([r], even(r) != odd(r)))
t.theorem(9, even(r*r) != odd(r*r), 8)
# I dunno. This idea is sunk. I can't even get this to work?
# I could try not using the built in stuff I guess and wwork in FOL.


#t.theorem(5, odd(r) == odd(r * r), 3, 4)
#t.theorem(3, Implies(even(r * r), even(r) ))
#t.theorem(3, Implies(  And(2 * n * n == m * m), even(m)))




#t.theorem(0, Implies(  p == m / n , m * m == 2 * n * n   ), "p_def" )
even(r * r) != odd(r * r)
```



```python
t = Hilbert()

Nat = Datatype('Nat')
Nat.declare('Zero')
Nat.declare('Succ', ('pred', Nat))
# Create the datatype
Nat = Nat.create()
Zero = Nat.Zero
Succ = Nat.Succ

n,m = Consts("n m", Nat)
plus = Function("+", Nat,Nat,Nat)
DatatypeRef.__add__ = lambda self, rhs : plus(self, rhs)
#type(n)
plus_zero = t.axiom("plus_zero", ForAll([m], Zero + m == m))
plus_succ = t.axiom("plus_succ", ForAll([n,m], Succ(n) + m == Succ(n + m)))
plus_def = [plus_zero, plus_succ]
def induction_schema(P):
    return  Implies(
                And(P(Zero), 
                    ForAll([n], Implies(P(n), P(Succ(n))))) ,
                ForAll([n], P(n))
    )
induction = t.add_schema("induction", induction_schema)

t.theorem( "plus_zero'",  ForAll([m], Zero + m == m , patterns=[Zero + m]), plus_zero) # guardedc version of the axiom
mylemma = t.instan(induction, "mylemma", lambda m : Zero + m == m + Zero )

t.theorem( "n_plus_zero", ForAll([m], Zero + m == m + Zero) ,  plus_zero, plus_succ,  mylemma )
t.theorem("test guarding", Zero + Zero == Succ(Zero), "plus_zero")

lte = Function("<=", Nat, Nat, BoolSort())
DatatypeRef.__le__ = lambda self, rhs : lte(self, rhs)

t.axiom("zero lte", ForAll([n], Zero <= n))
t.axiom("succ lte", ForAll([n,m], (Succ(n) <= Succ(m)) == (n <= m) ))
lte_def = ["zero lte", "succ lte"]


t.theorem("example",  (Zero + Zero) <= Zero,  *plus_def, *lte_def  )


reflect = Function("reflect", Nat  , IntSort())
x = Int("x")
t.axiom( "reflect succ", ForAll([x, n], (reflect(Succ(n)) == 1 + x) == (reflect(n) == x) ))
t.axiom( "reflect zero", reflect(Zero) == 0) 

t.formula

```

### Backwards Proof
<https://www.philipzucker.com/programming-and-interactive-proving-with-z3py>
At the end of this blog post I had kind of a neat system mimicking how coq feels.
Keep a goal stack. Allow usage of Z3 tactics.
I was trying to enforce every step as being sound by requiring Z3 to confirm what I though I was doing.
I don't think systems tend to make the backwards proof process part of their core. They use a tactic system which calls forward.
Probably sunk for the same reasons that Z3 just will not accept certain quanitifier proofs.

### Manual Proof System
Guidance from Harrison.

Reuse the Z3 syntax tree but build custom

https://en.wikipedia.org/wiki/Sequent_calculus

```python
from z3 import *
class Proof(): # Sequent?
  # private internal methods
  __hyps = []
  __concs = None # None means uninitialized.

  def smt(formula):
    s = Solver()
    s.add(Not(formula))
    status = s.check()
    if status == sat:
      raise s.model()
    elif status != unsat:
      raise status
    p = Proof()
    p.__concs = [formula]
    return p
  def hyps(self):
    return self.__hyps.copy()
  @property
  def concs(self):
    return self.__concs.copy()
  def __repr__(self):
    return f"{self.__hyps} |- {self.__concs}"
  def copy(self):
    p = Proof()
    p.__hyps = self.__hyps.copy()
    p.__concs = self.__concs.copy()
    return p
  def add_hyp(self, hyp): # strengthen hypothesis. Weaken Left (WL)
    p = self.copy()
    p.__hyps.append(hyp)
    return p
  def add_conc(self, hyp): # weaken conclusion. Weaken Right (WR)
    p = self.copy()
    p.__hyps.append(hyp)
    return p

a,b,c = Bools("a b c")
tt = BoolVal(True)
ff = BoolVal(False)
p = Proof.smt(tt)
# p.__hyps # results in attribute error
# print(p.concs) # can access attribute to look
# p.concs = [] error
print(p) #opaque
print(p.add_hyp(a))
print(p)
#print(Proof())
print(Proof())
```



