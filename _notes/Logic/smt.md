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
  - [Rationals](#rationals)
  - [test/regress](#testregress)
  - [options](#options)
- [Quantifiers](#quantifiers)
  - [Clark Completion for Datalog](#clark-completion-for-datalog)
  - [Rewriting](#rewriting)
  - [Option datatype](#option-datatype)
  - [Pseudo Boolean](#pseudo-boolean)
- [Finite Models](#finite-models)
  - [EPR](#epr)
- [Z3](#z3)
  - [Z3 source spelunking](#z3-source-spelunking)
  - [src - most of the goodies are here.](#src---most-of-the-goodies-are-here)
  - [paramaters, tactics, and commands](#paramaters-tactics-and-commands)
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

- z3
- bitwuzla
- boolector
- cvc4
- cvc5
- yices2
- [smtinterpol](https://github.com/ultimate-pa/smtinterpol)
- alt-ergo
- veriT
- colibri
- mathsat (ultimate eliminator https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/?ui=tool&tool=eliminator)
- smt-rat
- stp


vampire
aprove


https://yices.csl.sri.com/papers/manual.pdf yices has a `ef-solve` mode that synesthesia used for synthesis. Is this the analog of PBR solving?

[check sat assuming for many quefries](https://cs.pomona.edu/~michael/papers/iclp2020_sub.pdf)

Idea: Convert Z3 DRAT to tactic script <https://github.com/Z3Prover/z3/discussions/5000> <https://github.com/Z3Prover/z3/discussions/4881>

Idea: Analgous to intervals or complex numbers, do extended reals <https://en.wikipedia.org/wiki/Extended_real_number_line> Using Reals + ADTs. Interesting because algerbaic operations become partial. Do as smt macro?


User propagated theories

delta debugging  - https://ddsmt.readthedocs.io/en/master/

https://twitter.com/RanjitJhala/status/1391074098441187328 - jhala asks for help on a slowdown

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



https://github.com/Z3Prover/z3/pull/5625/commits/ec792f64205a6aea5ab21d2859a632676726bedf user propagation of theories example






How to get Z3 to return models with quantified statements.
mbqi needs to saturate? epr
Can I do it by explicitly gassing?

Axiom schema


[decision prcoesures book](http://www.decision-procedures.org/)
[calculus of computation books](https://theory.stanford.edu/~arbrad/book.html)


ford-fulkerson push relabelling for special relations?
https://en.wikipedia.org/wiki/Push%E2%80%93relabel_maximum_flow_algorithm
https://microsoft.github.io/z3guide/docs/theories/Special%20Relations

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

[smtlib float defs](https://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml)
[z3guide](https://microsoft.github.io/z3guide/docs/theories/IEEE%20Floats)

```z3
(declare-const x Float64)
(assert (fp.isNormal x))
(check-sat)
(get-model)
(eval (fp.to_real x))
```

(closest(x,fp)  (forall fp2 (<= (abs (- x fp.to_real)  ) <= (abs (- x (fp.to_real fp2))  )     )

http://smtlib.cs.uiowa.edu/papers/BTRW14.pdf
https://www.lri.fr/~melquion/doc/17-cav-article.pdf

(round x r)  log2(x)  <= x - r <=

```z3
; This is an under approximation of log2. Is that a problem? How can we be careful about this?
(define-fun log2 ((x Real) (y Real)) Bool
   (and true
        (=> (and (<= 1 x) (< x 2)) (= y 0))
        (=> (and (<= 2 x) (< x 4)) (= y 1))
        (=> (and (<= 4 x) (< x 8)) (= y 2))
   )
)


;(declare-const x Real)
(declare-const y Real)

(assert (log2 6 y))
(check-sat)
(get-model)
```

We should just directly compute eps from 

```
(define-fun eps32 ((x Real) (y Real))
     (and true
        (=> (and (<= 1 x) (< x 2)) (= y 0))
        (=> (and (<= 2 x) (< x 4)) (= y 1))
        (=> (and (<= 4 x) (< x 8)) (= y 2))
   )
)

```

remainder form

sin(0) = 0
-1 <= sin(x) <= 1
forall x, sin x = x - x^3 / 3! + R_sin_5(x)
R(x)


## Rationals
Rationals are kind of not an intrinsic. Reals are.
```z3
(declare-sort Rat)
(declare-fun mkrat (Int Int) Rat)

(assert 
  (forall ((x Int) (y Int) (a Int) (b Int)) 
    (=> (= (* x b) (* y a))  
       (= (mkrat x y) (mkrat a b))
     ) 
   )
)

(declare-fun ratmul (Rat Rat) Rat)

(assert
(forall ((x Int) (y Int) (a Int) (b Int)) 
    (= (ratmul (mkrat x y) (mkrat a b))
       (mkrat (* x a) (* y b))
    )
    )
)


;(assert 
;  (forall ((p Rat))
;    (exists ((x Int) (y Int))
;        (and (= p (mkrat x y))
;              (not (= y 0))
;    )
;)

; but skolemize it explicitly
(declare-fun num (Rat) Int) ; picks arbitrary consistent num denom
(declare-fun denom (Rat) Int)

(assert 
  (forall ((p Rat))
        (and (= p (mkrat (num p) (denom p)))
             (not (= (denom p) 0))
        )
    )
)


;(assert (exists ((p Rat)) 
;        (= (ratmul p p) (mkrat 2 1))
;        )
;)


(define-fun even ((x Int)) Bool
  (exists ((c Int))  
          (= x (* 2 c))
  )
)


(define-fun odd ((x Int)) Bool
  (exists ((c Int))  
          (= x (+ 1 (* 2 c)))
  )
)

;(assert (exists ((c Int)) 
;        (and (even c) (odd c))
;))
; unsat. good.

(assert 
  (forall ((p Rat))
             (not (and (even (num p)) (even (denom p))))
    )
)
(assert (exists ((m Int) (n Int)) 
        (let ((p (mkrat m n))) 
        (and (= (ratmul p p) (mkrat 2 1))
             (not (and (even m) (even n)))
             (= (* m m) (* 2 (* n n)))

        )
        )
        )
)





(check-sat)
(get-model)
```

```z3
(define-fun even ((x Int)) Bool
  (exists ((c Int))  
          (= x (* 2 c))
  )
)


(define-fun odd ((x Int)) Bool
  (exists ((c Int))  
          (= x (+ 1 (* 2 c)))
  )
)

;(declare-const m Int)
;(declare-const n Int)

;(assert (not (even m)))
;(assert (not (even n)))

;(assert (= m (* 2 n)))
;(assert (= (* m m) (* 2 (* n n))))

(assert (not (forall ((x Int)) (=> (even (* x x)) (even x)))))

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

# Quantifiers
[pointers to quantifiers on cvc5](https://github.com/cvc5/cvc5/discussions/8770)
```
(1) Bernays-Schönfinkel, when using the option --finite-model-find (https://homepage.divms.uiowa.edu/~ajreynol/cade24.pdf).

(2) Quantified linear int/real arithmetic (with arbitrary nested quantification), where cvc5 uses techniques from https://homepage.divms.uiowa.edu/~ajreynol/fmsd17-instla.pdf by default.

(3) Finite interpreted quantification, e.g. quantifiers over bitvectors (which also can be arbitrarily nested). See e.g. https://homepage.divms.uiowa.edu/~ajreynol/cav18.pdf for the techniques cvc5 uses; these techniques are used by default for quantifiers over e.g. BV when other theories are not present. They can be forced on using the option --cegqi-all.
```


- MBQI - model based quantifier instantiation. Consider quantified formula as opaque propositions. Upon getting prop assignment, ask for countermodel to proposition. Infer _term_ instantiation from countermodel
- E-matching - syntactic trigger.s
- enumeration

[An Overview of Quantifier Instantiation in Modern SMT Solvers - Reynolds](http://homepage.divms.uiowa.edu/~ajreynol/pres-ssft2021.pdf)

[Alex Summers course quantifiers lecture](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Courses/SS2017/Program%20Verification/04-Quantifiers.pdf)

Amin Leino Rompf, [Computing with an SMT Solver”](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml237.pdf)
They translate functions to versions that have fuel. They don't give them much fuel
Lit marking. 
Lit(x) + Lit(y) => Lit(x + y). This is another wya to encode constant propagation into egglog 

Trigger whispering. Can I use Z3 as an egglog? Completely using the trigger system I can't trigger on equality can I?

Michal Moskal's thesis - interesting
[Moskal programming with triggers](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.161.4917&rep=rep1&type=pdf)

Claire Dross, Sylvain Conchon, Johannes Kanig, and Andrei Paskevich. Reasoning with
triggers. In Pascal Fontaine and Amit Goel, editors, 10th International Workshop on Satisfiability Modulo Theories, SMT 2012, EasyChair 2013 EPiC Series, pages 22–31, 2012. - a logical semantics of triggers

http://www.rosemarymonahan.com/specsharp/papers/SAC_Final.pdf Reasoning about Comprehensions with
First-Order SMT Solvers
Duplicate functions. Trigger on only one version. Avoids things going off the rails.


https://microsoft.github.io/z3guide/docs/logic/Quantifiers
Stratified sorts fragment

(set-option :smt.mbqi true)
(set-option :model.compact true)

What is compact models?

[what's decidable about arrays](http://theory.stanford.edu/~arbrad/papers/arrays.pdf)

Essentially (Almost) Uninterpreted Fragment
[Complete instantiation for quantified formulas in Satisfiability Modulo Theories](https://leodemoura.github.io/files/ci.pdf)
```z3

(declare-sort MyInt)
(declare-fun add (MyInt MyInt) MyInt)
(declare-fun num (Int) MyInt)

(assert (distinct (num 1) (num 2) (num 3)))

(assert (forall ((x MyInt) (y MyInt)) 
    (= (add x y) (add y x))
))

(check-sat)
(get-model)
; right. it can give me a trivial ish model


```

f-inv trick for injective function axiomatization


Hmm. Z3 has `sin` built in? https://github.com/Z3Prover/z3/blob/f1bf660adc6f40cfdbd1c35de58c49b5f9960a9c/src/ast/arith_decl_plugin.h doesn't really seem so. It just recognizes it as defined. subpaving is interesting



Using define-fun-rec as a bounded forall. Make the recursive function that enumarates the range. Probably it is a bad idea to
```z3

(define-fun-rec bforall ((low Int) (high Int) (pred (Array (Array Int Int) Bool)) Bool
  true
)
```

Quantify over bounded domains only. This might play nice with mbqi. Not so much with ematching. This is explicit parametrization of a finite subset of an infinite domain. Which might help. 

```
(forall (x0 (_ BitVec 8))   (let ((x (+ offset (bv2int x0))))   (yadayada x)   )   )
```


Finite model finding. Finitizing a set of axioms in such a way that the resulting model has a useful relationship to the actual infinite model. Just truncating isn't very satisfactory. 

I guess I could stratify sorts? A lot of duplication. I can't make equalities across strata.
I don't have counters in z3. Possibly we do have gas. things with different gas aren't equal though. hmm.

depth metric? But that isn't stable across eclass.

explicit eid labelling for fresh const.



## Clark Completion for Datalog
[clark completion](https://www.inf.ed.ac.uk/teaching/courses/lp/2012/slides/lpTheory8.pdf)
Only things that are forced to be true are true.
Take horn clause  head(x) :- b(x).
Normalize by putting equalities in the body. This means ground facts become. `edge(1,2). ---> edge(X,Y) :- X = 1, Y = 2.`
Now collect up all rules with heads. head == body1 \/ body2 \/ body3 \/


```z3
(declare-fun edge (Int Int) Bool)
(declare-fun path (Int Int) Bool)
(assert (forall ((x Int) (y Int))
  (= (edge x y)
     (or  (and (= x 1) (= y 2))
          (and (= x 2) (= y 3))
          (and (= x 3) (= y 4)))
)))

(assert (forall ((x Int) (y Int))
  (= (path x y)
     (or
          (edge x y)
          (exists ((z Int)) (and (edge x z) (path z y))))
)))
(check-sat)
(get-model)
```


Closed world assumption. I guess that's simpler

## Rewriting

z3 `simplify` command. This only simplifies under the base theories though.

```z3
(declare-sort aexpr)
(declare-fun add (aexpr aexpr aexpr) Bool)
(declare-fun fadd (aexpr aexpr) aexpr)

(declare-const x aexpr)
(declare-const y aexpr)
(declare-const z aexpr)

(assert (add x y z))

; reflection / functional dependency
; (add x y (fadd x y))  is slightly different. This generates all fadd.
(assert 
  (forall ((x aexpr) (y aexpr) (z aexpr)) (=> (add x y z)  (= z (fadd x y) ) ))
)

; clark completion?
(assert 
  (forall ((x aexpr) (y aexpr) (z aexpr))  (= (add x y z) (add y x z)))
)

; we need something that says two aexpr are only equal if forced to be. There exists a reason.
; clark completion works on atoms
(= (= x y) (exists z (add x y z) ())


; functional dependency
; using implication. fishy?
;(assert 
;  (forall ((x aexpr) (y aexpr) (z aexpr) (z1 aexpr))  (=> (and (add x y z) (add x y z1))) (= z z1))
;)


(check-sat)
(get-model)


```


```z3
(declare-sort aexpr)
(declare-fun add (aexpr aexpr aexpr) Bool)
(declare-fun fadd (aexpr aexpr) aexpr)

(declare-const x aexpr)
(declare-const y aexpr)
(declare-const z aexpr)

(assert (add x y z))

; reflection / functional dependency
; (add x y (fadd x y))  is slightly different. This generates all fadd.
(assert 
  (forall ((x aexpr) (y aexpr) (z aexpr)) (=> (add x y z)  (= z (fadd x y) ) ))
)

; clark completion?
(assert 
  (forall ((x aexpr) (y aexpr) (z aexpr))  (= (add x y z) (add y x z)))
)




(check-sat)
(get-model)


```
(not (= x y)) iff no functional dependency violation. 



forall z1, z2, (not (= z1 z2)) iff (not (exists (x y) (add x y z1) (add x y z2)))
what about simple constants
(X x) (Y y) => x != y all pairs of constant tables?
But why?

forall z1, z2. z1 != z2 <->  (not (add(x,y,z1) /\ add(x,y,z2)) ) 
forall z1, z2. z1 != z2 <->  (not (mul(x,y,z1) /\ mul(x,y,z2)) ) 
forall z1, z2. z1 != z2 <->  (not (add(x,y,z1) /\ add(x,y,z2)) ) 
forall z1, z2. z1 != z2 <->  (not (X z1 /\ X z2) ) 

// No but this isn't right. We _might_ have these equal
forall z1, z2. Y z1 /\ X z2 -> z1 != z2  // all pairs
forall z1, z2. Y z1 /\ Z z2 -> z1 != z2 

Yes some are existential head rules. hmm.
exists z, X z.
where does the exists go?
Skolemize them I guess.
forall x y, head(x, y) <-> \/  ( y = skolem(x) /\ body(x)  )


so 
exists z, X z. becomes 
exists z, forall x, X x <-> x = z.

exists z, f(y,z) :- f(x,y)

f(a).
f(f(X)) <- f(X).

forall z y, f(y,z) = (z = f(y) /\ exists x, f(x,y)  \/  f(a,fa)   )


algerbaic datatypes + datalog have the same problem


Maybe if I know the big terms that are causing nontermination, I could cap them. Over approximate equality.
Checking two terms can be done as a separate smt query.

((depth (num 1)) = 1)

(depth (add x y)) <= 1 + max(depth(x),depth(y))




mbqi is a kind of like datalog isn't it?

If we want things bounded, perhaps explicilty bound the state of eids? 
n : _ BitVec 20
(eid n)

Logically there is nothing forcing it to have 3 universe elements here. Hmm. We need equality to be forced by some reason. clark semantics on the equality relation. (= x y) = 

(eid n x) as a relation (eid bitvec aexpr)

bounded skolem function?

We could explicitly use three valued semantics. What about encoding an ASP query to smt?


= is explicitly a relation. We can't quantify the thing?
One reason is refl. But we can't really talk about refl
So we need to expand the forall and exlude the refl cases, which don't need to be dignified. 
(= (= a b)  ((a = c) /\ (= b c)
(skolem x) = a

(= (= x y) (or (((exists a b) (= (add a b) x) and (= (add a b) y)
            ((   exists a b     (= (add a b) x) (= (add b a) y)  ))
            
            )
add(a,b) = add(b,a) if


## Option datatype
```z3
(declare-datatypes (T) ((Option None (Some (val T)))))
(declare-sort aexpr)
(declare-fun add (aexpr aexpr) (Option aexpr))

(declare-const x aexpr)
(declare-const y aexpr)
(declare-const z aexpr)

(assert (is-Some (add x y)))
(define-const xy aexpr 
  (val (add x y))
)

;(assert (= (= x z)  
;      (exists ((a aexpr) (b aexpr))
;          (and (= (add a b) (Some x))
;            (= (add a b) (Some z))
;          )
;      )
;))

(assert is-Some (add xy z))

(assert 
  (forall ((x aexpr) (y aexpr))
   (= (add x y) (add y x)) 
  )
)

(check-sat)
(get-model)


```
## Pseudo Boolean

# Finite Models
There is a sense in which getting a model returend is much more powerful and satisfying than merely getting `unsat`.
When you start using quantifiers, it feels as though 
Z3 can output finite models.

Not all axioms have finite models.
Is there a pile of tricks or systematic thing I can do to a set of axioms such that they have or may have a finite model and this model has some useful relationship to the infinite model.

one suggestion. Try to use relational definitions, not functional definitions. total functions tend to lead to infinite models.


## EPR
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

Using existentials is in a sense defining skolem function symbols
Defining function symbols is in a sense invoking an implicit congruence and totality axiom which have scary quantifiers. 




[interestting tidbit](https://stackoverflow.com/questions/24062292/most-efficient-way-to-represent-memory-buffers-in-z3) suggests not using array initialization using stores. Instead element by element. Also extensionality axiom for arrays can be turned off

https://stackoverflow.com/questions/28149863/why-is-e-matching-for-conjunctions-sensitive-to-order-case-splitting-strategy



# Z3 



## Z3 source spelunking

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

## paramaters, tactics, and commands
`z3 -in`  interactive mode

SOme interesting looking commands:

```
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

(mbi <expr> <expr> (vars))
    perform model based interpolation
 (mbp <expr> (<vars>))
    perform model based projection
(get-proof)
    retrieve proof
 (get-proof-graph)
    retrieve proof and print it in graphviz
 (euf-project (exprs) (vars))
    perform congruence projection
 (eufi <expr> <expr> (vars))
    perform model based interpolation
```

muz has: datalog, bmc, and spacer mode, and xform?
:print-certificatie fives "inductive invataint" even in datalog?


## Z3 Add Commutative Benchmark
This is making and abstract sort for which we are defining commutativity and associativity rules.
Z3 is quite fast even here at proving some particularly rearrangement.


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

It is alarming it feels like i can't use instantiation of proven theorems. What am I missing.

We could explicilty maintain the signature and check when new stuff comes in to add to it

https://ncatlab.org/nlab/show/sequent+calculus

https://github.com/jonsterling/lcf-sequent-calculus-example

```python
from z3 import *
def z3_contains(t1, x):
  print(t1)
  if x.eq(t1):
    return True
  else:
    for c in t1.children():
      if contains(c,x):
        return True
  return False

class Proof(): # Sequent?
  # private internal methods
  __hyps = [] # Would dictionary or set be nice?
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
  def smt_cut(p,q):
    assert isinstance(p, Proof) and isinstance(q, Proof)
    s = Solver()
    s.add(Implies(And(p.concs), Or(q.hyps)))
    assert s.check() == unsat
    r = Proof()
    r.__hyps = p.__hyps
    r.__concs = q.__concs
    return r
  def axiom(hyps,concs):
    p = Proof()
    p.__hyps = hyps
    p.__concs = concs
    return p
  def id(q):
    p = Proof()
    p.__hyps = [q]
    p.__concs = [q]
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
  def forall_l(self,x):
    f = self.__hyps[0]
    p = self.copy() 
    p.__hyps.append(ForAll([x], f))
    return p
  def forall_r(self,x): 
    if any(z3_contains(t, x) for t in self.__hyps):
      raise BaseException("hypothesis contains x")
    elif any(z3_contains(t,x) for ti in self.__concs[1:]):
      raise BaseException("conclusions contains x")
    f = self.__hyps[0]
    p = self.copy()
    p.__concs.append(ForAll([x], f))
    return p
  def refl(self, t): # right equality rule
    p = self.copy()
    p.__concs.append(t == t)
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

print(Proof.id(a).forall_l(a))

def induction_schema(p):
  i = FreshInt("i")
  j = FreshInt("j")
  base_case = p(IntVal(0))
  induction_case = Implies(And(p(i), i >= 0), p(i+1))
  hyp = And(base_case, induction_case)
  conc = Implies(j >= 0, p(j))
  return Proof.axiom([hyp],[conc])

```

```python
from z3 import *
x = Int("x")

print(dir(Exists([x], x >= 0).body().arg(0)))

#print(Exists([x], x >= 0).body().arg(0).)

print(substitute(Exists([x], x >= 0).body(), (x, IntVal(3))))

def z3_contains(t1, x):
  print(t1)
  if x.eq(t1):
    return True
  else:
    for c in t1.children():
      if contains(c,x):
        return True
  return False

print(contains(x + x, IntVal(3)))
print(contains(x + x, x))
print(contains(x + x >= 14, x))
print(contains(Exists([x], x >= 0), x))
  ''' instan is not a rule?
  def instan(self, t): 
    p = self.copy()
    forall = p.hyps[0]
    if not forall.is_forall() or notor 
      raise "Not a Forall"
    elif  forall.num_vars() != 0 :
      raise "not single arg quantifier"
    elif forall.num_sort(0) != t.sort():
      raise "wrong sort"
    else:
      p.hyps += substitute(forall.body(),Const(forall.var_name(), t.sort()), t)
      return p
  '''

```


```python
from z3 import *
#help(substitute_vars)

x = Int("x")
y = Int("y")
f = Function("f", IntSort(), BoolSort())

t= Exists([x], And(f(x),Exists([y], f(x)) ))
print(t)
print(t.body())
print(substitute(t.body(), (Var(0, IntSort()), IntVal(3))) )
print(dir(t))
print(t.var_name(0))


```

https://leanprover.github.io/logic_and_proof/natural_deduction_for_propositional_logic.html
https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch2-natded.pdf
Use tuples instead of lists for immutability?

```python
from __future__ import annotations
from z3 import *
def z3_contains(t1, x):
  print(t1)
  if x.eq(t1):
    return True
  else:
    for c in t1.children():
      if z3_contains(c,x):
        return True
  return False

class Proof():
  # private internal methods
  __hyps = () # Would dictionary or set be nice?
  __conc = None # None means uninitialized.
  def implI(self,n : int):
    assert(0 <= n < len(self.__hyps))
    p = Proof()
    p.__hyps = self.__hyps[:n] +  self.__hyps[n+1:]
    p.__conc = Implies(self.__hyps[n], self.__conc)
    return p
  def implE(self, x : Proof):
    assert(isinstance(x, Proof))
    assert(is_implies(self.conc))
    assert(self.conc.num_args() == 2)
    assert(self.conc.arg(0).eq(x))
    p = Proof()
    p.__hyps = x.__hyps + self.__hyps
    p.__conc = self.__conc.arg(1)
    return p
  def conjI(*ps : Proof):
    assert(all([isinstance(x, Proof) for x in ps]))
    p = Proof()
    p.__hyps = x.__hyps + self.__hyps
    p.__conc = And(self.__conc, x.__conc)
    return p
  def disj1I(self, b : BoolRef):
    p = Proof()
    p.__hyps = self.__hyps
    p.__conc = Or(self.__conc, b)
    return p
  def disjE(self, p1 : Proof, p2 : Proof):
    assert(p1.__hyp[0].eq(self.__conc.arg(0)))
    assert(p2.__hyp[1].eq(self.__conc.arg(1)))
    assert(p1.__conc.eq(p2.__conc))
    p = Proof()
    p.__hyp = p1.__hyp[1:] + p2.__hyp[1:]
    p.__conc = p1.__conc
    return p
  def forallI(self, x : ExprRef):
    assert(is_const(x) and x.decl().kind() == Z3_OP_UNINTERPRETED)
    assert(all([not z3_contains(hyp,x) for hyp in self.__hyps]))
    p = Proof()
    p.__hyps = self.__hyps
    p.__conc = ForAll([x], self.__conc)
    return p
  def forallE(self, e : ExprRef):
    assert(is_quantifier( self.__conc) and self.__conc.is_forall())
    # test for number of bound vars?
    p = Proof()
    p.__hyps = self.__hyps
    p.__conc = substitute( self.__conc.body(), (Var(0, e.sort()), e))
    return p
  def existsI(self, t, e):
    assert(is_quantifier(e) and e.is_exists())
    assert(substitute(e.body(), (Var(0, t.sort()), t)).eq(self.__conc))
    p = Proof()
    p.__hyps = self.__hyps
    p.__conc = e
    return p
  def existsE(self,)
  def refl(x : BoolRef):
    assert(isinstance(x, BoolRef))
    p = Proof()
    p.__hyps = (x,)
    p.__conc = x
    return p
  def smt(hyps, conc):
    s = Solver()
    formula = Implies(And(hyps), conc)
    s.add(Not(formula))
    status = s.check()
    if status == sat:
      raise Exception("Countermodel", s.model())
    elif status != unsat:
      raise Exception("Bad Z3 status", status)
    p = Proof()
    p.__hyps = tuple(hyps)
    p.__conc = conc
    return p
  @property
  def hyps(self):
    return self.__hyps
  @property
  def conc(self):
    return self.__conc
  def eqI(x):
    p = Proof()
    p.conc = x == x
    return p
  #def eqE(self,t):
  def __repr__(self):
    return f"{self.__hyps} |- {self.__conc}"
  
x = Bool("x")
z,y = Ints("z y")
print(Proof.refl(x).implI(0))
#print(Proof.smt([], Implies(x,False) ))
print(Proof.smt([], z + y == y + z).forallI(z).forallI(y).forallE(z))


```