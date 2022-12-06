---
layout: post
title: SMT Solvers
---

- [What is SMT?](#what-is-smt)
  - [SAT solving](#sat-solving)
  - [Bitvectors](#bitvectors)
  - [Integers](#integers)
  - [Reals](#reals)
  - [Difference Logic](#difference-logic)
  - [Arrays](#arrays)
  - [Constraint problems](#constraint-problems)
- [Datatypes](#datatypes)
  - [List](#list)
  - [Option datatype](#option-datatype)
  - [Records](#records)
    - [Rationals](#rationals)
    - [Intervals](#intervals)
    - [Modules](#modules)
  - [Church / Recursors / Final](#church--recursors--final)
- [Solvers](#solvers)
- [Optimization](#optimization)
- [Synthesis](#synthesis)
  - [Constrained Horn Clauses](#constrained-horn-clauses)
  - [Interpolation](#interpolation)
  - [Abduction](#abduction)
  - [Syntax Guided Synthesis Sygus](#syntax-guided-synthesis-sygus)
- [Higher Order](#higher-order)
  - [Lambda](#lambda)
  - [Normalization By Evaluation](#normalization-by-evaluation)
- [Models](#models)
  - [Separation logic](#separation-logic)
  - [Temporal Logic](#temporal-logic)
  - [Kripke Intuitionism](#kripke-intuitionism)
- [Polymorphism](#polymorphism)
- [Type Checking](#type-checking)
  - [Refinement types](#refinement-types)
- [Transcendentals](#transcendentals)
- [Float](#float)
- [Quantifiers](#quantifiers)
  - [Gas](#gas)
  - [Mechanisms for abstraction](#mechanisms-for-abstraction)
    - [`let`](#let)
    - [define](#define)
    - [datatype DSL](#datatype-dsl)
  - [Quantifiers and define](#quantifiers-and-define)
    - [A Manual Proof Discipline](#a-manual-proof-discipline)
    - [Reflection](#reflection)
    - [Minkanren](#minkanren)
  - [Relations vs Functions](#relations-vs-functions)
  - [Bounded Quantification](#bounded-quantification)
    - [define-fun-rec](#define-fun-rec)
    - [Bitvec Quantify](#bitvec-quantify)
  - [Datalog](#datalog)
    - [uZ3](#uz3)
    - [Clark Completion](#clark-completion)
    - [Transitive Closure](#transitive-closure)
    - [Explicit datalog iteration](#explicit-datalog-iteration)
    - [Well founded](#well-founded)
    - [Proof Relevant](#proof-relevant)
      - [First Class Union Find](#first-class-union-find)
  - [Rewriting](#rewriting)
  - [Pseudo Boolean](#pseudo-boolean)
- [Parsing](#parsing)
- [Finite Models](#finite-models)
  - [EPR](#epr)
- [Query Containment](#query-containment)
- [Program Verification](#program-verification)
  - [Nand2Tetris Cpu](#nand2tetris-cpu)
  - [Arm](#arm)
  - [Forth](#forth)
  - [WASM](#wasm)
  - [Weakest Precondition](#weakest-precondition)
    - [Initial Style](#initial-style)
    - [Final Style](#final-style)
- [Proofs](#proofs)
  - [Proof Objects](#proof-objects)
  - [Interactive Proof](#interactive-proof)
    - [A Manual Proof Discipline](#a-manual-proof-discipline-1)
    - [Python Hilbert Proof](#python-hilbert-proof)
    - [Python Backwards Proof](#python-backwards-proof)
    - [Python Forward Proof](#python-forward-proof)
  - [Hoare LCF](#hoare-lcf)
- [Z3](#z3)
  - [Z3 source spelunking](#z3-source-spelunking)
  - [src - most of the goodies are here.](#src---most-of-the-goodies-are-here)
  - [paramaters, tactics, and commands](#paramaters-tactics-and-commands)
  - [Z3 Add Commutative Benchmark](#z3-add-commutative-benchmark)
- [CVC5](#cvc5)
  - [test/regress](#testregress)
  - [options](#options)
- [Resources](#resources)
- [Resources](#resources-1)

See also:
- SAT solvers
- Synthesis
- automated theorem proving
- Imperative Verification

# What is SMT?

SAT solvers search over boolean variables to make a formula true. SMT solvers allow these booleans to represent external facts like `p := x >= 7` and use other algorithms to determine things like if both `x >= 7` and `x <= 3` can both be true. These are kind of like secret extra constraints on the boolean variables.

For more:

- [Tutorial](https://github.com/philzook58/z3_tutorial)
- [Copy of Z3 rise 4 fun](https://www.philipzucker.com/z3-rise4fun/)
- [Z3 guide](https://microsoft.github.io/z3guide/)
- [smtlib standard](https://smtlib.cs.uiowa.edu/language.shtml)


<iframe width="560" height="315" src="https://www.youtube.com/embed/56IIrBZy9Rc" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>


## SAT solving
If you just stick to boolean variables, SMT is just a SAT solver (albeit with a better input format).
See notes on SAT

## Bitvectors
[Bitwuzla](https://bitwuzla.github.io/) and Boolector seem like winners here (for quantifier free). I don't know why

Some interesting ops
```
(declare-const a (_ BitVec 4))
(simplify (concat a #x0 #x1 #x2))
(simplify ((_ zero_extend 4) #xF))
(simplify ((_ sign_extend 4) #xF))
(simplify ((_ extract 15 8) #xABCD1234))
(simplify ((_ rotate_left 4) #xABCD))
(simplify ((_ rotate_right 4) #xABCD))
(simplify ((_ repeat 3) #xABC))
```

`(_ bv42 64)` is really useful for not having to write so many zeros.

## Integers

## Reals
## Difference Logic
For special integer inequalities of the form `x - y <= 7`, you don't need a general linear arithemtic solver. You can use graph algorithms to determine if 

https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-smt/diff_solver.html
https://www.cs.upc.edu/~erodri/webpage/cps/theory/sat/SMT-DL/slides.pdf
[ast and Flexible Difference Constraint Propagation for DPLL(T)](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.67.1781&rep=rep1&type=pdf)
[Deciding Separation Logic Formulae by SAT and Incremental Negative Cycle Elimination](https://cpb-us-e1.wpmucdn.com/sites.usc.edu/dist/c/321/files/2019/03/Wang05SLICE-1txv47w.pdf)
## Arrays
- https://microsoft.github.io/z3guide/docs/theories/Arrays
- https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml
- 

- `(_ map and)` map functions
- `((_ const T) a)` constant arrays
- `(as-array f)` to lift a named function to an array.

Using Arrays as Sets, Bags.
- https://stackoverflow.com/questions/17706219/defining-a-theory-of-sets-with-z3-smt-lib2?rq=1
- 
```
(define-fun bag-union ((x A) (y A)) A
  ((_ map (+ (Int Int) Int)) x y))
```


```z3
;z3 has some pre-defined set stuff
(declare-const a (Set Int))

(assert (= a ((as const (Set Int)) false)))
(assert (select a 12))

(assert (= a (union a a)))
(assert (subset a a))
(assert (= a (intersection a a)))
(check-sat)
```


## Constraint problems
See notes on constraint satisfaction

- N-queens
- Sudoku


# Datatypes
cvc5

`Tuple`
`dt.size`
`tuple_select` `tuple_update`


Datatypes are great. They let you bundle stuff into records.

[cvc4 codatatypes](https://www.ijcai.org/Proceedings/16/Papers/631.pdf)

datatypes add an infinite number of acyclicity conditions
## List
List already comes in Z3
List vs Seq


## Option datatype
Option datatypes are a tempting way to model partial functions. I can't say I've had much success.

```z3
(declare-datatypes (T) ((Option None (Some (val T)))))
(declare-sort aexpr)
(declare-fun add (aexpr aexpr) (Option aexpr))

(declare-const x aexpr)
(declare-const y aexpr)
(declare-const z aexpr)

(assert (is-Some (add Sx y)))
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
## Records
### Rationals
Rationals are kind of not an intrinsic. Reals are.

Rationals are a tuple of ints with a notion of equivalence.

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
### Intervals
Intervals are a tuple of reals.
[CEGARing Exponentials into Z3 with Intervals and Python Coroutines](https://www.philipzucker.com/z3-cegar-interval/)
### Modules
Explicit record passing style. You nutter. But it is hard/impossible to pass types. Hmm.

```z3
;re
(declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))

(declare-datatype Any 
(
  (AnyInt (anyint Int))
  (AnyBool (anybool Bool)) 
  (AnyString (anystring String)) 
  (AnyPair (anypair (Pair Any Any)))
 ; (AnyArray (anyarray (Array Any Any))) ; (error "line 6 column 1: datatype is not co-variant"). Ruh roh.
  ; Error
))

;(define-sort T () Int)
(declare-datatype AExpr (par (T)
  ((AExpr (add_ (Array (Pair T T) T)) 
          (lit_ (Array Int T))))       
))

(define-fun example ((M (AExpr Int))) Int 
  (let ((add_ (add_ M)) (lit_ (lit_ M))) ; "open" the module
    (add_ (pair (lit_ 1) (lit_ 2)))
  )
)
; polymorphism is weak enough I need to repeat myself
(define-fun example_string ((M (AExpr String))) String 
  (let ((add_ (add_ M)) (lit_ (lit_ M))) ; "open" the module
    (add_ (pair (lit_ 1) (lit_ 2)))
  )
)

(define-fun example_any ((M (AExpr Any))) Any
  (let ((add_ (add_ M)) (lit_ (lit_ M))) ; "open" the module
    (add_ (pair (lit_ 1) (lit_ 2)))
  )
)

(define-const aexprlit (AExpr Int) 
  (AExpr
   (lambda ((x (Pair Int Int))) (+ (first x) (second x)))
   (lambda ((x Int)) x)
  ))
(define-const aexprstring (AExpr String) 
  (AExpr
   (lambda ((x (Pair String String))) (str.++ "[" (first x) "+" (second x) "]" ))
   (lambda ((x Int)) (str.from_int x))
  ))

; should use error producing "first" that uses a match.

(define-const aexprlit2 (AExpr Any) 
  (AExpr
   (lambda ((x (Pair Any Any))) (AnyInt (+ (anyint (first x)) (anyint (second x)))))
   (_ as-array AnyInt)  ;(lambda ((x Int)) (AnyInt x))
  ))
(define-const aexprstring2 (AExpr Any) 
  (AExpr
   (lambda ((x (Pair Any Any))) (AnyString (str.++ "[" (anystring (first x)) "+" (anystring (second x)) "]" )))
   (lambda ((x Int)) (AnyString (str.from_int x)))
  ))

;(define-const astring (AExpr Any)
;  (AExpr (AnyString aexprstring
;)
(simplify (example aexprlit))
(simplify (example_string aexprstring))
(simplify (example_any aexprlit2))
(simplify (example_any aexprstring2))

```
Hmm. Phantom hoas?

## Church / Recursors / Final
To what degree can I go church / bohm-berarducci / recursor?
We have arrays as higher order functions. Can used boxed universals to simulate forall.

( P a -> (P a -> P a) -> P a)

Dependent datatypes?


Final style encodings using `define-fun` are great. 
You can use a poor man's module system using `(include)` to import interpretations of these things

# Solvers
Q: What options are actualy worth fiddling with
It is interesting to note what unusual characteristics solvers have.

- z3
- bitwuzla
- boolector
- cvc4
- cvc5
- yices2 https://yices.csl.sri.com/papers/manual.pdf yices has a `ef-solve` mode that synesthesia used for synthesis. Is this the analog of PBR solving?
- [smtinterpol](https://github.com/ultimate-pa/smtinterpol)
- alt-ergo
- veriT
- colibri - good at floats?
- mathsat (ultimate eliminator https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/?ui=tool&tool=eliminator)
- smt-rat
- stp
- [dreal](http://dreal.github.io/)

Other systems
- vampire
- aprove
- E

# Optimization
Is Z3 good for classic optimization problems?
I don't know. Without any data I'd guess probably not. It is an after thought to the system. If it beats systems built from the ground up for this purpose that's kind of embarassing.

But minimization can be useful
- Datalog models are minimal ones
- abduction / synthesis is looking for minimal ish solutions
- 

- [νZ - An Optimizing SMT Solver](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-nuz.pdf)
- [Programming Z3 -  Optimization](https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-optimization)
- [z3 guide](https://microsoft.github.io/z3guide/docs/optimization/intro)

- MaxSAT solvers


Implementing datalog as a minsat problem. Minimal model.
`WARNING: optimization with quantified constraints is not supported`. Hmm well, maybe there goes that idea. It does seem to be working though.
```z3
;re
(declare-sort Vert)
(declare-fun path (Vert Vert) Bool)
(declare-fun edge (Vert Vert) Bool)

(declare-const a Vert)
(declare-const b Vert)
(declare-const c Vert)

(assert (forall ((x Vert) (y Vert))
  (=> (edge x y) (path x y))
))

(assert (forall ((x Vert) (z Vert))
  (=> (exists ((y Vert)) (and (edge x y) (path y z))) (path x z))
))

(assert (edge a b))
(assert (edge b c))

;(assert  (=> (edge a b) (path a b)))

(assert-soft (not (path a a)))
(assert-soft (not (path a b)))
(assert-soft (not (path a c)))

(assert-soft (not (path b a)))
(assert-soft (not (path b b)))
(assert-soft (not (path b c)))

(assert-soft (not (path c a)))
(assert-soft (not (path c b)))
(assert-soft (not (path c c)))

(check-sat)
(get-model)
```

# Synthesis

[aeval](https://github.com/grigoryfedyukovich/aeval/) quantifier elimination that also synthesizes


[Synthesizing an Instruction Selection Rule Library from Semantic Specifications](https://pp.ipd.kit.edu/uploads/publikationen/buchwald18cgo.pdf)

## Constrained Horn Clauses
See note on CHC

## Interpolation
[interpolation slide](https://userpages.uni-koblenz.de/~sofronie/vtsa-2015/slides-griggio2.pdf)
[Craig interpolation](https://en.wikipedia.org/wiki/Craig_interpolation)

For unsatisifable formula `A => B`, produces a C such that `A => C`, `C => B` whihc only uses shared variables. Considered as sets, B is a subset of A.

For finite unrolling of transition relation, we can use it to produce an abstraction of the initial state that is sufficient to prove the property. Maybe this gets us a full inductive invariant. `unroll*10 => Prop of only last timesteps vars`

For pure sat interpolation can be found from resolution proof / unsat certificate

Theory specific interpolation.

Maybe `A |- B` is a more interesting perspective. Interpolation is deriving a cut proof.

For propositional variables you can derive the appropriate interpolat by exsitentializing the unshared variables and doing sort of quantifier elimination.

cvc5 has an interpolation solver
You can also use CHC solvers - see spacer tutorial
[iZ3](http://mcmil.net/wordpress/2019/12/09/interpolating-z3/) old no longer maintained z3 extension
https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-propositional-interpolation POGO. Using unsat cores to derive interpolants



## Abduction
Absduction is a synthesis problem. See notes on synthesis 

Abduction -

Given A and C, find some B such that. `A, B |- C` Super underconstrained. A and B should be consistent. Should generalize well. A is accepted axioms, C is observations.

Houdini

- Planning. A = initial state, B is final state, C is plan
- spec synthesis
- invariant synthesis. 


Houdini explicitly parametrizes candidate things with boolean turns ons `(and (=> enable1 (x < 7)) (=> enable 2 (= x 0)). We may want to minsat these enables.




https://plato.stanford.edu/entries/abduction/index.html
https://en.wikipedia.org/wiki/Abductive_reasoning
https://en.wikipedia.org/wiki/Abductive_logic_programming

https://fbinfer.com/docs/separation-logic-and-bi-abduction
https://blog.sigplan.org/2020/03/03/go-huge-or-go-home-popl19-most-influential-paper-retrospective/

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

## Syntax Guided Synthesis Sygus
Semgus

https://cvc5.github.io/docs/cvc5-1.0.0/examples/sygus-inv.html

```cvc5
;; The background theory is linear integer arithmetic
(set-logic LIA)

;; Name and signature of the function to be synthesized
(synth-fun max2 ((x Int) (y Int)) Int
    
    ;; Declare the non-terminals that would be used in the grammar
    ((I Int) (B Bool))

    ;; Define the grammar for allowed implementations of max2
    ((I Int (x y 0 1
             (+ I I) (- I I)
             (ite B I I)))
     (B Bool ((and B B) (or B B) (not B)
              (= I I) (<= I I) (>= I I))))
)

(declare-var x Int)
(declare-var y Int)

;; Define the semantic constraints on the function
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= x (max2 x y)) (= y (max2 x y))))

(check-synth)
```

```z3
;re
(define-datatype ()
(
  (I
  (X) (Y) (Zero) (One)
  (Add (add1 I) (add2 I)) 
  (Sub (sub1 I) (sub2 I)) 
  (Ite (ite1 B) (ite2 I) (ite3 I))
  )
  (B
      (And (and1 B) (and2 B)) 
      (Or (or1 B) (or2 B))
      (Eq (eq1 I) (eq2 I)) 
      (Lte1 (lte1 I) (lte2 I)) 
  )
)
)
(define-fun-rec eval-B ((e Expr) (x Int) (y Int))

)

(declare-const max2 B)
; This probably won't end well.
;(assert (forall ((x Int) (y Int))  (>= (eval max2 x y) x)))
;(assert (forall ((x Int) (y Int))  (>= (eval max2 x y) y)))
;(assert (forall ((x Int) (y Int))  (or (= x (eval max2 x y)) (= y (eval max2 x y)))))

; but examples might
(define-fun spec ((x Int) (y Int)) Bool
  (and (>= (eval max2 x y) x)
       (>= (eval max2 x y) y))
       (or (= x (eval max2 x y)) (= y (eval max2 x y)))
)

(assert (spec 0 0))
(assert (spec 1 2))
(assert (spec 7 8))
(assert (spec 17 8))
(assert (spec 23 -1))

(check-sat)

```

```z3
;re
(declare-datatypes ()
(
  (Expr
  (X) (Y) 
  ;(Zero) (One)
  ;(Add (add1 Expr) (add2 Expr)) 
  ;(Sub (sub1 Expr) (sub2 Expr)) 
  (Ite (ite1 Expr) (ite2 Expr) (ite3 Expr))
   ;   (And (and1 Expr) (and2 Expr)) 
   ;   (Or (or1 Expr) (or2 Expr))
   ;   (Eq (eq1 Expr) (eq2 Expr)) 
      (Lte (lte1 Expr) (lte2 Expr)) 
  )
  (Univ
    (Int (int1 Int))
    (Bool (bool1 Bool))
  )
))


(define-fun-rec eval ((e Expr) (x Int) (y Int)) Univ
  (match e (
    (X (Int x))
    (Y (Int y))
    ;(Zero (Int 0))
    ;(One (Int 1))
    ;((Add ex ey) (Int (+ (int1 (eval ex x y)) (int1 (eval ey x y)))))
    ;((Sub ex ey) (Int (- (int1 (eval ex x y)) (int1 (eval ey x y)))))
    ((Ite c ex ey) (Int (ite (bool1 (eval c x y))  (int1 (eval ex x y))  (int1 (eval ey x y)))))
    ; ((And ex ey) (Bool (and (bool1 (eval ex x y)) (bool1 (eval ey x y)))))
    ; ((Or ex ey) (Bool (or (bool1 (eval ex x y)) (bool1 (eval ey x y)))))
    ; ((Eq ex ey) (Bool (= (int1 (eval ex x y)) (int1 (eval ey x y)))))
     ((Lte ex ey) (Bool (<= (int1 (eval ex x y)) (int1 (eval ey x y)))))
  ))
)
;(simplify (eval (Add X Y) 42 7))
(simplify (eval (Ite (Lte X Y) Y X) 42 7))

(declare-const max2 Expr)

(define-fun spec ((x Int) (y Int)) Bool
  (and (>= (int1 (eval max2 x y)) x)
       (>= (int1 (eval max2 x y)) y)
       (or (= x (int1 (eval max2 x y))) (= y (int1 (eval max2 x y)))))
)

(assert (spec 0 0))
(assert (spec 1 2))
(assert (spec 7 8))
(assert (spec 17 8))
(assert (spec 23 -1))

(check-sat)
(get-model)
(eval (eval max2 0 0))
(eval (eval max2 1 2))
(eval (eval max2 17 8))
(eval (eval max2 23 1))
(eval (bool1 (Int 17))) ; something very weird is happening here

```

```z3
;re
(declare-datatypes ()
(
  (Expr
  (X) (Y) 
  ;(Zero) (One)
  ;(Add (add1 Expr) (add2 Expr)) 
  ;(Sub (sub1 Expr) (sub2 Expr)) 
  (Ite (ite1 Expr) (ite2 Expr) (ite3 Expr))
   ;   (And (and1 Expr) (and2 Expr)) 
   ;   (Or (or1 Expr) (or2 Expr))
   ;   (Eq (eq1 Expr) (eq2 Expr)) 
      (Lte (lte1 Expr) (lte2 Expr)) 
  )
))


(define-fun-rec eval ((e Expr) (x Int) (y Int) (res Int)) Bool
  (match e (
    (X (= x res))
    (Y (= y res))
    ;(Zero (= 0 res))
    ;(One (= 1 res))
    ;((Add ex ey) (Int (+ (int1 (eval ex x y)) (int1 (eval ey x y)))))
    ;((Sub ex ey) (Int (- (int1 (eval ex x y)) (int1 (eval ey x y)))))
    ((Ite c ex ey) (Int (ite (bool1 (eval c x y))  (int1 (eval ex x y))  (int1 (eval ey x y)))))
    ; ((And ex ey) (Bool (and (bool1 (eval ex x y)) (bool1 (eval ey x y)))))
    ; ((Or ex ey) (Bool (or (bool1 (eval ex x y)) (bool1 (eval ey x y)))))
    ; ((Eq ex ey) (Bool (= (int1 (eval ex x y)) (int1 (eval ey x y)))))
     ((Lte ex ey) (Bool (<= (int1 (eval ex x y)) (int1 (eval ey x y)))))
  ))
)
;(simplify (eval (Add X Y) 42 7))
(simplify (eval (Ite (Lte X Y) Y X) 42 7))

(declare-const max2 Expr)

(define-fun spec ((x Int) (y Int)) Bool
  (and (>= (int1 (eval max2 x y)) x)
       (>= (int1 (eval max2 x y)) y)
       (or (= x (int1 (eval max2 x y))) (= y (int1 (eval max2 x y)))))
)

(assert (spec 0 0))
(assert (spec 1 2))
(assert (spec 7 8))
(assert (spec 17 8))
(assert (spec 23 -1))

(check-sat)
(get-model)
(eval (eval max2 0 0))
(eval (eval max2 1 2))
(eval (eval max2 17 8))
(eval (eval max2 23 1))
(eval (bool1 (Int 17))) ; something very weird is happening here
```


Sort gas. But then we still can't define-fun-recs
(define-sort S)
(delare-datatypes (N) (
  (I
      (Add (S N) (S N)))
)


# Higher Order
[Extending SMT Solvers to Higher-Order Logic](https://www.verit-solver.org/papers/cade2019.pdf)

```cvc5
(set-logic HO_ALL) ; HO_UF; HO_LIA
(declare-const f (-> Int Int))
(assert (= (f 1) 2))
(assert (= f (lambda ((x Int)) 2)))
(assert (= f f))
(check-sat)
(get-model)
```

## Lambda
https://microsoft.github.io/z3guide/docs/logic/Lambdas
Z3 supports lambdas. I believe they are lambda lifted.
```z3
;re
(simplify (select (lambda ((x Int)) (+ x 3)) 17))


```

How else can we make arrays that have a definition?

```z3
;re
(declare-const a (Array Int Int))
(assert (forall ((x Int)) (= (select a x) (+ x 42))))
(check-sat) ; nope. This hangs.
```

relational-style, underapproximate constraints on a by only requiring usage sites.
```z3

(declare-const a (Array Int Int))
(define-fun select-a ((x Int) (res Int)) Bool
  (and (= res (select a x))
       (= (select a x) (+ x 3))
  )
)

;(declare-const x Int)
(declare-const res Int)
(assert (select-a 7 res))
(check-sat)
(get-model)
```


```z3
(define-const a (Array Int Int) (lambda ((x Int)) (+ x 3)))
(check-sat) ; sat. no problemo
(get-model)
```

`as-array` lifts functions to arrays. That's pretty cool.
`define-fun-rec` can be lifted into array not `define-fun`.
```z3
;re
(define-sort Arrow (A B) (Array A B))
(define-fun-rec foo ((x Int)) Int (+ x 4))
(simplify (select (_ as-array foo) 7)) ;11
(define-const a (Arrow Int Int) (_ as-array foo))
(check-sat)
(get-model)
(eval (select a 7)) ;11

```
## Normalization By Evaluation

We can deeply embed a lambda calculus and use define-fun-rec to normalize it. Perhaps by defining eval with explicit envs, defunctionalize?, perhaps by abusing Array system.
```z3
;nbe
(declare-datatype Term (
  (Lam (t Term))
  (App (f Term) (x Term))
  (Var (n Int))
))
(declare-datatype Value
  (
    (VLam (Closure))

  )
)
```


SKI combinators. I've heard tale that F* compiles to ski combinators in some part and discharges to smt

# Models
## Separation logic
<https://www.philipzucker.com/executable-seperation/> blog post modelling separation logic in Z3
http://cvc4.cs.stanford.edu/wiki/Separation_Logic
Can do the same sort of thing directly in define-fun

Using the Option encoding seems to work very poorly
```z3
;re
;(declare-datatype Heap 
;  ((Heap (data (Array Int Int)) (valid (Array Int Bool))))
;)
(define-sort Ptr () (_ BitVec 4))
(declare-datatype Option (par (T) (
  (Some (some T))
  (None)
  )
))
(define-sort Heap () (Array Ptr (Option Ptr)))
(define-sort Prop () (Array Heap Bool))

(define-const empty-heap Heap (lambda ((p Ptr)) None))
(define-const emp Prop (lambda ((h Heap)) (= h empty-heap)))
(define-fun pto ((x Ptr) (y Int)) Prop
  (lambda ((h Heap)) (= h (store empty-heap x (Some y)))))

; regular connectives are just lifts
(define-fun and_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (and (a h) (b h))))
(define-fun or_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (or (a h) (b h))))
(define-fun impl_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (=> (a h) (b h))))

(define-fun ** ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) 
  (exists ((h1 Heap) (h2 Heap))
  (and (a h1) (b h2)
   (forall ((x Ptr))
   (and
    (match (select h x) (
      (None (and (= None (select h1 x)) (= None (select h2 x))))
      ((Some y)
        (not (= (and (= (select h1 x) (Some y)) (= (select h2 x) None))
                (and (= (select h1 x) None) (= (select h2 x) (Some y)))
        
        )))

   ))
  ))
))))

(declare-const heap Heap)
;(assert (select (** emp (pto 3 4)) heap))
;(assert (select (** emp emp) heap))
;(assert (select (pto 3 4) heap))
(assert (select (** emp (pto (_ bv3 4) 4)) heap))
(check-sat)
(get-model)



```
```
  (lambda ((h Heap)) 
    (exists ((h1 Heap))
      (let ((h2 (lambda ((x Int))
                (match (select h x) ( 
                  (None None)
                  ((Some x) (match (select h1 x) (
                          (None (Some x))
                          ((Some y) None)
                          )))
      )))))
      (and
          (= h1 (lambda ((x Int))
            (match (select h x) ( 
                  (None None)
                  ((Some x) (match (select h2 x) (
                           (None (Some x))
                          ((Some y) None)
                           )))
      ))))
        (a h1) (b h2)
      )
```

Using a separate valid and data encoding, it goes much better. We can share the data everywhere, which is nice
```z3
;re
(define-sort Ptr () (_ BitVec 64))
(define-sort Mask () (Array Ptr Bool))
(define-const empty-mask Mask (lambda ((p Ptr)) false))
(declare-datatype Heap 
  ((Heap (data (Array Ptr Int)) (valid Mask)))
)

(define-sort Prop () (Array Heap Bool))
(define-const emp Prop (lambda ((h Heap)) (= (valid h) empty-mask)))
(define-fun pto ((x Ptr) (y Int)) Prop
  (lambda ((h Heap)) (and (= (select (data h) x) y) 
                             (= (valid h) (store empty-mask x true)))))

; regular connectives are just lifts
(define-fun and_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (and (a h) (b h))))
(define-fun or_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (or (a h) (b h))))
(define-fun impl_ ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) (=> (a h) (b h))))

(define-fun sep ((a Prop) (b Prop)) Prop 
  (lambda ((h Heap)) 
  (match h (
    ((Heap data valid)
      (exists ((h1 Mask) (h2 Mask))
          (and (a (Heap data h1)) (b (Heap data h2))
              (forall ((x Ptr))
                (and (= (valid x) (or (h1 x) (h2 x)))
                     (not (and (h1 x) (h2 x))))
          ))
      )
  )))
))

(declare-const heap Heap)
;(assert (select (** emp (pto 3 4)) heap))
;(assert (select (** emp emp) heap))
;(assert (select (pto (_ bv3 4) 4) heap))
;(assert (select (** emp (pto (_ bv3 4) 4)) heap))
(assert (select (sep (pto (_ bv4 64) 8) (pto (_ bv3 64) 42)) heap))
;(assert (select (sep (pto (_ bv3 4) 8) (pto (_ bv3 4) 4)) heap))
(check-sat)
(get-model)

```

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
## Temporal Logic
- [Modelling TLA+ in Z3py](https://www.philipzucker.com/Modelling_TLA_in_z3py/)
- https://en.wikipedia.org/wiki/Temporal_logic

We could try to find models for temproal logic statements.

Typically one is trying to model check. Does such and such statement hold on a particular transition system.


## Kripke Intuitionism
[Basic semantcs](https://plato.stanford.edu/entries/logic-intuitionistic/#BasSem)
https://en.wikipedia.org/wiki/Kripke_semantics#Semantics_of_intuitionistic_logic
http://therisingsea.org/notes/talk-shawn-kripke.pdf

```z3


(declare-sort World)
; https://microsoft.github.io/z3guide/docs/theories/Special%20Relations
(define-fun R ((x World) (y World)) Bool ((_ partial-order 0) x y))


; propisitions becomes functions from world to bool.
;(declare-fun p (World) Bool)

; Alternative explicit formulas?
; or explicit valuations on atoms
(declare-sort Atom)
(declare-fun value (World Atom) Bool)

(declare-datatypes () ((Formula
  (FAtom (atom Atom))
  (Not (getnot Formula))
  (Conj (fst Formula) (snd Formula))
  (Disj (dfst Formula) (dsnd Formula))
  (Impl (hyp Formula) (conc Formula))
  ))
)

(define-fun-rec satis ((w World) (f Formula)) Bool
  (match f (
    ((FAtom p)  (value w p))
    ((Conj p q) (and (satis w p) (satis w q)))
    ((Disj p q) (or (satis w p) (satis w q)))
    ((Not p)    (forall ((u World)) (=> (R w u) (not (satis u p)))))
    ((Impl p q) 
          (forall ((u World))
            (=> (and (R w u) (satis u p)) (satis u q))
          )
    )
  ))
)

;(define-sort Prop (-> World Bool))



;persistance property
(assert
  (forall ((p Atom) (u World) (w World))
  (=>
    (and (value w p) (R w u))
    (value u p)
  )
  )
)

(declare-const w World)
;(assert (R w w))
(declare-const p Atom)
(declare-const q Atom)
(assert-not (satis w (Disj (Not (FAtom p)) (FAtom p))))
;(assert (satis w (Impl (Conj (FAtom q) (FAtom p)) (FAtom p))))




(check-sat)
(get-model)

```

# Polymorphism
It is a consistent theme that many people have tried in various ways to build a more powerful type system on top of the simple one in smtlib.
This often involves encoding the types into smtlib terms, the analog in some sense of using runtime type checking.

- [Implementing Polymorphism in SMT solvers](https://www.lri.fr/~conchon/publis/conchon-smt08.pdf) why3
- [Extending Smt-Lib v2 with λ-Terms and Polymorphism](https://www.verit-solver.org/papers/smt2014.pdf)
- [Expressing polymorphic types in many sorted languages](http://tertium.org/papers/frocos-11.pdf)
- [A Polymorphic Intermediate Verification Language: Design and Logical Encoding - Boogie](https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.160.9672) Very interesting. Discusses extracting types from terms.

```z3



```

# Type Checking
https://cstheory.stackexchange.com/questions/37211/how-to-do-type-inference-using-an-smt-solver
[SMT-based Static Type Inference for Python 3](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Mostafa_Hassan_BA_report.pdf)

[Practical SMT-Based Type Error Localization](https://cs.nyu.edu/~wies/publ/practical_smt-based_type_error_localization.pdf)

```z3
;re
(declare-datatype Type (
    (Unit)
    (-> (from Type) (to Type))
))
(define-sort Var () String)
(declare-datatype Term (
  (Lambda (var Var) (body Term))
  (Var (name Var))
  (App (app1 Term) (app2 (Term)))
  (TT)
))

(define-sort TEnv () (Array String Type))

(define-fun-rec type ((e TEnv) (t Term) (ty Type)) Bool
  (match t (
    (TT (= ty Unit))
    ((Var v) (= ty (select e v)))
    ((App f x) (exists ((a Type)) 
                (and
                  (type e f (-> a ty))
                  (type e x a)
    )))
    ((Lambda v body) 
      (match ty
      (
          (Unit false)
          ((-> a b) (type (store e v a) body b))
      )
      ))
  )
))


(declare-const ty Type)
(define-const ex Term 
  (Lambda "x" (Var "x"))
)
(define-const tempty TEnv ((_ const Var) Unit))
(assert (type tempty ex ty))
(check-sat)
(get-model)
```

## Refinement types


```z3
;re
(define-sort -> (A B) (Array A B))
;(define-sort Pred (T) (-> T Bool))

(declare-datatype Pair (par (T1 T2)
  ((Pair (fst T1) (snd T2)))))

(define-sort Var () String)
(define-sort Env () (-> Var Int))
(define-sort Pred () (-> (-> Var Int) Bool))
;(define-sort Base () (Pair Var Pred))
; predicates in refinement types refer to all introduced variables.
(declare-datatype Type (
  (Forall (forall_ (-> Var (Pair Type Type)))) ; (-> Var (Pair Type Type)) hoas?
  (Base (base  (-> Var Pred)))
))
; types are a thing I check substyping on.

; list of VCs. a meta conjunction
; hughs list
(define-sort Constraint () (-> (List Pred) (List Pred)))

(define-sort TEnv () (-> Var Type))
(define-sort Synth () (-> TEnv (Pair Constraint Type)))
(define-sort Check () (-> (Pair TEnv Type) Constraint))

(define-const fail Constraint (lambda ((tl (List Pred)) 
  (insert (lambda ((rho Env)) false)) tl)))
(define-fun var_ ((v Var)) Synth 
  (lambda ((gam TEnv)) (Pair nil (gam v))))
(define-fun lit_ ((c Int)) Synth
  (lambda ((gam TEnv)) (Pair nil (Base "c" (lambda ((rho Env)) (= (rho "c") c))))))
(define-fun app_ ((f Synth) (x Var)) Synth
(lambda ((gam TEnv))
  (match (f gam) (
    ((Pair c ty) (match ty (
          ((Forall f) 
            (Pair 
              (lambda ((tl (List Pred)) ((x (Pair gam a)) (c tl)))
              (b v x) 
            
            ))
         (Base  ??? (Pair fail )
    ))
  )
)))

;(define-fun lam_ ((v Var) (b Check)) Check)
;(define-fun let_ ((v Var) (e1 Synth) (e2 Check)) Check




;(define-const Int (Base (lambda ((rho Env)) true))




```

```
; Little ideas 
;global error variable. Could use these for IO?
(declare-const error_msg String)
(ite make-sense goeahead (str.substr error_msg "This property doesn't make sense."))

; Well typed state is too hard.
(declare-datatype State (T) (
  (State (val Value)
          (state T)
  )
))
(define-sort State (T) (-> T (Tup Value T)))


(define-fun bind ((x State) (f (-> Value State))
  ((select f (val x)) (state x))
)


; (Tup a b) to store interior types?

; how close can i get to smtlib3 as it stands

(define-sort Code (T) T)
; I can mark what I consider compile vs runtime
; alternatively
(declare-const Code (par (T) (
  (Quote (unquote T))
)))

(declare-datype MultiEnv
  (
    (MultiEnv
      (intenv (-> Var Int))
      (boolenv (-> Var Bool))
      (stringenv (-> Var String))
    )
  )
)
; or use untyped (Env Var Value)

; basic implication.
(Pair Pred Pred) --> (forall rho (=> (p rho) (q rho)))

```

# Transcendentals
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
# Float
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

```
; https://en.wikipedia.org/wiki/Machine_epsilon
(define-const eps32 Real (^ 2 -23))

; given eps > 0, abs-bound encodes |x| <= eps as conjunction of linear constraints
(define-fun abs-bound ((x Real) (eps Real)) Bool
    (and (<= x eps) (<= (- eps) x )))

(declare-fun rnd-fun (Real) Real)
(define-fun rnd ((x Real) (res Real)) Bool
        (and (= res (rnd-fun x)) ; it is a functional relationship
            (abs-bound (- x res) (* eps32 (abs x))) ; with |x - rnd(x)| <= eps32 * |x|
        ))

; floating point addition is Real addition then round.
(define-fun fp-add ((x Real) (y Real) (res Real)) Bool
    (rnd (+ x y) res))

(define-fun fp-mul ((x Real) (y Real) (res Real)) Bool
    (rnd (* x y) res))

(define-fun box ((x Real) (lower Real) (upper Real)) Bool
    (and (<= lower x) (<= x upper)))
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (and (box x 1 2) (box y 1 2) (box z 1 2)))

; intermediate variables
(declare-const xy Real) (declare-const xyz Real)
; xyz := (* (x + y) z)
(assert (fp-add x y xy))
(assert (fp-mul xy z xyz))
(push)
(assert-not (<= (abs (- xyz (* (+ x y) z))) 0.0001))
(check-sat) ; unsat
(pop)
(assert-not (<= (abs (- xyz (* (+ x y) z))) 0.0000001))
(check-sat) ; sat
```





# Quantifiers
[really good f* summar of z3 whispering](http://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html#understanding-how-f-uses-z3)

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

## Gas
https://namin.seas.harvard.edu/files/krml237.pdf
https://microsoft.github.io/z3guide/docs/logic/Quantifiers#patterns

```z3
; Nah. This isn't doing what I want it to
;re
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) 
(declare-datatype Gas (
  (Z)
  (S (prev Gas))
))

(declare-sort Num)
(declare-fun add (Gas Num Num) Num)

(assert
  (forall ((g Gas) (x Num) (y Num))

     (!   (= (add g y x) (add g y x)) ; (add g y x)
    :pattern ((add (S g) x y))
  )
))

; how to express gas transferrence?
; (= (add g x y) (add g a b))
; (add (S g) x y)) (add (S g) )

(declare-const x Num)
(declare-const y Num)
(declare-const z Num)
(assert 
  (= (add (S Z) x (add (S Z) y z)) (add (S Z) x (add (S Z) z y)))
)

(check-sat)
(get-model)


```
   ; (! (=> (= (add (S g) x y) e)

```z3
(define-sort Nat (T) (-> T (-> T T) -> T))



```



## Mechanisms for abstraction

### `let`
### define
### datatype DSL
include and poor man module system



## Quantifiers and define
Sometimes you can eliminate quantifiers by using define rather than a quantifier. Some quantifiers are turned into macros by macrofinders. `define-fun` is explicitly macro expanded.

```
;re
; instan is forall elimination. But by convention.
(define-fun instan-lemma1 ((x Int)) Bool  (or (> x 0) (< x 0) (= x 0)))
; notice this isn't _asserting_ the lemma
(define-const lemma1 Bool (forall ((x Int)) (instan-lemma1 x)))


; exists
; skolem? 



; altogether proof check. Can also be seperated into mutliple push pop
(assert-not (and lemma1 lemma2 lemma3 theorem))

```

### A Manual Proof Discipline
Separation between module signature and proofs. Seperate files.
Proof datatype to separate from bool definitions

```z3
;re
(declare-datatypes () (
  (Proof (Proof (getformula Bool)))
))
(define-fun proved ((p Proof)) Bool 
  (match p (
    ((Proof p) (not p))
  ))
)
(define-fun instan-lemma1 ((x Int)) Bool  (or (> x 0) (< x 0) (= x 0)))
(define-const lemma1 Proof (Proof (forall ((x Int)) (instan-lemma1 x))))

(push)
;------------
(assert (proved lemma1))
(check-sat)
(pop)

```

Other possibility for Proof type
Forall (Expr)
Exists (Expr)
Eh. I don't really want to reflect everything.

A shallower HOAS embedding
```z3
;re
(declare-datatype Formula (
  (Bool (bool1 Bool))
  (Forall (forall1 (Array Int Formula)))
  (Exists (exists1 (Array Int Formula)))
))


```

```z3
;re
(declare-datatype Exists 
  (
    (Pair (x Int) (pred (Array Int Bool)))
  ))

```


Universals can be proven by having
(define-const x)
```
; other hypothesis do not mention x
;-----------------
(instan-lemma1 x)
```
or by
; other hypothesis can't possibly mention x
;-----------
(assert (proved lemma1))

Universal can be used by using lemma1 or by instan-lemma1 on anything

Existentials can be proved
```
----------
(exists x (relx x))
```
or by
```
whatever
---------
(relx 3)

```

They can be used via
```
define-const x
(relx x)
; no other use of x
;----------------
conclusion may refer to x

```


ExistsE (ExistsE Bool)
ForallE (ForallE (forallE Bool)) ; (apply?)
Forall (ForallI (forallE Bool)) 


(Exists Int Bool) ; can I pack the witness?

define-const lemma Forall (forall x (forallE (instan-lemma x)))
define-fun instan-lemma ((x Int)) ForallE



The method is related to lambda lifting.
We need to give names to different free parameter things.





```z3
;re
(declare-fun even-fun (Int) Int)
(define-fun even ((x Int)) Bool (= (* 2 (even-fun x)) x))

(declare-fun odd-fun (Int) Int)
(define-fun odd ((x Int)) Bool (= (+ 1 (* 2 (odd-fun x))) x))

;(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-const even-axiom Bool (forall ((x Int)) (=> (exists ((y Int)) (= (* 2 y) x)) (= (* 2 (even-fun x)) x))))
;(define-fun even ((x Int)) Bool (exists ((y Int)) (and (= y (even-fun x)) (= (* 2 y) x))))
(define-fun not-even ((x Int)) Bool (forall ((y Int)) (distinct x (* 2 y))))
;(define-fun instan-not-even ((x Int) (y Int)) (distinct x (2 * y)))

(declare-const m Int)
(declare-const n Int)
(assert (odd m))
(assert (odd n))
(assert (not (even m)))
(assert (not (even n)))
;(assert (instan-not-even m (even-fun )))
(assert-not (even (+ n m)))
;(assert (not-even (+ n m)))
(check-sat)
(get-model)

```

```z3
;re
(define-fun even ((x Int) (y Int)) Bool (= (* 2 y) x))
(define-fun odd ((x Int) (y Int)) Bool (= (+ 1 (* 2 y)) x))


(declare-const m Int)
(declare-const n Int)
(declare-const mo Int)
(declare-const no Int)
(assert (odd m mo))
(assert (odd n no))
(assert-not (exists ((x Int)) (even (+ m n) x)))
(check-sat)

```
```z3
;re
(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun odd ((x Int)) Bool (exists ((y Int)) (= (+ 1 (* 2 y)) x)))

(declare-const m Int)
(declare-const n Int)
(assert (odd m))
(assert (odd n))
;--------------------------
(assert-not (even (+ m n)))
(check-sat)
```

```z3

```z3
;re
(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun div4 ((x Int)) Bool (exists ((y Int)) (= (* 4 y) x)))

(declare-const m Int)
(assert (not (even m)))
;---------------------------
(assert-not (not (div4 m)))
(check-sat)
```

Positively asserting existence isn't so bad. It is just asserting on a fresh variable.

Only allow mention variable once on existential elim in hyps

I'm a little worried about circulaity if I pack everything into one proof thing.

existential lemma can be used in hyps.
Instantiated version in a conc (give explicitly). Or just let it crank.
```
(declare-const e) appears only once in hyp for existential elim

(assert-not
  (=> (and (existse e) (instan-lemma1 ))
      (and lemma1 )
  )

)

```

```z3
;re
(define-fun instan-theorem ((m Int) (n Int)) Bool (not (= (* m m) (* 2 (* n n)))))
(define-const theorem Bool (forall ((m Int) (n Int)) (not (= (* m m) (* 2 (* n n))))))


```


### Reflection

Reflection through ADTs + define-fun-rec interpreters

Reflection through arrays

```z3
;re

(define-const add (Array Int Int Int) (lambda ((x Int) (y Int)) (+ x y)))
(define-const mul (Array Int Int Int) (lambda ((x Int) (y Int)) (* x y)))
(define-const and_ (Array Bool Bool Bool) (lambda ((x Int) (y Int)) (and x y)))

;(define-fun-rec add ((x Int) (y Int)) Int )
(simplify (select add 1 2))


```


### Minkanren
define-fun-rec gives you the ability to do an embedded mininkanren

Hmm. minikanren is structured more like clark completion. Interesting.


```z3
(define-sort LInt () (List Int))
(define-fun-rec appendo ((x LInt) (y LInt) (z LInt)) Bool
  (or
    (and (= x nil) (= y z))
    (exists ((w Int) (ws LInt) (res LInt)) 
        (and 
          (= x (insert w ws))
          (= z (insert w res)) 
          (appendo ws y res)
        ))
  )
)

(declare-const x LInt)
(declare-const y LInt)
(declare-const z LInt)
(assert (appendo nil nil nil))
(assert (appendo (insert 0 nil) nil (insert 0 nil)))
(assert (appendo nil (insert 0 nil) (insert 0 nil)))
;(assert (appendo x y z))
;(assert (appendo x y (insert 4 (insert 0 nil))))
(assert (appendo x y (insert 42 nil)))
(check-sat)
(get-model)
```

```z3
(define-sort LInt () (List Int))
(define-fun-rec appendo ((x LInt) (y LInt) (z LInt)) Bool
  (match x (
    (nil (= y z))
    ((insert w ws) 
      (match z (
        (nil false) ; impossible
        ((insert v vs) (and (= v w) (appendo ws y vs)))
      ))
  )))
)

(declare-const x LInt)
(declare-const y LInt)
(declare-const z LInt)
;(assert (appendo x y z))
(assert (appendo x y (insert 42 nil)))
(check-sat) ;sat
(get-model)
;(
;  (define-fun z () (List Int)
;    (insert 2 nil))
;  (define-fun y () (List Int)
;    (insert 2 nil))
;  (define-fun x () (List Int)
;    nil)
;)
```   (insert 2 nil))
;  (define-fun x () (List Int)
;    nil)
;)
```


```z3
;re
(define-sort LInt () (List Int))


;(define-fun-rec appendo ((x LInt) (y LInt) (z LInt)) Bool
;  (or
;    (and (= x nil) (= y z))
;    (exists ((w Int) (ws LInt) (res LInt)) 
;        (and 
;          (distinct x nil)
;          (= x (insert w ws))
;          (= z (insert w res)) 
;          (appendo ws y res)
;        ))
;  )
;)

; This one appears to be working better. Why?
; less existentials?
;(define-fun-rec appendo ((x LInt) (y LInt) (z LInt)) Bool
;  (match x (
;    (nil (= y z))
;   ((insert w ws) 
;      (exists ((res LInt))
;          (and 
;            (= z (insert w res)) 
;            (appendo ws y res)
;        )
;      )
;    )
;  )))


;(define-fun-rec appendo ((x LInt) (y LInt) (z LInt)) Bool
;  (match x (
;    (nil (= y z))
;    ((insert w ws) 
;      (match z (
;        (nil false) ; impossible
;        ((insert v vs) (and (= v w) (appendo ws y vs)))
;      ))
;  )))
;)


(declare-fun appendo (LInt LInt LInt) Bool)
(assert
  (forall ((x LInt) (y LInt) (z LInt))
      (= (appendo x y z)
          (match x (
            (nil (= y z))
            ((insert w ws) 
              (match z (
                (nil false) ; impossible
                ((insert v vs) (and (= v w) (appendo ws y vs)))
              ))
          )))
      )
  )
)

(declare-const x LInt)
(declare-const y LInt)
(declare-const z LInt)
;(assert (appendo (insert 0 nil) y z))
;(assert (appendo nil nil nil))
;(assert (appendo (insert 0 nil) nil (insert 0 nil)))
;(assert (appendo nil (insert 0 nil) (insert 0 nil)))

;(assert (appendo x y (insert 42 nil)))

(assert (appendo x y z))
;(assert (distinct x nil (insert 2 nil)))
;(assert (appendo x y (insert 4 (insert 0 nil))))


(check-sat)
(get-model)
```


```z3

(declare-datatypes () (
  (Proof)

))


```

```z3
; sorts have to have at least one element. Huh.
(declare-sort Void)
(assert (forall ((x Void))
  false
))
(check-sat)
;(get-model)
```

```z3
;re
(declare-datatype Void ())
; invalid datatype declaration, datatype does not have any constructors"
```

## Relations vs Functions
Sometims you may want to work relationally rather than functionally.



## Bounded Quantification
Some ideas
- Inject from bounded domain like BitVec
- (forall x (=> subset P)) use implication to constrain
- Use define-fun-rec to recursively define quantification
- Use define-fun to reccurve define quantification. Can use lambda

### define-fun-rec
Using define-fun-rec as a bounded forall. Make the recursive function that enumarates the range. Probably it is a bad idea to
```z3

(define-fun-rec bforall ((low Int) (high Int) (pred (Array (Array Int Int) Bool)) Bool
  (ite (>= high low)     )
)
```


Hmm. This is actually slower than the quantified form below
```z3
; but really it is hard to habstract this in z3. Specialize bforall for each predictae of interest.
(define-fun-rec bforall ((low Int) (high Int) (pred (Array Int Bool))) Bool
  (ite (>= high low)  (and (select pred low) (bforall (+ low 1) high pred)) true )
)
(declare-const foo (Array Int Bool))
(assert (bforall 0 1000 foo))
(assert (bforall 2000 3000 foo))
(assert-not (select foo 1500))
(check-sat)
(get-model)


```
The models look different too. The first gives a nicer model in some subjective sense.


```z3
; but really it is hard to habstract this in z3. Specialize bforall for each predictae of interest.

(declare-const foo (Array Int Bool))
(assert (forall ((i Int))
  (=> (and (<= 0 i) (<= i 1000)) (select foo i))
))
(assert (forall ((i Int))
  (=> (and (<= 2000 i) (<= i 3000)) (select foo i))
))
(assert-not (select foo 1500))
(check-sat)
(get-model)
```
### Bitvec Quantify
Quantify over bounded domains only. This might play nice with mbqi. Not so much with ematching. This is explicit parametrization of a finite subset of an infinite domain. Which might help. 

```
(forall (x0 (_ BitVec 8))   (let ((x (+ offset (bv2int x0))))   (yadayada x)   )   )
```





## Datalog
### uZ3
```z3
;re

(declare-sort A)

(declare-rel add (A A A))
(declare-var a A)
(declare-var b A)
(declare-var c A)
(declare-const x1 A)
(declare-const x2 A)
(declare-const x3 A)

(rule (=> (add a b c) (add b a c)))
(rule (add x1 x2 x3))

(query add :print-answer true)


```

```z3
;(set-option :fixedpoint.engine datalog)
(define-sort s () (_ BitVec 3))
(declare-rel edge (s s))
(declare-rel path (s s))
(declare-var a s)
(declare-var b s)
(declare-var c s)

(rule (=> (edge a b) (path a b)))
(rule (=> (and (path a b) (path b c)) (path a c)))

(rule (edge #b001 #b010))
(rule (edge #b001 #b011))
(rule (edge #b010 #b100))

(declare-rel q1 ())
(declare-rel q2 ())
(declare-rel q3 (s))
(rule (=> (path #b001 #b100) q1))
(rule (=> (path #b011 #b100) q2))
(rule (=> (path #b001 b) (q3 b)))

(query q1)
(query q2)
(query q3 :print-answer true)
```
### Clark Completion
[clark completion](https://www.inf.ed.ac.uk/teaching/courses/lp/2012/slides/lpTheory8.pdf)
Only things that are forced to be true are true.
Take horn clause  head(x) :- b(x).
Normalize by putting equalities in the body. This means ground facts become. `edge(1,2). ---> edge(X,Y) :- X = 1, Y = 2.`
Now collect up all rules with heads. head == body1 \/ body2 \/ body3 \/

This example may be deceptive.
`p :- p.` is an example rule that in clark completion allows self reinforcing of p. It justifies itself. Not good.
So perhaps one way of thinking about this is you need some kind of termination argument, inductive type, or minimality restriction. 
This particular example got lucky



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
### Transitive Closure
[relational constraint solving in smt](https://homepage.divms.uiowa.edu/~ajreynol/cade17.pdf)
https://cvc5.github.io/docs/cvc5-1.0.0/theories/sets-and-relations.html

special relations. Transitive closure cannot be expressed in first order logic
https://math.stackexchange.com/questions/295298/is-reflexive-transitive-closure-of-relation-r-a-first-order-property

My gut says this is a pretty nuanced statement.

Simple obvious axioms actually express that it is an overapproximation of the theory. For example R(a,b) = True is a valid model of the transtivieity axioms

[Some Remarks on the Definability of Transitive Closure in First-order Logic and Datalog](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.127.8266&rep=rep1&type=pdf)

https://microsoft.github.io/z3guide/docs/theories/Special%20Relations#transitive-closures

expansion operator of database. This is a little nuts
{(a,b), (b,c)} R  (a,b)

explicit

deterministic transitive closure. Transitive closure of a functional relationship is a little bit lesser.
http://cs.technion.ac.il/~shachari/dl/thesis.pdf tricking your way around these restrictions. Kind of using an indirect minimality condition.



### Explicit datalog iteration
```
(define-fun path (Int Vert Vert) Bool)

;(define-fun-rec )
(forall ((iter Int) (x Vert) (y Vert))
  (=> (and (< 0 i) (<= i iterlim))
     (= (path (+ 1 iter) x y)
        (or (path iter x y)
            ; clauses.
        )
     )
)

(forall x y
 (path 0
)


```
We can check if `(assert (!= (path N x y) (path (+ N 1) x y))` for whether we've terminated or not.

### Well founded 

`Option Bool` is also acceptable
```z3
(declare-datatype WF (
  (ProveTrue) (ProveFalse) (Unknown)
))

(define-fun <== ((x WF) (y WF)) Bool
  (match x (
    (KnownTrue)
    (KnownFalse)
    (Unknown)
  )
  
  )
)

(define-fun not_ ((x WF)) Bool

)

```

This doesn't really help. Well founded semantics still has a minimality condition
### Proof Relevant
```z3
;re
(declare-datatype Vert (
  (a)
  (b)
  (c)
))
; datatype is much faster. Interesting.
;(declare-sort Vert)
;(declare-const a Vert)
;(declare-const b Vert)
;(declare-const c Vert)
;(assert (distinct a b c))
(declare-datatype Proof (
  (Edge)
  (Trans (trans-y Vert) (trans-pf Proof))
  )
)
(declare-datatype Option (
  par (T) (
    (None)
    (Some (get-some T))
  )
))



(define-fun edge ((x Vert) (y Vert)) Bool
  (or
    (and (= x a) (= y b))
    (and (= x b) (= y c))
  )
)

(declare-fun path (Vert Vert) (Option Proof))

; forward inference
(assert
  (forall ((x Vert) (y Vert))
    (=> (edge x y) (distinct None (path x y)))
  )
)

(assert
  (forall ((x Vert) (y Vert) (z Vert))
    (=> (and (edge x y) (distinct None (path y z))) (distinct None (path x z)))
  )
)
; backward direction. Every relation that is not None is justified.
(assert
  (forall ((x Vert) (y Vert))
    (=> (= (Some Edge) (path x y)) (edge x y))
  )
)

(assert
  (forall ((x Vert) (y Vert) (z Vert) (pf Proof))
    (=> (= (Some (Trans y pf)) (path x z)) 
        (and (edge x y) (= (Some pf) (path y z))))
  )
)

; alternative formulation. Meh.
;(assert
;  (forall ((x Vert) (y Vert))
;    (match (path x y)
;    (
;      (None true)
;      ((Some Edge) (edge x y))
;      ((Some (Trans z pf)) (and (edge x z) (= (Some pf) (path z y))))
;    )
;)))


(check-sat)
(get-model)
(eval (path a b))
(eval (path a a))
(eval (path a c))
(eval (path c a))
(eval (path b c))
```
In some sense, inductive datatypes are also a minimal fixed point. It seems that by making proof relevant relations, we can inherit this minimality?

One might thing you could remove the arguments to Trans. You can't remove `pf`. That is what is guaranteeing well foundedness of the derivation / acyclicity.


See also "Proof Objects" below.

```z3

;re
(declare-datatype Vert (
  (a)
  (b)
  (c)
))
(declare-datatype Proof (
  (Edge)
  (Trans (trans-y Vert) (level Int))
  )
)

(assert 
  (= (level Edge) 0)
)

(declare-datatype Option (
  par (T) (
    (None)
    (Some (get-some T))
  )
))



(define-fun edge ((x Vert) (y Vert)) Bool
  (or
    (and (= x a) (= y b))
    (and (= x b) (= y c))
  )
)

(declare-fun path (Vert Vert) (Option Proof))


(forall ((x Vert) (y Vert) (g Int))
 (=> (= (Some g) (path x y)) (>= (level g) 0))
)


; forward direction
(assert
  (forall ((x Vert) (y Vert))
    (=> (edge x y) (distinct None (path x y)))
  )
)

(assert
  (forall ((x Vert) (y Vert) (z Vert))
    (=> (and (edge x y) (distinct None (path y z))) (distinct None (path x z)))
  )
)
; backward direction. Every relation that is not None is justified.
(assert
  (forall ((x Vert) (y Vert))
    (=> (= (Some Edge) (path x y)) (edge x y))
  )
)

(assert
  (forall ((x Vert) (y Vert) (z Vert) (n Int) (pf Proof))
    (=> (= (Some (Trans y n)) (path x z)) 
        (and (edge x y) (= (level pf) (- n 1)) (= (Some pf) (path y z))))
  )
)

(check-sat)
(get-model)
(eval (path a b))
(eval (path a a))
(eval (path a c))
(eval (path c a))
(eval (path b c))
```

Proof semantics / Provenance
Do we cast to bool or not?
There is a proof relevant thing that tells you which case of the `or` you're in in the completion semantics.
I need negation because I need == and !=?



```
(declare-datatype Proof
  (Trans (trans1 Int))
  (Base)
  (Unknown)
)
(define and_ ((x Proof) (y Proof))  Bool
    (not (or (is-Uknown x) (is-Uknown y))
)

(assert
  (forall ((x Int) (y Int) (z Int)))
   (=> (= (path x z) (Trans y))
       (and_ (edge x y) (path y z))
   )
)


(assert
  (forall ((x Int) (y Int) (z Int)))
   (=> (= (path x z) (Trans y p q))
       (and (= p (edge x y)) (= q (path y z)))
   )
)

(assert 
(=> (= (path x y) (Base)))
    (not (is-Unknown (edge x y))
)

(assert 
  (=> (edge x y) (path x y)
)

(assert 
  (=> (and_ (edge x y) (path y z))
      (path )
  )
)
)

```

#### First Class Union Find
Hmm. Making an adt for spanning trees is difficult and annoying. Maybe using the notion of 
x -> zipper. Because funion, it has unique spot in tree.

Is this n*2 space though? with sharing it shouldn't be
Using an order to tie break?
a -> Int
explain -> Explain i, reason

binary tree. Ordered.

SpanTree.

root(x) = root(y)
explain(x) = path between root(x) and x. = Trans(y,just_xy, pf)
```z3
;re
(declare-datatype Vert (
  (a) (b) (c) (d)))

(declare-datatype Path (
  (Refl)
  (Trans (y Vert) (trans-pf Path))
))
(declare-fun root (Vert) Vert)
(declare-fun explain (Vert) Path)

(define-fun edge0 ((x Vert) (y Vert)) Bool
  (or 
    ;(and (= x a) (= y b))
    (and (= x c) (= y d))
    (and (= x c) (= y a))
  )
)
(define-fun edge ((x Vert) (y Vert)) Bool
  (or (edge0 x y) (edge0 y x)))

; forward inference
(assert (forall ((x Vert) (y Vert))
      (=> (edge x y) (= (root x) (root y)))
))

; backwards justification
(assert (forall ((x Vert))
  (=> (= (explain x) Refl) (= (root x) x))
))

(assert (forall ((x Vert) (y Vert) (pf Path))
  (=> (= (explain x) (Trans y pf))
      (and (= (root x) (root y)) 
           (= pf (explain y)) ; optional? This is what makes it a spanning tree
           (edge x y)))))

(check-sat)
(get-model)


```


```z3
;re
(declare-datatype SpanTree (
  ((x Vert) ()
)
)

(declare-datatype Zipper
  (Zippper (List ))
)
(define-fun-rec in-tree ((x Int) (t Tree))
  (match t (

  ))
)
(define-fun-rec all-jsutified (t Tree)

)
(declare-fun component (Int) SpanTree)
(assert
  (= (comp a) (comp b))
)
(assert
  (= (comp b) (comp c))
)

(assert
    (forall ((x Vert)) (and (in-tree (comp x)) (all-jusitified (comp x)))
)


(declare-fun parent (Vert) (Option Vert)) ; but acuyclic.
(declare-fun parent (Vert) (Option SpanTree))
(declare-fun root (Vert) SpanTree)
(declare-fun root (Vert) Vert)
(declare-fun explain (Vert))


```


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


(add a b c)
(=

)


(= (baseeq x y) (or (= x y)
                    (and (add a b x) (and a b y))
)

(= (_ transitive baseq)  (a = b)


## Pseudo Boolean





# Parsing
This is not working.
```z3
;re
(declare-datatype Tree (
  (Leaf)
  (Node (left Tree) (right Tree))
  (Nest (nest Tree))
))

(define-fun-rec parse ((x String) (p Tree)) Bool
  (match p (
    ((Leaf) (= x ""))
    ((Nest n)  (exists ((s String)) 
        (and (= x (str.++ "(" s ")")) (parse s n))))
    ((Node l r) 
      (exists ((s1 String) (s2 String))
        (and 
         (= x (str.++ s1 s2))
         (parse s1 l) (parse s2 r)
    )))
    )
))

(declare-const p Tree)
(assert (parse "(())" p))
;(assert (= "(())" (str.++ "(" "" ")" )))
(check-sat)
(get-model)

```


# Finite Models
There is a sense in which getting a model returend is much more powerful and satisfying than merely getting `unsat`.
When you start using quantifiers, it feels as though 
Z3 can output finite models.

Don't ask Z3 questions it can't have finite answers for. Asking for functions symbols for complex infinite functions is destined for pain. Ask for underapproximation, or use define-fun, define-fun-rec where it doesn't have to figure out the function.

Not all axioms have finite models.
Is there a pile of tricks or systematic thing I can do to a set of axioms such that they have or may have a finite model and this model has some useful relationship to the infinite model.

one suggestion. Try to use relational definitions, not functional definitions. total functions tend to lead to infinite models.

Finite model finding. Finitizing a set of axioms in such a way that the resulting model has a useful relationship to the actual infinite model. Just truncating isn't very satisfactory. 

I guess I could stratify sorts? A lot of duplication. I can't make equalities across strata.
I don't have counters in z3. Possibly we do have gas. things with different gas aren't equal though. hmm.

depth metric? But that isn't stable across eclass.

explicit eid labelling for fresh const.



## EPR
[a (kinda long) thread on the decidability of EPR (a fragment of first-order logic) - James Wilcox](https://twitter.com/wilcoxjay/status/1367698694988992513?s=20&t=kFDTTfb0qkcnSqysfiGJ4A)
EPR is pretty powerful. axioms for transitivity, reflexivity, and antisymmetry are all expressible, as are simple uniqueness and cardinality constraints. so for example, you can go to town on reasoning about trees, graphs, or database-y things (primary key constraints, etc.). 
see http://cs.technion.ac.il/~shachari/dl/thesis.pdf for an application to imperative linked list manipulation!
[Complete instantiation for quantified formulas in Satisfiability Modulo Theories](http://leodemoura.github.io/files/ci.pdf)

"Bernays Schonfinkel"
A decidable fragment of first order logic.
It relies on there being no function symbols, it's similar to datalog in this sense.
Also the only quantifiers allowed are exists, forall.
Quantifier alternation also leads to a form of function symbols thanks for skolemization.
There are more sophisticated variants which can have function symbols satisfying certain straitifcation conditions.


The finite model property.

<http://microsoft.github.io/ivy/decidability.html>
<https://github.com/wilcoxjay/mypyvy>
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



# Query Containment
https://www.logic.at/emclworkshop12/slides/student_talks/Sergey/presentation.pdf
https://ieeexplore.ieee.org/document/9161435
[Conjunctive-Query Containment and Constraint Satisfaction](https://www.cs.rice.edu/~vardi/papers/pods98rj.pdf)

Explicit modelling of homomorphism
```
(declare-fun h (domA) domB)
(declare-fun A (domA) Bool)
(define-fun B (domB) Bool)

; A --> B
(assert 
  (forall ((x domA))
    (=>
      (A x)
      (B (h x))
    )
  )
)

; initialize database
(assert (A biz))

; B is model
(forall ((y domB))
  (=>  
     (body)
     (head)
     )
)

; universality
; ???
(forall ((C (Array domB Bool)))
      ; if C is model
      ; exists homomorhism from domC to B
)

```

Any function defines equivalence classes based on it's preimages.

```z3
(declare-fun uf (Int) Int)
;(assert (= (uf 1) (uf 2)))

(declare-sort A)


(assert (forall ((x Int) (y Int)) 
  (= 
    (= (uf x) (uf y))
    (or (= x y) (and (= x 1) (= y 2)) (and (= x 2) (= y 1)))
  )
))

(check-sat)
(get-model)

```


```z3
(declare-sort A)
(declare-fun uf (A) Int)

(declare-const a A)
(declare-const b A)
(declare-const c A)
(assert (distinct a b c))

(assert (forall ((x A) (y A)) 
  (= 
    (= (uf x) (uf y))
    (or (= x y) 
        (and (= x a) (= y b)) 
        ;(and (= x b) (= y a))
        ;(and (= x a) (= y c))
        ;(and (= x c) (= y a))
        (exists ((z A)) (and (distinct x y z)) (= (uf x) (uf z)) (= (uf y) (uf z)))) ; (not (= y z))
        )
  )
))

(check-sat)
(get-model)
(eval (uf a))
(eval (uf b))
(eval (uf c))

```

Yeah, this is nonsensical. There aren't enough hooks to control what is equal and isn't. Externally, we could try to search


# Program Verification
Small scale and large scale choices:

- Predicate transformers
- Transition relation between state
  + Use a transition function vs transition relation

Modelling the state
- explicit store Array
- 
Dealing with the frame problem

- Bounded checking vs complete
- Infer invariants or provide them
- Termination. It kind of matters
- Structure vs unstructured control flow
- Use Constrained horn clauses for control flow
- 




[jitterbug](https://unsat.cs.washington.edu/projects/jitterbug/)
[serval](https://unsat.cs.washington.edu/projects/serval/)

## Nand2Tetris Cpu
https://www.philipzucker.com/nand2tetris-chc/

```z3
;re
(define-sort BV16 () (_ BitVec 16))
(define-sort Addr () (_ BitVec 10))
(define-sort -> (A B) (Array A B))
(declare-datatype State (
  (
    (mem (Array Addr BV16))
    (areg BV16)
    (dreg BV16)
    (pc BV16)
  )
))

;(define-const ROM (Array BV16 Insn))

(define-fun incpc ((s State)) State
  ((_ update-field pc) s (bvadd (pc s) (_ bv1 16)))
)


(define-fun ainsn ((a BV16)) (-> State State) ; actualy zero extend bv15
  (lambda ((s State))
    (incpc ((_ update_field areg) s a))
  )
)



(define-fun seq ((f (-> State State))))




```

## Arm
## Forth
## WASM

```z3

```

## Weakest Precondition
- [Weakest Precondition with Z3py](https://www.philipzucker.com/weakest-precondition-z3py/)


### Initial Style
Deep embedding of weakest precondition
```z3

(define-sort Var () String)
(define-sort Store () (Array Var Int))
(declare-datatypes ()
  (

    (BinOp
      ADD
      SUB
      MUL
    )

    ;(Var X Y Z)

    (Expr
      (EVar (evar String))
      (EBin (op BinOp) (o1 Expr) (o2 Expr))
    )

    (Stmt
      Skip
      (Seq (fst Stmt) (snd Stmt))
      (Move (var Var) (e Expr))
    )
))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)


;(define-fun eval-var ((v Var)) Int
;  (match v (
;    (X x)
;    (Y y)
;    (Z z)
;  ))
;)

(define-fun-rec eval-expr ((e Expr) (rho Store)) Int
  (match e (
    ((EVar v) (select rho v))
    ((EBin op x y)
      (let
        ((x (eval-expr x rho)) (y (eval-expr y rho)))
        (match op (
          (ADD (+ x y))
          (SUB (- x y))
          (MUL (* x y))
        ))
      )
    )
  ))
)


;(define-fun-rec)
; Formula
```

```z3
;re
(define-sort Var () String)
(define-sort Env () (Array Var Int))
(declare-datatypes ()(
  (Term
    (Var (var1 Var))
    (Lit (lit1 Int))
    (Add (add1 Term) (add2 Term))
    (Sub (sub1 Term) (sub2 Term))
    ; And so on
  )
  (Formula
    (And (and1 Formula) (and2 Formula))
    (Or (or1 Formula) (or2 Formula))
    (Impl (impl1 Formula) (impl2 Formula))
    (Eq (eq1 Term) (eq2 Term))
    (Lte (lte1 Term) (lte2 Term))
    (Not (not1 Formula))
    (Let (let1 String) (let2 Term) (let3 Formula))
    (IteF (ite1 Formula) (ite2 Formula) (ite3 Formula))
   ; (Forall (forall1 Formula))
  )
  (Stmt 
    (Skip)
    (Set (set1 Var) (set2 Term))
    (Seq (seq1 Stmt) (seq2 Stmt))
    (IteS (ite-cond Formula) (ite-then Stmt) (ite-else Stmt))
   ; (While (while-cond Formula) (while-inv Formula) (while-body Stmt))
  )
)
)

(define-fun-rec eval-term ((t Term) (rho Env)) Int
  (match t (
    ((Lit i) i)
    ((Var v) (select rho v))
    ((Add x y) (+ (eval-term x rho) (eval-term y rho)))
    ((Sub x y) (- (eval-term x rho) (eval-term y rho)))
  )
  )
)

(define-fun-rec eval-form ((f Formula) (rho Env)) Bool
  (match f (
    ((Eq x y) (= (eval-term x rho) (eval-term y rho)))
    ((Lte x y) (<= (eval-term x rho) (eval-term y rho))) 
    ((And x y) (and (eval-form x rho) (eval-form y rho)))
    ((Or x y) (or (eval-form x rho) (eval-form y rho)))
    ((Impl x y) (=> (eval-form x rho) (eval-form y rho)))
    ((Not x) (not (eval-form x rho)))
    ;(Forall v f) (forall ((x Int)) (eval-form f (store rho v x)))
    ;(Exists v f) (exists ((x Int)) (eval-form f (store rho v x)))
    ;((Forall b)  (forall ((rho Env)) (eval-form b rho)))
    ((Let v t f)  (eval-form f (store rho v (eval-term t rho))))
    ((IteF c t e) (ite (eval-form c rho) (eval-form t rho) (eval-form e rho) ))
  )
  )
)

;(declare-const rho Env)
(define-const myform Formula
  (And (Not (Eq (Var "x") (Var "y"))) (Eq (Var "x") (Lit 42)))
)

;(assert (eval-form myform rho))
;(check-sat)
;(get-model)

; Term is a first order representation of Env -> Int
; Formula is a first order representation of Env -> Bool.
(define-fun-rec eval-wp ((prog Stmt) (post Formula)) Formula
  (match prog (
    (Skip post)
    ((Seq s1 s2) (eval-wp s1 (eval-wp s2 post)))
    ((Set v e) (Let v e post))
    ((IteS c t e) (IteF c (eval-wp t post) (eval-wp e post)))
   ; ((While cond inv body) (And inv (Forall (Impl inv (IteF cond (eval-wp body inv) post)))))
  )
  )
)



(define-const myprog Stmt
  (Seq (Set "x" (Lit 7))
       (IteS (Lte (Var "z") (Lit 0))
            (Set "y" (Var "x"))
            (Set "y" (Lit 1))
  )
))

;(assert (eval-form myform rho))
(check-sat)
(get-model)
(declare-const rho Env)
(eval (eval-form (eval-wp myprog (Eq (Var "y") (Var "z"))) rho))

; helpers
(define-fun begin2 ((s0 Stmt) (s1 Stmt)) Stmt
  (Seq s0 s1)
)
(define-fun begin3 ((s0 Stmt) (s1 Stmt) (s2 Stmt)) Stmt
  (Seq s0 (begin2 s1 s2))
)
(define-fun begin4 ((s0 Stmt) (s1 Stmt) (s2 Stmt) (s3 Stmt)) Stmt
  (Seq s0 (begin3 s1 s2 s3))
)

```

There is nothng stopping me from doing ForAll I think. The clobbering exactly matches the clobbering of the forall anyway.

```
;re
(Forall v f) (forall ((x Int)) (eval-form f (store rho v x)))
(Exists v f) (exists ((x Int)) (eval-form f (store rho v x)))
(Let v t f)  (eval-form f (store rho v (eval-term t rho)))

```


Fresh variables. Use skolem function  and counter. I guess this is a fresh var counter?
(f Int)
(+ counter 1) 

IntTerm
BoolTerm


### Final Style
```z3
;re
(define-sort Var () String)
(define-sort Env () (Array Var Int))
(define-sort Term () (Array Env Int))
(define-sort Formula () (Array Env Bool))
(define-sort Stmt () (Array Formula Formula))

(define-fun var ((x String)) Term (lambda ((rho Env)) (select rho x)))
(define-fun lit ((x Int)) Term (lambda ((rho Env)) x))
(define-fun add ((x Term) (y Term)) Term (lambda ((rho Env))  (+ (x rho) (y rho))))
(define-fun sub ((x Term) (y Term)) Term (lambda ((rho Env))  (- (x rho) (y rho))))

(define-fun eq ((x Term) (y Term)) Formula (lambda ((rho Env)) (= (x rho) (y rho))))
(define-fun lte ((x Term) (y Term)) Formula (lambda ((rho Env)) (<= (x rho) (y rho))))

(define-const skip Stmt (lambda ((post Formula)) post))
(define-fun seq ((s1 Stmt) (s2 Stmt)) Stmt (lambda ((post Formula))  (s1 (s2 post))))
(define-fun set ((x Var) (e Term)) Stmt (lambda ((post Formula)) (lambda ((rho Env)) 
  (select post (store rho x (select e rho))))))
(define-fun ite_s ((c Formula) (then Stmt) (else Stmt)) Stmt
  (lambda ((post Formula)) 
  (lambda ((rho Env))
      (ite (c rho)
            (select (then post) rho)
            (select (else post) rho)
      ))))
(define-fun while ((c Formula) (inv Formula) (body Stmt)) Stmt
  (lambda ((post Formula)) 
  (lambda ((rho Env))
       (and (inv rho)
        (forall ((rho Env))
          (=> (inv rho)
              (ite (c rho)
                  (select (body inv) rho)
                  (post rho))
))))))

(define-const empty-env Env ((as const Env) 0))
(declare-const x Int)
(declare-const y Int)
(declare-const rho Env)
(simplify 
  (let (
    (rho (store (store empty-env "y" y) "x" x)) ; cleans up the output a little.
    (post (eq (var "x") (lit 42))))
    (select (select
      (seq 
        (set "x" (add (var "y") (lit 1)))
        (set "x" (add (var "x") (lit 1))))
      post)
      rho)
))

(assert-not 
  (let (
    ;(rho (store (store empty-env "y" y) "x" x)) ; cleans up the output a little.
    (post (eq (var "x") (lit 11))))
    (select (select
        (seq 
          (set "x" (lit 0))
          (while (lte (var "x") (lit 10))
                (lte (var "x") (lit 11))
                (set "x" (add (var "x") (lit 1)))))
      post) rho)))
(check-sat)


;(define-sort idsort () (par (A) A))



```
Huh. I can't make polymorphic functions, but I can make polymorphic array types. Uh. But I can't instantiate them.
Can use explicit boxed polymorphism. Runtime.

```z3
(declare-datatype Value
  ((Int (int Int)))
  ((Bool (bool Bool)))
  ((Real (real Real)))

)


```



```
;re
; abstract type?
(declare-sort Proof)

; but how can we stop it from inventing proofs?
(declare-fun formula (Proof) Formula)
(define-fun modus-ponens ((p1 Proof) (p2 Proof)) Proof
  (match (formula p1) (

  )
  
  )

)


(declare-datatypes () (
(Proof
  (Modus (p Proof) (p Proof))

)

))

; This is the minikanren function.
(define-fun-rec check ((p Proof) (f Sequent))


)


```

alpha-kanren. nominal sets ~ finite sets. Hmm.


Can I do this shallowly? It's hard because of variable bindings.
It's also hard because we we can't do much higher order stuff.
Reuse z3 formula as formula
```z3

;(define-fun when ((cond Bool) ()  (post Bool)))
(define-fun while ((cond Bool) (inv Bool) (body Bool) (post Bool))
  (and (=> inv body)
)


```


# Proofs
How do you get proofs out of smt solvers?
It's tough.

cvc5 supports a proof production
- [proof production](https://cvc5.github.io/docs/cvc5-1.0.2/proofs/proofs.html)
- alethe, lfsc, dot

```cvc5
(set-logic ALL)
(set-option :produce-proofs true)
(declare-const x Int)
(assert (= x 1))
(assert (= x 2))
(check-sat)
(get-proof)
```

So does Z3. They are hard to interpret
- [State of Proof Checking](https://github.com/Z3Prover/z3/discussions/5981)
- [On proof generation and proof checking ](https://github.com/Z3Prover/z3/discussions/4881)
- [state of proofs slides](https://z3prover.github.io/slides/proofs.html)

## Proof Objects
A la coq inductive datatypes. Searching for a proof object.

```z3
;re
(declare-datatype Edge ((Edge (edge1 Int) (edge2 Int))))

(define-fun wf-edge ((e Edge)) Bool
  (match e ((
    (Edge i j)     
     (or
      (and (= i 1) (= j 2))
      (and (= i 2) (= j 3))
    )
  ))
))  

(declare-datatype Path (
  (BaseEdge (baseedge1 Edge))
  (Trans (trans1 Edge) (trans2 Path))
))

(define-fun-rec wf-path ((p Path) (i Int) (j Int)) Bool
  (match p (
    ((BaseEdge e) (and (= (edge1 e) i)
                       (= (edge2 e) j)
                          (wf-edge e)))
    ((Trans e p)
                  (and (wf-edge e) 
                        (= (edge1 e) i)
                        (wf-path p (edge2 e) j))
    ))
))
                    
(declare-const p Path)
(assert (wf-path p 1 3))
(check-sat)
(get-model)

```


## Interactive Proof
[Automating Theorem Proving with SMT - leino](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml234.pdf)
### A Manual Proof Discipline
Separation between module signature and proofs. Seperate files.
Proof datatype to separate from bool definitions

```z3
;re
(declare-datatypes () (
  (Proof (Proof (getformula Bool)))
))
(define-fun proved ((p Proof)) Bool 
  (match p (
    ((Proof p) (not p))
  ))
)
(define-fun instan-lemma1 ((x Int)) Bool  (or (> x 0) (< x 0) (= x 0)))
(define-const lemma1 Proof (Proof (forall ((x Int)) (instan-lemma1 x))))

(push)
;------------
(assert (proved lemma1))
(check-sat)
(pop)

```

Other possibility for Proof type
Forall (Expr)
Exists (Expr)
Eh. I don't really want to reflect everything.

A shallower HOAS embedding
```z3
;re
(declare-datatype Formula (
  (Bool (bool1 Bool))
  (Forall (forall1 (Array Int Formula)))
  (Exists (exists1 (Array Int Formula)))
))


```

```z3
;re
(declare-datatype Exists 
  (
    (Pair (x Int) (pred (Array Int Bool)))
  ))

```


Universals can be proven by having
(define-const x)
```
; other hypothesis do not mention x
;-----------------
(instan-lemma1 x)
```
or by
; other hypothesis can't possibly mention x
;-----------
(assert (proved lemma1))

Universal can be used by using lemma1 or by instan-lemma1 on anything

Existentials can be proved
```
----------
(exists x (relx x))
```
or by
```
whatever
---------
(relx 3)

```

They can be used via
```
define-const x
(relx x)
; no other use of x
;----------------
conclusion may refer to x

```


ExistsE (ExistsE Bool)
ForallE (ForallE (forallE Bool)) ; (apply?)
Forall (ForallI (forallE Bool)) 


(Exists Int Bool) ; can I pack the witness?

define-const lemma Forall (forall x (forallE (instan-lemma x)))
define-fun instan-lemma ((x Int)) ForallE



The method is related to lambda lifting.
We need to give names to different free parameter things.





```z3
;re
(declare-fun even-fun (Int) Int)
(define-fun even ((x Int)) Bool (= (* 2 (even-fun x)) x))

(declare-fun odd-fun (Int) Int)
(define-fun odd ((x Int)) Bool (= (+ 1 (* 2 (odd-fun x))) x))

;(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-const even-axiom Bool (forall ((x Int)) (=> (exists ((y Int)) (= (* 2 y) x)) (= (* 2 (even-fun x)) x))))
;(define-fun even ((x Int)) Bool (exists ((y Int)) (and (= y (even-fun x)) (= (* 2 y) x))))
(define-fun not-even ((x Int)) Bool (forall ((y Int)) (distinct x (* 2 y))))
;(define-fun instan-not-even ((x Int) (y Int)) (distinct x (2 * y)))

(declare-const m Int)
(declare-const n Int)
(assert (odd m))
(assert (odd n))
(assert (not (even m)))
(assert (not (even n)))
;(assert (instan-not-even m (even-fun )))
(assert-not (even (+ n m)))
;(assert (not-even (+ n m)))
(check-sat)
(get-model)

```

```z3
;re
(define-fun even ((x Int) (y Int)) Bool (= (* 2 y) x))
(define-fun odd ((x Int) (y Int)) Bool (= (+ 1 (* 2 y)) x))


(declare-const m Int)
(declare-const n Int)
(declare-const mo Int)
(declare-const no Int)
(assert (odd m mo))
(assert (odd n no))
(assert-not (exists ((x Int)) (even (+ m n) x)))
(check-sat)

```
```z3
;re
(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun odd ((x Int)) Bool (exists ((y Int)) (= (+ 1 (* 2 y)) x)))

(declare-const m Int)
(declare-const n Int)
(assert (odd m))
(assert (odd n))
;--------------------------
(assert-not (even (+ m n)))
(check-sat)
```

```z3

```z3
;re
(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun div4 ((x Int)) Bool (exists ((y Int)) (= (* 4 y) x)))

(declare-const m Int)
(assert (not (even m)))
;---------------------------
(assert-not (not (div4 m)))
(check-sat)
```

Positively asserting existence isn't so bad. It is just asserting on a fresh variable.

Only allow mention variable once on existential elim in hyps

I'm a little worried about circulaity if I pack everything into one proof thing.

existential lemma can be used in hyps.
Instantiated version in a conc (give explicitly). Or just let it crank.
```
(declare-const e) appears only once in hyp for existential elim

(assert-not
  (=> (and (existse e) (instan-lemma1 ))
      (and lemma1 )
  )

)

```

```z3
;re
(define-fun instan-theorem ((m Int) (n Int)) Bool (not (= (* m m) (* 2 (* n n)))))
(define-const theorem Bool (forall ((m Int) (n Int)) (not (= (* m m) (* 2 (* n n))))))

(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun odd ((x Int)) Bool (exists ((y Int)) (= (+ 1 (* 2 y)) x)))

(define-fun instan-even-odd ((x Int)) Bool (not (= (even x) (odd x))))
(define-const even-odd Bool (forall ((x Int)) (instan-even-odd x)))
(push)
(assert-not even-odd)
(check-sat)
(pop)



(push)
(declare-const m Int)
(declare-const n Int)
(assert (instan-even-odd m))
(assert (instan-even-odd n))
;---------------------
(assert-not (instan-theorem m n))
;(check-sat)
(pop)

(push)
(declare-const m Int)
(declare-const n Int)
(assert (or (odd m) (odd n)))
(assert (not (and (even m) (even n))))
(assert (even (* m m)))
;---------------------
(assert-not (instan-theorem m n))
(check-sat)
(pop)


```


```z3
;re
(define-fun even-evidence ((x Int) (ev Int)) Bool  (= (* 2 ev) x))
(define-fun odd-evidence ((x Int) (ev Int)) Bool (= (+ 1 (* 2 ev)) x))
(define-fun even ((x Int)) Bool (exists ((y Int)) (= (* 2 y) x)))
(define-fun odd ((x Int)) Bool (exists ((y Int)) (= (+ 1 (* 2 y)) x)))

(define-fun instan-even-odd ((x Int)) Bool (not (= (even x) (odd x))))
(define-const even-odd Bool (forall ((x Int)) (instan-even-odd x)))

(push)
(declare-const x Int)
(assert (even x))
;----------------
(assert-not (not (odd x)))
(check-sat)
(pop)

(push)
(declare-const x Int)
(assert (odd x))
;----------------
(assert-not (not (even x)))
(check-sat)
(pop)

(push)
(declare-const x Int)
(assert (not (even x))) ; these are exists in negative position ~ forall.
;----------------
(assert-not (odd x))
(check-sat)
(pop)

(push)
(declare-const x Int)
;----------------
(assert-not (or (even x) (odd x)))
;(check-sat)
(pop)

(push)
(declare-const x Int)
(assert (=> (even x) (not (odd x))))
(assert (=> (odd x)  (not (even x))))
;(assert (or (even x) (odd x)))
(assert (=> (not (even x)) (odd x)))
(assert (=> (not (odd x))  (even x)))
;----------------
(assert-not (instan-even-odd x))
(check-sat)
(pop)


(push)
(declare-const x Int)
(declare-fun odd1 (Int) Bool)
(declare-fun even1 (Int) Bool)
(assert (=> (even1 x) (not (odd1 x))))
(assert (=> (odd1 x)  (not (even1 x))))
(assert (=> (not (even1 x)) (odd1 x)))
(assert (=> (not (odd1 x))  (even1 x)))
;(assert (or (even1 x) (odd1 x)))
;----------------
(assert-not (not (= (even1 x) (odd1 x))))
(check-sat)
;(get-model)
(pop)



(define-fun induction ((p (Array Int Bool))) Bool
  (and (select p 0) 
       (forall ((n Int)) (=> (select p n) (select p (+ n 1))))
))

```


### Python Hilbert Proof
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

### Python Backwards Proof
<https://www.philipzucker.com/programming-and-interactive-proving-with-z3py>
At the end of this blog post I had kind of a neat system mimicking how coq feels.
Keep a goal stack. Allow usage of Z3 tactics.
I was trying to enforce every step as being sound by requiring Z3 to confirm what I though I was doing.
I don't think systems tend to make the backwards proof process part of their core. They use a tactic system which calls forward.
Probably sunk for the same reasons that Z3 just will not accept certain quanitifier proofs.

### Python Forward Proof
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

## Hoare LCF
A [hoare triple](https://en.wikipedia.org/wiki/Hoare_logic) is a judgement.$\{P\}C\{Q\}$ lives at the same level as $\Gamma \turnstile e : T$
We can literally construct the proof tree as a data structure, or we can go lcf style whrere we have trusted functions.

It would be fun (or confusing?) to use the python AST as our imperative program. Certainly I'm not going to actually.

It might be fun to do this in javascript to make a webdemo that outputs a bussproof.

```python

class Triple():
  def triple(self):
    pass
  def check(self):
    pass

class SkipAx():
  prop:Bool
  def triple(self):
    return P, "skip", P

class AssAx():
  x:str
  e:expr
  P:Bool

  def triple(self):
     return substitute(P, x, E), x == e, P


class ComposeAx():
  trip1:Triple
  trip2:Triple
  def triple(self):
    P,S,Q = self.trip1.triple()
    Q1,T,R = self.trip2.triple()
    assert Q1 == Q
    return P, (S,T), R

class CosnsAx():
  P1:Bool
  Q1:Bool
  trip:Triple
  def triple(self):
    P2,S,Q2 = self.trip.triple()
    prove(Impl(P1,P2))
    prove(Impl(Q2,Q1))
    return P1,S,Q1



```

Weakest precondition could be used to generate a particular hoare tree I think








# Z3 

mindiff on arrays?

https://github.com/Z3Prover/z3test tests repo

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


https://github.com/Z3Prover/z3/blob/master/src/smt/mam.h ematching machine


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
# Resources
[datalog based systems can us incremental smt solving ](https://cs.pomona.edu/~michael/papers/iclp2020_extabs.pdf) Nice trick to use (=> label clause). This trick also comes up in unsat cores. (check-sat-assuming label label) then. ALso consider doing minimal number of push pops or keep pool of solver contexts to find miniaml push pop

[Fuzzy-sat](https://arxiv.org/pdf/2102.06580.pdf) running smt queries through a fuzzer

natural domain smt

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


# Resources

https://ojs.aaai.org/index.php/AAAI/article/view/9755 sat modulo monotonic theories

https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-smt/index.html

https://github.com/awslabs/rust-smt-ir hmm. This is an smt preprocessor

http://reports-archive.adm.cs.cmu.edu/anon/2003/CMU-CS-03-210.pdf UCLID. Eager encoding to SAT