---
layout: post
title: Computer Numbers
---
- [Numbers](#numbers)
- [Finite Precision](#finite-precision)
- [Multiprecision Integers](#multiprecision-integers)
- [Rationals](#rationals)
- [Algebraic Numbers](#algebraic-numbers)
- [Intervals](#intervals)
- [Floats](#floats)
  - [Multiprecision FLoats](#multiprecision-floats)
  - [Core identities](#core-identities)
  - [Fused multiply add](#fused-multiply-add)
  - [Range reduction](#range-reduction)
  - [2Sum and Fast2Sum](#2sum-and-fast2sum)
  - [Veltkamp splitting](#veltkamp-splitting)
  - [Dekker Multiplication](#dekker-multiplication)
  - [Newton Raphson](#newton-raphson)
  - [Multiplication by arbitrary precision number like pi](#multiplication-by-arbitrary-precision-number-like-pi)
  - [Error Models](#error-models)
  - [Sterbenz lemma](#sterbenz-lemma)
  - [Gappa](#gappa)
  - [FPBench](#fpbench)
  - [Brute Force Verification](#brute-force-verification)
- [Constructive / Exact Reals](#constructive--exact-reals)
- [Misc](#misc)


# Numbers
There are multiple ways of representing numbers in computers. There are different axes upon which to limit a pure mathemtical notion of number. You can finitize in magnitude and approximate.

Computers can represent 0/1 as a bit.

A small-ish set of numbers and operations on them can be represented by lookup table. 0b001101 is 893204.34234 when you look it up in the table.

You can decide to fix different aspects. You can limit choices of sizes

Fixed point is gotten when the denominator is fixed at compile time. You can't perform arithemtic exactly anymore

Intervals represent a number by giving an under and over approximation of the number

Floating point numbers are mostly gotten by fixing the denominator to be a power of 2.

# Finite Precision
Finite integers are representable as primitives (64-bit / 32-bit) / as lists of 0/1

# Multiprecision Integers
Lists or arrays of integers can be used to make arbitrary sized integers

gmp
limbs

# Rationals
Two integers (a tuple or struct) describes fractions. You can do `+-*/` exactly for fractions. That can be very powerful, since you can then analyze more complicated operations


# Algebraic Numbers
You can represent an exact number by stating an exact polynomial it is the solution of.

# Intervals

# Floats
https://github.com/VeriNum/vcfloat

[sam pollard fpbench talk](https://sampollard.github.io/research/artifacts/pollard_fpbench23_presentation.pdf)

[Odyssey: An Interactive Workbench for Expert-Driven Floating-Point Expression Rewriting](https://arxiv.org/pdf/2305.10599.pdf)
## Multiprecision FLoats
mpfr
## Core identities

Normal floating points are of the form

`x = m * 2 ^ e`
`m` and `e` are bounded in size above and below.
1 < m < 2 in regular float
`x = M * 2 ^ {e - p + 1}

2^{e} <= x < 2^{e+1}


Every operation that floating point does has an implicit `rnd` operation.
`x .+ y` is really `rnd(x + y)`

`rnd` picks the closest representable value. This leads to the fact that
`|rnd(x) - x| < 2^e`

I'm being a little fuzzy here.

32 bit float
1.bbbbbb
precision = 24 bits

Theorem 2.2
`err(x) < 2 ^ {1 - p} = 2 ^ - 23`
`| x - rnd(x)| <= 2 ^ {e - p + 1}`

e = 0 if 1 <= x < 2 
e = 2 if 2 <= x < 4

```z3
;re

; https://en.wikipedia.org/wiki/Machine_epsilon
(define-const eps32 Real (^ 2 -23))



; given eps > 0, abs-bound encodes |x| <= eps as conjunction of linear constraints
(define-fun abs-bound ((x Real) (eps Real)) Bool
    (and
        (<= x eps)
        (<= (- eps) x )
))

(declare-fun rnd-fun (Real) Real)

; Describing operations relationally is nice because you can instantiate properties at use site.
; We describe an overapproximation of the rounding operation
(define-fun rnd ((x Real) (res Real)) Bool
        (and (= res (rnd-fun x)) ; it is a functional relationship
            (abs-bound (- x res) (* eps32 (abs x))) ; with |x - rnd(x)| <= eps32 * |x|
        )
)

; floating point add is Real add then round.
(define-fun fp-add ((x Real) (y Real) (res Real)) Bool
    (rnd (+ x y) res)
)

(define-fun fp-mul ((x Real) (y Real) (res Real)) Bool
    (rnd (* x y) res)
)

; box is useful shorthand for stating initial conditions
(define-fun box ((x Real) (lower Real) (upper Real)) Bool
    (and (<= lower x)
         (<= x upper)
    )
)

(declare-const x Real)
(assert (box x 1 2))
(declare-const y Real)
(assert (box y 1 2))
(declare-const y Real)
(assert (box z 1 2))

(declare-const xy Real)
(assert (fp-add x y xy))
(declare-const xyy Real)
(assert (fp-add xy y xyy))

(declare-const xyz Real)
(assert (fp-mul xy z xyz))
(check-sat)
(get-model)
(eval (abs -1))

(push)
(assert-not (<= (- xyy (+ x y y)) 0.0001))
(check-sat)
(pop)

(push)
(assert-not (>= (- xyy (+ x y y)) -0.00001))
(check-sat)
(pop)

(push)
(assert-not (>= (- xyy (+ x y y)) -0.001))
(check-sat)
(pop)

;(get-model)
;(eval (- xyy (+ x y y)))


(define-fun myprog ((x Real) (y Real) (res Real)) Bool
    (exists ; define local variables
        ((xy Real) (fp73 Real))
     (and ; res := 7/3 * (x + y)
        (fp-add x y  xy)
        (rnd (/ 7 3) fp73)
        (fp-mul fp73 xy res)
     )

    )
)

(define-fun myprog-pre ((x Real) (y Real)) Bool

)

(define-fun myprog-post ((x Real) (y Real) (res Real))
    
)

(assert-not (forall ((x Real) (y Real) (res Real))
            (=> (myprog-pre x y)
                (and (myprog x y res) (myprog-post x y res))
            )
))
```


```
;re

(define-fun is-normal ((x Real)) Bool
    (or (and
            (< x (^ 2 300))
            (< (^ 2 -300) x)
         )
        (and
            (< (- x) (^ 2 300))
            (< (^ 2 -300) (- x))
        )
    )
)

(define-fun ulp ((x Real)) Real
   
)

(declare-fun rnd (Real) Real)

(assert (forall ((x Real)) 
    (=> (is-normal x)
         yada
    ) 

    (and (< (- (rnd x) x) (ulp x))
            (< (- (ulp x)) (- (rnd x) x) (ulp x))
))


(assert (forall ((x Real))
    (=>
        (and (< 1 x)
             (< x 2))
        (=  ulp(x))
    )
)


(define-fun-rec ulp ((x Real)) Real
    (ite (and (< x 1) (< x 2)))
         1
    (ite (x < 1)
        (/ (ulp (* x 2) 2)
    (ite (x > 2)
        (* 2 (ulp (/ x 2))
    )
)

;(define-fun fp-mul ((x Real) (y Real))
;    (rnd (* x y)))


; better as a relation?
; relations allow us to bundle in the lemmas we want
; without resorting to forall

; recipe: take a forall axiom, turn it into a define-fun
; This is kind of taking a forall and making it an axiom schema.
; You can still add the forall using (assert (forall ((x )) (my-pred x))
; but it gives the ability to explicitly instantiate

(define-fun rnd-ulp ((x Real)) Bool
    (and (< (- (rnd x) x) (ulp x))
        (< (- (ulp x)) (- (rnd x) x) (ulp x))
)




(define-fun rnd ((x Real) (res Real))
    (and 
        (= res (rnd-fun x))
        (rnd-ulp x)
    )
)


; that these are functions is almost a side feature
; Sometimes the functional nature is useful to the proof.
; probably not that often though

(define-fun ulp ((x Real) (y Real))
    (and
        (= y (ulp-fun x)))
)

(define-fun ulp-def ((x Real)) Bool

)

(define-fun fp-mul ((x Real) (y Real) (z Real))
    (let ((z1 (* x y)))
    (and 
        (= z z1)
        (rnd-ulp z1)
        (ulp-rel z1)

    )

(define-fun fp-sub ((x Real) (y Real) (res Real)) 
    (and
        ...
        (sterbenz x y)
    )

)

```

```z3
(define-sort Var () String)
(define-sort Env () (Array Var Int))
(declare-datatypes ()(
  (Term
    (Var (var1 Var))
    (Lit (lit1 Real))
    (Add (add1 Term) (add2 Term))
    (Mul (add1 Term) (add2 Term))
    (Sub (sub1 Term) (sub2 Term))
    ; And so on
  )
))

(define-fun-rec interp ((e Expr) (rho Env)) Bool
    (match e (
        ((Lit x) x)
        ((Var x) (select rho x))
        ((Add x y) (+ (interp x rho) (interp y rho))

    )
    
    )

)

; outer exists (exists ((rho Env))) is the same as (exists a b c d)
; So we don't get blocked going under an exists.

```



```python
from z3 import *
rnd = Function("rnd", RealSort(), RealSort)
class MyFloat():
    def __init__(self):
        self.x = rnd(FreshReal())
    def __add__(self,rhs):
        return rnd(self.x * rhs.x)

```

```souffle

.type interval = [l : float, u : float]
.decl meet(x : interval , y : interval, z : interval) inline
meet([lx,ux],[ly,uy],[max(lx,ly), min(ux,uy)]) :- true.

.decl join(x : interval , y : interval, z : interval) inline
join([lx,ux],[ly,uy],[min(lx,ly), max(ux,uy)]) :- true.

.decl add(x : interval , y : interval, z : interval) inline
add([lx,ux],[ly,uy],[lx + ly, ux + uy]) :- true.

.decl sub(x : interval , y : interval, z : interval) inline
sub([lx,ux],[ly,uy],[lx - uy, ux - ly]) :- true.

.decl mul(x : interval , y : interval, z : interval) inline
mul([lx,ux],[ly,uy],[min(a,b,c,d), max(a,b,c,d)]) :- a = lx * ly, b = ux * ly, c = lx * uy, d = ux * uy.

.decl abs(x : interval , y : interval) inline
abs([lx,ux],[lx,ux]) :- lx > 0.
abs([lx,ux],[-ux, -lx]) :- ux < 0.
abs([lx,ux],[0, max(-lx, ux)]) :- lx <= 0, ux >= 0.


.decl test(x : interval)
test(z) :- mul([2,4], [4,5],z).
.output test(IO=stdout)


.type Expr = 
      Add {x : Expr, y : Expr}
    | Sub {x : Expr, y : Expr}
    | Mul {x : Expr, y : Expr}
    | Rnd {x : Expr}
    | Lit {x : float}
    | Var {x : symbol}

// Expression e is in interval i
.decl BND(e : Expr, i : interval)
// Absolute value of e is in interval i
.decl ABS(e : Expr, i : interval) 
// x = y * (1 + e) 
.decl REL(x : Expr, y : Expr, i : interval)
// 
//.decl FIX(x : Expr, k)

// The value of expression x is not zero.
.decl NZR(x : Expr)
.decl EQL(x : Expr, y : Expr) eqrel

EQL(x,y) :- BND(x, [a,a]), BND(y, [a,a]).
NZR(x) :- BND(x, [a,b]), (a > 0 ; b < 0).

.decl exprs(e : Expr)
EQL(x,x) :- exprs(x).

BND(t, [a,a]) :- exprs(t), t = $Lit(a).
BND(t, [0,0]) :- exprs(t), t = $Sub(a, a).

BND(z, iz) :- exprs(z), BND(x,ix), BND(y,iy), (
            (z = $Add(x,y), add(ix,iy,iz));
            (z = $Sub(x,y), sub(ix,iy,iz));
            (z = $Mul(x,y), mul(ix,iy,iz))).

ABS(e, iy) :- BND(e, ix), abs(ix,iy).





```

## Fused multiply add
[multiply accumlate](https://en.wikipedia.org/wiki/Multiply%E2%80%93accumulate_operation)

[Remez algorithm](https://github.com/simonbyrne/Remez.jl) Find minimax optimal polynomial over range

How to calculate things
1. taylor series. We often have these in closed form. We can bound errors using remainder theorem (The error of a taylor series is bounded by the maximum value the next term can take over the interval). If nothing else, taylor series can boot strap other methods by using them to define arbitrary precision approximations.
2.

Dyadic rationals = $$ m \times 2^d $$. These are an idealized model of floating point. They can add, subtract, and multiply exactly.

ULP - Unit in Last place. a measure of how accurate an fp calculation is. 0.5 ulp is the best you can do for approximating an anagonisitcally chosen number.

How and how not to compute matrix exponentials https://www.maths.manchester.ac.uk/~higham/talks/exp10.pdf
19 dubious ways

[interesting discussion of deriving a specific approximator](https://discourse.julialang.org/t/a-faster-pow-x-1-12-function-available-in-fast12throot-jl/10893/11)

## Range reduction
Powers of 2 are often easier to handle seperately, leaving behind a problem

exp = 2^(log_2(e) * x)

sin/cos don't matter modulo 2 pi. modulo pi for some signs.

polynomial Approximations typically are only ok over small ranges

## 2Sum and Fast2Sum
https://en.wikipedia.org/wiki/2Sum
Compensated summation
Exact roundoff in floating point addition.
From an information perspective, taking two 64 bit numbers into 1 is lossy? Well, yeah but so what?
What if you kept an entire error tape?
You can't get exact roundoff

You can get exact errors. If you try to keep doing this, the error terms keep growing in size though.
(a + (b + c)) gets two seperate error terms. Exact addition of these gives you exact error.

Fused multiply add let's you obviously get the exact error of a multiplication
```
x = o(a * b)
err = o(a*b - x)
```

[kahan summation](https://en.wikipedia.org/wiki/Kahan_summation_algorithm)
[pairwise summation](https://en.wikipedia.org/wiki/Pairwise_summation) simple divide and conquer summation.

## Veltkamp splitting
You can split a float into 2 floats that add together to it precisely. This is useful sometimes
## Dekker Multiplication
Exact error can be represented in floating point for floating point multiplication

## Newton Raphson
## Multiplication by arbitrary precision number like pi
Compute a hgh and low part of the number
Ch = RN(C)
Cl = RN(C - x)


## Error Models
https://pavpanchekha.com/blog/epsilon-delta.html

o(x op y) = (x op y)(1 + e)
e <= u




## Sterbenz lemma
Addition and subtraction are exact if the numbers are really close to each other. (A factor of 2)

## Gappa
<https://gappa.gitlabpages.inria.fr/gappa/index.html>
Proofs about 
https://gappa.gitlabpages.inria.fr/gappa/theorems.html The rules that gappa uses.
Woah. This could work

multiple proof output modes
-B latex -Bcoq

[Implementing Cosine in C from Scratch (2020) (](https://news.ycombinator.com/item?id=30844872)
[musl __cos](https://github.com/ifduyue/musl/blob/master/src/math/__cos.c)
Boldo
[Formal Verification of Scientific Computing Programs icfp 19](https://www.youtube.com/watch?v=d38KO5UgHv8&ab_channel=ACMSIGPLAN)

Ranged Floats {range : interval; x : float code}

Numerical Analysis
Higham

[comparing floating point is tricky](https://www.reddit.com/r/cpp/comments/tavh14/comparing_floatingpoint_numbers_is_tricky/)
[precisa](http://precisa.nianet.org/) program round off error certifier via static analysi. Accepts subset of PVS. Hmm outputs framaC with annotations. Web demo is interesting.
[fprock](https://github.com/nasa/FPRoCK)


[One Polynomial Approximation to Produce Correctly Rounded Results of an Elementary Function for Multiple Representations and Rounding Modes](https://people.cs.rutgers.edu/~sn349/papers/rlibmall-popl-2022.pdf)
[shaman](https://gitlab.com/numerical_shaman/shaman) operator overloading to estimate numerical error

Daisy
[accruate algorithms](https://accurate-algorithms.readthedocs.io/en/latest/index.html)

[rlibm](https://arxiv.org/pdf/2111.12852.pdf) better polynomial approximations using linear programming

Handbook of floating point

Elementary Functions: Algorithms and Implementation by Muller

Intervals arithmetic
[interval mooc](https://www.ensta-bretagne.fr/jaulin/iamooc.html)

[Linkes to dd arithmetic](https://twitter.com/hypergeometer/status/1493976347177275394?s=20&t=HpXMueCpbbces3-09fMYhw). dd+d and qd+d. airthemtic. Ball arithemtic using float formats for everything? double double arithemtic. using two doubles to represent and one double for ballradius. Sometimes you need to go to higher precision to correctly round. So 2 doubles is attarcive sine 128bit floas rarely exist in hardware

compute recude bound |result| * 2^-53 or "error-free transformation"

mathemagix


[Formally Verified Approximations of Definite Integrals](https://hal.inria.fr/hal-01630143/file/main.pdf)

Henessey and Patterson Appendix H has a good section with reference by the same Golberg who wrote the 
[What Every Computer Scientist Should Know About Floating-Point Arithmetic](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html)

- NaN
- Denormalized numbers



[Fixed point smtlib encoding pysmt](https://www.youtube.com/watch?v=sny9X77ZjTQ&t=1224s)

[john harrison](https://www.youtube.com/watch?v=2F3tQL-SmgI) p-adic and floats are similar? msb vs lsb? 

harrison book - Proving About Real Numbers
Boldo Melquiond book - computer arithemtic and formal proofs

Can I directly write down the principals of interval arithmetic?
The contraction map principle.
True ODES are the capability to do something for all dt


<https://news.ycombinator.com/item?id=29201473> The dangers of fast-math flags. Herbie comments
ocaml crlibm <https://github.com/Chris00/ocaml-crlibm>


Herbie is super cool.
1. you can just do rancom sampling to estimate errors, with extreme multiprecision accuracy and regular. Dynamic analysis in a sense?
2. rewriitng
Denali

Arith_2021 - a conference on FP?
FPTalks

Hamming book


What is fluctuat?
precisa
precision tuning
Real2float
rosa


https://monadius.github.io/FPTaylorJS/#/ FPTaylor demo
https://github.com/arnabd88/Satire - scaling numerical rounding analysis
[FPBench](https://fpbench.org/) , FPTalk 
Herbie
https://github.com/soarlab
https://gitlab.com/numerical_shaman/shaman shaman - another error tracking thing

Gappa
Sollya
textbook on coq floating point
FlocQ

Verified plotting -Melquiond

https://twitter.com/santoshgnag/status/1396807877260726280?s=20 generating correctly rounded math libraries for 32 bit

http://www.lix.polytechnique.fr/~putot/fluctuat.html Fluctuat analyzer

https://pavpanchekha.com/blog/understanding-fptaylor.html

Textbook Formal Verification fo Floatng Point Hardware



My coq pendulum swing up. Could I verify it?
 
https://www.cs.cmu.edu/~quake/robust.html Adaptive Precision Floating-Point Arithmetic and Fast Robust Predicates for Computational Geometry
https://github.com/mourner/robust-predicates
https://github.com/mikolalysenko/robust-arithmetic-notes

http://doc.cgal.org/latest/Number_types/classCGAL_1_1Gmpq.html
http://www.algorithmic-solutions.info/leda_guide/geometryalgorithms.html

https://twitter.com/santoshgnag/status/1381959477759463429?s=20 
https://arxiv.org/pdf/2104.04043.pdf - synethesizing a correctly rounded floating point guy

CRLibm
MetaLbim
gappa
http://toccata.lri.fr/fp.en.html tocatta 
http://toccata.lri.fr/gallery/newton_sqrt.en.html
I guess why3 has extensive support for floating point?

https://gitlab.inria.fr/why3/whymp a multirpecision library verified using why3

https://scicomp.stackexchange.com/questions/1026/when-do-orthogonal-transformations-outperform-gaussian-elimination

https://www.youtube.com/watch?v=RxOkV3wmEik&ab_channel=ACMSIGPLANACMSIGPLAN Generating Correctly Rounded Math Libraries for New Floating Point Variants (full)
https://www.youtube.com/watch?v=B_J7DSX_ZXM&ab_channel=ACMSIGPLAN  λS: Computable Semantics for Diff'ble Programming with HO Functions and Datatypes (full)

[Verified Compilation and Optimization of Floating-Point Programs in CakeML](https://cakeml.org/ecoop22.pdf)

Core-math library


learning about floating point. fp triage

libultim
[fpvm floating point virtual machine](https://nickw.io/publication/hpdc22/) use virtual machine to do alternaitve fp semantics
naN boxing - store pointers in Nans
Nans trap, Some won't trap so they need to insert correctness traps
garbage collection
x1000 overhead

fpdebug
herbgrind
fpsanitizer



unbounded expoentn
https://tcpp.cs.gsu.edu/curriculum/?q=peachy
https://www.cl.cam.ac.uk/teaching/1011/FPComp/fpcomp10slides.pdf
https://www.mccormick.northwestern.edu/computer-science/documents/2021-12-comparing-understanding-of-iee-floating-point1.pdf

https://dl.acm.org/doi/10.1145/3410463.3414660 vp float

https://www.amazon.com/Numerical-Computing-Floating-Point-Arithmetic/dp/0898714826 textbook

Round to odd mode - double rounding?
[When double rounding is odd](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.75.5554&rep=rep1&type=pdf)
rlibm-all


vscode -recisa



## FPBench
http://fpbench.org/talks/fptalks20.html
https://fpbench.org/talks/fptalks21.html



bound error of (a + (b + c))

## Brute Force Verification



# Constructive / Exact Reals
Constructive reals allow you to request an accuracy of the result, rather than specify the accuracy of the input.
This ordering is reminsicent of epsilon delta definitions in analysis, which are often explained as exactly this kind of game. You ask for an epsilon, I need to figure out a delta.

Constructive Reals are similar to automatic differentiation. 

It is tempting, but maybe a red herring, to point out that differentiability is a stronger requirement than continuity, but the two are related mathemtically.
More concretely, reverse mode differentiation asks something of th output of a function, which calculates something about the input by backpropagation. Exact reals need to do something similar. So implementation techniques for one often have analog in the other.

- Making a dataflow graph
- Wengert Tapes
- Constructive Reals as a lens


You can convert intervals arithmetic to constructive reals if you retain the ability to run the function over and over, searching for a small enough interval,

Interval arithmetic has much of the implementation flavor of forward mode auto differentiation, both of which use an overloaded notion of number. Forward mode differentiation is kind of like infinitesimal ball arithmetic.

https://github.com/holgerthies/coq-aern
# Misc
[coq robot](https://github.com/affeldt-aist/coq-robot)
[nasa stuff](https://shemesh.larc.nasa.gov/fm/) precisa

yves bertot said he was working in collision avoidance? http://www-sop.inria.fr/members/Yves.Bertot/internships/curve_collision.pdf bezier curves. Lavalle collision planning algorithms http://lavalle.pl/books.html

[assia mahboubi habiliaton](https://theses.hal.science/tel-03107626v2/document)

https://rtca2023.github.io/pages_Lyon/m2.html workshop may 2023. Sounds cool. Certified ans Symbolic computation

[seven sins of numerical linear algebra](https://nhigham.com/2022/10/11/seven-sins-of-numerical-linear-algebra/)

https://verinum.org/