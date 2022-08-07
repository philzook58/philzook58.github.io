---
layout: post
title: Floating Point and Numerical verification
---

# Fused multiply add
[multiply accumlate](https://en.wikipedia.org/wiki/Multiply%E2%80%93accumulate_operation)

[Remez algorithm](https://github.com/simonbyrne/Remez.jl) Find minimax optimal polynomial over range

How to calculate things
1. taylor series. We often have these in closed form. We can bound errors using remainder theorem (The error of a taylor series is bounded by the maximum value the next term can take over the interval). If nothing else, taylor series can boot strap other methods by using them to define arbitrary precision approximations.
2.

Dyadic rationals = $$ m \times 2^d $$. These are an idealized model of floating point. They can add, subtract, and multiply exactly.

ULP - Unit in Last place. a measure of how accurate an fp calculation is. 0.5 ulp is the best you can do for approximating an antagonisitcally chosen number.

How and how not to compute matrix exponentials https://www.maths.manchester.ac.uk/~higham/talks/exp10.pdf
19 dubious ways

[interesting discussion of deriving a specific approximator](https://discourse.julialang.org/t/a-faster-pow-x-1-12-function-available-in-fast12throot-jl/10893/11)

# Range reduction
Powers of 2 are often easier to handle seperately, leaving behind a problem

exp = 2^(log_2(e) * x)

sin/cos don't matter modulo 2 pi. modulo pi for some signs.

polynomial Approximations typically are only ok over small ranges

# 2Sum and Fast2Sum
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

# Gappa
<https://gappa.gitlabpages.inria.fr/gappa/index.html>
Proofs about 

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
FPBench , FPTalk
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



## Constructive / Exact Reals
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

# Misc

https://rtca2023.github.io/pages_Lyon/m2.html workshop may 2023. Sounds cool. Certified ans Symbolic computation
