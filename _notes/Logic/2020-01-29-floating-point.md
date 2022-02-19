---
layout: post
title: Floating Point and Numerical verification
---

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
kahan summation

What is fluctuat?
precisa
precision tuning



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