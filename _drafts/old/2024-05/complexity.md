---
layout: post
title: Complexity
---

[descriptive complexity](https://en.wikipedia.org/wiki/Descriptive_complexity_theory) queries in these logics when restricted to finite structures have this computational complexity

Lower bounds
Master theorem

NP
PSPACE

Reductions

<https://en.wikipedia.org/wiki/P_versus_NP_problem>

Language

<https://en.wikipedia.org/wiki/Blum_axioms>

cook-levin is basically symbolically executing a turing machine using SAT.

```python
import turing

```

# Proof complexity
<https://www.cs.cornell.edu/~sabhar/publications/iaspcmi-proofcomplexity00.pdf>
Proofs are objects/
co-NP = NP if proofs are small
ASP might be nice for this.
"transcript"

<https://homes.cs.washington.edu/~beame/projects/proofcomplexity.html>
 Size of resolu8tuion proofs?
A strategy is to encode proofs as objects and sat search for them. Presumably proofs are too big for this to work well.

Weak pigeonhole
<https://people.cs.uchicago.edu/~razborov/files/php_survey.pdf>
Pigeonhole =
<https://x.com/codydroux/status/1712501511270420508> completeness is infinirary pigeonhole "Though in reverse mathematics, PH is much weaker than BW, mostly owing to the complexity of talking about reals. B-W is on par with some of the Ramsey theorems, apparently." Bolzano Weierstrauss

<https://terrytao.wordpress.com/2007/05/23/soft-analysis-hard-analysis-and-the-finite-convergence-principle/>

So there is sort of Soft / Analytic hiearchy
Hard / Finitary / arithmetic hierarchy
Complexity / polynomial hierachy
