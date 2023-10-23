---
layout: post
title: HOL
---

# Axioms

Encoding forall
``\x P(x) = \x true` is saying that the predictae p is always true.

# HOL

- [cakeml](https://cakeml.org/) a verified implementation of an ML in HOL4
- [holpy](https://github.com/bzhan/holpy) <https://arxiv.org/abs/1905.05970>

HOL4
<https://kth-step.github.io/itppv-course/>

# HOL light

- [wikpedia](https://en.wikipedia.org/wiki/HOL_Light)
- [Harrison's page](https://www.cl.cam.ac.uk/~jrh13/hol-light/)
- [tutorial](https://www.cl.cam.ac.uk/~jrh13/hol-light/tutorial.pdf) quite good
- [Thomas Hale - Formal Proof article](https://cmartinez.web.wesleyan.edu/documents/FP.pdf) Succinct summary of axioms
- [](https://crypto.stanford.edu/~blynn/compiler/Hol.html)

<https://github.com/jrh13/hol-light/>
[harrison itp school](https://itp-school-2023.github.io/slides/slides_jrh_part1.pdf)
<https://cakeml.org/candle> candle hol light on cakeml

botstrap <https://github.com/jrh13/hol-light/blob/master/hol.ml>

kernel <https://github.com/jrh13/hol-light/blob/master/fusion.ml>

```bash
echo "
;question, can I write re
(declare-const b Bool)
(assert (distinct b b))
(check-sat)" > /tmp/test.smt2
vampire /tmp/test.smt2
```

#

# Isabelle

[from lcf to isabelle](https://dl.acm.org/doi/pdf/10.1007/s00165-019-00492-1)
[sel4](https://sel4.systems/) - verified microkernel

[](https://www.cse.unsw.edu.au/~cs4161/)

Metalevel is a syntax for describing inference rules

- `!! x.`     \Lambda Universal variables at the meta level. enables Schema
- `==>` is inference rule
- `%x.` is meta level lambda?

[typeclasses vs locales](https://twitter.com/LawrPaulson/status/1506603400267505669?s=20&t=y2AWW1GNA8vyxsWqTXmKPQ)

[Sledgehammer: some history, some tips](https://lawrencecpaulson.github.io/2022/04/13/Sledgehammer.html)
[isabelle cookboook: programming in ML](https://web.cs.wpi.edu/~dd/resources_isabelle/isabelle_programming.urban.pdf)
[more isabelle ML programming notes](https://www.lri.fr/~wolff/papers/other/TR_my_commented_isabelle.pdf)

[Baby examples](https://lawrencecpaulson.github.io/2022/05/04/baby-examples.html)

Isabelle => vs --> vs ==>
=> is the function type
--> is implication
==> is meta implication, which is something like a sequent |-

```isabelle
{% include_relative isabelle/play.thy %}
```

Querying

```isabelle
{% include_relative isabelle/isabelleplay.thy %}
```
