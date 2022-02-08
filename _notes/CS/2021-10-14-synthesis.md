---
layout: post
title: Synthesis
---

See also note on:
- Constrained Horn Clauses
- Invariant Synthesis
- Prolog/Minikanren
- SMT


Sketch

Courses:
- [Armando solar-lezama course](https://people.csail.mit.edu/asolar/SynthesisCourse/)
- [CSE 291: Program Synthesis - nadia-polikarpova ](https://github.com/nadia-polikarpova/cse291-program-synthesis)

People:
- Armando Solar-lezama
- Hila Peleg
- Yotam Feldman
- Nadia Polikarpova
- Isil Dillig
- rahul sharma



https://github.com/logic-and-learning-lab/Popper

synquid - type driven program synthesis

rosetta?

Minikanren - barliman.   Inseven examples there is also an interpreter run backwards

https://github.com/TyGuS/suslik syntheiss of heap maniuplation programs from seperation lgoic

https://www.youtube.com/watch?v=mFjSbxV_1vw&ab_channel=Fastly Synthesis in reverse engineering
Synesthesia

Alternating Quantifiers

inductive logic programming

# Syntax Guided Synthesis (Sygus)
Sygus - syntax guided synthesis

PDR

[Question about survey on synethesizing inductive ivanraints](https://twitter.com/lorisdanto/status/1483556907596013570?s=20&t=OSBR7Kcf7AOCicTAypA9yQ)

Yotam Feldman answers:
1. Houdini: invariant inference for conjunctive propositional invariants. I like the exposition in https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.153.3511&rep=rep1&type=pdf
2. Interpolation: McMillan's seminal paper on unbounded SAT-based model checking, which is hugely influential.
<https://people.eecs.berkeley.edu/~alanmi/courses/2008_290A/papers/mcmillan_cav03.pdf>
3. IC3/PDR: Another hugely influential technique, originally also for propositional programs. I like the exposition in the extension to universally quantified invariants over uninterpreted domains: <https://tau.ac.il/~sharonshoham/papers/jacm17.pdf>
4.  Spacer: PDR for software, with arithmetic, also hugely influential in this domain. https://t.co/gVlNrL6xts
5.  Syntax-guided methods: less familiar with these ones, but I'd hit the survey <https://sygus.org/assets/pdf/Journal_SyGuS.pdf> and work by Grigory Fedyukovich (e.g. https://ieeexplore.ieee.org/document/8603011)

https://www.youtube.com/watch?v=-eH2t8G1ZkI&t=3413s
syntax guided synthesis
sygus-if https://sygus.org/
CVC4 supports it.
LoopInvGen, OASES, DryadSynth, CVC4


polikarpova, peleg, isil dillig

https://www.youtube.com/watch?v=h2ZsstWit9E&ab_channel=SimonsInstitute - 
automated formal program reapir
"fault localization" 
https://github.com/eionblanc/mini-sygus


https://arxiv.org/pdf/2010.07763.pdf refinement types constrained horn lcauses. Describes using simple houdini algorithm,.