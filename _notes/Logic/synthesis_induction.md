---
layout: post
title: Synthesis
---
- [ChatGPT](#chatgpt)
- [Induction](#induction)
  - [Cyclic Proofs](#cyclic-proofs)
- [Invariants](#invariants)
- [Bottom Up Enumerative synthesis](#bottom-up-enumerative-synthesis)
- [Alternating Quantifiers](#alternating-quantifiers)
- [inductive logic programming](#inductive-logic-programming)
- [Syntax Guided Synthesis (Sygus)](#syntax-guided-synthesis-sygus)
  - [Sketch](#sketch)

See also note on:

- Constrained Horn Clauses
- Invariant Synthesis
- Prolog/Minikanren
- SMT
- Inductive logic programming

<https://www.cis.upenn.edu/~alur/SyGuS13.pdf> syntax guided synthesis
<https://polgreen.github.io/polgreen_thesis.pdf> syntehsis withotu syntactic templates

<https://arxiv.org/pdf/2102.13183> RbSyn: Type- and Effect-Guided Program Synthesis
<https://drops.dagstuhl.de/opus/volltexte/2020/13159/pdf/LIPIcs-ECOOP-2020-2.pdf>  Perfect Is the Enemy of Good: Best-Effort Program Synthesis - Peleg

<https://arxiv.org/pdf/2106.06086.pdf> PSB2: The Second Program Synthesis Benchmark Suite <https://github.com/thelmuth/psb2-python> <https://github.com/thelmuth/program-synthesis-benchmark-datasets>
<https://thelmuth.github.io/GECCO_2015_Benchmarks_Materials/>

<https://cseweb.ucsd.edu/~lerner/papers/parsify-pldi15.pdf>
parser synthesis, grammar

Sketch <https://github.com/asolarlez/sketch-backend>

Courses:

- [Armando solar-lezama course](https://people.csail.mit.edu/asolar/SynthesisCourse/)
- [CSE 291: Program Synthesis - nadia-polikarpova](https://github.com/nadia-polikarpova/cse291-program-synthesis)

People:

- Armando Solar-lezama
- Hila Peleg
- Yotam Feldman
- Nadia Polikarpova
- Isil Dillig
- rahul sharma

Hoare logic in +-+ mode?

<https://github.com/logic-and-learning-lab/Popper>

synquid - type driven program synthesis

rosetta?
Cosette - sql synthesis

type inference is a form of synthesis

Minikanren - barliman.   Inseven examples there is also an interpreter run backwards

<https://github.com/TyGuS/suslik> syntheiss of heap maniuplation programs from seperation lgoic
[Structuring the Synthesis of Heap-Manipulating Programs](https://arxiv.org/pdf/1807.07022.pdf)

<https://www.youtube.com/watch?v=mFjSbxV_1vw&ab_channel=Fastly> Synthesis in reverse engineering
Synesthesia

[Program Syntehsis book](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/10/program_synthesis_now.pdf) gulwani polozov singh

# ChatGPT

# Induction

Graph induction / functional induction <https://types.pl/@pigworker/112016003109279373> <https://types.pl/@pigworker/112016097261103609>
<https://coq.inria.fr/doc/V8.13.0/refman/using/libraries/funind.html>
Equations
ACL2 induction <https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____INDUCTION>

Actually reify the callgraph.
f : callgraph (stack?) -> args -> res, callgraph
Then an outer loop can dispatch the callgraph I suppose. Analyze the graph/stack for decreasing-ness in some sense?
One could generate a type defunctionalizing the call stack I guess.. (?)

```lean
inductive fib in out where
  | base : fib 0 0 
  | base : fib 1 1
  | step : n > 1 -> fib n-1 a -> fib n-2 b -> fib n (a+b)

-- Also, I'd get rid of the a+b in the step conclusion, in favour of an extra hypothesis involving the graph of +.

-- fib n : ex m, fib n m := yada
```

Yes. This datatype really is a big call graph. This is kind of odd from a non depednent type perspective. A graph is usually not so shallowly represented.

This is both the call graph (internally) and the _mathemtical_ graph of the function. the graph being the set of pairs or relation of input/output as you might find in set theory.

A non loopy (infinite) call graph I guess is representable. Arguments supprssed

```
type baz = Base
type bar = Baz of baz
type foo = Bar of bar | Baz of baz 
```

And the graph is well founded. Only the projection onto function symbols without arguments becomes a loopy cyclic graph.

Build a trace recognizer first. (traces are obviously destructively recognized / fib_trace is more obviously a well founded induction function)

```python
def fib_trace(tr):
  match tr:
    case ("base0", 0, 0):
      return True
    case ("base1", 1, 1):
      return True
    case ("step", n, res, tr_n1, tr_n2):
      assert n > 1:
      assert fib_trace(tr_n1)
      assert fib_trace(tr_n2)
      assert res == tr_n1[2] + tr_n2[2]
      return True
```

```lean
-- but actually we could do this non depednet trace in lean too
inductive trace where
 | base0 : n m : Nat -> trace
 | base1 : n m : Nat -> trace
 | step : n m : Nat -> trace -> trace -> trace


def trace_recog1 : trace -> bool :=
def trace_recog2 n m : trace -> Option (fib n m) := 
 -- this does seem kind of leaky
```

bove capretta <https://gallium.inria.fr/blog/bove-reloaded/>
<https://easychair.org/publications/open/wV7> djinn monotonic mcbride
<https://inria.hal.science/hal-00691459/file/main.pdf> Partiality and Recursion in Interactive Theorem Provers - An Overview bove kruass sozeau

<https://ceur-ws.org/Vol-3201/paper9.pdf> vampire approach to induction

Chatper of auotmated reasoning handbook

cyclic proofs

<https://dl.acm.org/doi/abs/10.1007/978-3-030-53518-6_8>  Induction with Generalization in Superposition Reasoning

<https://link.springer.com/chapter/10.1007/978-3-662-46081-8_5> indcution for smt solvers eydnolds

induction vs termination. Termination is kind of saying that execution is well founded. Induction is saying that the proof is well-founded.

## Cyclic Proofs

<http://www0.cs.ucl.ac.uk/staff/J.Brotherston/slides/PARIS_FLoC_07_18_part1.pdf>

cycleq
cyclegg
inductionless induction

<https://hal.archives-ouvertes.fr/hal-01558132/document> a cut free cyclic proof system for kleene

Suppose I had a termination certificate of a program. Is induction for the program then easy? Since I can use induction over the structure of the termination certificate (well founded induction)? i mean the program I've given is already a proof of some kind.

# Invariants

# Bottom Up Enumerative synthesis

<https://people.csail.mit.edu/asolar/SynthesisCourse/Lecture3.htm>

# Alternating Quantifiers

Exists forall problems

There exists instanitations of holes in your program such that for all possible inputs, the program is correct.
Vaguely speaking:
$$\exists H \forall x \phi(x)$$

However, what is phi? One approach would be to define it using weakest precondition semantics. Or strongest postcondition

$$\exists H \psi(H) \land \forall x pre(x) \rightarrow WP(Prog,post(x))$$

$$\forall$$ is kind of like an infinite conjunction. For finite types you're quantifying it over, you can expand it into conjunction.
$$\forall c \phi(c) = \phi(red) \land \phi(blue) \land \phi(green)$$

You can also attempt to partially expand these quantifiers as a method to solve the alternating quantifier problem. This is CEGIS

$$\exists  H. finite expansion $$

In some sense, constraint solvers/smt/mathematical programming solvers are solving problems with implicit existential quantification over all the free variables.

Fixing the synthesis parameters, we

# inductive logic programming

# Syntax Guided Synthesis (Sygus)

[Sygus](https://sygus.org/) - syntax guided synthesis
[demo of sygus](https://www.youtube.com/watch?v=VkbDQtCS1VY&ab_channel=DG)
[sygus 2](https://sygus.org/assets/pdf/SyGuS-IF_2.0.pdf) compatbile with smtlib2?
[search based program synthesis](https://sygus.org/assets/pdf/CACM'18_Search-based_Program_Synthesis.pdf)

```cvc5
(set-option :lang sygus2)
()
;(check-synth)
;(define-fun spec ((x (BitVec 4)) (y BitVec 4)) (BitVec 4)
;    (ite (bvslt x y) y x)
;)

```

invariant synthesis: `Spec = Inv /\ body /\ Test' => Inv'`
Proof synthesis?

## Sketch

PDR

[Question about survey on synethesizing inductive ivanraints](https://twitter.com/lorisdanto/status/1483556907596013570?s=20&t=OSBR7Kcf7AOCicTAypA9yQ)

Yotam Feldman answers:

1. Houdini: invariant inference for conjunctive propositional invariants. I like the exposition in <https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.153.3511&rep=rep1&type=pdf>
2. Interpolation: McMillan's seminal paper on unbounded SAT-based model checking, which is hugely influential.
<https://people.eecs.berkeley.edu/~alanmi/courses/2008_290A/papers/mcmillan_cav03.pdf>
3. IC3/PDR: Another hugely influential technique, originally also for propositional programs. I like the exposition in the extension to universally quantified invariants over uninterpreted domains: <https://tau.ac.il/~sharonshoham/papers/jacm17.pdf>
4. Spacer: PDR for software, with arithmetic, also hugely influential in this domain. <https://t.co/gVlNrL6xts>
5. Syntax-guided methods: less familiar with these ones, but I'd hit the survey <https://sygus.org/assets/pdf/Journal_SyGuS.pdf> and work by Grigory Fedyukovich (e.g. <https://ieeexplore.ieee.org/document/8603011>)

<https://www.youtube.com/watch?v=-eH2t8G1ZkI&t=3413s>
syntax guided synthesis
sygus-if <https://sygus.org/>
CVC4 supports it.
LoopInvGen, OASES, DryadSynth, CVC4

polikarpova, peleg, isil dillig

<https://www.youtube.com/watch?v=h2ZsstWit9E&ab_channel=SimonsInstitute> -
automated formal program reapir
"fault localization"
<https://github.com/eionblanc/mini-sygus>

<https://arxiv.org/pdf/2010.07763.pdf> refinement types constrained horn lcauses. Describes using simple houdini algorithm,.

<https://dspace.mit.edu/bitstream/handle/1721.1/140167/Achour-sachour-PhD-EECS-2021-thesis.pdf?sequence=1&isAllowed=y> Sara Achour synthesis/compilation for analog computation decided
