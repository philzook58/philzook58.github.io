---
layout: post
title: Imperative Proving
---
- [Hoare Logic](#hoare-logic)
- [Weakest Precondition](#weakest-precondition)
- [Why3](#why3)
- [Boogie](#boogie)
- [Dafny](#dafny)
- [KAT](#kat)
- [Misc](#misc)
    - [Fun old timey books.](#fun-old-timey-books)

See also notes on:
- Model Checking
- SMT
- separation logic
- CHC invariant generation

# Hoare Logic
https://en.wikipedia.org/wiki/Hoare_logic
I have heard somewhere that actually we should distinguish Floyd's work on flow charts as something different. Maybe in a Lamport paper?

Axiom schema


# Weakest Precondition


# Why3

# Boogie
<https://boogie-docs.readthedocs.io/en/latest/index.html>
# Dafny

# KAT

https://link.springer.com/chapter/10.1007/978-3-030-81685-8_3 algerbaic program anlaysis
graphs and paths can be represent by taking the letters of the alphabet to representedges in the graph. The paths from a to b can be represented as a regex
Tarjan's algorithm http://i.stanford.edu/pub/cstr/reports/cs/tr/79/734/CS-TR-79-734.pdf "path expression problem"
If you have the path expression, you can just intepret it to calculate program quantities.

Kleene algerba with tests
MOdelling language for 
horn equational?
Relative of Propositional Hoare Logic. Which is a neat idea on it's own

tutorial https://alexandrasilva.org/files/talks/kat-tutorial.pdf https://popl20.sigplan.org/details/POPL-2020-tutorialfest/7/-T7-Programming-and-Reasoning-with-Kleene-Algebra-with-Tests
https://www.cl.cam.ac.uk/events/ramics13/KozenTutorial1.pdf

GKAT  guarded kleene with test https://arxiv.org/abs/1907.05920 https://www.youtube.com/watch?v=Dp68j9Wi_84&ab_channel=ACMSIGPLAN
Kleene algebra modulo theories
https://github.com/mgree/kmt
https://arxiv.org/pdf/1707.02894.pdf
https://github.com/mgree/katbury hmm. guess invariants

[On the Coalgebraic Theory of Kleene Algebra with Tests](https://www.cs.cornell.edu/kozen/Papers/ChenPucella.pdf)
Automatic proof generaton via derivatives? That sounds neat.
Chen and Pucella - coalgerba theory of KAT

[Automated Reasoning in Kleene Algebra](http://www.hoefner-online.de/home/pdfs_tr/trCS-07-04-Shef.pdf) Prover9/Mace4

[Symbolic Algorithms for Language Equivalence and Kleene Algebra with Tests](https://dl.acm.org/doi/10.1145/2775051.2677007) bdds + union find for language equivalence

topkat incorrectess logic and kat https://www.youtube.com/watch?v=gLLlrnxB5Jg&ab_channel=ACMSIGPLAN popl22

NetKat - kat for network reasoning
[Kleene Algebra with Tests and Coq Tools for While Programs](https://arxiv.org/abs/1302.1737)

syntax are kleene expressions / logic is kleene algebra manipulation. logic is algebra on steroids
semantics are strings

algerbraic laws + leastness of fixed point

hmm. 2x2 matrices have a schur complement representation theorem. hmmm.

a <= b <-> a + b = b


Well, this is basically doable

```
(datatype K 
 (+ K K) ; choice
 (* K) ; iterate
 (Fail)
 (Skip)
 (# K K) ; sequence
)
(define a K)
(define b K)
(# (* a) b)
(: (+ One a) (+ One b))
(* (+ a b))

; idempotent semiring
(rewrite (+ e Fail) e)
(rewrite (+ e f) (+ f e))
(rewrite (+ e f)) ; assoc
(rewrite (+ e e) e)

(rewrite (: ))

; star is least fix point

(rewrite (: (+ One a) a) (* a))



```

efficient procesure - antichain doyen upto bis9mualtion bonchi-pous 2015

kleene algerab with tests Add booleans as subset of kleene stuff

if b then p else q = b;p + ~b;q
while b do p = (b;p)* not b

booleans commute under seq

guarded semantics. a kleene command is every possible pre and post condition.
sequence needs the bools to meet in the middle

(Bool K Bool)

propositional hoare logic.
{b}p{c} = bp~c == 0
what does that mean? oooooh. b p not(c). Ok that's neat.

Models
Language models - just actions
Trace models - interspersed with states in btwee
relation models - relation compose, relation closure
tropical semiring and convex polyhedra
matrices over another kleene algerba


# Misc
[jitterbug](https://unsat.cs.washington.edu/projects/jitterbug/)
[serval](https://unsat.cs.washington.edu/projects/serval/)

[Static Program Analysis](https://cs.au.dk/~amoeller/spa/) book. dataflow analysis etc.

[modelling the heap](https://www.youtube.com/watch?v=AbiVYHVU0mQ&ab_channel=MicrosoftResearch)

[why3 implemtnation of stackify](https://gitlab.inria.fr/why3/why3/-/merge_requests/453)
Stackifty algorithm of llvm for wasm

Why is structuring unstructured control flow so important?

[Weakest-precondition of unstructured programs banrett leino](https://dl.acm.org/doi/pdf/10.1145/1108792.1108813?casa_token=ob3emjwEGOMAAAAA:UhXOCwPb0Kt_tnRPAoscxpjMkFo744scDwCvwbBu6OiWH0TwZ0wBhJG8jxTFuW7h1BXETVL7zjB-)

<https://alastairreid.github.io/uses-for-isa-specs/> what can you do with an isa spec - alastair reid

Imp stmt to stack machine
Imp expr to stack machine

Expr as state?
Expr + Context as state. Ok sure.
List stack as state
Try just binary operator
Try booleans rather than nats

There is a single reflection step to a machine


forall s1 : S1, s2 : S2, (p : s1 ~ s2), (R1 s1 s1') (R2 s2 s2') : s1' ~ s2'

Maybe verifying a pipelined processor (how hard could it be amirite?!?!) would be a fun concurrency example to attempt int ivy or tla+ or whatever


<https://dl.acm.org/doi/pdf/10.1145/3314221.3314601> instruction semantics for x86 in K
<https://cs.stanford.edu/people/eschkufz/docs/pldi_16.pdf> Synthesiszing automatically learning semantics of x86



The Hamming Book. Gilbert Strang book. Numerical analysis
Geometrical algorithms
Stuff in CLRS?

limbs circuit. 3d printed snapping.


Use z3-wasm.

Specit - word based specification challenges.
Prove equivalence using Z3?

let's as assignemnt
injecting block addigment variables after phi nodes
gated ssa vs

smtlib preporcoesor - wp mode.

boogie why


https://github.com/UniMath/SymmetryBook
https://github.com/xavierleroy/cdf-mech-sem


Different styles of proving on CFGs.

The CFG is already giving you a lot, to pretend you know what jumps are possible. This does let you

Nand2Tetris style, we could model the gates of the hardware. And then unfold in time using BMC

- Do we maintain the instruction pointer as a concept?
- For every block, with every entrance and exit, one could manually state a summary entrance and summary exit predciates. For every edge linking an exit to and entrance one requires that P |- Q. And in addition that the entrance predicates imply the exit predicates of the block itself
- DAGs present no problems as CFGs. You can finitely produce a trasntiion relation for them, or run WP on them. So one perspective if that you need to cut enough edges to make the cfg a dag. And every time you cut an edge, you need a predicate associated with that edge or perhaps one with the entrance and one with the exit of that edge.
- Lamport had some mention of ther Floyd method as being more general than the hoare method. Floyd seemed to be considering cfgs. TLA+ does explicitly model the program counter.
- Symbolic execution branches at the logical level instead of at the logical level. This does not lend itself obviously to something that works in the presence of loops. 

We could do the Micro-WP to demonstrate these styles. But it is a pain.
Infer a CFG for Nand2Tetris? Perhaps hards because it can be difficult to know what locations you may jump to. We could instead work in a CFG intermediate representation that compiles.

class Block:
    code: list[instr] # no jumps
    jump: A1, A2, JMP 






Fuzzing is so fuckin useful. To not beusing dynamic techniques
https://github.com/mykter/afl-training afl fuzzing training

https://www.youtube.com/watch?v=sjLFf9q2NRc&ab_channel=FuzzingLabs-PatrickVentuzelo afl++ qemy
libfuzzer vs afl vs honggfuzz
corpus grammar based fuzzing, differential fuzzing




What changes do yoiu need to make to use arbitrary control flow graphs vs structured programs




https://www.lulu.com/en/us/shop/k-rustan-m-leino-and-kaleb-leino/program-proofs/paperback/product-wqy8w5.html?page=1&pageSize=4
Rustan leino book
https://github.com/backtracking/program-proofs-with-why3

Djikstra monads - this might be a stretch
F* 
Djikstra moand + interaciton trees https://www.seas.upenn.edu/~lucsil/papers/dmf.pdf
Interaction trees ~ free monad rearranged for total language
related to freer monads - kiselyov thing. This is what lexi king was working on yea?
http://hackage.haskell.org/package/freer
http://okmij.org/ftp/Haskell/extensible/more.pdf


General Monad mcbride
https://www.cis.upenn.edu/~bcpierce/papers/deepweb-overview.pdf from C to interaction trees li-yao xia






Disjkstra and Scholten
That link off of Leino

Could I make an equation style system in Z3py? Probably, right?
Take Agda as an example
Backhouse
Hehner
https://news.ycombinator.com/item?id=11797522



I've been feeling like i should be doing manual hoare logic/ imperative proofs

There is a vast assortment of tools out there that aren't proof assistants.

Boogie, dafny, frama-c, viper, verifast, whyml, why3, liquidhaskell, spark/ada, spec#
JML, ESC/java https://www.openjml.org/ whiley
esc/modula-3 

dafny
vs code plugin
https://rise4fun.com/Dafny/tutorial
https://web.cecs.pdx.edu/~apt/cs510spec/
https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef
http://leino.science/dafny-power-user/ 
http://web.cecs.pdx.edu/~apt/cs510spec/


viper
vs code plugin
http://viper.ethz.ch/tutorial/


frama-c
https://alhassy.github.io/InteractiveWayToC.html
https://github.com/fraunhoferfokus/acsl-by-example


verifast tutorial
https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf


https://github.com/hwayne/lets-prove-leftpad
vcc
ZetZZ https://github.com/zetzit/zz https://news.ycombinator.com/item?id=22245409
https://news.ycombinator.com/item?id=23997128 dafny discussion
Verilog + symbiyosys, 
KeY, KeymaeraX
CBMC, ESBMC http://www.esbmc.org/ , EBMC
cpa-checker https://cpachecker.sosy-lab.org/
TLA might be in this category
Event-B alloy


https://github.com/johnyf/tool_lists/blob/master/verification_synthesis.md god this list is nuts
https://www.pm.inf.ethz.ch/research/verifythis.html verify this
https://sv-comp.sosy-lab.org/2020/ sv-comp


https://github.com/tofgarion/spark-by-example

Eiffel for pre post conditions

https://github.com/microsoft/Armada
chalice
ATS

F*, Iris, 
VST, Bedrock
Isabelle?


It's interesting that logical psecs are so foreign, and somewhat longwinded when applied to imperative code,
that they aren't that much more understandable or high assurance.
Really it might be about formally proving equaivlance between just specs in different languages.
Python and C for example.


A good question is: what are interesting programs to prove?
1. List manipulation
2. sorts
3. red black trees
4. find

### Fun old timey books. 
If you go before 1980, a decent chunk of all books had assembly in mind.

  * discpline of programming - djikstra https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf
  * Reynolds - The craft of programming
  * Knuth - The Art of Computer Programming
  * The science of programming - D Gries
  * Pascal, wirth
  * structured programming https://seriouscomputerist.atariverse.com/media/pdf/book/Structured%20Programming.pdf djikstra hoare
  * Eric Hehner
  * https://dl.acm.org/collections/classics ACM classic books
  * lambda papers
  * per brinch hansen
  * https://en.wikipedia.org/wiki/List_of_important_publications_in_theoretical_computer_science#Formal_verification
  * https://en.wikipedia.org/wiki/List_of_important_publications_in_computer_science
  * http://www.mathmeth.com/read.shtml some welevant EQD notes. Derivation of alogrithms
  * winskel 