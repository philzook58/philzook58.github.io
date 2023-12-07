---
layout: post
title: Software Verification
---
- [Static Analysis](#static-analysis)
  - [SV-Comp](#sv-comp)
  - [Large Scale Linty](#large-scale-linty)
  - [Bounded Model Checking](#bounded-model-checking)
    - [CBMC / ESBMC](#cbmc--esbmc)
    - [Cpachecker](#cpachecker)
    - [Rust](#rust)
- [Hoare Logic](#hoare-logic)
  - [Incorrectness Logic](#incorrectness-logic)
  - [Weakest Precondition](#weakest-precondition)
  - [Separation Logic](#separation-logic)
  - [Systems](#systems)
    - [Why3](#why3)
      - [frama-C](#frama-c)
    - [Dafny](#dafny)
    - [ADA/Spark](#adaspark)
    - [Fstar](#fstar)
    - [Iris](#iris)
    - [VST](#vst)
    - [Assembly](#assembly)
- [Invariants](#invariants)
  - [CEGAR](#cegar)
  - [IC3 / PDR](#ic3--pdr)
  - [Constrained Horn Clauses](#constrained-horn-clauses)
- [Software Engineering](#software-engineering)
- [Memory](#memory)
  - [Memory Safety](#memory-safety)
- [Misc](#misc)
    - [Fun old timey books](#fun-old-timey-books)
- [old model checking notes](#old-model-checking-notes)
  - [wordpress\_id: 879](#wordpress_id-879)
- [Old Sep Logic](#old-sep-logic)
- [Old CHC / Invariants](#old-chc--invariants)
    - [BTOR2](#btor2)
- [Resources](#resources)
    - [What is a query?](#what-is-a-query)
    - [Program Verification](#program-verification)
  - [Tricks](#tricks)
- [Ideas](#ideas)

See also notes on:

- SMT
- CTF Stuff

# Static Analysis

<https://en.wikipedia.org/wiki/Category:Static_program_analysis_tools>

SAST - Static application security testing. Totally goofball acronym that corporate people use.
DAST - dynamic application security testing. See CTF stuff.

Conferences

- ASE
- FSE
- ICSE

checked C [C to checked C by 3C](https://arxiv.org/abs/2203.13445)

## SV-Comp

  [International Competition on Software Verification](http://sv-comp.sosy-lab.org/)
  
- ESBMC / CBMC
- CPAChecker
- Symbiotic

coveriteam <https://www.sosy-lab.org/research/coveriteam/> `pip install CoVeriTeam`

```python
import coveriteam

```

witnesses
<https://gitlab.com/sosy-lab/software/btor2c>
compoenent based cegar

## Large Scale Linty

Systems to go larger scale.
See also notes on C/C++

- Infer
- Clang analyzer
- Cppcheck
- Semgrep
- Codeql - See also note on datalog

Companies

- klocwork
- code sonar
- coverity
- checkmarx
- Sonarqube
- gitlab sast <https://docs.gitlab.com/ee/user/application_security/sast/>

Abstract interpretation
Shape analysis - <https://github.com/kdudka/predator> predator

Algebraic program analyis - Reps

## Bounded Model Checking

See note on

- CTF stuff - Symbolic execution. KLEE
- Automata for temporal logic and non bounded model checking

<https://github.com/kind2-mc/kind2> takes in lustre. Multiple smt backends. ocaml implementations of ic3 and invarait
<https://kind.cs.uiowa.edu/kind2_user_doc/1_techniques/1_techniques.html>
SV-comp <https://sv-comp.sosy-lab.org/2022/>
Based on these results, given that I don't know shit, looks like cpachecker is a reasonable default if you're gonna pick one

veriabs - wins in reachability. Can you even buy it?

ADA Spark

TLA

Seahorn

### CBMC / ESBMC

Nice, fairly easy to use
[homepage](https://www.cprover.org/cbmc/)
<https://arxiv.org/abs/2302.02384>
`sudo apt install cbmc`
<https://github.com/diffblue/cbmc> gitbub
<https://diffblue.github.io/cbmc/> docs

<https://github.com/diffblue/aws-training>
<https://model-checking.github.io/cbmc-training/>
<https://github.com/model-checking/cbmc-starter-kit> starter kit template <https://model-checking.github.io/cbmc-starter-kit/tutorial/index.html> insstrumenting a maloc
<https://github.com/model-checking/cbmc-proof-debugger>

[manual](http://www.cprover.org/cprover-manual/) see tutorial

```bash
echo "
int main()
{
  int buffer[10];
  buffer[20] = 10;
}
" > /tmp/overflow.c
cbmc /tmp/overflow.c --bounds-check --pointer-check --trace
```

All kinds of analysuis options

```bash
cbmc --help
```

User defined stuff via `assert` or specialized

Supports lots of different smt and sat backended. Generic dimacs, Could toss into kissat

ESBMC

- C++ frontend
- Float support
- Still actually developd

<https://awslabs.github.io/aws-proof-build-assistant/>
<https://github.com/awslabs/aws-c-common>
corejson <https://github.com/FreeRTOS/coreJSON/tree/main/test/cbmc>
s2n-tls <https://github.com/aws/s2n-tls/tree/main/tests/cbmc>
<https://github.com/aws/aws-encryption-sdk-c/tree/master/verification/cbmc>
<https://github.com/aws/s2n-quic>

bounded proof vs harnes vs contracts

<https://crates.io/crates/libcprover_rust/5.91.0> rust api

### Cpachecker

<https://www.youtube.com/watch?v=d8iOP4QZ6m0&ab_channel=INISeminarRoom1>
Start in blast?
There is a yearly workshop

introductin to cpachecker <https://sosy-lab.gitlab.io/research/tutorials/CPAchecker/ShortIntroductionCPAchecker.html>

`script/cpa.sh`

### Rust

<https://rust-formal-methods.github.io/welcome.html>
<https://github.com/model-checking/kani>

# Hoare Logic

The above is more software engineery. This is more PL/logic flavored.

Winskel Book
[software foundations](https://softwarefoundations.cis.upenn.edu/plf-current/toc.html)

<https://en.wikipedia.org/wiki/Hoare_logic>
I have heard somewhere that actually we should distinguish Floyd's work on flow charts as something different. Maybe in a Lamport paper?

Axiom schema

Propositionbal hoare logic - see KAT

[Outcome logic](https://github.com/gleachkr/OL-Slides)
Extension of hoare logic that can express some thins in incrroectness logic

Compcert - see compilers
sel4 - see operating systems

Semantic frameworks - Maude / K framework
llvm semantics. Languages are so different.

## Incorrectness Logic

## Weakest Precondition

Dijkstra.
Interpret statements as _syntacticaly_ transforming symbolic formulas rather than states

<https://www.philipzucker.com/weakest-precondition-z3py/>

<https://en.wikipedia.org/wiki/Predicate_transformer_semantics>
Discipline of Programming <https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf> - Edsger Dijkstra

## Separation Logic

<https://x.com/sarah_zrf/status/1722303679741489413?s=20>
<https://arxiv.org/abs/1909.08789> proof pearl wand as frame. `P * (P -* Q)` is better than `P -* Q`

<https://en.wikipedia.org/wiki/Bunched_logic>

<https://cs.nyu.edu/~wies/software/grasshopper/>

<https://softwarefoundations.cis.upenn.edu/slf-current/index.html>

<https://alastairreid.github.io/RelatedWork/notes/separation-logic/>

CVC4 for automatically checking simple seperation logic.

<https://sl-comp.github.io/>

- Reynolds course  <https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html> Reynolds has a 2006 course as well <https://www.cs.cmu.edu/~jcr/seplogic.pdf> 2001 review paper
- <https://iris-project.org/tutorial-material.html> Iris tutorial
- <https://cacm.acm.org/magazines/2019/2/234356-separation-logic/fulltext> ACM survey ohearn

## Systems

- <https://www.isa-afp.org/entries/Isabelle_C.html>

Rust verification - see rust note

JML <https://www.openjml.org/>
Viper <https://www.pm.inf.ethz.ch/research/viper.html>

### Why3

[why3 implemtnation of stackify](https://gitlab.inria.fr/why3/why3/-/merge_requests/453)
Stackifty algorithm of llvm for wasm

WhyML <http://why3.lri.fr/python/>

Standard library reference
<https://why3.lri.fr/stdlib/>

Commands:
`why3`

why3 prove -P z3

why3 execute -use=ModulName

#### frama-C

Frama-C <https://frama-c.com/>

### Dafny

See Dafny Language notes.

boogie <https://boogie-docs.readthedocs.io/en/latest/index.html>

### ADA/Spark

### Fstar

<https://fstar-lang.org/>
Low*

### Iris

### VST

verified software toolchain
<https://vst.cs.princeton.edu/>

### Assembly

[bil-to-boogie](https://github.com/UQ-PAC/bil-to-boogie-translator) By god they did it.
BinSec
Cbat
ghihorn

arguably all symbolic execution engines - the trick is to cut loops

# Invariants

## CEGAR

## IC3 / PDR

## Constrained Horn Clauses

[Prof. Daniel Kroening | Encodings CHCs for low level Code](https://www.youtube.com/watch?v=Flc8Cjx6OUI&list=PL9-ncTy2ag0FMw3BDhlKUGc_RGU1dok6M&index=18&ab_channel=INISeminarRoom1)

# Software Engineering

https://github.com/binsec/preca  PreCA : Precondition Constraint Acquisition

https://dl.acm.org/doi/10.1145/3611643.3616296 semantic debugging AVICENNA

https://dbgbench.github.io/

spec synthesis

automated program repair

http://www.icse-conferences.org/ conference on software engineering
FSE
ASE

# Memory

Uninterpreted state encoding. malloc has an internal state. "load store"

Using SMT arrays.
A big block of 2^84 addresses or different models.
Tagged memory separating heap and stack. Chaos when gets confused. Does pointer arithmetic get it confused?

[Synthesizing an Instruction Selection Rule Library from Semantic Specifications](https://pp.ipd.kit.edu/uploads/publikationen/buchwald18cgo.pdf)
[A Formal Model of a Large Memory that Supports Efficient Execution](https://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD12/014.pdf)

<https://dl.acm.org/doi/abs/10.1145/3622855?af=R>  Static Analysis of Memory Models for SMT Encodings - oopsla 23
<https://github.com/hernanponcedeleon/Dat3M> datragnan tool. memory model aware verification

## Memory Safety

[Beyond the PDP-11: Architectural support for a memory-safe C abstract machine](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201503-asplos2015-cheri-cmachine.pdf)
Diehard allocator
[The meaning of memory safety](https://arxiv.org/abs/1705.07354)
Noninterferece as memory safety. The details of malloc should not leak
[Baggy Bounds Checking: An Efficient and Backwards-Compatible Defense against Out-of-Bounds Errors](https://www.usenix.org/legacy/event/sec09/tech/full_papers/akritidis.pdf)
[In Memory Safety, The Soundness Of Attacks Is What Matters*](https://openwall.info/wiki/_media/people/jvanegue/files/soundness_of_attacks.pdf)
[RUDRA: Finding Memory Safety Bugs in Rust  at the Ecosystem Scale](https://taesoo.kim/pubs/2021/bae:rudra.pdf)
[is memory safety still a concern](https://www.cs.columbia.edu/~mtarek/files/candidacy_exam_syllabus.pdf)

# Misc

[jitterbug](https://unsat.cs.washington.edu/projects/jitterbug/)
[serval](https://unsat.cs.washington.edu/projects/serval/)

[Static Program Analysis](https://cs.au.dk/~amoeller/spa/) book. dataflow analysis etc.

[modelling the heap](https://www.youtube.com/watch?v=AbiVYHVU0mQ&ab_channel=MicrosoftResearch)

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
<https://kframework.org/index.html>

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

<https://github.com/UniMath/SymmetryBook>
<https://github.com/xavierleroy/cdf-mech-sem>

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

What changes do yoiu need to make to use arbitrary control flow graphs vs structured programs

<https://www.lulu.com/en/us/shop/k-rustan-m-leino-and-kaleb-leino/program-proofs/paperback/product-wqy8w5.html?page=1&pageSize=4>
Rustan leino book
<https://github.com/backtracking/program-proofs-with-why3>

Djikstra monads - this might be a stretch
F*
Djikstra moand + interaciton trees <https://www.seas.upenn.edu/~lucsil/papers/dmf.pdf>
Interaction trees ~ free monad rearranged for total language
related to freer monads - kiselyov thing. This is what lexi king was working on yea?
<http://hackage.haskell.org/package/freer>
<http://okmij.org/ftp/Haskell/extensible/more.pdf>

General Monad mcbride
<https://www.cis.upenn.edu/~bcpierce/papers/deepweb-overview.pdf> from C to interaction trees li-yao xia

Disjkstra and Scholten
That link off of Leino

Could I make an equation style system in Z3py? Probably, right?
Take Agda as an example
Backhouse
Hehner
<https://news.ycombinator.com/item?id=11797522>

I've been feeling like i should be doing manual hoare logic/ imperative proofs

There is a vast assortment of tools out there that aren't proof assistants.

Boogie, dafny, frama-c, viper, verifast, whyml, why3, liquidhaskell, spark/ada, spec#
JML, ESC/java <https://www.openjml.org/> whiley
esc/modula-3

dafny
vs code plugin
<https://rise4fun.com/Dafny/tutorial>
<https://web.cecs.pdx.edu/~apt/cs510spec/>
<https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef>
<http://leino.science/dafny-power-user/>
<http://web.cecs.pdx.edu/~apt/cs510spec/>

viper
vs code plugin
<http://viper.ethz.ch/tutorial/>

frama-c
<https://alhassy.github.io/InteractiveWayToC.html>
<https://github.com/fraunhoferfokus/acsl-by-example>

verifast tutorial
<https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf>

<https://github.com/hwayne/lets-prove-leftpad>
vcc
ZetZZ <https://github.com/zetzit/zz> <https://news.ycombinator.com/item?id=22245409>
<https://news.ycombinator.com/item?id=23997128> dafny discussion
Verilog + symbiyosys,
KeY, KeymaeraX
CBMC, ESBMC <http://www.esbmc.org/> , EBMC
cpa-checker <https://cpachecker.sosy-lab.org/>
TLA might be in this category
Event-B alloy

<https://github.com/johnyf/tool_lists/blob/master/verification_synthesis.md> god this list is nuts
<https://www.pm.inf.ethz.ch/research/verifythis.html> verify this
<https://sv-comp.sosy-lab.org/2020/> sv-comp

<https://github.com/tofgarion/spark-by-example>

Eiffel for pre post conditions

<https://github.com/microsoft/Armada>
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

### Fun old timey books

If you go before 1980, a decent chunk of all books had assembly in mind.

- discpline of programming - djikstra <https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf>
- Reynolds - The craft of programming
- Knuth - The Art of Computer Programming
- The science of programming - D Gries
- Pascal, wirth
- structured programming <https://seriouscomputerist.atariverse.com/media/pdf/book/Structured%20Programming.pdf> djikstra hoare
- Eric Hehner
- <https://dl.acm.org/collections/classics> ACM classic books
- lambda papers
- per brinch hansen
- <https://en.wikipedia.org/wiki/List_of_important_publications_in_theoretical_computer_science#Formal_verification>
- <https://en.wikipedia.org/wiki/List_of_important_publications_in_computer_science>
- <http://www.mathmeth.com/read.shtml> some welevant EQD notes. Derivation of alogrithms
- winskel

# old model checking notes

---

author: philzook58
comments: true
date: 2020-11-19 21:28:58+00:00
layout: post
link: <https://www.philipzucker.com/?p=879>
published: false
slug: Model Checking - TLA+
title: Model Checking - TLA+
wordpress_id: 879
---

CFA control flow automata. Abstracting out control flow. An over approximation is that you can non detemirnstically take branches

Model checking
Software Model Checking for
People who Love Automata
<https://swt.informatik.uni-freiburg.de/staff/heizmann/2013cav-heizmann-hoenicke-podelski-software-model-checking-for-people-who-love-automata.pdf>
<http://www2.informatik.uni-freiburg.de/~heizmann/2010POPL-HeizmannHoenickePodelski-Nested_Interpolants-Slides.pdf>
nested interpolants hiezmann

interpolant mcmillan
BLAST and other jhala
<https://dl.acm.org/doi/10.1145/2858965.2814304> auomtating grammar compiarsno
file:///home/philip/Documents/coq/game/3434298.pdf - verifying context free api protoclls
java path finder
<https://ultimate.informatik.uni-freiburg.de/smtinterpol/news.html>
<https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/> - ultimate program analyzers
CPAchecker

Ivy
EPR a decidable fragment?
<https://twitter.com/wilcoxjay/status/1367698694988992513?s=20>
<https://graydon.github.io/ivy-notes/logical-fragment.html>

exists*forall* is decidable - cody mentions this is synthesis? Connection here?
Other fragments too. Monadic full first order logic (without function symbols?)
Goldfarb, Gurevich, Rabin, Shelah: all decidable and undecidable prefix classes completely characterized.

Modal logics are "robustly decidable" translation to first order has a particular guarded form

LTL vs CTL
Ok, I think I've got it. When you're model checking a CTL formula, you're checking a  single Tree |= CTL_formula, single entry in the entailment relation. But when you're model checking an LTL formula you're checking a family path paths p |= LTL_formula, a bunch of entries of the entailment relation.

Stuttering is important.
Stuttering is when y' = y.
It is this option which allows refinement.

Using Z3 I feel has a decent shot of being more scalable than the checking used by TLC, which as I understand it is brute force search for countermodels.

Back on the TLA+ train

- <https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf> Specifying Systems
- <https://pron.github.io/tlaplus>
- <https://github.com/cobusve/TLAPLUS_DeadlockEmpire>
- <https://www.learntla.com/introduction/>
- <https://github.com/tlaplus/Examples>

<https://news.ycombinator.com/item?id=14728226>

I find something very conceptually pleasing about making the program counter an explicit thing. Every language has things that are implicit. Powerful new languages constructs are often backed by runtime data structures. Even in "low level" languages like C, there is a whole lot of implicit stack shuffling. The stack exists. It is a data structure.
However, even in assembly I tend to take the program counter for granted most of the time. When you thnk about what the insturction `add` does, you don't tend to mention the movement of the program counter. It is so obvious that it increments to the next instruction that usually remains tacit.

<http://muratbuffalo.blogspot.com/2020/06/learning-about-distributed-systems.html>

5/2019

We're starting a reading group on TLA+ at work.

reifying the program counter

TLA+ is more of a spec or modelling language. No implicit temporal flow.

It actually is similar to verilog, which can be conisdered a layer underneath using a cpu. One needs to build a program counter to do what imperative programs do

pluscal is an imperative ish language that compiles to TLA+

Everything uses the TLA

If you don't use x', then tla is just a constraint satisfaction solver.

maybe x == x' as a constraint?

Hmm. One NQueens example actually writes out the brute force search algorithm. That's intriguing.

<https://github.com/tlaplus/Examples>

I have no idea how TLC is working

can encode relation R(x,x') into contraint solver. and also induction principle P(x) => P(x'). Difficult to know if you are in a reachable state though. Can unroll in time.

Keep track of possible states using BDD sturctur

Storm

Prism

nuSMV

SPIN

Kind model checker - SMT based and some other dtechnques. Takes in Lustre files which feel like some kind of verilog. I suppose you could model check with verilog too. Outputs rust (experimentally)

How does TLC work

It sounds like it does some kind of explicit state modelling?

<https://lemmster.de/publications/MSc_MarkusAKuppe_1497363471.pdf>

Thesis about TLC

Exlplicit state model checker. It actually is BFS the entire reachable state space?

Symbolic state model checker - BDD based storage of the set of states

Refinement model checker - Holds state space via abstraction?

<http://hackage.haskell.org/package/search-algorithms>

Seems lik it would be feasible to build an embedded model checker in haskell of this style

par combinators. Maybe lazily distribute out products.

<https://www.phil.pku.edu.cn/personal/wangyj/files/Teaching/Delta/16/haskell-and-mc.pdf>

<https://malv.in/2018/funcproglog/>

Petri nets keep showing up.

Binary Decision Diagrams for model checking

state-nextstate relation. Relation Algebraic perspective?

Decision Diagrams have a quasi applicative instance. The domain needs an Ord constraint. Useful when the range is small? (i.e. binary), but domain can be quite large. Map data structures are useful mostly for partial functions or for small domains.

The applicative instance is how you build ocmplicated BDDs from simple ones.

Decision diagrams let you dominate questions about functions. All sorts of queries become possible.

Sharing in Haskell

<https://jtobin.io/sharing-in-haskell-edsls>

Either store indices of shared locations

Could have a respresentable stored monad.

Fix of ExprF.

Use HOAS. Use explicit index locations (mockup of an internal pointer system). Use categorical DSL, use actual physical pointers

In catgoerical style, we need to explicilty state dup and join nodes. We will have both I think. Unless I build the trre from the ground up. I kind of have a stack.

Hillel Wayne's short tutorial

<https://www.learntla.com/pluscal/toolbox/>

He also has a book

<https://www.youtube.com/channel/UCUXDMaaobCO1He1HBiFZnPQ/videos>

<https://www.researchgate.net/profile/Mary_Sheeran/publication/220884447_Checking_Safety_Properties_Using_Induction_and_a_SAT-Solver/links/02bfe5110f2e5a50f8000000/Checking-Safety-Properties-Using-Induction-and-a-SAT-Solver.pdf>

Mary Sheeran et al. Checking safety properties using SAT solvers

Lava and Ruby papers

<https://github.com/Copilot-Language/copilot-theorem/blob/master/doc/talk.pdf>

This is a really good talk on bounded model checking. How to show it is complete. loop free paths. Find property being dissatisfied. Weaken Transition relation to allow more states if gives easier to reason theory. interval arithmetic in z3?

[http://elina.ethz.ch/](http://elina.ethz.ch/)

Fast polyhedral domain library. Intervals, octagons, polyhedral. has python bindings

PPL Parma polyhedral library. - <https://www.bugseng.com/parma-polyhedra-library>
Apron <http://apron.cri.ensmp.fr/library/>
I'm seeing a lot of ocaml bindings?
<https://github.com/yihming/aihaskell> -- not in awesome shape though
<https://github.com/bollu/simplexhc-cpp>
<http://polly.llvm.org/>
<https://pixel-druid.com/blog/> interesting blog
isl -- integer set library
<https://polyhedral.info/>

Relaxation ~ abstraction. We might want to relax an LP to an outer box. A box is easier towork on. Or octagons.

Relax Sat instance to 2-Sat
Bounded model checking - Transition relation, laid out in time. Check that you never rpeat a state.
Induction I[x] => P[x], P[x]/\ T[x,x'] => P[x']
Can strengthen induction in various ways? By rolling out in time?
Seahorn
FDR4
IC3 algorithm?
Operations Researhc/optimization - abstract interpetation
relaxation - abstraction
? - galois connection

- lattice
feasible - satisfiable

TLA+, SPIN, NuSMV are all model checkers

Simple programming systems or simple robots or distributed system, or AI and things can be simulated using the technique of finite automata.

Finite Automata have finite states and labelled transitions. You can choose to make the transition deterministic or nondeterministic, meaning it is obvious which edge to take or you still have some choices.

This automata perspective is useful for a couple things. If you wanted to implement your own regular expression evaluator it is useful. It is also a good persepctive for writing fpgas, or converting a program into a state machine for the fpga.

Your process has a register called the program counter (roughly corresponds to the line number in your program in a sense). Most of the numbers it manipulates are 64 bits. The program counter paired with the variable values can give you a finite state you can work with (especially if you are dynamically building data structures a la malloc).

The labelled arrow is somewhat like the monad arrow (a -> m b). This also makes sense in the context of kmett's comments during Foner's comonad talk.

The IO arrow is a catch all for all the nondeterminism possible. But perhaps making (-> m) a more first class object you could prove more?

Constructions on NFA:

Concat: Take any edge that leads to an accepting and bring it into the start state of the second automata

Union: Just place the automata side by side

Intersection: Product construction. Make states pairs of original states. Make actions go at the same time. Only accept if both states are accepting.

Star: Take any incoming edge to accepting state and loop it back to start states

Complement: Determinize NFA (see below) and swap accept and reject states.

with these combinators you could easily construct NFA from a regular expression. Just interpret the regular expression syntax tree.

Some useful derived operations include:

do n times: can just concat the epxression n times

one or more (+): concat the star with one instance

complement with respect to: complement and then intersect

Determinization - Make states the power set of the original states. Only need to keep the ones you actually can visit from the start state

The Algebra of Regular Expressions:

<http://www.cs.cornell.edu/courses/cs786/2004sp/>

Kleene Star is a geometric series. a* = 1 + a + a^2 + a^3 + ... ~ 1/(1-a). As usual, it is not clear that the right hand side has an interpetation

Matrix regular expressions

Derivatives of regular expressions

<https://people.mpi-sws.org/~turon/re-deriv.pdf>

<https://www.youtube.com/watch?v=QVdBPvOOjBA>

Buchi Automata and $latex \omega$- regular expressions

Buchi automata accept infinite strings.

They are also represented by transition diagrams, but the acceptance condition is now that a string is accepted if it passes through the accepting state infinitely often. Basically, this means the string has to get into a cycle.

LTL - Linear Temporal Logic. This is one logic for describing properties of a transition system. It consists of ordinary boolean logic combined with temporal operators, X F G and U (which are not necessarily independent of the others). Each state in the transition systems is labelled with which propositions are true in that state. $latex G \phi$ is true if that statement $phi$ is true on all possible states you could end up on forever. $latex F \phi$ is true if you always enter a state at some point for which $latex \phi$ is true. In other words $latex \phi$ is eventually true. $latex X \phi$ is true if in the next state $latex \phi$ is true.

# Old Sep Logic

<https://cs.nyu.edu/~wies/software/grasshopper/>
<https://github.com/wies/grasshopper>
"GRASShopper is an experimental verification tool for programs that manipulate dynamically allocated data structures. GRASShopper programs can be annotated with specifications expressed in a decidable specification logic to check functional correctness properties. The logic supports mixing of separation logic and first-order logic assertions, yielding expressive yet concise specifications."

<https://blog.sigplan.org/2020/03/03/go-huge-or-go-home-popl19-most-influential-paper-retrospective/>

There is a theme that "special" logics are implicitly talking about something. The two examples are temporal logics, which are implicitly talking about some kind of notion of time, and separation logic. I suppose intuitionistic logic could be put on the same pedestal.

Dynamic assertions of separation logic queries. Programmers like these. Can be written in host language. Can be turned off. Useful debugging and documentation tool. Gets people thinking about the right stuff. Lightweight verification.
Cody had the idea that garbage collectors must already be doing a lot of the work necessary.
Might be an interesting
&& is easy
(heap, bool) * (heap, bool)

emp _(x -> y)
x.head -> y is   ([x.head] , x.head === y)
emp is ([], true)
(x, a )_ (y, b) = ( x ++ y,  noverlap(xs, ys) && a && b )

nooverlap(  )

Using physical equality to reify the heap graph.

A language that is low level enough
What about a seperation logic fuzzer?

Shape analysis is talking about something similar. It tracks graphs <https://research.cs.wisc.edu/wpis/papers/cc2000.pdf>  Null? May alias, must alias, others. An abstract domain for heap states.

Abstract domain of other graphs. Armando had that one class.

Heaps as partial maps. Heaps as graphs?

strong equality

Points-to analysis

Compiling speration logic to Z3. I'd want to representy maps.
The big shift for me is that seperation logic wants to talk about partial maps/functions.

Choices for map:
association lists
Sets of tuples
Abstract definition with axioms

<https://stackoverflow.com/questions/52313122/map-data-structure-in-z3> dafny axioms for maps. Maybe use this to model
 <https://github.com/Z3Prover/z3/issues/811> pointers to seperation logic stuff in smt
viper has seperation logic?

Chris : Sequent and Hoarse are similiar
Could you intersperse tactics and commands? {A /\ B }split{A, B} drop A { B }
apply C x { x : B,  }
if() {} {}

What is logic?

Logic can mean discussion in prose the faculty of human reasoning.

Logic is manipulation of syntax according to rules that seem to demonstrate the truth of something to people. Syntax in my mind is typically a tree data structure. The rules are functions that can inspect the data structure and output a changed out if it fits their criteria. The things that i wish to prove are usually mathematuical statements.

Logic is ~ first order logic ~ boolean logic. If something feels like a small change from these, then i also accept it as a logic. This occurs transitively, so the subjects which I accept as logic are changing with time.

Logic is anything with horizontal bars.

What is physics? It's what physicist's do. The interests of people who call themselves physicist's diffuse over centuries. Perspectives widen.

The imperative curry howard correspondence. Chris put forward that the command in hoare logic is the analog of turnstile. What makes hoare logic a logic?

What makes a reduction relation not a logic? Is it a logic?

What is "the logic" and what are the subjects, the axioms?

The heap is modeled as a partial function. Concretely then, the heap can be modeled conveniently as a dictionary for the purposes of simulation or interpetation, which is a finite data structure familiar and readily available in most languages. `heap = {}`. The seperating conjunction is non-deterministic or slightly under specified in that it does not tell you how to split the dictionary. You'll need to perform search.

    <code>def split(d): # recusrive definition of all splits. 2^numkeys
       k = d.keys()[0]
       del k d
       for d1,d2 in split(d):
          yield d1+k, d2
          yield d1, d2 + k</code>

You can model program behavior inside a logic. Hoare logic is intuitively not a logic to me.

That something that is a framework for truth has explicit reference to a heap inside of it feels insane.

The easiest thing that sometimes feels so trivial or useful is to intrepet the syntax of a logical statement and see whther a particular example. For example $latex x >\gt 3$ is a statement that requires a value of x to interpret it's meaning. Another statement is $latex x \gt 4$.

The logic and the metalogic.

Separation logic vs temporal logic. In some light sense, seperation logic is a spatial logic kind of how temporal logic with time. Not the full properties of space, and not 2 or 3 or 4 dimensional space either.

Separation logic gives us lightweight partial functions for some purposes. Apparenlty it's about partial commutative monoids, for which combining definitions of partial functions is one useful example

We do not intrinisically want to support pointer airthmetic. We need not have references be integers. There are still interesting questions about aliasing

- Reynolds course  <https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html> Reynolds has a 2006 course as well <https://www.cs.cmu.edu/~jcr/seplogic.pdf> 2001 review paper
- <https://iris-project.org/tutorial-material.html> Iris tutorial
- <https://cacm.acm.org/magazines/2019/2/234356-separation-logic/fulltext> ACM survey ohearn
- <https://www.chargueraud.org/teach/verif/>
- VST, Bedrock
- Frama-C ?
- <https://www.youtube.com/watch?v=ZmqvuxORL88&list=PLiHLLF-foEez5Dis-VqoGcg3WepdMh4XT&index=25&ab_channel=MicrosoftResearchMicrosoftResearchVerified> OPLSS summer school 2016. Hoare triples as indexed monad.
- verifast, small foot
- <https://fbinfer.com/docs/separation-logic-and-bi-abduction/> facebook infer
- <http://staff.ustc.edu.cn/~fuming/papers/p97-cao.pdf> veryfing C in coq. some useful references

One way we understand what a logic is is by seeing what it is talking about. It's semnatics. The syntactical rules of the logic correspond with aspects of it's models

A very useful method for me to understand computer science and logic papers is to translate the inference rule style notation into some function or relation. Often a checker function is easiest. The syntax of computer science notation (see Guy Steele talk) is off putting and confusing to me. You can directly translate stuff into inductive relations in Coq often. What about prolog?

```
data Addr = Int -- Many choices here. It is interesting to consider a finite set of addresses
data Value = Addr Addr | Bool Bool 
data HeapProp = Star HeapProp HeapProp | Emp | Singleton Addr Value |
type Heap = Map Addr Value
hasprop :: HeapProp -> Heap -> Bool
hasprop (Star hp1 hp2) h = any [  hasprop hp1 h1 && hasprop hp2 h2  |  (h1,h2) <- split h ]
hasprop Emp h = isempty h
hasprop (Singleton p x) h = h == (singleton p x)

```

The sentences of HeapProp are are description language for sets of heaps.

We could equivalently think about logical sentences as describing sets of integers. The free variables of the sentence tell us what dimensionality of set of the integers we are describing. Closed formula are propositions. Open formula I dunno. <https://en.wikipedia.org/wiki/Sentence_(mathematical_logic)> , predicate. well formed formula. So formula involving emp are in some sense open formula. And this is why it may not make sense  to consider the assertions in isloation from the hoare reasoning. However, it is commonplace also to assume universal quantification as implicit over all remaining free variables. x < x + 1  is shorthand for forall x. x < x + 1. We implcitly unversally quantify over the heap.

[https://en.wikipedia.org/wiki/Bunched_logic](https://en.wikipedia.org/wiki/Bunched_logic)

A map can be built out of the following definitions: empty, singleton a b, and the disjoint union of dictionaries `union m1 m2` . An alternative definition might be empty, `add a b m`. This is the difference between cons and append.

A sentence made of only Emp,Singleton, and Star is specificed by exactly zero or one heap. If it's impossbiel because seperation tried to use the saem address there is no heap.

It is essential that the heap is treated as a partial map. In principle, memory is a total map of addresses to values.

Addresses may or may not be considered abstract entities. It is not quite clear to me if they must be capable of equality comparison, but certainly inequality and arithmetic are not necessary.

Now this language is not very interesting. We can spice it up however by adding existential quantifiers. Now we have sort of hidden explicit pointers. This gives us the ability to describe very similar heaps.

```haskell
data HeapProp = Star HeapProp HeapProp | Emp | Singleton Addr Value | Exists (p -> HeapProp)
hasprop (Exists hp) h = any [  hp k |  k <- keys h] -- ? Is this ok actually? Surely sometimes we must p to not be in the heap

-- is there a seperating quantifier?

hasprop (Disj hp1 hp2) h = hasprop hp1 h || hasprop hp2 h
hasprop (Conj hp1 hp2) h = hasprop hp1 h && hasprop h

hasprop (Not hp) h = not (hasprop hp h)

hasprop (Implies hp1 hp2) h = if (hasprop hp1 h) then (hasprop hp2 h) else True
hasprop (Wand hp1 hp2) h = all [  hasprop hp2 (merge h h1) |  h1 <- satisfies hp1] -- we have to check merge succeeds
```

But what if I wanted a set of heaps that didn't all have the same size? I need disjunction. `Disj (Singleton p x) Emp` describes a union on possibilities. In the sense that `hasprop hp` is a functional representation of a set of heaps, disj and conj take the union and intersection of these sets. Star takes the "merge" of the two sets.

```haskell

data Expr = Add Expr Expr | Var String | ReadRef p | 
data PointLang = Seq PointLang PointLang | Skip | SetRef Expr Expr |  
-- maybe get rid of var string and read
```

Hoare logic. You can consider features of programming languages in isolation. Assignment of variables. If then else control flow. Loops.

separation logic and ST. Could we build liquid haskell predicates?

# Old CHC / Invariants

### BTOR2

Btor is a model checking format supported by bitwuzla.

Hmm. Interesting.
So btor is intended for hardware model checking. There is a single transition relation. If you want more, you should model a program counter.
btormc is a boolector based model checker. It iteratively unwraps the state relation
K induction mode --kind
Refers to variables and calculations by number. Many operations are predicated on sort. You can repeat sort definitions
`20 sort bitvec 1` defines at 20 a bitvector sort of length 1

Ok doesn't allow duplicate symbol declaration
`21 state 20 fred` defines a symbol of sort "20" called fred

`22 add 1 4 2` add takes a sort. It isn't inferred. `eq` also takes a sort? Can it not be bitvec 1?

`b` bad states and `j` justice states?
bad, constraint, fair, output.
`constraint` lets you assume something (an invariant)
`input` for un constraied stuff

Yeah, it all makes sense. Especially in a hardware context.

How do you put suggested hand written invariants in?

```
; int i = 1, factorial = 1;
; assert (i <= 2 || !(factorial & 1));
; for (;;) {
;   factorial *= i;
;   i++;
;   assert (i <= 2 || !(factorial & 1));
; }
1 sort bitvec 4
2 one 1
3 state 1 factorial  ; defining 2 state variables
4 state 1 i
5 init 1 3 2      ; initialization of factorial= 1
6 init 1 4 2      ; initialization of i =  1
7 add 1 4 2       ; expression i + 1
8 mul 1 3 4       ; expression factorial * i
9 next 1 4 7      ; next state i = i + 1
10 next 1 3 8     ; this is setting factorial = factorial * i
11 ones 1         ; b1111
12 sort bitvec 1
13 eq 12 4 11     ; predicate i == b1111 overflow condition?
14 bad 13
15 slice 12 3 0 0
16 constd 1 3
17 ugt 12 4 16    ; comparing i > 3
18 and 12 17 15
19 bad 18
```

# Resources

[golem](https://github.com/usi-verification-and-security/golem)
[eldarica](http://uu.diva-portal.org/smash/get/diva2:1268767/FULLTEXT01.pdf) <https://github.com/uuverifiers/eldarica> [web](http://logicrunch.it.uu.se:4096/~wv/eldarica/) Impressive seeming examples.

```
• CEGAR and predicate abstraction, such as HSF [20],
Duality [30], and ELDARICA;
• IC3/PDR, such as the PDR engine in Z3 [21]. The algorithm implemented in SPACER [28] extends IC3/PDR by
maintaining both under- and over-approximations during
analysis;
• Transformation of Horn clauses, such as VeriMAP [13]
and Rahft [26];
• Machine learning, such as SynthHorn [33], FreqHorn
[17] and HoIce [11], which progressively drive concrete
invariant samples and use machine learning classification
techniques to find the inductive invariant.
```

[liquid fixpoint](https://github.com/ucsd-progsys/liquid-fixpoint) Not entirely sure what this is, but it is a solverified version of liquid haskell ish? Using liquid types as a horn clause problem specification language?

[cartesian predciate abstraction](https://swt.informatik.uni-freiburg.de/berit/papers/boolean-and-cartesian-....pdf)

[Analysis and Transformation of Constrained Horn Clauses for Program Verification∗](https://arxiv.org/pdf/2108.00739.pdf) Good review article. Bottom up CHC = DMT?

[higher order chc](https://github.com/penteract/HigherOrderHornRefinement) <https://research-information.bris.ac.uk/ws/portalfiles/portal/142259264/popl18_p253.pdf>
<https://github.com/hopv/mochi>
<https://github.com/hopv>
[Higher order PDR](https://dl.acm.org/doi/10.1145/3607831)
[HFL(Z) Validity Checking for Automated Program Verification](https://dl.acm.org/doi/abs/10.1145/3571199)

[magic set for chc](https://bishoksan.github.io/papers/scp18.pdf) [tools for chc](https://arxiv.org/pdf/1405.3883.pdf)
[solving constrained horn cluases using interpolation mcmillan Rybalchenko 2013](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf)
[Solving Constrained Horn Clauses Modulo Algebraic Data Types and Recursive Functions](https://www.youtube.com/watch?v=AGaYhwe-mYU&ab_channel=ACMSIGPLAN)
Forward vs backwards chaining. One could also consider a datalog like execution model.

Linear logic and CHC. Perhaps a more convenient language for frames.

<https://github.com/Z3Prover/z3/discussions/5093> Interpolants with CHCs and List. Using List to represent a stack. Seems reasonable.. Lists of questionable support.

Consider using sexp macro expansion to chc.

higher order model checking? Kobayashi?
There's some stuff here <https://ericpony.github.io/z3py-tutorial/fixpoint-examples.htm> that didn't register
See the bottom

<https://insights.sei.cmu.edu/blog/ghihorn-path-analysis-in-ghidra-using-smt-solvers/> ghihorn - using horn solver on ghidra pcode

(<https://www.youtube.com/watch?v=kbtnye_q3PA&t=677s&ab_channel=VSS-IARCS>)

[Constrained Horn Clauses: Z3 has kind of a prolog in it](https://www.youtube.com/watch?v=kbtnye_q3PA&t=677s&ab_channel=VSS-IARCS)

[Maurizio Proietti: Removing Algebraic Data Types from Constrained Horn Clauses… (IJCAR A)](https://www.youtube.com/watch?v=LUR_F8m7nnI&ab_channel=IJCAR-FSCD2020)
adtrem  - interestintg Program trasnformations from prolog can be used on CHC to remove or deforest annoying structures. mentions a CVC4+induction mode

[rusthorn](https://github.com/hopv/rust-horn) +holce?
[Towards Automatic Verification of Unsafe Rust with Constrained Horn Solvers](https://www.youtube.com/watch?v=yJQZ7sG8xSM&ab_channel=Rust)

Horn clauses are a logical view on the form of programs allowed in prolog programs. They can explained in a couple different ways. <https://www.youtube.com/watch?v=hgw59_HBU2A>
One way is to describe them as logical statements of the form `a /\ b /\ c /\ d -> e`, a conjunction of literals implying a single conclusion predicate. The reason this form is nice is because it lends itself to back-chaining. If we need to prove `e` we can look for all the rules that have `e` in their head and try them one byu one, recursively seeing if we can also backchain the rules requirements.
Alternatively we can easily drive the forward. We can look at each clause in turn, see if we satisfy the requirements, and if so add the conclusion to the database of things we know. This is roughly how a datalog program is typically run.
We can also throw variables into the mix and lift the `a/b/c/d/e` into being predicates.

There is a sense when you are constructing a normal z3 query that you need to be talking about a kind of fixed arena. You need to define enough variables to describe all the possibilities you want z3 to explore. If you have a query where a system could go down road A and take 20 steps and road B and take 3 steps, you need to spell out enough variables ahead of time to encode all these steps.

Quantifiers kind of let you get around this. There are different mechanisms in Z3 for working with quantifiers. One is the ematching engine that looks for patterns in the stuff you have lying around and instantiates forall quantifiers with those patterns. Another is the horn clause engine.

Constrained logic programming and constrained horn clauses are the same thing. The first name comes from the logic programming/prolog community and the second from the verification/smt solver community.
<https://www.metalevel.at/prolog/clpz> Basically, it seems you call it one or the other depending on whether you're tacking constraints onto a prolog implementation or a "prolog" onto some kind of constraint engine like an smt solver.

Z3 currently has a bounded model checker, datalog, and a mode called spacer as distinct engines for solving horn clauses. It has had different options such as the "duality" engine in the past that are now defunct.

I do say and feel that you need a rough picture of what a tool/library is doing to be able to use it.

The most obvious way to me to check a system is to unroll it out in time. This is bounded model checking (BMC). If it finds a counterexample, great! That's a real counterexample If not, well, you haven't proven anything that useful without more analysis. You probably have gained some confidence in the system though.

IC3/PDR (Property Directed Reachability) is a kind of model checking algorithm that doesn't unroll executions out into a giant query. Instead it maintains an approximate representation of reachable sets N step out in time. This representation is basically as a logical formula, which you can query and refine by using SMT queries. The spacer algorithm is some kind of twist on these algorithms.

### What is a query?

Z3 has a separate interface you can use to define prolog like rules, or you can phrase them in the ordinary smtlib interface and specify to use the horn solver. It is somewhat confusing that the return codes of `sat/unsat` mean opposite things depending on the mode you're using. Using the fixedpoint interface, `sat` means the query succeeded, like how a prolog query might succeed. This means there was a way to successfully chain together the horn clauses
<https://stackoverflow.com/questions/39403644/%E2%88%83-queries-and-%E2%88%80-queries-with-z3-fixedpoint-engine>

I rather like the perspective from Miller and Nadathur where they describe a prolog query as intuitinistic proof search. A query `p(X)` creates an executions that corresponds to a proof of `exists x. p(x)`

However prolog is usually considered in a background of classical logic, and Z3 certainly is a classical logic engine. A successful query is a proof of unsat by adding `(not p)` or equivalently `(=> p false)` from the perspective of the sat solver. It is trying to backchain a proof of `false` or forward chain finding `p` to be true and then immediately finding false. The resolution proof of false is the analog of <https://www.javatpoint.com/ai-resolution-in-first-order-logic>
The production of learned clauses is a form of resolution proof. The DRAT format records a trace of the SAT execution. It records the clauses you need to resolve together to make lemma clauses eventually leading to a contradiction.
Classically, if you want to prove `p`, a uniform way of doing so is to add `not p` as an assumption and try to prove false.

### Program Verification

Reachable

Just as you can write a functional program to emulate the execution of some imperative code or assembly, you can write a prolog program to do the same. In these pure languages, this is achieved by explicitly passing state as a parameter.

To actuallyl get the output state.
start(State, EndState) :- body_start(State, State1), block2(State1, EndState).
block2(State1, )

You could query a program to give back those states for which there is an error.

main_err(State) :- body_start(State, State1), block2_err(State1).
main_err(State) :- err_inside_main(State).
block2(State1)

How does one

```
for(int i = 0; i < 10; i++){ y += 5; }
```

```
main(Y) :- loop_entry(0, Y).
loop_entry(I, Y) :- I >= 10, loop_exit(Y).
loop_entry(I, Y) :- I < 10,  I1 = I + 1, Y1 = Y + 5, loop_entry(I1, Y1).  
```

```lisp
(define-fun main (Int Int) Bool)
(define-fun loop-entry (Int Int) Bool)
(define-fun loop-exit (Int Int) Bool)
```

## Tricks

- Tracking inputs.
- Product Program
- WP using let
- Program counter exists.
- Memory modelling -

"partial evaluations"
You can ask for the program counter to stay in a known set. This is an invariant
You can ask that only certain PC -> PC edges exist. This is more difficult. It requires remembering prev_PC? No, but not tracked through the predciate. Just put a ghost `prev_PC := PC` before every  
Once you know that you can fuse the firs program counter variables with the predicate itself. Then you havethe CFG flavored version.
You can also pre-fuse linear program flow.

Getting a counterexample - the counterexample is in the UNSAT proof. But you can instead try negating the initial condition clause and remove it's forall binder to expose the initial variables? But then the forall of each statement are a disaster. Hmm. Maybe flip Bad -> Good and make horn clauses equalities? Yeah. This doesn't work. nvm

<https://www.cs.stevens.edu/~ejk/papers/cav21-preprint.pdf> - relational verficiation using some enhancement on CHC

I guess the most basic version of invaraint generation is to use an abstract interpetation. If the invaraint falls within the epxressive power of the abstract domain and it terminates (not too much erroenous widening) Then you can discover invaraints in the abstract domain.

Z3, eldraica, hsf?

<http://theory.stanford.edu/~nikolaj/nus.html> - Bjorner talk

<http://seahorn.github.io/blog/>
<https://github.com/seahorn/seahorn-tutorial>

<https://www.youtube.com/watch?v=yJQZ7sG8xSM&ab_channel=Rust> - horn clasues generation from rust - eldarica

<https://www.cs.utexas.edu/~tdillig/cs395/esc-houdini.ps> houdini leino and flanagan.
<https://www.cs.utexas.edu/~isil/fmcad-tutorial.pdf> abduction
<https://theory.stanford.edu/~aiken/publications/papers/pldi19.pdf>

# Ideas

How to help along the solver.
I think, maybe, that if you can guess parts of the invariant that helps.
(declare-const pvar )
(define-fun p ()   (and known_invariants pvar )

This goes into both heads an bodies. Is that okay?
Or have a reach-exit, reach-entry split.
Fill this in with info from user annotation and abstract analysis.

isil dillig - mistral an abduction generating smt solver?
On LIA, get minimal satisyinfyng assignemtn (pins least variables) and quantifier eliminate the rest

Interesting z3 tidbit - use unsat core to get minimal satisfying assignment
unsat core tricks in general are something to think about.
Partial models to avoid the else case <https://stackoverflow.com/questions/41425514/partial-assignments-in-z3>

<http://www.cs.cmu.edu/~aldrich/courses/17-355-19sp/notes/slides27-daikon.pdf> - daikon - dynamic checking of guessed invaraints. Fuzzing basically.

C2I
LoopInvGen
ICE-DT
CODE2Inv

CHC clauses allows us to get predictaes out. These predicate solutions are over approximations of possible state sufficient to satisfy the problem.

<https://arxiv.org/abs/2002.09002> rusthorn. Trick involving old new values to model borrowing from creusot talk

<https://arieg.bitbucket.io/pdf/gurfinkel_ssft15.pdf>
IC3/PDR

deadlock empire using CHC? Well deadlock empire has counterexamples.

Recursion and Loops are where it comes handy. We can reduce the straight line behavior (and branching) with ordinary wp. But the loops are tougher.
Function calls may not be recursive of course. If we previously establidshed

Keeping overapproximations of Reachable sets.
Generalize counterexamnple and push them backwards

Z3 implementation.
<https://github.com/pddenhar/Z3-IC3-PDR>

really nice description
<http://www.cs.tau.ac.il/~msagiv/courses/asv/IC3.pdf>

ic3/pdr vs interpolation based
use unsat cores

<https://github.com/Z3Prover/z3/blob/master/examples/python/mini_ic3.py>

There is some interpolation happening in SPACER

The SAT version
Maintain cnf fomrulas (sets of clauses)for each time step
A cube = an assignment = a conjunction of literals.
We manitain a queue of counterexamples
If the counterexample is in F0, then we found a bad trace
NewLemma - take negation of counterexample.. This is candidate clauses (possibly we may delete some literals). We want to exclude an errant counterexample.

Push - pick a clauses in Fi. split it into two pieces. if a subpiece is not in Fi+1
unfold - we initialize a new Fi to have no clauses (no constraints). Candidate will pick any bad state now.
Predecessor- m0 and m1 is a combined state picked. m1 -> m means we may add literals to m. We need to find a state that ends up in m. We pushed the counterexample backwards. That makes sense. And we might find multiple.
Requeue - if this counterexample can't be reached from previous guy, push it forward.

```python
init = And(p, q, r, yada)
sets = [init]

def check_unreachable():
  for F, Fn in zip(sets, sets[1:]):
    if check(Implies(Fn,F)):
      retrun True
  return False



queue = []
while true:
  check_reachable()
  check_unreachable
```

So if I used spacer naively with a predicate per programs point, each would be solved in the PDR manner.

Hmm. So the horn clauses don't give you anything in regards to wp itself. They are useful for interprcoedural and invaraints?

Interesting stuff in here.
Locking examples.
Concurrency
In raw smtlib but also using tool
<https://github.com/seahorn/seahorn-tutorial>

Hmm. The tutorial shows the block-like CHC form
But then takes macro steps using wp to fuse out?

Hmm. So the horn clauses aren't because they are a natural modelling framework, but because they have a natural solution method.

CHC and CLP are the same thing, different communities

init -> inv
inv /\

<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-yurifest.pdf>

Maybe there is some connection to the datalog stuff?
One predicate per line of program?
Or you could have program point as varaible?

Lifting blocks to clauses. How would one model a control flow diagram in prolog?
block1in(x') :- blockout(x) /\ blocktransition(x,x')

blockin(x) :- (blockout( wp()  ))

block1in :- block7out

which direction should be in/out? depends on wp vs sp?

Alternatively an explciit variable for control point block(n, )

Or should entire block be a predicate?
block(invars, outvars) :- blocka(outvars, invars')

<https://www.youtube.com/watch?v=bTPSCVzp1m8&ab_channel=WorkshoponSoftwareCorrectnessandReliability2013>

The expnasion / unrolling operator.

<https://arxiv.org/abs/2104.04224> - A theory of heap[s for cxonstrained horn clauses

Houdini dillig
daikon - random execution traces infer stuf
"invasraint inference"
Aiken - <https://ti.arc.nasa.gov/m/events/nfm2013/pubs/AikenNFM13.pdf> "sounds like daikon"
Notes on z3 codebase
muz = muZ. fixedpoint solvers.
There are a vairety

PDR / IC3 always come up.
I should try to know what those are

Meta foregin code base techniques

- checkout build files - Gives a hierarchy of the structure of the project. Dependency sorted.
- checkout tests

muz has: datalog, bmc, and spacer mode, and xform?
:print-certificatie fives "inductive invataint" even in datalog?

[data driven horn clause solver](https://www.cs.purdue.edu/homes/suresh/papers/pldi18.pdf). They use decision trees?
That's interesting. What about a scikit-learn loop,
Or polynomial fitting?
Good invariants candidates over bit vectors? That cbat thing sounds kind of good.
One of those domains. There was also that thing. That paper for comparative whatever that was guessing useful conditions inside.

[houdini](https://www.cs.utexas.edu/~isil/cs389L/houdini-6up.pdf)

Constrained horn clauses

<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf>

<https://chc-comp.github.io/>

<https://spacer.bitbucket.io/>

<https://seahorn.github.io/>

<https://theory.stanford.edu/~arbrad/papers/Understanding_IC3.pdf>

Programming Z3 tutorial
Spacer jupyter tutorial <https://github.com/agurfinkel/spacer-on-jupyter/blob/master/Dagstuhl2019.ipynb>
<https://arieg.bitbucket.io/pdf/synasc2019.pdf>

IC3 / PDR unbounded model checking

This is somehow more than a prolog. It's inferring *predicates*

<https://people.eecs.berkeley.edu/~sseshia/219c/#books> modelchecking course.

Subgoal induction. ??? Seems tailor fitted to CHC. From Mitchel Wand paper refernces to Morris paper
"inductionless induction / narrowing" are the things cody seemed to find this reminsent of

Wait, so SAT is solving the problem, but unsat is a counterexample trace?

```python
from z3 import *
x = BitVec("x",16)
x1 = BitVec("x'",16)
s = SolverFor("HORN")
i16 = BitVecSort(16)
Inv = Function('mc', i16, BoolSort())

'''
x = 0
while(x < 10)
  x++
assert(x < 11)
'''
init = ForAll(x, Implies(x == 0, Inv(x)))
loop = ForAll([x,x1], Implies( And(x < 10, Inv(x), x1 == x + 1), Inv(x1) ) )
post = ForAll(x, Implies(Inv(x), x < 11)) #ForAll(x, Implies(And( x < 11 , Inv(x)), False)) 

s.add(init, loop, post)
s.check()
s.model().eval( Inv(x) )
```

You can use horn clauses to perform craig interpolation.
A => I
I /\ B => False
Hmmmmmm. But what do you use craig interpolation for?
IC3 I think. You can build over approximations of intermiedate sets.

Running a prolog query:

forall(x, plus(s(x), ) )
plus(x,y,z) => False
Or
True => plus(x,y,z) ? with no quantification?
