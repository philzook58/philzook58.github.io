---
layout: post
title: Imperative Proving
---
- [Hoare Logic](#hoare-logic)
- [Weakest Precondition](#weakest-precondition)
- [Why3](#why3)
- [Boogie](#boogie)
- [Dafny](#dafny)
- [Model Checking](#model-checking)
  - [ESBMC](#esbmc)
  - [cpachecker](#cpachecker)
- [Misc](#misc)
    - [Fun old timey books.](#fun-old-timey-books)
- [old model checking notes](#old-model-checking-notes)
  - [wordpress\_id: 879](#wordpress_id-879)

See also notes on:
- Model Checking
- SMT
- separation logic
- CHC invariant generation

# Hoare Logic
https://en.wikipedia.org/wiki/Hoare_logic
I have heard somewhere that actually we should distinguish Floyd's work on flow charts as something different. Maybe in a Lamport paper?

Axiom schema

Prpositionbal hoare logic - see KAT


# Weakest Precondition


# Why3

frama-C
[why3 implemtnation of stackify](https://gitlab.inria.fr/why3/why3/-/merge_requests/453)
Stackifty algorithm of llvm for wasm
# Boogie
<https://boogie-docs.readthedocs.io/en/latest/index.html>
# Dafny



# Model Checking
https://github.com/kind2-mc/kind2 takes in lustre. Multiple smt backends. ocaml implementations of ic3 and invarait
https://kind.cs.uiowa.edu/kind2_user_doc/1_techniques/1_techniques.html
SV-comp https://sv-comp.sosy-lab.org/2022/
Based on these results, given that I don't know shit, looks like cpachecker is a reasonable default if you're gonna pick one

veriabs - wins in reachability. Can you even buy it?

ADA Spark




TLA

Seahorn

## ESBMC


## cpachecker






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
https://kframework.org/index.html

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

# old model checking notes
---
author: philzook58
comments: true
date: 2020-11-19 21:28:58+00:00
layout: post
link: https://www.philipzucker.com/?p=879
published: false
slug: Model Checking - TLA+
title: Model Checking - TLA+
wordpress_id: 879
---

CFA control flow automata. Abstracting out control flow. An over approximation is that you can non detemirnstically take branches



Model checking
Software Model Checking for
People who Love Automata
https://swt.informatik.uni-freiburg.de/staff/heizmann/2013cav-heizmann-hoenicke-podelski-software-model-checking-for-people-who-love-automata.pdf
http://www2.informatik.uni-freiburg.de/~heizmann/2010POPL-HeizmannHoenickePodelski-Nested_Interpolants-Slides.pdf
nested interpolants hiezmann

interpolant mcmillan
BLAST and other jhala
https://dl.acm.org/doi/10.1145/2858965.2814304 auomtating grammar compiarsno
file:///home/philip/Documents/coq/game/3434298.pdf - verifying context free api protoclls
java path finder 
https://ultimate.informatik.uni-freiburg.de/smtinterpol/news.html
https://monteverdi.informatik.uni-freiburg.de/tomcat/Website/ - ultimate program analyzers
CPAchecker

Ivy
EPR a decidable fragment?
https://twitter.com/wilcoxjay/status/1367698694988992513?s=20
https://graydon.github.io/ivy-notes/logical-fragment.html

exists* forall * is decidable - cody mentions this is synthesis? Connection here?
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


  * https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf Specifying Systems
  * https://pron.github.io/tlaplus
  * https://github.com/cobusve/TLAPLUS_DeadlockEmpire
  * https://www.learntla.com/introduction/
  * https://github.com/tlaplus/Examples

https://news.ycombinator.com/item?id=14728226

I find something very conceptually pleasing about making the program counter an explicit thing. Every language has things that are implicit. Powerful new languages constructs are often backed by runtime data structures. Even in "low level" languages like C, there is a whole lot of implicit stack shuffling. The stack exists. It is a data structure.
However, even in assembly I tend to take the program counter for granted most of the time. When you thnk about what the insturction `add` does, you don't tend to mention the movement of the program counter. It is so obvious that it increments to the next instruction that usually remains tacit.


http://muratbuffalo.blogspot.com/2020/06/learning-about-distributed-systems.html


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

https://github.com/tlaplus/Examples

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

https://lemmster.de/publications/MSc_MarkusAKuppe_1497363471.pdf

Thesis about TLC

Exlplicit state model checker. It actually is BFS the entire reachable state space?

Symbolic state model checker - BDD based storage of the set of states

Refinement model checker - Holds state space via abstraction?

http://hackage.haskell.org/package/search-algorithms

Seems lik it would be feasible to build an embedded model checker in haskell of this style

par combinators. Maybe lazily distribute out products.

https://www.phil.pku.edu.cn/personal/wangyj/files/Teaching/Delta/16/haskell-and-mc.pdf

https://malv.in/2018/funcproglog/


Petri nets keep showing up.


Binary Decision Diagrams for model checking


state-nextstate relation. Relation Algebraic perspective?


Decision Diagrams have a quasi applicative instance. The domain needs an Ord constraint. Useful when the range is small? (i.e. binary), but domain can be quite large. Map data structures are useful mostly for partial functions or for small domains.


The applicative instance is how you build ocmplicated BDDs from simple ones.


Decision diagrams let you dominate questions about functions. All sorts of queries become possible.


Sharing in Haskell


https://jtobin.io/sharing-in-haskell-edsls


Either store indices of shared locations


Could have a respresentable stored monad.


Fix of ExprF.


Use HOAS. Use explicit index locations (mockup of an internal pointer system). Use categorical DSL, use actual physical pointers


In catgoerical style, we need to explicilty state dup and join nodes. We will have both I think. Unless I build the trre from the ground up. I kind of have a stack.


Hillel Wayne's short tutorial


https://www.learntla.com/pluscal/toolbox/


He also has a book


https://www.youtube.com/channel/UCUXDMaaobCO1He1HBiFZnPQ/videos


https://www.researchgate.net/profile/Mary_Sheeran/publication/220884447_Checking_Safety_Properties_Using_Induction_and_a_SAT-Solver/links/02bfe5110f2e5a50f8000000/Checking-Safety-Properties-Using-Induction-and-a-SAT-Solver.pdf



Mary Sheeran et al. Checking safety properties using SAT solvers



Lava and Ruby papers




https://github.com/Copilot-Language/copilot-theorem/blob/master/doc/talk.pdf




This is a really good talk on bounded model checking. How to show it is complete. loop free paths. Find property being dissatisfied. Weaken Transition relation to allow more states if gives easier to reason theory. interval arithmetic in z3?



[http://elina.ethz.ch/](http://elina.ethz.ch/)



Fast polyhedral domain library. Intervals, octagons, polyhedral. has python bindings



PPL Parma polyhedral library. - https://www.bugseng.com/parma-polyhedra-library
Apron http://apron.cri.ensmp.fr/library/
I'm seeing a lot of ocaml bindings?
https://github.com/yihming/aihaskell -- not in awesome shape though
https://github.com/bollu/simplexhc-cpp
http://polly.llvm.org/
https://pixel-druid.com/blog/ interesting blog
isl -- integer set library
https://polyhedral.info/



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


http://www.cs.cornell.edu/courses/cs786/2004sp/


Kleene Star is a geometric series. a* = 1 + a + a^2 + a^3 + ... ~ 1/(1-a). As usual, it is not clear that the right hand side has an interpetation


Matrix regular expressions


Derivatives of regular expressions


https://people.mpi-sws.org/~turon/re-deriv.pdf


https://www.youtube.com/watch?v=QVdBPvOOjBA


Buchi Automata and $latex \omega$- regular expressions


Buchi automata accept infinite strings.


They are also represented by transition diagrams, but the acceptance condition is now that a string is accepted if it passes through the accepting state infinitely often. Basically, this means the string has to get into a cycle.


LTL - Linear Temporal Logic. This is one logic for describing properties of a transition system. It consists of ordinary boolean logic combined with temporal operators, X F G and U (which are not necessarily independent of the others). Each state in the transition systems is labelled with which propositions are true in that state. $latex G \phi$ is true if that statement $phi$ is true on all possible states you could end up on forever. $latex F \phi$ is true if you always enter a state at some point for which $latex \phi$ is true. In other words $latex \phi$ is eventually true. $latex X \phi$ is true if in the next state $latex \phi$ is true.
