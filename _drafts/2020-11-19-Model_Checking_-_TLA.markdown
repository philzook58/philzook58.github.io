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

Back on the TLA+ train


  * https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf Specifying Systems
  * https://pron.github.io/tlaplus
  * https://github.com/cobusve/TLAPLUS_DeadlockEmpire
  * https://www.learntla.com/introduction/
  * https://github.com/tlaplus/Examples

I find something very conceptually pleasing about making the program counter an explicit thing. Every language has things that are implicit. Powerful new languages constructs are often backed by runtime data structures. Even in "low level" languages like C, there is a whole lot of implicit stack shuffling. The stack exists. It is a data structure.
However, even in assembly I tend to take the program counter for granted most of the time. When you thnk about what the insturction `add` does, you don't tend to mention the movement of the program counter. It is so obvious that it increments to the next instruction that usually remains tacit.




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
