
# Motivation

SMT solvers are really cool and powerful. They are the basis of

You can quickly and automcially verify properties of bitvectors and other such things (show a couple quick examples)

bitvector tricks
hillel random prng reverser
Geometric theorems.

Can z3 do Gropu theory in one shot?

Show a huge smtlib dump of some aweful problem

# What is it?

- Interactive theorem prover  as a library in Python

- A library
- An interactive theorem prover in Python
- Maximally shallow wrapping around Z3
- Rigorous chaining of SMT solves
- Piles of little logical gizmos (rewriters, unifiers, printers, etc)

- Piles of little logical gizmos (rewriters, unifiers, printers, etc)

- Maximally shallow wrapping around Z3

I've spent a lot of time playing around with amt solvers

A large fraction of Automated Software verification is turning code into a sequence of smt calls to sEARCH FOR counterexamples. An unsat says there are not countrwxAMPLES AND a sat is a counterexample.

The language of smt is a barebones first order-ish logic. The emphasis is on the ability to meet decision prcosdured in the middle. SMT is an IR.

The lagguage of smt is far more expressive than the solvers are powerful. This is a fundamental feature of the lanuage. The language can express for example Fermat's problem or factoring of large integers or equational theories that can encode the word problem.

A low barrier proof assistant.

The mottivation

1. Language choice is a different axis than formal methods.

2. I have built or been part of teams that uilt binary verifiers. I have spent a lot of time coaxing.

3. How far can boring logic + fully featured metaprogramming go?

4. Building theories that go beyond what the solver can do i one shot, optimizating formulations. Is my formulation the same?

4. FFI problems. Every itp basically does it's thing for various reaosns (aesthetic, dogmatic, practical). But SMTsolvers are extremely successful and people want to make tactics. Why the runaround?

5. Shallow emdedded theorem proving. Strong host language with all the gizmos.
