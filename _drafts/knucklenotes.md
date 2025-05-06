
Other features
Actually impressive things?

Listing all the sorts of things z3 can prove

maybe lose the group examples

```
G = z3.DeclareSort("Group")
mul = z3.Function("mul", G, G, G)
e = z3.Const("e", G)
inv = z3.Function("inv", G, G)
x, y, z = z3.Consts("x y z", G)
mul_assoc = z3.ForAll([x, y, z], mul(x , mul(y,  z)) == mul(mul(x, y), z))
id_left = z3.ForAll([x], mul(e, x) == x)
inv_left = z3.ForAll([x], mul(inv(x), x) == e)

inv_right = z3.ForAll([x], mul(x, inv(x)) == e)
#z3.prove(z3.Implies(z3.And(mul_assoc, id_left, inv_left), inv_right), timeout=1000)
```

```

# https://en.wikipedia.org/wiki/Group_(mathematics)
G = smt.DeclareSort("G")
mul = smt.Function("mul", G, G, G)
e = smt.Const("e", G)
inv = smt.Function("inv", G, G)

kd.notation.mul.register(G, mul)

x, y, z = smt.Consts("x y z", G)
mul_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
id_left = kd.axiom(smt.ForAll([x], e * x == x))
inv_left = kd.axiom(smt.ForAll([x], inv(x) * x == e))

# The Calc tactic can allow one to write explicit equational proofs
c = kd.Calc([x], x * inv(x))
c.eq(e * (x * inv(x)), by=[id_left])
c.eq((inv(inv(x)) * inv(x)) * (x * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * ((inv(x) * x) * inv(x)), by=[mul_assoc])
c.eq(inv(inv(x)) * (e * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * inv(x), by=[id_left])
c.eq(e, by=[inv_left])
inv_right = c.qed()
```

pf = kd.prove(x == x)
type(pf)

kd.utils.alpha_eq(smt.ForAll([x], x + 0 == x), smt.ForAll([y], y + 0 == y))

# Applications

Examples? I want to talk about stuff that isn't just applications Sheffer stroke

- Software foundations
- Ghidra pypcode
- Verilog - smt importing
- Sympy
- Arb

## Reflection

```
import kdrag.reflect as reflect

@reflect.reflect
def fact(x : int) -> int:
    if x <= 0:
        return 1
    else:
        return x*fact(x-1)
```

Sometimes just shear scale of queries.

All of these are reasons

1. To go interactive
2. Distinguish proven formula

# Motivation

SMT solvers are really cool and powerful. They are the basis of

You can quickly and automcially verify properties of bitvectors and other such things (show a couple quick examples)

bitvector tricks
hillel random prng reverser
Geometric theorems.

Can z3 do Gropu theory in one shot?

Show a huge smtlib dump of some aweful problem

Although even if we had some great oracle that could answer all ourt questions yes or no, it would still be valuable and enjopyablke to understand why sometimes.

```markdown
∀x:T, P(x) True      t : T
--------------------------------- instan
         P(t) True
```

```markdown
t1 True  t2 True ....    Not(Implies(And(t1,t2,...), t)) unsat    
---------------------------------------------------------------- prove
                           t True
```

```markdown
    t : T       P : T -> Bool    T inductive 
----------------------------------------- datatype induct
     (/\_{C_T} (∀y, P(y) => P(C(y)))) => P(t) True
```

As an example

```
      t : Nat      
-------------------------------------------------- Nat induct
  (P(Z) /\ (∀y, P(y) => P(Succ(y)))) => P(t) True
```

# System Comparison

- Isabelle
- Lean/Coq
- ACL2
- Why3 / Boogie

import kdrag.theories.logic.intuitionistic as intuitionistic
import kdrag.theories.logic.temporal as temporal

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

# Bits and Bobbles

```markdown
          P(t) True
--------------------------------- ∃I
        ∃x P(x) True
```

The world is a big place. Part of how to work in it is to Jeet Kune Do on what already exists or is popular.

Software and Hardware verification boils down to a bucnh of SMT queries with handwaving in between
I found myself writing a sequence of smt calls and then knowing that I'm reusing previous proved stuff

What is knuckeldragger 1 slide

1. The shallowest possible layer over z3 to make it compsoablte a proof system
The fumbest thing that could work

z3 prove is
def prove(e : smt.BoolRef) -> bool:
    s = smt.Solver()
    s.add(smt.Not(e))
    smt.check()
    if s.check() == smt.unsat:
        return True
    else:
        return True
boolean blindness

a parse tree is a trace of a maethod that says is there a valid parse.

Certificates of the SMT processes is hard.
The meta chainsing of SMT calls is not that hard.

Exhuastively failing to find counterexamples.

LCF style theorem proving
3/2 types formulas expressions and proof
Anything goes on terms
pf -> tm
details of proof don't matter, but basically they are recording the call tree that produced them.
inference rules ~ functions
COmplete erasure pf ~ tm is fine

The big inference rule is

t1 proved  t2 proved ...     Not(t1 /\ t2/\ t3 => t)  z3unsat
---------------------------------------------------------

                      t proved
mega modus ponens

But not actually

Definitions
Quantifier Instantiation
Induction

Tactics

Why python?
What are proofs

# Subsystems

- Reflection
- Quickcheck
- Typeclasses
- Generics

# Applications
