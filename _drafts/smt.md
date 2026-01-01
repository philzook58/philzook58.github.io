---
marp: true
---

# Satisfiability Modulo Theories

---

# Overview

- Glue together decidable domain specific solvers
  - SAT solver
  - E-graph
- SMT moves up from what is obviously doable / decidable. Make it fast. Simple at scale can crush complex but slow sometimes.

---

# Demo

```
x = z3.BitVec("x", 32)
s = z3.Solver()
s.add(z3.Not(x | x == x))
s.check()
```

```
x,y,z = z3.Ints("x y z")

```

---

# Uses

- Theorem proving
- Symbolic Execution - show asmc
- Alive translation validation
- Synthesis
  - Ruler
  - CF blog post <https://pypy.org/posts/2024/07/finding-simple-rewrite-rules-jit-z3.html>
- Package Management
- Denis yurichev <https://smt.st/>

---

# Syntax and Semantics

---

# What do they give you

- SAT
  - Models - CounterExamples, Holes, Parameters, Solutions
- UNSAT
  - Unsat cores
  - Proofs

# Minimal Models

- The model returned by z3 is basically an egraph. Not a minimal egraph.
- Incompleteness

---

# SAT Solving

- Triumph of automated reasoning
- Abstract theory propsitions as `p`.
- Deemphasize
- Reduce to a conjunction of literals
  - Disjunctive normal form
  - Brute loop Search
  - Backtracking
  - Conflict Driven Clause Learning (CDCL)

---

---

# Theories

- Atomic equality
- Uninterpreted Functions
- Arithmetic
  - Intervals
  - Linear Eqaulity
  - Two Variable
  - Simplex
  - Tractable theories often show up in abstract interpretations
- Bitvectors
- Arrays
- Algebraic Datatypes
- Sequences

---

# Theories

- Theories are an API
- Theories as sets of formulas

---

# Theories and Abstract Interpretation

- Communities have their own perspectives

- Intervals
- Octagon domain
- Polyhedral domain

---

# Theory Combination

- Nelson-Oppen
- Shostak

---

# Nelson Oppen

- Purify
- Guess arrangement `=` `!=`
- Propagate

---

# Theory Interface

---

# Resources

- de Moura Slides
- Tinelli Review
- Bjorner Slides <https://www.youtube.com/watch?v=TgAVIqraCHo&t=227s>
-
