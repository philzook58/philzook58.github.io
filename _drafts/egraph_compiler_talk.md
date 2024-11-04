---
marp: true
---

## Egraphs and Compilers

 A Tapas

Philip Zucker

---

# Greedy Simplification

Equations are great.

---

## Egraphs

What are the?

- store multiple equivalent versions of trees in compact representation

---

### Sharing

Compelling from a data structure perspective

a *(b + c) = a* (c + b)

Shallow sharing is easy.
Deep sharing

note: Look at egg video for tips

---

### Theorem Proving

Congruence Closure
Ground kb
SMT solvers
EMatching

---

### Equality Saturation

- Rules are ematched
- Equations asserted into egraph
- Extract out best term
- Egraph only grows. We only learn. Monotonic.

---

## Egglog

Program analysis and datalog
What is datalog
Program analsyis
Fixed points
graphs

Why was I initially interested

Conditional rewrite rules. Conditional optimizations. Liveness

---

## What are compilers

Maybe start at high dsl stuff

---

## Domain Specific

---

### Tensors

Tensor canonizaliation

glenside

Strcuture of compiler
front end
middle end
back end

Optimization diagram from muchnick

---

### Block Level

inlining
CFG

---

### Global Code Motion

What is SSA? A functional sublanguage

general purpose IRs

---

#### superblocks

---

#### cranelift aegraph

---

#### pegs

---

#### rvsdg

---
IR types: rvsdg, ssa cfg

speciality IRs
---

### GVN

You already had an egraph in your compiler

---

### Instruction Selection, Register Allocation, Scheduling

Instruction Selection and Extraction
Compiling with Constraints

What is a SAT/SMT/CSP solver (I don't know what kind of audience I have)

Unison
VIBES

Pluses
Minuses

ISLE

---

### Vectorization

instruction selections
diospyros

---

### Peephole  Optimization

Linear IRs
Denali
Linear
Sequential first

---

# What am I excited about

Features upcoming  (stuff i said in pldi talk)

- slotted
- colored
- destructive rewrite rules
- refinement - alive2 smtgcc

Egraphs modulo theories
Knuth bendix for compilers

---

# Bits and Bobbles

If I have 10 days to get numbers to prove my points, what would I do?

# Automated Reasoning for Compilers

Simplification mode vs proving mode

Knuth bendix completion

---

## Bitter Pills

Hmm. This compiler pessimism is not universal.
Maybe don't do this

<https://proebsting.cs.arizona.edu/law.html>
Proebsting's Law: Compiler Advances Double Computing Power Every 18 Years

<https://blog.regehr.org/archives/1515> Compiler Optimizations are Awesome <https://news.ycombinator.com/item?id=14453962>

- LLVM and GCC are insane

- Flexibility
- Simplicity. How many man years
- Declarativeness and trustworthiness
- enable Higher level abstractions at low cost

Parallelism. All your FLOPS are in your tensor processing units.

Frances Allen optimizations
