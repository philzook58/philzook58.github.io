---
marp: true
paginate: true
theme: gaia
---


<!--
Tasks:
- review papers
- make diagram
- expand egraph basics section

## EGraphs and Compilers: Good and Getting Better
-->
## Egraphs, Compilers, and YOU

<style scoped>
p { text-align: center; }
</style>
![width:10cm](/assets/eggman.webp)
Philip Zucker

---

# ToC

- Equations and EGraphs
- Compiler Tapas
  - Cranelift
  - Egglog
  - Tensors
  - Kernels  
- Improvements
  - AC, polynomials, and linear expressions
  - Controls Flow
  - Context and Refinement

<!-- 
Baking Theories into EGraphs

What's missing

and Automated Reasoning

Baking in

 Modulo Theories

- Wrinkles
- Loops
- Backend
Automated re
- Local Optimizationsasoning and compilers
AR -> Simplifiers
The fully declarative compiler

The dust isn't settled.

I'm excited to give this talk.
I think egraphs are fun.
Tool in the toobox
Green
reduce human misery
save money
save time
more declarative

-->

---

# Equations are Great

- $1 + 2 = 3$
- $x + 0 = x$
- `x * 16 = x << 4`
- $x \times 0 / 0 = x$ :raised_eyebrow:
- `select(store(mem,p,v),p) = v`
- ($A \otimes B) \cdot (C \otimes D) = (A \cdot C) \otimes (B \cdot D)$
- `(map f) . (map g) = map (f . g)`

<!-- 
Compact and beautiful are correlated with efficient and effective.

Mathematics in engineering and physics
Compilers
Rchily expressive
- \int u dv = uv - \int v du
- \sum_i \sum_j a_{ij} = \sum_j \sum_i a_{ij}

- Relation algebra
- peephole

https://leahneukirchen.org/caudex/equational-reasoning.html
http://www.mathmeth.com/read.shtml
https://inst.eecs.berkeley.edu/~cs294-260/sp24/2024-01-24-haskell-rewriting 
deforestation
-->

<!--
---

# Compiler

- Frontend - parsing
- Middle end - IR transformations
- Backend
  - Instruction selection
  - Register Allocation
  - Scheduling
  - Peephole

-->

<!--
If I were to nanopass it I'd go the other way.
 -->

<!--
---

# Middle End Transformations (Optimizations?)

[Allen & Cocke - a Catalogue of Optimizing Transformations](https://www.clear.rice.edu/comp512/Lectures/Papers/1971-allen-catalog.pdf)

- Termy (Local)
  - Constant Folding
  - Common Subexpression Elimination
  - Rewrites
  - Dead Code Elimination
  - Inlining
  - Rebalancing
  - Value Numbering
- Loopy (Global)
  - Loop unrolling
  - Loop fusion
  - Loop Invariant Code Motion
  - Tiling

-->

---

# Greedy Simplification

- $x + 0 \rightarrow x$
- Fast
- Simple
- Declarative-ish
<!-- 
Show incremenetal simplifcation diagram?
-->
$$
\begin{aligned}
& c(b + a \times 0) + 7 + -cb + 6 + x \\
&= c(b + 0) + 7 + -cb + 6 + x \quad && X\times 0 \rightarrow 0\\
&= cb + 7 + -cb + 6 + x \quad && X + 0 \rightarrow X \\
\end{aligned}
$$

---

## Suboptimality

$$
\begin{aligned}
& c(b + a \times 0) + 7 + -cb + 6 + x \\
&= c(b + 0) + 7 + -cb + 6 + x \quad && X\times 0 \rightarrow 0\\
&= cb + 7 + -cb + 6 + x \quad && X + 0 \rightarrow X \\
\end{aligned}
$$

---

## Suboptimality

$$
\begin{aligned}
& c(b + a \times 0) + 7 + -cb + 6 + x \\
&= c(b + 0) + 7 + -cb + 6 + x \quad && X\times 0 \rightarrow 0\\
&= cb + 7 + -cb + 6 + x \quad && X + 0 \rightarrow X \\
&= cb - cb + 7 + 6 + x \quad && \textcolor{red}{X + Y \rightarrow Y + X} \\
&= 0 + 7 + 6 + x \quad && X - X \rightarrow 0 \\
&= 13 + x \quad && \text{const prop}
\end{aligned}
$$

---

## Phase Ordering

- Optimizations interact
- Result is order dependent
- Missed optimization opportunities
<!-- 
Redundant Load

GCC rules
https://github.com/gcc-mirror/gcc/blob/master/gcc/passes.def

Graph Rewriting to transform loops in CFG.
Sea of Nodes. 

Which analyses interact. Good example?
-->
$$a * 2 / 2 \rightarrow (a \ll 1) / 2$$
$$a * 2 / 2 \rightarrow a$$

---

# Redundant Loads

```c
v2 = x1 + 1;
v3 = mem[v2];
// ... mutation of mem[v1 + 1]?
v10 = v1 + 1;
v11 = mem[v10];
```

```C
v2 = x1 + 1;
v3 = mem[v2];
// ... no mutation of mem[v1 + 1].
v10 = v2;
v11 = v3;
```

---

<https://github.com/gcc-mirror/gcc/blob/master/gcc/passes.def>

```
NEXT_PASS (pass_cselim);
…
NEXT_PASS (pass_cse_sincos);
NEXT_PASS (pass_cse_reciprocals);
…
NEXT_PASS (pass_cse);
…
NEXT_PASS (pass_cse_after_global_opts);
…
NEXT_PASS (pass_cse2);
…
NEXT_PASS (pass_postreload_cse);
```

---

## Brute Equational Search

<!-- 
Draw lots of little dags

- Don't destructively mutate
- Maximize sharing

- Just explore the equality space

- Rewrites at top vs bottom
-->
<style scoped>
p { text-align: center; }
</style>
![](/assets/eqsearch.png)

---

## Sharing is Caring (about memory)

<style scoped>
p { text-align: center; }
</style>

![width:25cm center](/assets/egraph_share.png)

---

## EGraphs

- Bipartite graph of eclass and enodes
- Compact Representation of a system of Ground Equalities
<!--
What are they?

- Mechanical : Compact Data Structure for equivalent trees
- Logical : Congruence closure

-->

<!-- 

(a + (b + c + (d + e)))
rewrite commutativity at top sharing

rewriter at bottom with sharing

more egraph
class

Pull literally from max's slides and say source: Max Willsey
https://simons.berkeley.edu/sites/default/files/2023-12/LADT23-3%20Slides%20-%20Max%20Willsey.pdf
-->

<!-- Two mantras: Flat and Shared -->

![](https://egraphs.org/assets/4-egraphs.svg)

$$a * 2 / 2 = (a \ll 1) / 2 = a$$

---

### Equality Saturation

<!-- - Rewrite Rules `lhs -> rhs` -->
- Insert initial term $a * 2 / 2$
- Loop
  - E-match pattern: $X * Y / Y$
  - Assert: $a * 2 / 2 = a$
- Extract out best term
- [egg](https://github.com/egraphs-good/egg) :egg: Rust library

![width:20cm bg right](https://egraphs.org/assets/4-egraphs.svg)
<!-- Egraph only grows. We only learn. Monotonic. 
psuedo code?
```python
root = egraph.insert(a * 2 / 2)
for i in range(N):
    eid, subst = egraph.ematch(X * Y / Y)
    egraph.union(eid, subst[X])
return egraph.extract(root)
```

-->

---

# An EGraph-y Compiler Tapas

<style scoped>
p { text-align: center; }
</style>
![width:12cm](/assets/comp_tapas.webp)

---

## Cranelift

- Production quality JIT backend for [wasmtime](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift)

- Your compiler already has (most of) an egraph in it
  - EGraph ~ Global Value Numbering
<!--
-Rust

Get some numbers?

  - GVN
  - CSE

- Getting into and out of egraph is a significant transformation
- Common subexpression elimination
- similar global value numbering
- 
-->

<!-- 
Put numbers 
- [Acyclic EGraphs and smart constructors](https://www.philipzucker.com/smart_constructor_aegraph/)

- The CFG is not fully in the egraph.
https://cfallin.org/pubs/egraphs2023_aegraphs_slides.pdf

<https://www.philipzucker.com/smart_constructor_aegraph/>
<https://vimeo.com/843540328>
-->

---

## Control Flow

- Single Block
- Super Block
- PEGs
- RVSDG

---

## Egglog (PLDI '23)

<!-- 
On a different axis.
Datalog combined with
-->
- Equality Saturation and Datalog
- Datalog and Program Analysis <!-- (liveness aliasing) -->
- [Relational E-matching](https://arxiv.org/abs/2108.02290)
- Multipatterns
- Rewrites guarded on analysis
  - $cols(A) = rows(C) \rightarrow (A \otimes B) \cdot (C \otimes D) = (A \cdot C) \otimes (B \cdot D)$

<!-- 
https://dl.acm.org/doi/10.1145/3591239
Guarded
and finding terms

Program analysis and datalog
What is datalog
Program analsyis
Fixed points
graphs
Relational e-matching

- E-match = SQL Query
- egglog-sqlite Duckegg

Why was I initially interested

Conditional rewrite rules. Conditional optimizations. Liveness

Example
-->

<!--
---

Herbie
SPORES
Szalinski
Ruler

Maybe have the awesome egraphs slide here.
And a huge list of projects

-->

---

### Tensors

- Tensat, Glenside, SPORES, $\Delta$SD

<style scoped>
p { text-align: center; }
</style>

![w:900px](/assets/tensat.png)

<!-- pull stuff from their slide decks.
Maybe just pull this section or glide over it.
I don't feel that comfortable going into depth

https://slideslive.com/38952736/oral-equality-saturation-for-tensor-graph-superoptimization

https://pl.cs.princeton.edu/generals/slides/dh7120.pdf
 -->
---

## SpEQ (PLDI '24)

- Find patterns corresponding to Kernels <!-- YOGO -->

<!-- 
- Loops via fold
  - Slotted Egraphs
- Image here
https://pnwplse.org/slides/2024/Avery%20Laird.pdf
-->

```C
for (j = 0; j < lastrow - firstrow + 1; j++) {
 sum = 0.0;
 for (k = rowstr[j]; k < rowstr[j+1]; k++)
 sum = sum + a[k]*p[colidx[k]];
 q[j] = sum;
}
```

```C
if (preconditions(a, rowstr, colidx)) {
 very_fast_spmv(a, rowstr, ..., p, q);
} else {
 // execute original code
}
```

---

### Vectorization

- Diospyros & Isaria
- Vector algebra

$$
ab+cd+de \rightarrow ab+cd+de+0*0 \rightarrow Vec4(a,b,c,0) \cdot Vec4(b,d,e,0)
$$

- Synthesis using Ruler

<!--
https://jamesbornholt.com/papers/isaria-asplos24.pdf
Decompilation
Speed of getting new IRs
Specialty instructions

instruction selections
diospyros

-->
---

# Even More
<!--
### Hardware

Sam Coward
RTL
Lakeroad

---
- Hardware

-->
- Hardware
- Applications
  - Szalinksi
  - Physics

---

# Flies in Ointment
<!-- put way later? Don't lead with flies -->

- AC Explosion
- Side Effects and State
- Context
- Refinement
- Control Flow

---

#### Egraphs and Automated Reasoning

- EGraphs come from automated reasoning
- Usage modes
  - `prove : Term -> Term -> Bool`
  - `simplify : Term -> Term`
- Automated Reasoning can make compilers
- The fully declarative compiler
<!-- 
- Demodulation
- Paramodulation
- Knuth Bendix

- Superposition
- 

TPTP simplify category
Vampire EProver etc could be amazing simplification engines.

-->

---

<style scoped>
table {
    margin-left: auto;
    margin-right: auto;
}
</style>

| Propositions | Equations |
|------|------------|
| Resolution     |   Paramodulation         |
| Ordered Resolution | Superposition |
| ? | Knuth Bendix Completion |
| Ground Ordered Resolution | EGraph |
| Prolog | Functional Logic Programming |
| Datalog | Egglog |

<!--
/ Ground Completion / Ground Superposition

 ? | Decomdulation | 
| ?  | Completion |
| ASP | ? |
| Lambda Prolog | ? |
| Hypothetical Datalog | ? |
| Minikanren | ? |
-->

---

# Egraphs as Rewrite Systems

<style scoped>
table {
    margin-left: auto;
    margin-right: auto;
}
</style>

| TRS | Egraph |
|------|--------|
| Canonical Term | EClass |
| R/L-simplify | Canonization |
| Run Rules | Extract |
| Term Orders | Extract Objective |
| KBO Weights  |  Weights |

---

<!--
# WAKEUP! THE MOST IMPORTANT SLIDE
<center> <img src="/assets//egraph2.svg">
<img src="assets/egraphs2024/egraphs_1.svg">
</center>
[svg](egraphs_talk_files/egraphs_talk_29_0.svg)

[svg](egraphs_talk_files/egraphs_talk_29_1.svg)
$$  mul(a, two) \rightarrow shift(a, one) $$
$$  mul(a, one) \rightarrow a $$
$$ div(two, two) \rightarrow one $$
$$  div(shift(a, one), two) \rightarrow a $$

-->
<style scoped>
p { text-align: center; }
</style>
![](/assets/egraph2024/egraphs_1.svg) ![](/assets/egraph2024/egraph2.svg)

$$
\begin{aligned}
    a \times 2 &\rightarrow a \ll 1 \\
    a \times 1 &\rightarrow a \\
    2 / 2 &\rightarrow 1 \\
    (a \ll 1) / 2 &\rightarrow a
\end{aligned}
$$

---

#### EGraphs Modulo Theories-lite

- ENodes are ordered
- Containers
  - Sets  `{a,b,c}`
  - Multisets  `{a,a,a,b}`
  - Polynomials
  - Vectors `[a,b,c,a]`
- [Bottom Up E-matching](https://www.philipzucker.com/bottom_up/)

---

#### EGraphs Modulo Theories

- Canonicalization by Ground E-Knuth Bendix

<!-- 
Egphs and automated reasoning

- Ground E-Knuth Bendix
- Equations $\rightarrow_{KB}$ "Good" Rules

-->
<style scoped>
table {
    margin-left: auto;
    margin-right: auto;
}
</style>

|  Theory | Algorithm  | Example  |
|---|---|---|
| Atomic  | Union find   |  `a = b`  |
| Ground Term | EGraph   |  `f(g(a),b) = g(b)` |
| Linear  | Gaussian Elimination   |  $3a + b = c$ |
| Polynomial  | Groebner Bases   |  $s^2 + c^2 = 1$ |
| Multiset / AC | Graver Bases   |  $\{a,a,b\} = \{b,b,c\}$ |
| Associativity | String Completion | `dec; inc; = nop;`   |

<!--

- Union find = atomic equations a -> b b -> c
- Egraph = ground equations
- Gaussian Elim 
- Grobner Bases Polynomial equations

Old topics, highly written about

- Pedogogy
- Data structure focus
- Pragmatics and Incompleteness
- Simplification vs Proof

- a superposition solver could be an incredible simplifying search engine

- Lower barrier to entry
- Go ground me boys!
- <https://www.philipzucker.com/egraph2024_talk_done/>
- <https://www.philipzucker.com/linear_grobner_egraph/>

- Irony. AC is difficult to orient, the point of egraphs.

I'm mostly talking about optimizations on pure theories here. Not things that help state or loops persay.
Oh wait. Combinators often have lots of AC problems

  -->

<!--
#### AC Egraphs

- Combinator approaches and common theories have AC symbols
- Old observation and problem
- Multiset Rewriting
- <https://www.philipzucker.com/multiset_rw/>

---
-->

<!-- 
## A Wrinkle: Side Effects

- Purely functional modelling of state:
  - Monadic
  - World or Array tokens
- Branches
- Side effects (print, memory, etc)
- Order between
- Side Effecting Skeleton

-->

<!-- 
State isn't really perceived as that big of a wrinkle.

Although lead in to sequence egraphs is interesting
-->

<!-- 

### Sequence Egraphs

- String Knuth bendix
- The Two Tribes
- Intrinsically imperative reasoning is possible
- Math doesn't own reasoning.

-->

<!-- - An irony maybe is that even getting to and from the egraph or SSA constitutes a pretty significant transformation

- Peephole  Optimization

Linear IRs
Denali
Linear
Sequential first

Sequence Egraphs here?

---
-->

<!--
# Loops
 Control Flow? 
 
 
 # Loops and Equations

- Syntactic Loops
- combinators - fold, map, reduce
- Matrix algebra
- Tensor Algebra
- Algebra of Programming
- Functional Programming
- Streams

---
 -->

<!--
#### Fold combinators

- Probably requires variable binding
- [SpEQ](https://dl.acm.org/doi/10.1145/3656445) somehow got away with it. Fantastic work
- Slotted egraphs

---

-->

<!--
---
#### CFG Super Blocks

- tails calls ~ jumps
- 1 function per block
- block arguments are live variables ~ phi nodes
- Egraph good at inlining
- Loop unrolling

Appell SSA

---

## Example

```
entry:

```

```
let rec entry_block() = 
    loop_head()

```
-->
---

#### [Co-Egraphs](https://www.philipzucker.com/coegraph/)

- PEGs: Modelling programs as stream combinators
- Observations go down
- Unobserved Eids are maximally observed
- Observational Minimization

`enodes : Enode -> eid`
`obs : eid -> ObsRecord`

<style scoped>
p { text-align: center; }
</style>

![width:10cm](/assets/coegraphs/double.png)
$$ \{  f(f(f(\dots)))  \} $$

<!--
How to hash cons rational trees

https://arxiv.org/abs/2204.12368 Fast Coalgebraic Bisimilarity Minimization

- Flavored in SSA terminology
-

Co-egraphs
A way to get rational terms into the egraph. Compress bisimilarity

Don't make this one full slide
---

#### RVSDG

- Jamey Sharpe's [optir](https://github.com/jameysharp/optir)
- eggcc

IR types: rvsdg, ssa cfg

speciality IRs

-->

---

### An EGraphs for every Occasion

- HyperEgraphs
- Sequence EGraphs
- Extraction and Compiling with Constraints
- Context, color, and assume nodes
<!--
---

### Hyperegraphs

- Graph Rewriting
- Chop out as chunk of graph. put eclass hyperedge around it.
- Interfering rewritings? Smush the edges around
- No obvious notion of confluence compression
- Many tree encodings can be seen a "treeifying" a graph. Different schemes for treating it inductively
  - Categrical Combinators
  - Tree Decomposition
  - Series Parallel Graphs
- Open question: How to elegantly bake this in to a data structure?

-->

<!--
---

### A Wrinkle: Undefined Behavior

- Compiler transformations are not bidirectional
- Refinement
- Semantics is refined as it passes through the compiler
- poison and undef. alive2
- Egglog brute force
- Kleene Equality
- I'm somewhat convinced there isn't anything that great to do
- I would say this is an open issue
- In some ways equality saturation is useful because it has an implicit notion of well definedness

- Chained Resolution

-->
<!--
---

### Wrinkle: Context

- Ground Superposition
- Colored Egraphs
- Assume nodes

---

### Extraction and VIBES

-->

<!--

```

if x < 0 then sqrt(x * x) abs(x) else x
if x != 0 then x/x else 1

```

- Assume Nodes
- Colored Egraphs
-
<!-- Look at Sam's assume node examples? 
Maybe drop this one
-->

<!--
---

# Backend

- Instruction Selection
- Peephole Optimization
- Vectorization

---

-->
<!--
### Instruction Selection, Register Allocation, Scheduling

Instruction Selection and Extraction
Compiling with Constraints

What is a SAT/SMT/CSP solver (I don't know what kind of audience I have)

Unison
VIBES
<https://hci.social/@chrisamaphone/113472393034081686>
“if it works all the time it’s a compiler and if it works some of the time it’s synthesis”

Pluses
Minuses

ISLE

---
-->
---

# Conclusion

- EGraphs Good
- EGraphs Getting Better

---

# Thanks

- <https://github.com/philzook58/awesome-egraphs>
- [egraph community](https://egraphs.org/)
- [zulip](https://egraphs.zulipchat.com/)

---

<!--
# Bits and Bobbles

Calculaitng compilers.

# What am I excited about

Features upcoming  (stuff i said in pldi talk)

- slotted
- colored
- destructive rewrite rules
- refinement - alive2 smtgcc

Egraphs modulo theories
Knuth bendix for compilers

If I have 10 days to get numbers to prove my points, what would I do?

# Automated Reasoning for Compilers

Simplification mode vs proving mode

Knuth bendix completion

A Fully declarative compiler

- Syntax driven by machine needs
- Semantics driven by machine needs. Semantics enable or disable possible optimizations
- Global optimization
- type system optimized to minimize annotations

---

### GVN

You already had an egraph in your compiler

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

### Theorem Proving

Congruence Closure
Ground kb
SMT solvers
EMatching

---

### Sharing

Compelling from a data structure perspective

a *(b + c) = a* (c + b)

Shallow sharing is easy.
Deep sharing

note: Look at egg video for tips

---

## What are compilers

Maybe start at high dsl stuff

---

## Domain Specific

---
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

#### cranelift aegraph

---

-->