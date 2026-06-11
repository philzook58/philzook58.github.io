---
marp: true
---

# Lifting E-Graphs: A Function Isn't A Constant

Philip Zucker
EGRAPHS 2026

---

# The Plan

1. Problems with Named Variables
2. A Semantics for Variables I Like
3. Naive Nameless
4. Lifting & Thinning
5. Lifting E-Graphs
   1. Smart Constructors
   2. Union Find
   3. E-matching
6. Related Work

---

# Original Sin

---

# $\sin(x)$

<!--
It isn't the sine part that makes me uncomfortable it's the x.
We've had this from the get go. We want to manipulate / optimize programs and programs have unknown inputs

-->
---

# Explicit Names Kind of Suck

1. Runaway generation of names during eqsat
   - $P \rightarrow \forall x, P$ where $x$ is fresh
2. Scope Hygiene
   - $x * 0 = 0 \implies \text{lam}(y, 0) = \text{lam}(y,x * 0)$ 🤢
3. Not enough sharing
   - `f(g(h(x)))` and `f(g(h(y)))` share no memory
4. **_Too much sharing_...**

<!-- Scope? -->

  <!-- 
  Free varaible anaylsis ? Skolemize the name?

Too much sharing, some things we call sin(x)

  -->

  <!-- There is asemantics where this makes sense. Maybe fix at extraction time? -->
  <!-- And we are missing relationships -->

---

# What is $\sin(x)$?

<!-- Env -> R is one answer.  
You can't really draw a picture of that.
M |- sin(x) as model dependent is kind of the same thing.

Also R^inf semantics.
If I put my calc 1 hat on, this is the semantics I like.
Names being in the semantics makes me a little queasy
I know it's bread and butter to PL theory.
-->

---

# Is It This?

$x \mapsto \sin(x) : \mathbb{R}^1 \rightarrow \mathbb{R}$
<style scoped>
p { text-align: center; }
</style>
![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_2_1.png)

---

# Or This?

<style scoped>
p { text-align: center; }
</style>

 $x,y \mapsto \sin(x) : \mathbb{R}^2 \rightarrow \mathbb{R}$
<!-- >`x,y |-> sin(x) : R^2 -> R` -->

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_6_crop.png)

---

# Breaking the Ambiguity

## Today's Motto

**The Context $x,y \mapsto \_$ is
  not _where_ a term is,
  it is a part of _what_ a term is**

---

# Combinatorizing $x,y \mapsto \_$

- Naive Well-Dimensioned Nameless Representation
- Index everything on dimension/context $d$

  - $\text{var}_{di}$ - variable $i$ in dimension/context $d$
  - $\sin_0$, $\sin_1$, $\sin_2$
  <!-- - semantics: partial composition $\sin \cdot \_ : (\mathbb{R}^d \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^d \rightarrow \mathbb{R})$ -->
  <!-- - Semantics: Partial composition $\sin \cdot \_$ -->
<!--  - $[[\sin_d(t)]] = v_0, v_1, ... v_{d-1} \mapsto \sin([[t]](v_0, v_1, ..., v_{d-1}))$   -->
- Usable in ordinary e-graph
- Let's look at our examples:
<!--
I have made this confusing too early in the talk.
--
>
  <!-- - semantics: projections $\pi_{di}$ -
  -->
  <!-- - Semantics: Projection $\pi_{di}$ -->
<!-- - $[[\text{var}_{di}]]= v_0, v_1, ... v_{d-1} \mapsto v_i$ -->
<!-- - Break the vagueness directly -->

<!--
Is a semantic brackets clearer? It shows that the semantics in compositional

[[x_01]] = pi_di
[[sin_n(x)]] = sin . [[x]]

[[x_di]] = \lambda x0 x1 x2.. xd. xi
[[sin_d(x)]] = \lambda x0 ... xd. sin([[x]](x0,x1,...,xd))

x0,x1,... \mapsto sin([[x]]())
-->
<!--   -->

<!--: (\mathbb{R}^0 \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^0 \rightarrow \mathbb{R})$ 

Regular egraph could do this.
sin enodes etc have extra i64 parameters

 -->
---

# 1-D

<style scoped>
p { text-align: center; }
</style>

$x \mapsto \sin(x) : \mathbb{R}^1 \rightarrow \mathbb{R} \implies$
$\sin_1(\text{var}_{10})$

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_2_1.png)

---

# 2-D

<style scoped>
p { text-align: center; }
</style>

$x,y \mapsto \sin(x) : \mathbb{R}^2 \rightarrow \mathbb{R} \implies$
$\sin_2(\text{var}_{20})$

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_6_crop.png)

---

# Combinator Semantics

- A sleight of hand
- $[[\text{var}_{di}]]= v_0, v_1, ... v_{d-1} \mapsto v_i$
  - $var_{di}$ is a _projection_ of type $\mathbb{R}^d \rightarrow \mathbb{R}$
- $[[\sin_d(t)]] = v_0, v_1, ... v_{d-1} \mapsto \sin([[t]](v_0, v_1, ..., v_{d-1}))$
  - $\sin_d$ is a _higher order function_ of type $(\mathbb{R}^d \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^d \rightarrow \mathbb{R})$
  - $\sin_d \sim \sin \cdot \_$
- $[[t +_d s]] = v_0, v_1, ... v_{d-1} \mapsto [[t]](v_0, v_1, ..., v_{d-1}) + [[s]](v_0, v_1, ..., v_{d-1})$
- and so on...
<!-- - A relative of the Yoneda Embedding -->

---

# Is This Good?

- 😃 $\sin(x)$ semantic ambiguity gone
- 🙁 Even _more_ very similar data that shares no memory
  - $\sin_1(\text{var}_{10})$ and $\sin_2(\text{var}_{20})$ are not _equal_ but are clearly _related_
    - In what sense?

---

# Lifting Functions

- Lift = Keep some args and throw some away

```python
def lift(thin : list[bool], f):
  return lambda *args: f(*[arg for keep,arg in zip(thin,args) if keep])
```

- $\text{lift}_t : (\mathbb{R}^{\text{popcnt}(t)} \rightarrow \mathbb{R})\rightarrow (\mathbb{R}^{\text{len(t)}} \rightarrow \mathbb{R})$
- $t$ is a thinning bitvector (1=keep, 0=drop)
- Other "argument games" possible, but this is a useful one.

<!-- - Thinnings encode this data as bitvectors -->

<!-- lift([True, False], sin) # sin2(x20)

- Turn $\mathbb{R}^k \rightarrow \mathbb{R}$ into $\mathbb{R}^{k+t} \rightarrow \mathbb{R}$

There are both more general and less general systems for lifting functions.
I could allow swapping
I could only allow dumping from the front

This is kind of a sweet spot. Simple but also maybe not the first thing you think of

 -->
---

# Lifting

<style scoped>
p { text-align: center; }
</style>

$\sin_1(\text{var}_{10}) := \sin(\text{var})$
$\sin_2(\text{var}_{20}) := \text{lift}_{10}(\sin(\text{var}))$

![width:600](https://www.philipzucker.com/assets/thin_sin_sin.png)

---

# Lifting Rules
<!-- Laws of Lifting -->

|           |   |
|-----------|---|
|  Compaction / Constant Fold. |$\forall x, \text{lift}_i(\text{lift}_j(x)) = \text{lift}_{i \cdot k}(x)$ |
|  Pulling / Homomorphism   | $\forall x y, f(\text{lift}_i(x), lift_i(y)) = \text{lift}_i(f(x,y))$  |

<!--
1. `lift_i(lift_j(X)) = lift_k(X)` lift compaction rules
2. `f(lift_i(X), lift_i(Y)) = lift_i(f(X,Y))` lift pulling rules
-->

---

# Baking Lift In

- An example of an e-graph modulo theories (EMT)
- Thinned Eids

```python
type FatId = (list[bool], int)
```

<!-- See my talk last year -->

---

# Lift-Pulling Smart Constructors

```python
class ENode:
  f : str
  args : list[FatId]
```

- $f(\text{lift}_i(X), \text{lift}_i(Y)) \rightarrow \text{lift}_i(f(X,Y))$
- Factor out needed vars
  - needed = bitwise or of argument thinnings
  - ~ free variables analysis

---

# Examples

| Named Form | Unnormalized | Max Pulled  |
|----|---|--|
| $x,y,z,w \mapsto 42$ |$\text{lift}_{0000}(42)$  |  $\text{lift}_{0000}(42)$ |
|$x,y,z,w \mapsto 42 + 42$ |$\text{lift}_{0000}(42) + \text{lift}_{0000}(42)$ | $\text{lift}_{0000}(42 + 42)$ |
| $x,y,z,w \mapsto z + 42$   | $\text{lift}_{0010}(\text{var}) + \text{lift}_{0000}(42)$  |   $\text{lift}_{0010}(\text{var} + \text{lift}_0(42))$  |
| $x,y,z,w \mapsto x + z$  | $\text{lift}_{1000}(\text{var}) + \text{lift}_{0010}(\text{var})$ |  $\displaylines{\text{lift}_{1010}(  \text{lift}_{10}(\text{var}) + \\ \text{lift}_{01}(\text{var}))}$ |

---

# Thinning Union Find

<!-- - Union Find edge annotations don't quite require group structure 

-->
- `type UnionFind = list[FatId]`
- Like Offset (Group) Union Find $e_{8} \rightarrow e_{3} + 14$
  - `uf[8] == (14,3)`
- Find
  - Compose $e_{child} \rightarrow \text{lift}_t(e_{parent})$
- Union
  - Peel off common lift (lift is injective)
  - $\text{lift}_t$ is _not_ invertible
    - Parent is sometimes forced / requires makeset
<!--   - $e_{0} \rightarrow e_{1} + 14$
  - `[(14,1),(0,1)]` -->

---

# Ordinary Union Example

|   |   |
|---|---|
|Named Form| $(x,y \mapsto y*1) =  (x,y \mapsto y)$ |
|Pulled Form| $\text{lift}_{01}(\text{var} * \text{lift}_0(1)) = \text{lift}_{01}(\text{var})$ |
| Interned Form | $\text{lift}_{01}(e_{17}) = \text{lift}_{01}(e_{42})$ |
| Peel | $e_{17} = e_{42}$ |
| Orient | $e_{17} \rightarrow e_{42}$ (or $e_{42} \rightarrow e_{17}$) |

---

# Ordinary Union

- Example: $(x,y \mapsto y*1) =  (x,y \mapsto y)$
- Pulled: $\text{lift}_{01}(\text{var} * \text{lift}_0(1)) = \text{lift}_{01}(\text{var})$
- Union Call $\text{lift}_{01}(e_{17}) = \text{lift}_{01}(e_{42})$
- Peel off common lift to $e_{17} = e_{42}$
  - Semantics: $\text{lift}_t$ is injective
- Pick parent $e_{17} \rightarrow e_{42}$

---

# Redundancy Example 1: One Way Lift

|  |  |
|--|--|
| Named Form | $(x \mapsto x*0) = (x \mapsto 0)$ |
| Pulled Form | $\text{var}*\text{lift}_0(0) = \text{lift}_0(0)$ |
| Interned Form |  $e_{92} = \text{lift}_{0}(e_{8})$ |
| Orient (forced) | $e_{92} \rightarrow \text{lift}_{0}(e_{8})$  |

---

# Redundancy Example 1: One Way Lift

- Example: $(x \mapsto x*0) = (x \mapsto 0)$
- Pulled: $\text{var}*\text{lift}_0(0) = \text{lift}_0(0)$
- Union: $e_{92} = \text{lift}_{0}(e_{8})$
- $e_{92} \rightarrow \text{lift}_{0}(e_{8})$
  - Parent choice is forced

---

# Redundancy Example 2: Incompatible liftings

|  |  |
|--|--|
| Named Form | $(x,y \mapsto x*0) = (x,y \mapsto 0*y)$   |
| Pulled Form |  $\text{lift}_{10}(\text{var}*\text{lift}_0(0)) = \text{lift}_{01}(\text{lift}_0(0) * \text{var})$  |
| Interned Form | $\text{lift}_{10}(e_{92}) = \text{lift}_{01}(e_{13})$  |
| Fresh Makeset  | $e_{99}$
| Orient |  $e_{92} \rightarrow \text{lift}_0(e_{99})$ ,  $e_{13} \rightarrow \text{lift}_0(e_{99})$    |

---

# Redundancy Example 2: Incompatible liftings

- Example: $(x,y \mapsto x*0) = (x,y \mapsto 0*y)$
- Pulled: $\text{lift}_{10}(\text{var}*\text{lift}_0(0)) = \text{lift}_{01}(\text{lift}_0(0) * \text{var})$  
- Interned: $\text{lift}_{10}(e_{92}) = \text{lift}_{01}(e_{13})$
- Makeset fresh parent $e_{99}$
       - Only relevant variables in intersection (bitwise and)
       - Semantics: Learned some directions are constant
- $e_{92} \rightarrow \text{lift}_0(e_{99})$ ,  $e_{13} \rightarrow \text{lift}_0(e_{99})$

<!--  = fresh(d = popcnt(01 \& 10) = 0) -->

---

# Redundancy Example 2: Incompatible liftings

- Example: $(x,y \mapsto x*0) = (x,y \mapsto 0*y)$
- Pulled: $\text{lift}_{10}(\text{var}*\text{lift}_0(0)) = \text{lift}_{01}(\text{lift}_0(0) * \text{var})$  
- Interned: $\text{lift}_{10}(e_{92}) = \text{lift}_{01}(e_{13})$
- Makeset fresh parent $e_{99}$
       - Only relevant variables in intersection (bitwise and)
       - Semantics: Learned some directions are constant
- $e_{92} \rightarrow \text{lift}_0(e_{99})$ ,  $e_{13} \rightarrow \text{lift}_0(e_{99})$

<!--  = fresh(d = popcnt(01 \& 10) = 0) -->

---

# E-matching

<!-- - Mostly Nothing Changes. 
- $lift_i(e_1) =? f(?a, ?b)$
- $e_1 = f(e_2, e_3)$
- $lift_i(f(e_2,e_3)) =? f(?a, ?b)$
- $lift_i(f(e_2,e_3)) = f(lift_i(e_2), lift_i(e_3))$
- $f(lift_i(e_2), lift_i(e_3)) =? f(?a, ?b)$

$$
\begin{aligned}
\mathrm{lift}_i(e_1)
  &=_? f(?a, ?b) \\
\mathrm{lift}_i(f(e_2,e_3))
  &=_? f(?a, ?b) \\
f(\mathrm{lift}_i(e_2), \mathrm{lift}_i(e_3)) &=_? f(?a, ?b)
\end{aligned}
$$
-->

- Accumulate thinnings as you traverse into terms

$$
\begin{aligned}
\mathrm{lift}_i(e_1)
  &=_? f(?a, ?b)
  && \text{goal} \\
\mathrm{lift}_i(f(e_2,e_3))
  &=_? f(?a, ?b)
  && \text{nondet e-class expand } e_1 \rightarrow f(e_2,e_3) \\
f(\mathrm{lift}_i(e_2), \mathrm{lift}_i(e_3))
  &=_? f(?a, ?b)
  && \text{lift-pushing}\\
\Rightarrow \quad
?a &= \mathrm{lift}_i(e_2) \quad \land \quad
?b = \mathrm{lift}_i(e_3)
  && \text{decompose } f
\end{aligned}
$$

- Redundancies in union find $e_{\text{child}} \rightarrow \text{lift}_k(e_{\text{parent}})$ are trickier
  - Choice 1: Don't Match Through Them
  - Choice 2: Factor $\text{lift}_i(e_\text{parent}) = \text{lift}_{?j}(\text{lift}_k(e_\text{parent}))$
    - Multiple solutions
      - Ex: $(x,y \mapsto 0) =_? (x,y \mapsto ?a * 0)$
      - solutions $?a = x$ and $?a = y$

<!-- $?a = lift_i(e_2), ?b = lift_i(e_3)$ -->

---

# Related Work

- Slotted E-Graphs
- McBride's Everybody's Got to Be Somewhere (Co de Bruijn)
- Semantics of MLTT judgements $[[x : \mathbb{R},y : \mathbb{R} \vdash \sin(x) : \mathbb{R}]]$
- Explicit Weakening Calculi
- de Bruijn Succ Floating

---

# Questions?

 Blog Posts <https://www.philipzucker.com/lifting_egraph/>

1. Problems with Named Variables
2. A Semantics for Variables I like
3. Naive Nameless
4. Lifting & Thinning
5. Lifting E-Graphs
   1. Smart Constructors
   2. Thinning Union Find
   3. E-matching
6. Related Work

---

# Questions?

---

# E-matching Redundancies

- Non trivially thinned Union find edges
- Choices:
  1. Just don't pattern match into those
  2. Choice 2:

- `x |- x * 0 = 0`
- `x,y |- 0 =?  x,y |- ?a * ?b`
Two solutions:

1. {?a : x, ?b : 0}
2. {?a : y, ?b : 0}

---

# Thinnings

<style scoped>
p { text-align: center; }
</style>

- One _lifts_ functions by _thinning_ its arglist
- Thinnings are
  - A recipe to extract a subsequence
  - Representable as bitvectors (1 = keep, 0 = drop)
  - Graphically representable by non crossing wires from N to M dots
  - Strictly monotonic maps between total ordered sets
- Simpler than permutations
- Compaction of multiple de Bruijn shifts
- Have composition and identity

<!-- make new picture?
![width:300](https://www.philipzucker.com/assets/thinning/compose.png)

 -->

---

# THE MOST IMPORTANT SLIDE

![](/assets/thinning/simple-thinning.svg)

---

# Connections

- McBride's Everybody's Got to Be Somewhere
  - $x,y \mapsto sin(x)$
  - $n : \mathbb{N} \vdash (\text{Vec} \ n) \ \text{Type}$
- Semi-Simpilical Categories
- Explicit Weakening Calculi
- Presheaves and Families

---

# Differences with Slotted

|  Lifting | Slotted |
|----------|---------|
| Thinnings     | (Partial) Permutations |
| Ordered  Vars     | Unordered Vars |
|  Local Context  |  Global Context |
|  Presheaf     |  Nominal   |

---

# Similarities With Slotted

- Deal with "rigid" variables.
- `FatId` (renamed vs thinned)
- Special Union Finds
- Shape Computing Smart Constructors
- Public Slots ~ Minimal lifting
- Named vs Nameless is not really the difference

---

# Lift Pulling Smart Constructors

```python
class Node:
  f : str
  args : list[FatId]
```

- Smart enode construction $f(\text{lift}_i(X), lift_i(Y)) \rightarrow \text{lift}_i(f(X,Y))$
  1. Find Largest Common Lifting of arguments (bitwise or)
  2. Factor it out of arguments
  3. Intern normalized enode
  4. Return eid with largest common lifting applied

<!--

example might be best

- Float $\text{lift}_i$ as high as possible
 Justified by the pulling rule

```python
def app(self, f, *args : list[FatId]) -> FatId:
  thin, args1 = factor_common_lifting(args)
  id = self.add_node(Node(f, args1))
  return (thin, id)
```
-->

- Thinnest context ~ free variables analysis
- Similar to McBride's Co-de Bruijn
- Alpha invariant Hash Cons

<!-- - Only _needed_ context remains ~ free variable analysis -->

<!--
It is semantically meaningful. Unlike a free variable analysis, it can't be stale.

- Thinnings are kind of like a free variable analysis
- McBride's Co De Bruijn Everybody's Got to Be Somewhere
-->
---

# Comparing with Slotted

---

# Why Do Lifts Appear?

- User wants a convenient context of 20 variables
- $x * 0 = 0$ makes lifts appear during rebuilding
- Children have different variables appearing in them

---

# Binders

- Ok, but what about binders $\lambda, \forall, \exists,\int, \sum$?
- Binders are inessential. Lifting e-graphs make sense without them
- Binders have less dimensions than their children.
- Semantics: Binders are generalized higher order projection functions $(\mathbb{R}^d \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^{d-1} \rightarrow \mathbb{R})$
- Modified Pulling rules
  - "Transfer function" for liftings
  - Modified smart constructor
- Otherwise not much changes.
- `dump` and `subst` <https://www.philipzucker.com/dump_calculus/>

---

# Substitution

- $\beta$ ia hard and undecidable to bake in to e-matching
  - Higher order matching is undecidable
  - Restricted ~$\alpha$ fragment's like Miller $\beta_0$ are fine
- Bespoke substitution traversal routine may be useful. Thinnings tell when it may stop since ~ free variable analysis
- Not sure

---

# Rebuilding

- Reintern using smart constructor
- Not much changes

---

# PreTalk : What are E-Graphs?

- Non destructive Rewriting and the Phase Ordering Problem
- A data structure for compactly storing trees / asts and an equality relation

![](https://egraphs-good.github.io/assets/egraphs.svg)

---

# PreTalk : What are E-Graphs?

- Hash Cons / Intern Table + Union Find
- Enables sharing parents rather than just children
  - Aliasing ordinarily allows share big subterms of `f(f(f(f(a)))) -> g(f(f(f(a))))`
  - Naively, apply deep rewrite `a -> b`  inside `f(f(f(f(a))))` -> `f(f(f(f(b))))` share no storage
  - Eclass indirection   `f(f(f(f({a | b}))))` now can share
  - Bipartite graph of eclasses `{}` and enodes `f(_)`

---

---

# More

- Binders
- Baked in Substitution
- Types
- Generalized Union Finds

---

- Union
  1. Peel off common lift (vars both throw away)
     - $\text{lift}_i(\text{lift}_j(e_1)) = \text{lift}_i(\text{lift}_k(e_2)) \implies \text{lift}_j(e_1) = \text{lift}_k(e_2)$
     - $\text{lift}_t$ is injective
  2. Either
     - $e_1 = e_2$    Ordinary union
     - $e_1 = lift_i(e_2)$  Parent is forced.
     - $lift_i(e_1) = lift_j(e_2)$  Makeset new parent
       - Only relevant variables in intersection (bitwise and)
       - Semantically we have learned some directions are constant (no actual dependency)

<!--
$lift_i(e_1) = lift_j(e_2)$
 Lifting is injective
use makeset to make common parent.
$e_1 = lift_i(e_2)$ becomes $e_1 \rightarrow lift_i(e_2)$ `x*0 = 0`
 -->
---

# `x*0 = 0` and Redundancies

---

# Union

|   $x,y, ... \mapsto \_$   |   term     |  e-class |
|---------|--------|-----|
| $(x,y \mapsto y*1) = \\ (x,y \mapsto y)$ |  $\text{lift}_{01}(\text{var} * \text{lift}_0(1)) = \text{lift}_{01}(\text{var})$      |  $e_{y*1} = e_{y}$ |
| $(x \mapsto x*0) = (x \mapsto 0)$ |$\text{var}*\text{lift}_0(0) = \text{lift}_0(0)$ | $e_{x*0} = \text{lift}_{0}(e_{0})$ |
| $(x,y \mapsto x*0) = (x,y \mapsto y*0)$ | $\text{lift}_{10}(\text{var}*\text{lift}_0(0)) = \text{lift}_{01}(\text{var}*\text{lift}_0(0))$   | $\text{lift}_{10}(e_{x*0}) = \text{lift}_{01}(e_{y*0})$ |

$\text{lift}_{01}(e_{y*1}) = \text{lift}_{01}(e_y)$
<!-- | $(x,y \mapsto 1 + 2) = (x,y \mapsto 2 + 1)$   |  | -->

---

# Examples

| $x,y, ... \mapsto \_$ |  Maximally Pulled Form |
|----|---|
| $x,y,z,w \mapsto 42$ |  $\text{lift}_{0000}(42)$ |
|$x,y,z,w \mapsto 42 + 42$ |  $\text{lift}_{0000}(42 + 42)$ |
| $x.y.z.w \mapsto z$ | $\text{lift}_{0010}(\text{var})$ |
| $x,y,z,w \mapsto z + 42$   |   $\text{lift}_{0010}(\text{var} + \text{lift}_0(42))$  |
| $x,y,z,w \mapsto x + z$  |  $\text{lift}_{1010}(\text{lift}_{10}(\text{var}) + \text{lift}_{01}(\text{var}))$ |

---

# Problems

1. sinsinsins(x) sares not data with sinsinsins(y)
2. vairable gnerating rules
3. free variable analysis soundness
4. Names make me quesy

## Plot

$x |-> sin(x)$

x |- x is the identity
[[x,y |- x]] is fst
[[y,x |- x]] is snd

The context is a _part_ of the term. It isn't "where" the term is.

### Lifting to 2D

# This is Code

# Ground Congruence with Rigid Variables

### Baking it in

## My Nightmares

$0*x = 0$

## Egraph

## E-matching

#

- Simplicial Category
- Semantics of type theory
- Explicit Weakening

## Bits and Bobbles

I could try and make the talk and do it anyway on youtube. I might not be accepted anyhow. Stiff competition.

Maybe there isn't enough time to break it up like this

## Union Find

## Hash Cons

Ultimately I am motivated by an internal and subjective notion of aesthetics

# original sin

sin(x)

1 = I
1 + 1 = II

# What is "sin(x)", Too much sharing

x \mapsto sin(x)

x,y \mapsto sin(x)

# What is "x"

x \mapsto x

x,y \mapsto y

# Verbose Context Terms

1. 1 \mapsto sin_1 cos_1 (v0)

# Liftings

sin_1(x)

# THE MOST IMPORTANT SLIDE. Liftings

Diagram of wires 1010

you can take away whatever you want

# E-matching

# Comparison With Slotted

# Connections

- Semisimplicial categories
  - cubical
- slotted
- nominal

# Time

compress original sin and plots to a single slide.

Discomfort:

- what is all this really for?
- Can you do the manipulations you actually need to do?
- Substitution
- Lambda and binders.
- sum_i sum_j = sum_j sum_i sucks.

I was literally crying tears of blood to compress this talk into 15 mins. I think there are so many fascinating things I left out.
I recorded a longer version here.

### Lifting and Dropping

- Lift factoring. Normal form ~ co-de Bruijn

Going nameless

```
def lift_fun
def lift_dict
def thin_list
```

def dump_fun()
def wide_list()
def papply(): # subst

$sin(y)$
$1 + 2$
$sin(fred)$

$sin(fred) : \bR$ ? But aren't we trying to talk about functions?

partial derivative in thermo example

${x,y,z |-> sin(x)}$

Another approach/perpspective is to turtle this all the way down
${x,y,z |-> sin({x,y,z |-> x})}$

The context is part of the term.

# Variables Are Lifted Identity Functions

`x,y |-> x`

$lift_{10}(id)$

---
