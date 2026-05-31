---
marp: true
---

# Lifting E-Graphs: A Function Isn't A Constant

Philip Zucker
EGRAPHS 2026

---

# Original Sin

---

# $\sin(x)$  😱

<!--
It isn't the sine part that makes me uncomfortable it's the x.
We've had this from the get go. We want to manipulate / optimize programs and programs have unknown inputs

-->
---

# Explicit Names Kind of Suck

1. Runaway generation of names
   - `P -> forall x, P where x fresh`
2. Scope Hygiene
   - $x * 0 = 0 \implies \lambda y. 0 = \lambda y. x * 0$ 😱
3. Not enough sharing
   - `f(g(h(x)))` and `f(g(h(y)))` share no memory
4. _Too much sharing_...

<!-- Scope? -->

  <!-- 
  Free varaible anaylsis ? Skolemize the name?
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

$x \mapsto \sin(x) : \mathbb{R}^1 \rightarrow \mathbb{R}$
<style scoped>
p { text-align: center; }
</style>
![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_2_1.png)

---

<style scoped>
p { text-align: center; }
</style>

 $x,y \mapsto \sin(x) : \mathbb{R}^2 \rightarrow \mathbb{R}$
<!-- >`x,y |-> sin(x) : R^2 -> R` -->

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_6_crop.png)

---

# Today's Motto

**The Context $x,y \mapsto \_$ is
  not _where_ a term is,
  it is (part of) _what_ a term is**

---

# Combinatorizing

- Naive Well-Dimensioned Nameless Representation
- Index everything on dimension/context $d$
<!-- - Break the vagueness directly -->
- $\text{var}_{di}$
  - variable $i$ in dimension/context $d$
  <!-- - semantics: projections $\pi_{di}$ -
  -->
  <!-- - Semantics: Projection $\pi_{di}$ -->
  - $[[\text{var}_{di}]]= v_0, v_1, ... v_{d-1} \mapsto v_i$
- $sin_0$, $sin_1$, $sin_2$
  <!-- - semantics: partial composition $\sin \cdot \_ : (\mathbb{R}^d \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^d \rightarrow \mathbb{R})$ -->
  <!-- - Semantics: Partial composition $\sin \cdot \_$ -->
  - $[[\sin_d(t)]] = v_0, v_1, ... v_{d-1} \mapsto \sin([[t]](v_0, v_1, ..., v_{d-1}))$  
<!--
I have made this confusing too early in the talk.
--
>

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

<style scoped>
p { text-align: center; }
</style>

$x \mapsto \sin(x) : \mathbb{R}^1 \rightarrow \mathbb{R} \implies sin_1(\text{var}_{10}) : \mathbb{R}^1 \rightarrow \mathbb{R}$

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_2_1.png)

---
<style scoped>
p { text-align: center; }
</style>

$x,y \mapsto \sin(x) : \mathbb{R}^2 \rightarrow \mathbb{R} \implies sin_2(\text{var}_{20}) : \mathbb{R}^2 \rightarrow \mathbb{R}$

![](https://www.philipzucker.com/assets/2026-04-18-thin_egraph_files/2026-04-18-thin_egraph_6_crop.png)

---

# Is This Good?

- 😃 $\sin(x)$ ambiguity gone
- 🙁 Lots of similar data that shares no memory
- $\sin_1(x_{10})$ and $sin_2(x_{20})$ are not _equal_ but are clearly _related_
- How?

---

# Lifting Functions

- Accept higher dimensional arguments by keeping some args and throwing others away
<!-- - Thinnings encode this data as bitvectors -->

```python
def lift(thin : list[bool], f):
  return lambda *args: f(*[arg for keep,arg in zip(thin,args) if keep])
```
<!-- lift([True, False], sin) # sin2(x20) -->
---

# Lifting

<style scoped>
p { text-align: center; }
</style>

$\sin_1(x_{10}) := \sin(\text{var})$
$\sin_2(x_{20}) := \text{lift}_{10}(\sin(\text{var}))$

![width:600](https://www.philipzucker.com/assets/thin_sin_sin.png)

---

# Thinnings

<style scoped>
p { text-align: center; }
</style>

- One _lifts_ functions by _thinning_ its arglist
- Thinnings
  - are a recipe to extract a subsequence
  - can be represented as bitvectors
  - are simpler than permutations
  - have a notion of composition
  - Can be graphically represented by non crossing wires from N to M dots

![width:300](https://www.philipzucker.com/assets/thinning/compose.png)
<!-- make new picture? -->

---

# Equational Laws of Lifting

|           |   |
|-----------|---|
|  Compaction / Constant Prop. |$\forall x, \text{lift}_i(\text{lift}_j(x)) = \text{lift}_{i \cdot k}(x)$ |
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

---

# Lifting Smart Constructors

- Float $\text{lift}_i$ as high as possible
- Justified by the pulling rule $f(\text{lift}_i(X), lift_i(Y)) \rightarrow \text{lift}_i(f(X,Y))$

<!--
1. Find Largest Common Lifting from arguments (bitwise and)
2. Factor it out of arguments
3. Intern normalized enode
4. Return eid with largest common lifting applied
-->

```python
def app(self, f, *args : list[FatId]) -> FatId:
  thin, args1 = factor_common_lifting(args)
  id = self.add_node(Node(f, args1))
  return (thin, id)
```

- Only _needed_ context remains ~ free variable analysis

<!--
It is semantically meaningful. Unlike a free variable analysis, it can't be stale.

- Thinnings are kind of like a free variable analysis
- McBride's Co De Bruijn Everybody's Got to Be Somewhere
-->

---

# Lifting Union Find

<!-- - Union Find edge annotations don't quite require group structure -->
- Like a Group Union Find, but no inverse required.
- Find
  - Compose liftings during `find` akin to group union find
- Union
  - $\text{lift}_i(\text{lift}_j(e_1)) = \text{lift}_i(\text{lift}_k(e_2)) \implies \text{lift}_j(e_1) = \text{lift}_k(e_2)$ Lifting is injective
  - $e_1 = lift_i(e_2)$ becomes $e_1 \rightarrow lift_i(e_2)$ Parent is forced. `x*0 = 0`
  - $lift_i(e_1) = lift_j(e_2)$ use makeset to make common parent.

---

# E-matching

---

# Similarities With Slotted

- Deal with "rigid" variables.
- `FatId` (renamed vs thinned)
- Special Union Finds
- Shape Computing Smart Constructors
- Public Slots ~ Minimal lifting
- Named vs Nameless is not really the difference

---

# Differences with Slotted

|  Lifting | Slotted |
|----------|---------|
| Thinnings     | (Partial) Permutations |
| Ordered  Vars     | Unordered Vars |
|  Local Context  |  Global Context |
|  Presheaf     |  Nominal   |

---

# Connections

- McBride's Everybody's Got to Be Somewhere
- `x,y |-> sin(x)` vs $n : \mathbb{N} \vdash (\text{Vec} \ n) \ \text{Type}$
- Semi-Simpilical Categories
- Explicit Weakening Calculi
- Presheaves and Families

---

# Questions?

Blog posts

---

# Comparing with Slotted

---

# More

- Binders
- Baked in Substitution
- Types
- Generalized Union Finds

---

# `x*0 = 0` and Redundancies

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
