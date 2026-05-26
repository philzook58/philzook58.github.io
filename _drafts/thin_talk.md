# Lifting E-Graphs

Philip Zucker

---

# Problems With Variables

1. Runaway generation
    - "Skolemization" tricks / free vars analyses
    - P = forall x, P, x fresh
2. Not enough sharing
   - `sin(x) =? sin(y)`
3. Too much sharing

# Original Sin

$sin(x)$

---

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
