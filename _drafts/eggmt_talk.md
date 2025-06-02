---
marp: true
---


# Omelets need Onions

### E-graphs Modulo Theories via Bottom Up E-Matching

Philip Zucker (Draper Labs)

---

# Overview

- Bottom-up E-matching
  - Terms Modulo Theories
  - Patterns
- Semantic E-ids
  - E-graphs are models
  - UF is canonizer for atomic equations
  - Linear expressions, polynomials, multisets also have canonizers
  - Undecidable canonizers

---

# AC Sucks

$(x_1 + (x_2 + ...(x_{N-1} + x_N)...))$

   |  e-classes | e-nodes |
   |------------|-----------|
   | $2^N-1$ | $3^N - 2^{N+1} + 1$ |

<!-- picture? 
- The eqsat paradox
- We want stuff baked in.

import operator
z3.Solver()
xs = [smt.Int("x" + i) for i in range(100)]
z3.prove(reduce(operator.add, xs) == reduce(operator.add, reversed(xs)))

xs + [-x for x in xs]
z3.simplify(reduce(operator.add , xs))

TANSTAAFL ~ There ain't no such thing as a free lunch

-->

---

# EMT = SMT - SAT

- Built in reasoning over
  - Linear arithmetic
  -

---

# Terms Modulo Theories

- Convergent Smart constructors
- Children collections

<!-- Show rules. x + 0 -> x -->
<!-- show smart constructor

def add(x,y):
  return x if y == 0 else ("+", x, y)

-->

---

# Brute Term Search
<!-- Breadth first -->
- Hash cons a term bank. Rewrite over it. Mark discovered equalities.

---

|  Theory  |  Flatterns   |  Theory Factor $F$  |
|-------------|------------|--------|
|    N/A      |    $cons(X,Y) =^? cons(1, nil)$     |   1   |  
|  E-Graph  |   $foo(X,Y) \in^? \{foo(e_1,e_2), bar(e_2) \}$         |    $\frac{\#enodes}{\#eids}$ |
|      MultiSet 1     |  $[X,Y,Z] =^? [1,2,3]$ | (\#Vars)!  |  
|      MultiSet 2     |  $X + Y =^? [1,2,3]$  | #Partitions |
|    Linear   | $X + Y =^? 42$  |  $\infty$  |

<!-- https://en.wikipedia.org/wiki/Bell_number This also what people mean by using AC for addition.
AC1 is multiset matching. Both are really.
Maybe the second is ACI?
B_n

Flatterns
flatterms
 -->
---

# E-graphs and Term Banks

<!-- Example -->

---

# Bottom Up E-matching

- E-Graphs have Term Banks
- Theory Factor $F = \frac{N}{E}$
- Pattern depth $d$
- Top down $O(T F^d )$
- Bottom Up $O(T^V d ln(T))$

- Benefits of Theories & simplicity vs Flexibility and optimiality?
  - I dunno

- Generate terms, prune, discover equalities

---

## Demo

### Shallow Embedding BU Ematching

```python
for X in e c l a s s e s :
for Y in e c l a s s e s :
t r y :
# p o s s i b l y f a i l i n g l o o k u p i n h a s h c o n s
l h s = f o o [ b a r [X ] , Y ]
# c o n s t r u c t r h s
r h s = b i z (X)
# s e t e q u al
e g ra p h . u ni o n ( l h s , r h s )
except e :
```

```python
    def ematch(self, vs: list[smt.ExprRef], pat: smt.ExprRef) -> list[list[smt.ExprRef]]:
        res = []
        for eids in itertools.product(*[self.roots[v.sort()] for v in vs]):
            ts = [self.terms[eid] for eid in eids]
            lhs = smt.substitute(pat, *zip(vs, ts))
            if self.in_terms(lhs):
                res.append(ts)
        return res
```

---

### Brute Force SMT E-Graph

---

# What are E-graphs?

- E-graphs are models of a partial logic
- $\downarrow t$ and  $t_1 = t_2$
- SMT models (show z3)
  - Free Logic
  - Generalized Algebraic Theories
  - Essential Algebraic Theories
  - Partial Horn Logic

<!-- 
---

## Union finds

- Canonizers ground atomic equations
- What interface really matters?
- Shostak theories

-->
---

# What is this the interface to?

```ocaml
type t
type eid
val create : unit −> t
val eq : t −> eid −> eid −> bool
val fresh : t −> eid
val canon : t −> eid −> eid
val assert_eq : t −> eid −> eid −> unit
```

<!-- The union find? Yes. also the egraph itself 

SMT solvers and their theories present the same interface.
If you don't use SAT, SMT is its theory.

Egraphs and union finds also present the same interface.

type key
interpret : t -> key -> eid   union find dict
explain
lookup : t -> eid -> key (extract)

-->

---

# Semantic E-ids
<!-- e-ids as values -->
- Alternative names: Structured e-ids, Values
- Merge the concepts of containers, primitives, and e-ids

---

# Cheap Decidable

| eids |  example                       |    Rebuild        |    Data Structure
|------------------|--------------------|------------------|---------------------|
| Atomic / Uninterp |  $e_1$             |  Compress      | Union Find
| Value + Uninterp |   $Cons(7, e_1)$   |  Compress/Unify  | Value rooted UF + Unification
| Group(oid) Action   |   $e_1 + 7$     |      Compress   | Group UF
| Lin Expr         |    $2e_1 - 4e_7$     |   Gauss Elim   | Row Echelon
| Ground Terms    |      $foo(bar(e_7))$        |  Egraph Rebuild       | Inner E-Graph   |

<!--  Lighter to heavier weight 

Destructive rewrites over disjoint signature

Cheap Decidable  (P)
Expensive Decidable (Super polynomial)
Undecidable 
-->

---

# Expensive Decidable

| eids |  example                       |    Rebuild        |    Data Structure
|------------------|--------------------|------------------|---------------------|
|  Polynomials           |   $e_1 + 6e_4^3$      |   Buchberger   | Grobner Basis  
| Ground Multiset        |   $[e1, e1, e2]$       |   Knuth Bendix      |   Graver / Hilbert bases / Convergent Rewrite System  |
| SMT Terms       |                      | SMT sweeping  | SMT Solver |
| Bool Exprs       | $e_1 \land e_2 \lor e_3$ | SAT Sweeping  / BDDs / AIGs / Ordered Resolution      |            |

---

# More?

|
|-----------------|-----------|---|---|--|
|  Slotted eids?  |   ?       |   ?  | ? | ? |
| Colored eids?  |   ?         | ?  | ?  | ? |

---

## Strong (Undecidable) Theories

|  eid | ex  |  rebuild   |   |
|---|---|--|--|
|  Strings        | $e_1 e_4 e_2$ |  String KB  | Rewrite Rules |    Program seqeuences
| Non commutative Rings |    $\partial_x e_1$        |            |               |    Note: differentiation, quantum operators
| Variables Term  | $foo(e_1, X)$    |                                        |   Destructive Rewrite Rules

<!--

Is there a form of differentiable that would be solvable?
Linear differential (?)
partial_t only? That might make a module for with smith normal form works

- Black Boxes/Automation are decision procedures or linear time or constant time
- undecidable/interactive/tweakables    poly time
-->
---

# Thanks

---

# Bits and Bobbles

<https://arxiv.org/abs/2504.14340>

Pavel quantifier elimination

I don't really have to hit every point of the paper. It's too much.
A sale pitch for the paper kind of.

It would be good to have a running example.

Brute SMT?

Is this too much stuff for 20mins? What really are my priorities?

Look at reviewer suggestions.

Show shallow top down e-match
Show shallow bottom up e-matcher

There's a chance I could cut the second half of the talk about semantic e-ids.
