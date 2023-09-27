---
layout: post
title: Egglog
---

- [Welcome to Egglog](#welcome-to-egglog)
- [Examples](#examples)
  - [Shortest Path](#shortest-path)
  - [List Programming](#list-programming)
  - [Arithmetic Simplification](#arithmetic-simplification)
  - [Negation and Wellfounded Semantics](#negation-and-wellfounded-semantics)
  - [Geometry](#geometry)
  - [Delta equality](#delta-equality)
  - [Box / Generic DataStructures](#box--generic-datastructures)
  - [Disequality](#disequality)
  - [Inequality](#inequality)
  - [Choice Domains](#choice-domains)
  - [Refining equalities](#refining-equalities)
  - [Integration](#integration)
  - [BitVectors](#bitvectors)
  - [Peano](#peano)
  - [BDDs](#bdds)
  - [First Class Union Find](#first-class-union-find)
  - [Homotopy](#homotopy)
  - [Kleene Algebra](#kleene-algebra)
  - [Matrices](#matrices)
  - [Category](#category)
  - [Typechecking](#typechecking)
  - [Intervals](#intervals)
  - [Context](#context)
  - [Lambdas](#lambdas)
    - [Normalization by Evaluation](#normalization-by-evaluation)
  - [Let](#let)
  - [Polynomials](#polynomials)
  - [Arrays/Maps](#arraysmaps)
  - [Resolution](#resolution)
  - [SMTLIB](#smtlib)
  - [The Chase](#the-chase)
  - [Partial Application](#partial-application)
  - [RVSDG](#rvsdg)
  - [Algebra of Programming](#algebra-of-programming)
  - [AC](#ac)
- [Egglog0 posts](#egglog0-posts)
- [Souffle Posts](#souffle-posts)
  - [Merging Database](#merging-database)
  - [Extraction as datalog](#extraction-as-datalog)
- [Misc](#misc)
  - [Modulo theories](#modulo-theories)
  - [Propagators](#propagators)
  - [AC](#ac-1)
    - [slog](#slog)
- [GJ scribbles](#gj-scribbles)
  - [Bottom Up](#bottom-up)
- [Termination](#termination)
- [Rulesets](#rulesets)
- [Ideas](#ideas)

See also notes on [egraphs](../Logic/egraphs.md)

# Welcome to Egglog

Egglog is a term rewriting and analysis engine with a special eye towards applications involving program optimization.
It is backed by a high performance Rust database backend and uses E-graph techniques to retain a compressed representation of equivalent terms.

- If you like SMT solvers, Egglog is akin to a more programmable and predictable quantifier instantiation engine. It is an SMT solver without the SAT.
- If you like datalog, Egglog is a datalog with existentials / functions symbols, lattices, and a very special notion of equality backed by a union find. This union find behaves differently than the special equivalence relation representation in souffle.
- If you like pure functional programming, egglog is a functional programming system where everything is memoized by default and which allows a larger class of pattern matching rules than just matching on constructors

<iframe width="560" height="315" src="https://www.youtube.com/embed/N2RDQGRBrSY" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" allowfullscreen></iframe>

# Examples

<https://github.com/philzook58/egg-smol/tree/scratchpad2/tests>

## Shortest Path

The canonical datalog program is path connectivity.

```eggsmol
;re
(relation edge (i64 i64))
(relation path (i64 i64))
(rule ((edge x y) (path y z)) 
      ((path x z)))
(rule ((edge x y))
      ((path x y)))
(edge 1 2)
(edge 2 3)

(run 10)
(print path)
```

There are a couple of twists we can add to this.

```eggsmol
;re
(function edge (i64 i64) i64 :merge (min old new))
(function path (i64 i64) i64 :merge (min old new))
(rule ((edge x y) (path y z)) 
      ((path x z)))
(rule  ((= c (edge x y)))
       ((set (path x y) c)))
(set (edge 1 2) 3)
(set (edge 2 3) 4)

(run 10)
(print path)
```

A second interesting twist is

## List Programming

Some simple functional programming style manipulation of lists.
We wrap the primiive `i64` type in `Int` in order to get equational rewriting behavior. This is a common pattern for primitives. In order for a function to "return" it needs some way of tracking where it returns to. In an ordinary lnaguage, this information is held on the stack. There is no stack in egglog, so instead one registers a new "equivalence id" that is eventually unioned to the result.

```eggsmol
;re
(datatype Int (Lit i64))
(datatype List (Cons i64 List) (Nil))

(function append (List List) List)
(rewrite (append (Nil) l) l)
(rewrite (append (Cons x xs) l) (Cons x (append xs l)))

(function add (Int Int) Int)
(rewrite (add (Lit x) (Lit y)) (Lit (+ x y)))

(function sum (List) Int)
(rewrite (sum (Nil)) (Lit 0))
(rewrite (sum (Cons x xs)) (add (Lit x) (sum xs)))


(let t (append (Cons 3 (Nil)) (Cons 4 (Nil))))
(run 10)
(extract t)

(let x (sum t))
(run 10)
(extract x)
```

## Arithmetic Simplification

## Negation and Wellfounded Semantics

## Geometry

```eggsmol
;re
(datatype Point)
(datatype Mag)


(function dist (Point Point) Mag)
(rewrite (dist x y) (dist y x))

(datatype Seg)
(function seg (Point Point) Seg)
; hmm. Questionable. Should I define segments to be commutative?
; (rewrite (seg x y) (seg y x))

(function len (Seg) Mag)
(rewrite (len (seg x y)) (dist x y))

(datatype Line)
(function extend (Seg) Line)
(function line (Point Point) Line)

(birewrite (line x y) (extend (seg x y)))

; parallel lines form an equivalence class. Reflexive, transitive, symettric.
; ParaClass is a set of lines.
(datatype ParaClass)
(function para (Line) ParaClass)

(relation not-para (ParaClass ParaClass))
(rule ((not-para b a)) ((not-para a b)))


(relation perp (ParaClass ParaClass))
(rule ((perp a b)) ((perp b a)))
(rule ((perp a b) (perp b c)) ((set (para a) (para c))))
(rule ((perp a b) (= (para c) (para b)) ((perp a c))))

(rule ((perp a b)) ((not-para a b)))
(datatype Angle)
(function angle (Line Line) Angle)

(datatype Circle)
(function center-circ (Point Point) Circle)

(rewrite (center-circ p x) (center-circ p y)
  :when (= (dist p x) (dist p y))
)

; I wanted to deempasize coordinates, but we can construct points using coordinates if you like.
(function coord (Rational Rational) Point)

(datatype Triangle (Triangle Point Point Point) )
(rewrite (Triangle a b c) (Triangle b c a))
(rewrite (Triangle a b c) (Triangle b a c))

(relation equilateral (Triangle))
; definition
(rule ((= d (dist a b)) (= d (dist b c)) (= d (dist c a)))
      (equilateral (Triangle a b c)))
(rule ((equilateral (Triangle a b c)))
      ((define d (dist a b) 
      (union d (dist b c))
       (union d (dist c a)))
      ))

(relation inside (Point Seg)) ; in the interior of the segment. Strict Betweenness. Important for 

(push)
; Euclid prop I
(function X () Point)
(function Y () Point)

(define c1 (Circle X Y))
(define c2 (Circle Y X))
(function Z () Point)

; Z is on both circles
(union c1 (Circle X Z))
(union c2 (Circle Y Z))

(define t (Triangle (X) (Y) (Z)))

(run 10)
(check (equilateral t))
(pop)

```

## Delta equality

<https://alfa.di.uminho.pt/~nevrenato/probprogschool_slides/Prakash.pdf>
Dreal uses delta equality
Subsumptive character. a =eps b  --> a =eps' b  if  eps <= eps'
| a - b | <= eps. This is two inequalities, sure.

Order O(epsilon) classes are actual equality classes. njection functions can treat that
Congruence now involes the derivatives?
x =eps x' -> f(x) =df(eps) f(x')

Tightest eps is shortest path. Floyd Warshall. Bummer.
Minimum spanning tree as approximation?
LCA is convenient. Rem's algorithm?

heursistic:
union(a,b,l)
x = lca(a,b)
if d(a,x) + d(x,b) < l:
  if d(a,x) < d(x,b):
    parent(b) = parent(x)
    parent(x) = a
    parent(a) = b

eh seems pretty fishy.

Axioms of a metric = shortest path
See for example my encpding of shortest path. symmettry makes it way more natural (quasimetric is assymettric metric. No one ever does this)
<https://en.wikipedia.org/wiki/Metric_space>

```bash
echo "
;re

;(rewrite (dist x y) (dist y x)) ; symmettric
;(rewrite (dist x x) 0.0)

(datatype Expr (X) (Y) (Z))
(function dist (Expr Expr) f64 :merge (min old new))

(rule ((= d (dist x y))) ((set (dist y x) d))) ; symmettric
(rule ((= d (dist x x))) ((set (dist x x) 0.0))) ; reflexive
(rule ((= d1 (dist x y)) (= d2 (dist y z))) ((set (dist x z) (+ d1 d2)))) ; trans
(rule ((= 0.0 (dist x y))) ((union x y))) ; I don't know how this would fire.

(set (dist (X) (Y)) 3.0)
(set (dist (Y) (Z)) 3.0)
(set (dist (X) (Z)) 9.0)

(run 10)
(print dist)

" > /tmp/metric.egg
egglog /tmp/metric.egg


```

Clearly the reading of `(dist x y) = d` is wrong. What I am actually stating logically is `(<= (dist x y) d)`

We don't persay require a lattice. Could just be regulatr partial order + subsumption
`<=` would get confusing when it is actually `max`.

Monotonic functions have a property similar to congruence.
Also continuous functions have epsilon delta definitions.

## Box / Generic DataStructures

You can strip off the simple types of egglog by making a universal box type. This is not so bad as in other languages because datatypes are not closed.
Can make universal list functions in this manner

```bash
echo "
;re
(datatype Box)
(datatype BoxList (Cons Box BoxList) (Nil))
(function _i64 (i64) Box)
(function _String (String) Box)

(function append (BoxList BoxList) BoxList)
(rewrite (append (Nil) l) l)
(rewrite (append (Cons x xs) l) (Cons x (append xs l)))

" > /tmp/box.egg
egglog /tmp/box.egg

```

Note that egglog has [open datatypes](https://www.andres-loeh.de/OpenDatatypes.pdf) by default.

## Disequality

There is no current proposal for a runtime mechanism for disequality that is much better than a brute force `dif/2` table.

```bash
echo '
;re
(datatype Box)
(function Cons (Box Box) Box)
(function boxi64 (i64) Box)
(function Nil () Box)
(relation dif (Box Box))
(rule ((dif a b)) ((dif b a))) ; symmetric

; lift primitive disequality
(rule ((= a (boxi64 x)) (= b (boxi64 y)) (!= x y))
      ((dif a b))
)

; contrapositive injectivity
(rule ((dif (Cons a xs)) (Cons a ys))
      ((dif xs ys))
)
(rule ((dif (Cons a xs)) (Cons b xs))
      ((dif a b))
)

(rule ((= e (Cons x xs))) ; Distict constructors are never equal
      ((dif e (Nil)))
)
(rule ((dif a a)) ((panic "Explode!")))  ; something has gone awry


' > /tmp/dif.egg
egglog /tmp/dif.egg


```

## Inequality

inequalty / partial orders is a very common pattern. What can be done

## Choice Domains

Souffle has a feature called choice-domains which allows something to be set once.
This is emulatable in egglog using the unusual merge function which just tosses aways any new values

```eggsmol
(function choice-example (i64) i64 :merge old)
(set (choice-example 3) 4)
(set (choice-example 3) 5)
(print choice-example)

```

```eggsmol
; Example from https://souffle-lang.github.io/choice
; choice-domain is a somewhat subtle construct
; Using it in combination with other egglog features may be unsound.
; Perhaps it needs to be in it's own strata

(relation edge (String String))

(edge "L1" "L2") (edge "L2" "L10") (edge "L2" "L3")
(edge "L3" "L4") (edge "L4" "L8") (edge "L3" "L6")
(edge "L6" "L8") (edge "L8" "L2")


(function span-tree (String) String :merge old)

(set (span-tree "L1") "root")

(rule ((= (span-tree v) w) (edge v u)) ((set (span-tree u) v)))

(run 10)
(print span-tree)
(check (= (span-tree "L2") "L1"))
(check (!= (span-tree "L2") "L8"))

```

## Refining equalities

Geometry example - directed lines refine

partial functions - restriction of domain

equal up to epsilon. An equality over epsilon families - everythign that has same derivatives

## Integration

```
d(x*x) = x*d(x) + d(x)*x
chain rule can't be written
d(cos(e)) = -sin(e)*d(e) no, this is the chain rule
d(sin(e)) = cos(e)*d(e)

xd(x)

2xcos(x)d(x) -> cos(x*x)d(x*x) 
This works
d(e1 + e2) = d(e1) + d(e2)
d(pow(e,n)) -> pow(e, n-1)*d(e)

d(u*v) = d(u) * v + u * d(v)
d(u)*v -> d(u*v) - v * d(u) - integ by parts
- u substition happen by definition.

(cross u v) 

(* a b)  -> (neg (* b a)) :when (dim a = odd)
d (/ a b) 

int(a,b,f)
int(Domset,f)
sphere_int


int(sphere(R), )
rot_sym(r)
rot_sym(x), rot_sym(y) -> rot_sym(x*y)
rot_sym(x), rot_sym(y) -> rot_sym(x + y)
rot_sym(x) -> rot_sym(f(x))
rot_sym(lit(n))

int(sphere(R), e*d(r)), rot_sym(r) -> 4 * pi * 
int(ball(R))
int(interval(a,b), e*d(x)), dim(e) = 0 -> int(interval(0,1), d(y))
```

Differential forms works. These aren't binding operations anymore. sonova.

`sin(x) = 1`. we are learing about x. exists x. sin(x) = 1

`f(x) = 1`. we are learning about f. closer to forall x. f(x) = 1

The function sin(x) is more like the second. `x` is a coordinate function M -> R.
`sin : (R -> R) -> (M -> R)` is partially applied `comp(sin : R -> R,_)`.
Because of this, we can build in the chain rule.

A different modelling paradigm is to use hoas.
`int(\x -> sin(x))` Now x is alpha bound.

sum, set, fun, differential. WHat are the meanings of these symbols?

Integration:
See rubi
See winston lecture

```prolog

int(sin)

```

<https://github.com/egraphs-good/egg/blob/c590048817a35236ce9910e7c1e0b1fac670822c/tests/math.rs#L179>
Is there an example where the naive approahc is wrong?

Interesting. Metatheory used extraction then diff technqiue
<https://github.com/JuliaSymbolics/Metatheory.jl/blob/9045c7df97b910e57a644bf9c5ddc152d7b0d869/test/integration/cas.jl#L78>

Egraph starts at syntax and moves progressively towards semantics. You have to have a semantics in mind.

Can I do summation? Discrete exterior calculus I guess. Manifestly working in "2d" simplicial space avoids summation swapping problem.

Contour integrals

```bash
echo "
;re
(datatype Expr (Add Expr Expr)
 (Mul Expr Expr) 
 (Lit f64)
  (X) (Y) (R) (Th)
  (Cos Expr) (Sin Expr)
  (Neg Expr) (Pow Expr i64) (Sub Expr Expr) ; (Recip Expr)
  
)
; What "are" Expr? Scalar Fields maybe.

(function D (Expr) Expr)

(ruleset simp)

(rewrite (Neg (Neg x)) x :ruleset simp)
(rewrite (Neg x) (Mul (Lit -1.0) x))
(rewrite (Sub x y) (Add x (Neg y)))

(rewrite (Pow x 0) (Lit 1.0))
(rewrite (Pow x 1) x)
(rewrite (Mul x x) (Pow x 2))
(rewrite (Pow x n) (Mul x (Pow x (- n 1)))
  :when ((!= n 0))
)
(rewrite  (Mul x (Pow x n)) (Pow x (+ n 1)))

(rewrite (Add x y) (Add y x))
(birewrite (Add x (Add y z)) (Add (Add x y) z))
(rewrite (Mul x y) (Mul y x))
(birewrite (Mul x (Mul y z)) (Mul (Mul x y) z))
(birewrite (Mul (Add x y) z) (Add (Mul x z) (Mul y z)))

; solving
; (rule ((= (Add x y) z)) ((set (Sub z y) x)))
; (rule ((= (Add x y) z)) ((set (Sub z y) x)))

; Differentiation rules
(birewrite (D (Add x y)) (Add (D x) (D y))) ; linear
(birewrite (D (Mul x y)) (Add (Mul (D x) y) (Mul x (D y)))) ; product rule
(birewrite (D (Cos x)) (Neg (Mul (D x) (Sin x))))
(birewrite (D (Sin x)) (Mul (D x) (Cos x)))
(rewrite (D (Lit n)) (Lit 0.0))
(rewrite (D (Neg x)) (Neg (D x))) ; probably derived
; (rewrite (D (Pow x n)) (Mul (Lit (- n 1) (D x))))

; integration by parts (product rule with different demand)
(rewrite (Mul u (D v))  
  (Sub (D (Mul u v))
        (Mul v (D u))))


(union (X) (Mul (R) (Cos (Th))))
(union (Y) (Mul (R) (Sin (Th))))

; trig
(rewrite (Add (Mul (Cos x) (Cos x)) (Mul (Sin x) (Sin x))) (Lit 1.0))



(define t1 (Mul (X) (D (X))))
(define t2 (Add t1 t1))

; (define t3 (Mul (D x) (Mul (Cos x) (Cos x))))

; If you want to seek a shape, you can hack in. Don't offer sketch based extraction directly yet
;(relation antideriv (Expr Expr))
;(rule ((= (D x) t)) (antideriv t x))


(run 3)
;(check (= t2 (D (Mul x x))))
(extract t2)
(extract t1)
" > /tmp/integ.egg
egglog /tmp/integ.egg

```

```bash
echo "
%re
cnf(add_assoc, axiom,  add(add(X, Y),Z) = add(X,add(Y,Z))).
cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(mul_assoc, axiom,  mul(mul(X, Y),Z) = mul(X,mul(Y,Z))).
cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(add_mul_distr, axiom, mul(add(X,Y),Z) = add(mul(X,Z), mul(Y,Z))).
cnf()
" > /tmp/integ.tptp
vampire /tmp/integ.tptp

```

## BitVectors

<https://stackoverflow.com/questions/8273033/use-of-term-rewriting-in-decision-procedures-for-bit-vector-arithmetic>

```python
from z3 import *

x,y,z = BitVecs("x y z", 8)

# it doesn't pretty print assoc so good
rw2  = [
    (x + y) + z == x + (y + z)
]

rw = [
  x + y == y + x,
  x * y == y * x,
  -(-x) == x,
  x & y == y & x,
  x | y == y | x,
  x | (y & z) == (x | y) & (x | z),
  ~(~x) == x,
  ~(x | y) == ~x & ~y,
  ~x | ~y == ~(x & y),

  # x |  == True,


]

for rule in rw + rw2:
  prove(rule)

for rule in rw:
  print(rule.sexpr().replace("=", "rewrite"))

```

```python
# micro ruler
from z3 import *
import itertools
x,y,z = BitVecs("x y z", 8)

def genexpr():
  yield from (x,y,z)
  for i in genexpr():
    yield from (~i, -i)
    for j in genexpr():
      yield from (x + y, x - y)

exprs = {x,y}
for i in range(3):
  
  a = {~ i for i in exprs }
  b = {- i for i in exprs }
  c = {i + j for i in exprs for j in exprs }
  d = {i - j for i in exprs for j in exprs }
  exprs.update(a)
  exprs.update(b)
  exprs.update(c)
  exprs.update(d)


#exprs = itertools.islice(genexpr(), 10)
"""
for e1 in range(10):
  for e2 in 
  s = Solver()
  eq = e1 == e2
  s.add(Not(eq))
  if s.check() == unsat:
    print(eq.sexpr().replace("=", "rewrite"))
"""
print(exprs)
```

```bash
echo "
;re
;(datatype Size (Lit i64))
(datatype BV (Zero i64) (One i64) (Lit i64 i64)
  (bvnot BV) (bvand BV BV) (bvor BV BV) ; bitwise
  (bvadd BV BV) (bvneg BV) (bvmul BV BV) ; arith
  ;predicates
  ;
  (concat BV BV)
)
(ruleset bitblast)
(ruleset simp)

(rewrite (bvadd (bvadd x y) z) (bvadd z (bvadd y z)) :ruleset simp)

(function size (BV) i64)
(rewrite (Zero i) i)
(rewrite (One i) i)

(rewrite (bvadd x y) (bvadd y x))
(rewrite (bvmul x y) (bvmul y x))
(rewrite (bvneg (bvneg x)) x)
(rewrite (bvand x y) (bvand y x))
(rewrite (bvor x y) (bvor y x))
(rewrite (bvor x (bvand y z)) (bvand (bvor x y) (bvor x z)))
(rewrite (bvnot (bvnot x)) x)
(rewrite (bvnot (bvor x y)) (bvand (bvnot x) (bvnot y)))
(rewrite (bvor (bvnot x) (bvnot y)) (bvnot (bvand x y)))



" > /tmp/bitvector.egg
egglog /tmp/bitvector.egg


```

```python
# ingest smt using z3 parser, hack it to get in egglog form.
from z3 import *
import egglog

smtstring ="(define x )"


if __name__ == "main":

```

```python
from io import StringIO
from pysmt.smtlib.parser import SmtLibParser

# To make the example self contained, we store the example SMT-LIB
# script in a string.
DEMO_SMTLIB=\
"""
(set-logic QF_LIA)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun x () Bool)
(declare-fun y () Bool)
(define-fun .def_1 () Bool (! (and x y) :cost 1))
(assert (=> x (> p q)))
(check-sat)
(push)
(assert (=> y (> q p)))
(check-sat)
(assert .def_1)
(check-sat)
(pop)
(check-sat)
"""

# We read the SMT-LIB Script by creating a Parser.
# From here we can get the SMT-LIB script.
parser = SmtLibParser()

# The method SmtLibParser.get_script takes a buffer in input. We use
# StringIO to simulate an open file.
# See SmtLibParser.get_script_fname() if to pass the path of a file.
script = parser.get_script(StringIO(DEMO_SMTLIB))
```

Use ruler rules?

```python
import urllib.request, json 
with urllib.request.urlopen("https://nightly.cs.washington.edu/reports/ruler/1691466530%3Anightly%3Amain%3Aeb702fc89b/data/output.js") as url:
    data = json.loads(url.read().decode().replace("var data =", ""))
    for ex in data:
      if "rules" in ex and "spec_name" in ex:
        pass
        #print(ex["spec_name"])
        #print(ex["rules"])
        #print("\n".join(["(rewrite " + rule.replace(" ==>", "") + ")" for rule in ex["rules"]]))
      if "direct_gen" in ex:
        print(ex["domain"])
        ex = ex["direct_gen"]
        print("\n".join(["(rewrite " + rule.replace(" ==>", "") + ")" for rule in ex["rules"]]))


```

## Peano

```eggsmol
;re
(datatype Nat (Z) (S Nat))
(function plus (Nat Nat) Nat)
(birewrite (plus (Z) m) m)
(birewrite (plus (S n) m) (S (plus n m)))

;(relation lte (Nat Nat))

(push)
(function X () Nat)
(function Y () Nat)

(define t1 (plus (X) (Y)))
(define t2 (plus (Y) (X)))

(push)
; case x = zero
(union (Z) (X))
(run 10)
(check (= t1 t2))
(pop)

; case X = SUCC(A), induction hypothetsis plus(A,Y) = plus(Y,A)
(function (A) Nat)
(union (S (A)) (X))
(union (plus (A) (Y)) (plus (Y) (A)))
(run 10)
(check (= t1 t2))
(pop)

```

Binary nats

```eggsmol
(datatype Even (Z) (SO Odd) (DE Even) (DE Odd))
(datatype Odd (SE Even))
```

```
(datatype Rational1 (Ratio Nat Nat))

(datatype Real (Rat Rational) (sin Real) (cos Real) (plus Real Real) (mul Real Real))

```

## BDDs

```eggsmol
; Binary Decision Diagrams are if-then-else trees/ compressed tries that hash cons their leaves
; This is easily expressible in the facilities provided. Everything in egg-smol is automatcally shared
; and Compression is easily expressible as a rule.

; They are a notion of first class set useful for certain classes of uniformly describable sets.
; https://en.wikipedia.org/wiki/Binary_decision_diagram
; https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf Type-Safe Modular Hash-Consing - Section 3.3

(datatype BDD
    (ITE i64 BDD BDD) ; variables labelled by number
    (True)
    (False)
)

; compress unneeded nodes
(rewrite (ITE n a a) a)

(function and (BDD BDD) BDD)
(rewrite (and (False) n) (False))
(rewrite (and n (False)) (False))
(rewrite (and (True) x) x)
(rewrite (and x (True)) x)
; We use an order where low variables are higher in tree
; Could go the other way.
(rewrite (and (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (and a1 (ITE m b1 b2)) (and a2 (ITE m b1 b2)))
    :when ((< n m))
)
(rewrite (and (ITE n a1 a2) (ITE m b1 b2))
    (ITE m (and (ITE n a1 a2) b1) (and (ITE n a1 a2) b2))
    :when ((> n m))
)
(rewrite (and (ITE n a1 a2) (ITE n b1 b2))
    (ITE n (and a1 b1) (and a2 b2))
)

(define b0 (ITE 0 (True) (False)))
(define b1 (ITE 1 (True) (False)))
(define b2 (ITE 2 (True) (False)))

(define b123 (and b2 (and b0 b1)))
(define b11 (and b1 b1))
(define b12 (and b1 b2))
(run 5)
(extract b11)
(extract b12)
(extract b123)
(check (= (and (ITE 1 (True) (False)) (ITE 2 (True) (False)))
       (ITE 1 (ITE 2 (True) (False)) (False)))
)
;(check (= b123 (ITE 3 ()))

(function or (BDD BDD) BDD)
(rewrite (or (True) n) (True))
(rewrite (or n (True)) (True))
(rewrite (or (False) x) x)
(rewrite (or x (False)) x)
(rewrite (or (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (or a1 (ITE m b1 b2)) (or a2 (ITE m b1 b2)))
    :when ((< n m))
)
(rewrite (or (ITE n a1 a2) (ITE m b1 b2))
    (ITE m (or (ITE n a1 a2) b1) (or (ITE n a1 a2) b2))
    :when ((> n m))
)
(rewrite (or (ITE n a1 a2) (ITE n b1 b2))
    (ITE n (or a1 b1) (or a2 b2))
)

(define or121 (or b1 (or b2 b1)))
(run 5)
(extract or121)

(function not (BDD) BDD)
(rewrite (not (True)) (False))
(rewrite (not (False)) (True))
(rewrite (not (ITE n a1 a2)) (not (ITE n (not a1) (not a2))))

(function xor (BDD BDD) BDD)
(rewrite (xor (True) n) (not n))
(rewrite (xor n (True)) (not n))
(rewrite (xor (False) x) x)
(rewrite (xor x (False)) x)
(rewrite (xor (ITE n a1 a2) (ITE m b1 b2))
    (ITE n (xor a1 (ITE m b1 b2)) (or a2 (ITE m b1 b2)))
    :when ((< n m))
)
(rewrite (xor (ITE n a1 a2) (ITE m b1 b2))
    (ITE m (xor (ITE n a1 a2) b1) (or (ITE n a1 a2) b2))
    :when ((> n m))
)
(rewrite (xor (ITE n a1 a2) (ITE n b1 b2))
    (ITE n (xor a1 b1) (xor a2 b2))
)


```

## First Class Union Find

```eggsmol
; A "first class" / local / scope union find is encodable in egglog.
; This is perhaps not surprising, since there are also encodings to 
; souffle subsumption
; It's fairly natural to write though

;Similar to how a union find is encodable into Souffle using subsumption, union finds are encodable into egglog using a merge function.
;This is particularly interesting as I think it gives a notion of a "scoped", "keyed", or "first class" union find, if we expose the ability to compare eids. This is a very natural way of "reifying" equality in the context of egglog rather than reifying to an eq relation. It may be important to have the notion of the first class UFs notion of tie breaking match the internal egglog tie breaker (if possible).
;It may also be possible to encode generalized union finds whose edges are labelled by group elements.
;It is interesting to note that the keyed union find is kind of separating off a segment of the global union find for it's own use.


(function root (i64) i64 :merge (min old new))

; To make this more first class
; One can give union finds some kind of posibly structured "name" 
; in the standard first orderi representation of named first class functions
; (function apply_uf (Name i64) i64)

; root being undefined is it being the same eclass as itself

; reflexivity

; should this work?
;(rule ((< x (root x))) ((set (root x) x)))
(rule ((= y (root x)) (< x y)) ((set (root x) x)))

; transitivity
(rule ((= (root x) y) (= (root y) z)) 
    ((set (root x) z))
)

(set (root 0) 1)
(set (root 1) 2)
(set (root 4) 7)
(set (root 7) 0)
(set (root 7) 7)

(run 10)
(print root)
(check (= (root 0) (root 4)))


(datatype EClass)

; way more direct encoding

(function root2 (i64) EClass)

(set (root2 0) (root2 1))
(set (root2 1) (root2 2))
(set (root2 4) (root2 7))
(set (root2 7) (root2 0))
(set (root2 7) (root2 7))
(run 10)
(print root2)
(check (= (root2 0) (root2 4)))


; A keyed union find built out of union operations.

(datatype UF (Union i64 i64 UF) (Empty))
(function root3 (UF i64) EClass)

; These are nice compression laws / extensionality, but not necessary
; They are definitely not complete extensionality
; (rewrtie (union i j (union k l uf))) (union k l (union i j uf))))
(rewrite (Union i i uf) uf)
(rewrite (Union i j uf) (Union j i uf))
(rewrite (Union i j uf) uf
    :when ((= (root3 uf i) (root3 uf j))))

;(rewrite (root3 (Union i j uf) a) (root3 (Union i j uf) b)
; :when ((= (root3 uf a) (root uf b)))
;)

; Maybe this is smarter. Does this copy cleanly?
; Well it makes demand which is nice.
; And it avoid the large number of bound variables of the other trasnference rules.

(rewrite (root3 (Union i j uf) i) (root3 (Union i j uf) j))
(function root3-trans (UF EClass) EClass)
(rewrite (root3 (Union i j uf) a) (root3-trans (Union i j uf) (root3 uf a)))

(define uf1 (Union 2 3 (Union 1 2 Empty)))
(define r1 (root3 uf1 1))
(define r3 (root3 uf1 3))
(define r4 (root3 uf1 4))
(run 10)
(check (= r1 r3))
(check (!= r1 r4))
(print root3)
(print Union)



; It also plays nice with eclasses
;(datatype EClass (Name String))
; Need to define min. For this purpose, min over eids is probably ok?
;(function root2 (EClass) EClass :merge (min old new))

;(rule ((= y (root2 x))) ((set (root2 x) x)))

; transitivity
;(rule ((= (root2 x) y) (= (root2 y) z)) 
;    ((set (root2 x) z))
;)


; To use a particular first class union find in a rule under context C
; 
; one needs to now explicitly join with respect to (apply_uf C _) 
; over the eq relation. This is _not_ an N^2 join though. Maybe it is...


```

## Homotopy

## Kleene Algebra

## Matrices

## Category

## Typechecking

[Eqlog](https://www.mbid.me/posts/type-checking-with-eqlog-polymorphism/)
Vec example
Yihong hindley Milner

; <https://courses.engr.illinois.edu/cs522/sp2016/PureTypeSystemsInRewritingLogic.pdf>
; Pure Type Systems in Rewriting Logic:
; Specifying Typed Higher-Order Languages
; in a First-Order Logical Framework

## Intervals

[Interval Constraint Propagation](https://en.wikipedia.org/wiki/Interval_propagation)

## Context

Sam's paper. Assume nodes.

## Lambdas

First class function objects.

Non capturing lambdas: Just can pull out of an arguments object.

```
(datatype Fun)
(datatype Args (args))
(datatype Term)
(function call (Fun Args) Term) ; apply?

(function lambda1 (Term) Fun) ; no capturing allowed
(function arg (i64 Args) Term)


(define myadd (lambda1 (+ (arg 0 (args)) ((arg 1 (args))) )))

; indeed we recover alpha equivalence
(define myadd2 (lambda1 (+ (arg 0 (args)) ((arg 1 (args))) )))

; indeed we can observe extensional equality. myadd2 can be discovered to be equal to
(define myadd2 (lambda1 (+ (arg 1 (args)) ((arg 2 (args))) )))

(rewrite (apply (lambda1 body) args))
(let args body))

(function let1 (Args Term) Term)
(rewrite (let1 a (+ x y))  
  (+ (let a x) (let a y))
)

; OR we can defin super paplication to short circuit the let. Different choices for different desires.
(rewrite (apply myadd1 args)
  (+ (arg 1 args) (arg2 args) )
)


(define curryadd
  (lambda1 (apply myadd1 (store  (args)))
)

```

```
(datatype Lambda (Lam Expr))
(datatype Expr (EnvVar i64) (Var i64) (Add Expr Expr))
(datatype Closure (Close Env Lam))

(define curryadd (Lam 
  (Close (ECons (Var 0))
         (Lam (Add (Evar 0) (Var 0))
))))


```

### Normalization by Evaluation

## Let

`let` is a reified notion of sharing or subsitutions. There is a calculus of pushing lets through. `let` could be written as `subst`. They are very related notions.
Application of a lambdas converts it to a let.

<https://github.com/remysucre/triangles/blob/main/src/main.rs>

## Polynomials

## Arrays/Maps

One of the most useful SMT theories is that of arrays. Arrays can equally be called the theory of total maps.

```eggsmol
(datatype Int (Lit i64))
(datatype Array (Empty Int))


```

Observation Tries - do a trie set/map based on observations.

```eggsmol
; Smtlib theory of arrays
; https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml
; http://smtlib.cs.uiowa.edu/version1/theories/Arrays.smt

(datatype Math
  (Num i64)
  (Var String)
)


(datatype Array
  (Const i64)
  (AVar String)
)

(function add (Math Math) Math)
(function select (Array Math) Math)
(function store (Array Math Math) Array)

(relation neq (Math Math))

(rule ((neq x y))
      ((neq y x)))

(rule ((neq x x))
      ((panic "query (neq x x) found something equal to itself")))


; injectivity rules take not equal to not equal.
(rule  ((neq x y) (= (add x z) e))
       ((neq (add x z) (add y z))))
(rule  ((= (add x (Num i)) e) (!= i 0))
       ((neq e x)))


(rule ((= (Num a) n1) (= (Num b) n2) (!= a b))
      ((neq n1 n2)))

; select gets from store
(rewrite (select (store mem i e) i) e)
; select passes through wrong index
(rule ((= (select (store mem i1 e) i2) e1) (neq i1 i2))
      ((set (select mem i2) e1)))
; aliasing writes destroy old value
(rewrite (store (store mem i e1) i e2) (store mem i e2))
; non-aliasing writes commutes
(rule ((= (store (store mem i2 e2) i1 e1) mem1) (neq i1 i2))
      ((set (store (store mem i1 e1) i2 e2) mem1)))

; typical math rules
(rewrite (add x y) (add y x))
(rewrite (add (add x y) z) (add x (add y z)))
(rewrite (add (Num x) (Num y)) (Num (+ x y)))

(define r1 (Var "r1"))
(define r2 (Var "r2"))
(define r3 (Var "r3"))
(define mem1 (AVar "mem1"))

(neq r1 r2)
(neq r2 r3)
(neq r1 r3)
(define test1 (select (store mem1 r1 (Num 42)) r1))
(define test2 (select (store mem1 r1 (Num 42)) (add r1 (Num 17))))
(define test3 (select (store (store mem1 (add r1 r2) (Num 1)) (add r2 r1) (Num 2)) (add r1 r3)))

(run 4)
(check (= test1 (Num 42)))
(check (neq r1 r2))
(check (neq r1 (add r1 (Num 17))))
(check (= test2 (select mem1 (add r1 (Num 17)))))
(check (= test3 (select mem1 (add r1 r3))))



```

## Resolution

<https://github.com/inpefess/tptp-lark-parser/tree/master>
<https://github.com/AndrzejKucik/tptp_python_parser>

```python
from tptp_lark_parser import TPTPParser
from tptp_lark_parser.grammar import Variable, Function, Predicate
tptp_parser = TPTPParser()
parsed_text = tptp_parser.parse("""
cnf(add_assoc, axiom,  add(add(X, Y),Z) = add(X,add(Y,Z))).
cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(assoc, axiom,  times(times(X, Y),Z) = times(X,times(Y,Z))).
%cnf(comm, axiom, mul(X,Y) = mul(Y,X)).
%cnf(add_mul_distr, axiom, mul(add(X,Y),Z) = add(mul(X,Z), mul(Y,Z))).""")
clause_literals = parsed_text[0].literals
print(parsed_text)
print(clause_literals[0].atom.index)
#print(dir(tptp_parser))
#print(dir(tptp_parser.cnf_parser))
#print(tptp_parser.cnf_parser.token_map)
#print(tptp_parser.cnf_parser.token_map.keys())

fun_map = {v : k for k,v in tptp_parser.cnf_parser.token_map["functions"].items()}
pred_map = {v : k for k,v in tptp_parser.cnf_parser.token_map["predicates"].items()}
var_map = {v : k for k,v in tptp_parser.cnf_parser.token_map["variables"].items()}
print(pred_map[clause_literals[0].atom.index])

def format(f):
  if isinstance(f,Variable):

    return var_map[f.index]
  if isinstance(f,Function):
    name = fun_map[f.index]  
    args = " ".join(map(format, f.arguments))
    return f"({name} {args})"
  elif isinstance(f,Predicate):
    name = pred_map[f.index]
    if name == "=":
      name = "birewrite"
    args = " ".join(map(format, f.arguments))
    return f"({name} {args})"
  else:
    assert False

for clause in parsed_text:
  assert(len(clause.literals) == 1)
  print(format(clause.literals[0].atom))


import glob
for filename in glob.glob("/home/philip/Downloads/TPTP-v8.2.0/Axioms/*.ax"):
  print(filename)
  with open(filename) as f:
    tptp = tptp_parser.parse(f.read())
    print(tptp)



```

Do Sets "just work" now?

```
(relation elem ((Set Term) Term))

```

## SMTLIB

```python
import egglog
from z3 import *

x,y,z = Ints("x y z")

e = x + y + z

def format(e):
  c = map(format, e.children())



```

## The Chase

The procedure of egglog is intimately related to the chase.

The chase is used for reasoning about conjunctive queryes under schema (functional dependencues, tuple gen deps, eq gen deps). Data migration, some other things.

Understand chase applications, translate when possible to egglog

## Partial Application

`call` is super useful
The applicative encoding
We can do it manually to see how useful it is
Lambda lifting for binders

Monads / algerbaic effects

```egglog

(function cont1/0)
(define prog
  (set_ "x" 1 cont1/0)
)

(function cont1/1)
(rewrite (apply cont1/0 x) (cont1/1 x))
(rewrite (cont1 w)

)

; the obvious thing
; what is the issue if any?
(define prog
(seq 
  (set "x" 1)
  (set "y" 2)
))

; semantics of set is state -> state function
; seq is composition. Fine.
; var "x" is state -> int
; 


```

## RVSDG

SSA can be converted to a purely functional program <https://www.cs.princeton.edu/~appel/papers/ssafun.pdf>

The recipe is:

- make a function defintion for each block with the block's name
- Each phi node actually corresponds to a function call at the end of the incoming block. These function calls carry the variables that need to go into the function body. The outputs of the phi nodes are the arguments of the current block-function

```
fact:

loop:
 x <- x + 1 
end:

```

```ocaml
let fact x = 
  let rec loop = 
  and 

```

We want as much to be dataflow as possible. That is where egraph shines.

An interstig design angle is to disallow varable capture. This is what sharpe's optir is doing.
This is also what lambda-lifting does. Lambda lifting turns capture into threading extra parameters. This requires adjuestment of call sites of functions, so if you don't know what function you're calling, it doesn't work?

Now "de bruijn" indces aren't expressing traversing binding sites, it is just the variable argument number.

[Supercombinators](https://en.wikipedia.org/wiki/Supercombinator). SKI combinators are sufficient to express lambda calculus. But then you are doing a ton of equational manipulations. Doing a bunch of combinator reductions or manipulations for basically and often doesn't match the efficient thing for a target platform.
The supercombinator idea is to

Egraphs are essentially first order. Compiling programs to a first order form is analagous in itself to first ordering lambda expressions, or compiling to assembly. Egraphs are almost a machine.

Super blocks
<https://www.cs.princeton.edu/courses/archive/spr04/cos598C/lectures/05-Superblocks.pdf>

Is this even interesting? C doesn't really have a notion of variable capture in function calls. But mutation itself is a form of let capture
Allow multi-arity. Disallow
Everything must be

```
(datatype 1->1)
(datatype 2->1)
(datatype 2->2)

(datatype Func)
(datatype Expr)
(datatype Expr* (Cons Expr Expr*) (Nil))

(datatype Tup1)
(datatype Tup2 (Pair Expr Expr))


(function func-1-inputs-1-outputs (Expr) RVSDG)
(function func-1-inputs-2-outputs (Expr Expr) RVSDG)
(function func-2 (Expr Expr) RVSDG)
(function func (Expr*) Func)
(function call* (Func Expr*) Expr*) ; multiple input ultiple output
(function call1)
(function call2 (Func Expr Expr) Expr*)
(rewrite (call2 f e1 e2) (call f (Cons e1 (Cons e2 (Nil)))))
;(function call (Func Env) Expr)

(function get (i64) Expr)

(define neg (func-1-inputs-1-outputs (* -1 get-0)))
; specializing call to neg to get it in one shot.
(rewrite (call neg (Cons e (Nil))) (* -1 e))

(func-2-inputs-1-outputs (+ get-0 (get-0 (call ?neg get-1))))


(function call1 (RVSDG Expr) Expr)
(function subst1 (Expr Expr) Expr)

(rewrite (call1 (func-1-input1-1-output1 e) e1) (subst1 e e1))
(rewrite (subst1 (* a b) e) (* (subst1 a e) (subst1 b e)))
(rewrite (subst1 (get 0) e)) e)
(rewrite (subst1))
(rewrite (subst (call1 f x) e) (call1 f (subst1 x e))) ; we don't substitue into the function. Only explicit capture allowed

; hmm   maybe not recursing into the definition is what makes this different

; no capture is allowed. Anything body needs is explicitly passed (lambda lifting)
; But in exchance we have multi-arity as a primitive.
; slash we lift everything to work over lists? Whch is a curious form of env.
; The syntax of the language let's us restrict the context.

(function call2 (RVSDG Expr Expr) Expr)


(rewrite (= f  ... (call f)) (loop ))
```

```egglog
(function block1 () Int)

```

## Algebra of Programming

I feel as though RVSDG are a first order functional language using supercombinators

## AC

See blog post for some ideas

Primitive multisets. How much does this get you?

```python

def msunion(m1,m2):
  d = {k:v for k,v in m1}
  for k,v in m2:
    if k in d:
      d[k] += v
    else:
      d[k] = v
  return d

def msdiff(m1,m2):
  d = {k:v for k,v in m1}
  for k,v in m2:
    if k in d:
      d[k] += v
    else:
      d[k] = v
  return d


def sing(k):
  return {k : 1}

def add(m,k):
  m = m.copy()
  if k in m:
    m[k] += 1
  else:
    m[k] = 1

def card(d):
  return sum(k.values())
# patterns
def partitions(d): # (?X + ?Y)

# (?X + ?Y + ?Z)

def items(d):  # (?x + ...)
  for k,v in d.items():
    for i in range(v):
      yield k
# (?x + ?y + ...)

# (?x + ?y)


```

# Egglog0 posts

<https://www.philipzucker.com/egglog0>

<iframe width="560" height="315" src="https://www.youtube.com/embed/dbgZJyw3hnk?start=2725" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

Github repo: <https://github.com/philzook58/egglog0>
Read more here:

- [Talk abstract](https://github.com/philzook58/egglog0-talk/blob/main/out.pdf)
- <https://www.philipzucker.com/egglog-checkpoint/> - Early version of egglog, motivations.
- <https://www.philipzucker.com/egglog2-monic/> - A simple category theory theorem about pullbacks.
- <https://www.philipzucker.com/egglog-3/> - Arithmetic, SKI combinator, datalog, lists examples

# Souffle Posts

## Merging Database

It's interesting (to me) how similar this is to the union find dict. The difference is that all the tables share the same union find.
This formulation of merge and default functions is not mine. Some mix of yihong, max, remy, or zach came up with it.

```python
class BadUF():
  # no path compression. no depth stroage.
  def __init__(self):
    self.parent = []
  def find(self,i):
    p = self.parent[i]
    while p != self.parent[p]: # walrus?
      p = self.parent[p]
    return p
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    return x
  def set_size(self,n):
    while len(self.parent) < n:
      self.makeset()
    return
  def union(self,i,j):
    i = self.find(i)
    j = self.find(j)
    self.parent[i] = j
    return j


class DB:
  uf: BadUF
  tables: Dict[str,Any]
  merge: Dict[str,]
  default:Dict[str,]

  def set_(self, tablename, key, value):
    table = self.tables[tablename]
    if key in table:
      table[key] = self.merge[tablename](table[key], value)
    else:
      table[key] = value
  def union(self, x,y):
    return self.uf.union(x,y)
  def define(self, tablename, key):
    table = self.tables[tablename]
    if key in table:
      return table[key]
    else:
      v = self[tablename].default(key)
      table[key] = v
      return v
  def __get__(self, k):
    tablename, *k = k
    return self.tables[tablename][k]
  def rebuild(self):
    uf = self.uf
    for tablename, table in self.tables.items():
      temp = {}
      for k,v in table.items():
        temp[map(uf.find, k)] = uf.find(v)
      # Is this mutation wise? maybe not.
      self.tables[table] = temp
        
# struct of arrays ve array of structs




# merge dicts have their own definition of union
```

```python
from typing import TypeVar, Generic, Callable
K = TypeVar('K')
V = TypeVar('V')

# merge dict is a very natural extension of python's
# built in defauldict
# can capture uf in closures.

# man python typing is goofy
class MergeDict(Generic[K, V]):
  table: dict[K,V]
  default: Callable[K,V]
  merge: Callable[[K,K],V]

  def __init__(self, default=None, merge=None):
    self.table = {}
    self.default = default
    self.merge = merge
  def extend(self, items):
    for k,v in items:
        self[k] = v
  def items(self):
    yield from self.table.items()

  def keys(self):
    yield from self.table.keys()

  def __setitem__(self, key, value):
    if key in self.table:
      if self.merge != None:
        self.table[key] = self.merge(self.table[key], value)
      else:
        if self.table[key] != value:
            raise KeyError
    else:
      self.table[key] = value
    
  def __getitem__(self,key):
  # Is get memoized or not?
    if key in self.table:
      return self.table[key]
    else:
      if self.default != None:
        v = self.default(key)
        self.table[key] = v
        return v 
      else:
        raise KeyError
  def __repr__(self):
    return repr(self.table)


def UnitRelation():
    return MergeDict(merge = lambda x,y: ())

path = UnitRelation()
edge = UnitRelation()


edge[(1,2)] = ()
edge[(2,3)] = ()


def run(edge,path):
    path.extend([((x,y), ()) for x,y in edge.keys()]) # path(x,y) :- edge(x,y).
    path.extend([((x,z), ()) for x,y in edge.keys() for y1,z in path.keys() if y == y1]) # path(x,z) :- edge(x,y),path(y,z).

for i in range(10):
    run(edge,path)
print(edge)
print(path)


path = MergeDict(merge=lambda x,y:min(x,y))
edge = MergeDict(merge=lambda x,y:min(x,y))

edge[(1,2)] = 10
edge[(2,3)] = 3
edge[(1,3)] = 20


def run(edge,path):
    path.extend([((x,y), cost) for (x,y),cost in edge.items()]) # path(x,y) :- edge(x,y).
    path.extend([((x,z), c1 + c2) for (x,y),c1 in edge.items() for (y1,z),c2 in path.items() if y == y1]) # path(x,z) :- edge(x,y),path(y,z).

for i in range(10):
    run(edge,path)
print(edge)
print(path)
```

- The edges of comprenhensions start creaking. They aren't really overloadable enough
- flattening `add[(add(x,y),z)`. This is tablized adt datalog, not persay egglog
-

```python

class Var():
    name:str
    def __call__(self, k):
        return {self.name: k}
class MergeDict():
    def __call__(self,*args):
        for ks,v in self.items():            
            for k, arg in zip(ks,args):
                yield from arg(k) kind of
```

Modelling as
type gen = (subst, outval) -> list subst
This is basically top down ematching search.
I guess we could use [] for bottom up, and () for top down... that's not horrible.
Could literally try to do embedded gj. The idea being it is in some sense simpler.

Hmm. It's kind of an overloading of how subst dicts are merged... We could do normalization there?

Flattening is related to compiling to assembly. Very related. Hmm.

```ocaml
type expr = loc * bindings
let foo (a, froms, wheres) = 
  "freshrow.res", (foo,"freshrow") :: ,  ("freshrow.x = " ^ a) :: wheres   
```

It's a writer monad for froms and wheres. We should go top down to make biding pattern variables easy.

```python
counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def foo(a):
  def res():
    (rid, froms, wheres) = a()
    row = freshrow()
    return (f"{row}.rowid",  [f"foo as {row}"] + froms, [f"{rid} = {row}.a"]+ wheres)
  return res

def x():
  row = freshrow()
  return (row + ".rowid" ,[f"x AS {row}"], [])

def func(f):
  def res(*args):
    def res1():
      args = [arg() for arg in args]
      rids, froms, wheres = zip(*args)
      row = freshrow()
      (f"{row}.rowid",  [f"{f} as {row}"] + froms, [f"{rid} = {row}.arg{n}" for n,rid in enumerate(rids)] + wheres)
    return res1
  return res

print(foo(foo(x))())

```

How do we deal with variables? It's like datalog problems but more so.
`from foo as row, (select row.a) as x,` does this work?
analog of turn `let x = row.a` into `for x in [row.a]` where select plays role of []. Not really that much less complex. You still need to maintani a compile time env with a bool instead of a column.

What about GJ. GJ is actually pretty simple.

Trie. `(k, )` `dict[dict]
[None] = data held

```python
def insert(trie, k, v):
  node = trie
  for n in k:
    tnode = node.get(n)  
    if tnode == None:
      tnode = {}
      node[n] = tnode
    node = tnode
  node[None] = v

def lookup(trie, k):
  node = trie
  for n in k:
    node = node.get(n)
    if node == None:
      return None  
  return node.get(None)

t1 = {}
insert(t1,"aaa", "fred")
insert(t1,"aab", "larry")
insert(t1,"aac", "larry")
insert(t1,"ac", "gary")
print(lookup(t1, "aa"))
print(t1)

def of_keys(keys):
  t = {}
  for k in keys:
    insert(t,k, ())
  return t
print(of_keys([(1,2), (3,4), (1,4)]))

def rel2(table):
  empty_row = ()
  def res(nx,ny): # take in the order of where will appear?
    return of_keys([ (empty_row[nx] := row[0])[ny] := row[n1]   for row in table]) # this is not valid python
  # ok. We Have to address compression.
  # Then the semantics is just sets over all variables in play in a particular order.
  # path |= forall(lambda (x,y,z,w): (& & & &).proj(x,y))
```

```sql
-- canonicalize
insert into mytab select root(a), root(b), root(c) from mytab on conflict set c = union(c, excluded.c)
```

In the experiment, I tried internalizing the union find into sql. Maybe it is simpler not to

Wasm based union find? Would that be fun?

```python
class BadUF():
  # no path compression. no depth stroage.
  def __init__(self):
    self.parent = []
  def find(self,i):
    p = self.parent[i]
    while p != self.parent[p]: # walrus?
      p = self.parent[p]
    return p
  def makeset(self):
    x = len(self.parent) # right? 
    self.parent.append(x)
    return x
  def set_size(self,n):
    while len(self.parent) < n:
      self.makeset()
    return
  def union(self,i,j):
    i = self.find(i)
    j = self.find(j)
    self.parent[i] = j
    return j


import sqlite3
uf = UF()
conn = sqlite3.connect(":memory:")
cur = conn.cursor()
conn.create_function("_union", 2, lambda (x,y): uf.union(x,y))
conn.create_function("_find", 1, lambda (x): uf.find(x))

cur.execute("create table add(a,b, unique fd (a,b))")
cur.execute("insert into add select _root(a), _root(b) from add on conflict fd update set rowid = union(rowid, excluded.rowid)") 
cur.execute("insert into add select a,b from add as l, add as r where _root(l.rowid) = _root(r.rowid) ON CONFLICT ")


```

## Extraction as datalog

```souffle

.decl add0(x:number, y : number, z : number)
.decl num(x:number, y : number)
.decl add(x:number, y : number, z : number)

.type AExpr = Add {x : AExpr, y : AExpr} | Num {n : number}

.input add0(filename="../subsumpt/add0.facts")

// This is because of my sloppy previous encoding
num(i, i) :- add0(i, _, _), ! add0(_,_,i).
num(i, i) :- add0(_, i, _), ! add0(_,_,i).

.decl depth(id : number, d : unsigned) 
depth(i, 0) :- num(_,i).
depth(z, max(dx,dy) + 1) :- add0(x,y,z), depth(x,dx), depth(y,dy).

// min lattice
depth(x,d) <= depth(x, d1) :- d1 <= d.

// .output depth(IO=stdout)
add(x,y,z) :- (num(_, x) ; add(_,_,x)), (num(_, y) ; add(_,_,y)),
              d = min d1 : {add0(x,y,z1), depth(z1, d1)},  depth(z,d), add0(x,y,z).

.decl tree(id: number, e : AExpr) choice-domain id
tree(j, $Num(i)) :- num(i, j).
tree(z, $Add(tx,ty)) :- tree(x,tx), tree(y,ty), add(x,y,z).

.output tree(IO=stdout)

```

# Misc

<https://www.mbid.me/eqlog-algorithm/> Martin E. Bidlingmaier basically developed a system similar or identical to egglog on completely parallel lines. Maybe that means it's a good/natural idea?

## Modulo theories

Grobner bases are ~ knuth bendix method. Completion algorithm.
Modulo some a priori known equations.
Do grobner as a preprocessing step. Akin to running knuth bendix as preprocesing step.
= polynomials as objects modulo grobner. This is like datalog modulo term rewriting.

relations vs objects vs rules.
first class rules (rules as objects). first class sets (relations as objects). both blur the lines.
rules as relations?
(<=) : R -> R -> Bool
vs (<=) : R^n -> Bool
are pretty different.

first class rules ~ contexts. Kind of like sequent is first class inference rule.

Difference logic theory = theory of shortest path

galois connction between octagons and polytopes. Can we compute the relaxation of a polytope? It is a bunch of linear programming query. Can we do better?

maximize xi - xj s.t. polytyop
best objective c is then a bound. xi-xj <= c

likewise for intervals. Or any set of hyperplanes.

linear objective subject to difference constraints? probably.
Best interior octagon? Usually get a bunch of feasible points and construct convex hull. Can I build an octagon out of points? What are "best" points. Well, I could construct a polyhedra out of the points.

## Propagators

The whole database as a cell
Each relation as a cell

Context
R(x+y)
R may have arbtrary extent.
During term rewrting, we can track it. In egraphs we can't (unless I build it there)

```
let rewrite ctx t = 
```

## AC

Let's dial back to terms. What is wrong with using unordered vertices as "AC-nodes". Relational matching ought to basically work.

```
a \
b--ac - + - 
c /
```

```sql
create table plus(ac unique); -- functional to rowid
create table lit(n unique); -- functional to rowid
create table ac(in_,out_); -- a many to many relationship. A special table with special rebuild. Multiset semantics because can have terms like "a" + "a" + "a"
-- construct a + b + c as 
-- lit a  \
-- lit b -- ac - plus - 
-- lit c  /
insert into lit values ("a"), ("b"), ("c");--select * from generate_series(0,3);
insert into ac select lit.rowid,0 from lit;

--values (1,0), (2,0), (3,0);
insert into plus values (0);

select *, rowid from plus;
select *, rowid from ac;
-- This query is doing AC-matching (_ + ?x + ?y)
-- (?x + ?y) coule mean partition the AC set.
-- or (?x + ?y) could mean ony match sets of cardinality 2.
-- Depends if vars can bind to sets or
-- plus( { ?x , ?y }   ) vs  plus( { ?x , ?y, ... }) vs plus( ?x union ?y) 

select * from plus, ac as n1, ac as n2, lit as x1, lit as x2
 where n1.out_ = plus.ac and n2.out_ = plus.ac 
 and n1.rowid != n2.rowid -- multiset but don't match same term twice
 and n1.in_ = x1.rowid and n2.in_ = x2.rowid 
 and n1.in_ < n2.in_  -- break permutation symmetry
 ;
-- If I want to match (?x + ?y + ?z)... no this is impossible. Like what do you mean? Ok. Maybe in the plus case this is possible. Even a single term can be artbirarily in real valued plus.
-- Ok but AC is more dsicrete and combinatorial. There is the empty set. Maybe by vonvention you denote whether you want to allow vars to attach to the empty set.
-- I should always be allowed to bind y and z to null also.

--select * from ac 
-- groupby ac.j
```

### slog

```python
from lark import Lark, Transformer, v_args
grammar = '''
//prog : rule*
rule : head ":-" body  "."

body: body_fact ("," body_fact)*
head : NAME "{"  [ head_field ("," head_field)* ]  "}"
head_field : NAME ":" expr
body_fact :  
  | expr "=" expr -> eq
  | NAME "@" NAME -> from_

// op:
expr : NUMBER -> number
     | STRING -> string
     | NAME "." NAME -> field

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
'''

@v_args(inline=True)
class RuleTransformer(Transformer):
  froms = []
  wheres = []
  def field(self, row, field):
    return "{row}.{field}"
  def string(self,s):
    return '"' + s[1] + '"'
  def number(self,n):
    return n[1]
  def from_(self, table, row):
    self.froms.append(f"{table} AS {row}")
  def eq(self, lhs, rhs):
    wheres.append(f"{lhs} = {rhs}")
  def body(self,*args):
    wheres = " AND ".join(self.wheres)
    froms = ", ".join(self.froms)
    return f"FROM {froms} WHERE {wheres}"
  def head_field(self, key, val):
    return f"{val} AS {key}"
  def head(self,table, *fields):
    selects = ", ".join(fields)
    return f"INSERT INTO OR IGNORE {table} SELECT {selects}"
  def rule(self, head, body):
    self.froms = []
    self.wheres = []
    return  head + " " + body


parser = Lark(grammar, start="rule", parser="lalr", transformer=RuleTransformer())
print(parser.parse("path { x : e.x, y : p.y} :- edge @ e, path @ p, e.y = p.x"))
```

```python
from lark import Lark, Transformer, v_args
from dataclasses import dataclass
grammar = '''
//prog : rule*
rule : head ":-" body  "."

body: body_fact ("," body_fact)*
head : NAME "("  [ term ("," term)* ]  ")"
body_fact :  
  | term  "=" term -> eq
  | NAME "("  [ term ("," term)* ]  ")" -> rel

term : NUMBER -> number
     | STRING -> string
     | NAME -> var
     | NAME "("  [ term ("," term)* ]  ")" -> func

%import common.CNAME -> NAME
%import common.ESCAPED_STRING   -> STRING
%import common.NUMBER
%import common.WS
%ignore WS
'''

#parser = Lark(grammar, start="prog")
#print(parser.parse("foo(3,4).  edge(1,2). edge(\"a\"). path(x,z) :- edge(x,y), path(y,z).").pretty())

@dataclass(frozen=True, eq=True)
class Var():
  name:str

@v_args(inline=True)
class RuleTransformer(Transformer):
  env = {} # variable env 
  froms = [] 
  wheres = []
  counter = 0
  def fresh(self, n):
    self.counter += 1
    return f"{n}{self.counter}"
  def var(self,name):
    print(name)
    return Var(name)
  def string(self,s):
    return '"' + s[1] + '"'
  def number(self,n):
    return n[1]

  def rel(self,table,*args):
    self.func(table,*args)
  def eq(self, x, y):
    if isinstance(y, Var):
      y = self.env[y]
    if isinstance(x,Var):
        if x in self.env:
          self.wheres.append(f"{self.env[x]} = {y}")
        else:
          self.env[x] = y
    else:  
      self.wheres.append(f"{x} = {y}")
  def func(self, table, *args):
    row = self.fresh(table)
    self.froms.append(f"{table} AS {row}")
    for n, arg in enumerate(args):
      if isinstance(arg,Var):
        if arg in self.env:
          self.wheres.append(f"{self.env[arg]} = {row}.x{n}")
        else:
          self.env[arg] = f"{row}.x{n}"
      else:  
        self.wheres.append(f"{arg} = {row}.x{n}")
    return f"{row}.rowid"
  def body(self,*args):
    wheres = " AND ".join(self.wheres)
    froms = ", ".join(self.froms)
    return f"FROM {froms} WHERE {wheres}"
  def head(self,table, *args):
    # delay. Is this dumb? It's gnna bite me
    def res():
      print(self.env)
      selects = []
      for arg in args:
        if isinstance(arg,Var):
          selects.append(self.env[arg])
        else:
          selects.append(arg)
      selects = ", ".join(selects)
      return f"INSERT INTO OR IGNORE {table} SELECT {selects}"
    return res
  def rule(self, head, body):
    res = head() + " " + body
    self.env = {}
    self.froms = []
    self.wheres = []
    self.counter = 0
    return res


parser = Lark(grammar, start="rule", parser="lalr", transformer=RuleTransformer())
print(parser.parse("path(x,z) :- edge(x,y), path(y,z)."))
print(parser.parse("path(x,z) :- edge(x,\"y\"), path(y,z)."))
print(parser.parse("path(x,p(z)) :- add(mul(x,y), div(y,z)), y = x."))
```

Rename columns to x0-xn.
Multiheaded rules.
Accumulating semantics for multihead is kind of easy. Weird though.
purify the wheres
add root and union everywhere.
((d :- c)  /\ b) :- a
d :- a,b,c
b :- a

```sql
create table foo(rowid INTEGER PRIMARY KEY AUTOINCREMENT, a );
insert into foo (a) values (1), (2);
create table bar(rowid INTEGER PRIMARY KEY AUTOINCREMENT, a );
insert into bar (a) values (1), (2);

select * from foo;
select * from bar;
select * from sqlite_sequence;
```

Using `default` instead of rowid

```sql
create table foo(a,b,res default -1);
--describe foo;
insert into foo (a,b) values (1 ,2);
select * from foo;
```

```python

import sqlite3
counter = 0
def fresh():
  global counter
  counter += 1
  return counter
conn = sqlite3.connect(":memory:")
cur = conn.cursor()
conn.create_function("fresh", 0, fresh)
cur.execute("create table foo(a,b,c default (fresh()), unique (a,b))")
cur.execute("insert or ignore into foo (a,b) values (2,3), (3,4), (2,3), (4,5)")
cur.execute("select * from foo")
print(cur.fetchall())
# hmm. it calls fresh even on ignore. Don't like that
```

Too many fresh isn't persay a problem but it is kind of disappointing
I guess we could use a trigger after insert

```sql
create table foo(a,b,res default -1);
--describe foo;
create trigger after insert 
insert into foo (a,b) values (1 ,2);
select * from foo;
```

```
counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def var(x):
  def res(loc):
    return {x : loc}, [] , []
  return res


def foo(a):
  def res(loc):
    row = freshrow()
    (env, froms, wheres) = a(f"{row}.a")
    return (env,  [f"foo as {row}"] + froms, [f"{loc} = {row}.rowid"] + wheres)
  return res

def merge(env1,env2):
  if len(env1) > len(env2):
    env1, env2 = env2, env1
  wheres = [ f"{v} = {env2[k]}" for k,v in env1.items() if k in env2 ] # join
  return {**env1, **env2}, wheres

def func(table):
  def res(*args):
    def res1(loc):
      row = freshrow()
      if loc != None:
        wheres = [f"{loc} = {row}.rowid"]
      else:
        wheres = []
      froms = [f"{table} as {row}"]
      env = {}
      for n, arg in enumerate(args):
        e, f, w = arg(f"{row}.x{n}")
        wheres += w
        froms += f
        env, w2 =  merge(env,e)
        wheres += w2
      return env, froms, wheres
    return res1
  return res

plus = func("plus")
x = var("x")
print(plus(x,x)(None)) # This is ugly. I should also be returning the row.
```

Ugh, so I need to pass something down the tree so the vars can do something, or I can make retvals either var or not. I could make the env have concat merge semantics and collect up at the end. That's what I did in snakelog

a.1.1 = b.1.1, a.h =

plus @ a, a.x, a.x

Ok, so I need to build a datalog first. It sucks too much to

```
      #args1 = [arg(f"{row}.x{n}") for n, arg in enumerate(args)]
      #envs, froms, wheres = map(list, zip(*args1))
      #print(froms, wheres)
      #env1 = {}
      #wheres.append(f"{loc} = {row}.rowid")
      ##froms.append(f"{f} as {row}")
      #for env in envs:
      #  env1, w = merge(env, env1)
      #  wheres += w

counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def foo(a):
  def res():
    (rid, froms, wheres) = a()
    row = freshrow()
    return (f"{row}.rowid",  [f"foo as {row}"] + froms, [f"{rid} = {row}.a"]+ wheres)
  return res

def x():
  row = freshrow()
  return (row + ".rowid" ,[f"x AS {row}"], [])

def func(f):
  def res(*args):
    def res1():
      args = [arg() for arg in args]
      rids, froms, wheres = zip(*args)
      row = freshrow()
      (f"{row}.rowid",  [f"{f} as {row}"] + froms, [f"{rid} = {row}.arg{n}" for n,rid in enumerate(rids)] + wheres)
    return res1
  return res

print(foo(foo(x))())
```

Wait, would the join form be cleaner?
JOIN foo, a on a.rowid = foo.
Meh. Kind of.

# GJ scribbles

The incoming variables take signal values

```python

_edge = set()
def edge(x,y):
  if x != None:
    return { for (x1,y1) in _edge if x == x1 and  }



```

```ocaml
type req = Output | Ignore | Restrict of value

type = (value * () -> ) list

let edge = function
  | Output, Output


```

## Bottom Up

```ocaml


```

Value is [(a, env)]
Value is Tree -> eid
Rather than using named env, use positional env. Interesting.

Var is just

```python
_add = {}
class Var():
  name
def add(x,y):
  for (xv,yv),zv in _add:
    if isinstance(x,int) and x != xv:
      continue
    if isinstanc()
  if isinstance(x,Var):
    filter( ,_add)
maxeid = 0
def add(x,y):
  return { (x,y) : _add[(ex,ey)] for x,ex in x.items() for y,ey in y.items() if (ex,yx) in _add }

def var():
  return { eid : eid for eid in range(maxeid) }

```

```python

db = {}

class UF():
  pass
class Env():
  def union(self, b):


class DB():
  def __init__(self):
    self.db = {}
    self.uf = UF()
  def function(self,name, merge=None):
    self.db[name] = {}
    def res(*args):
      self.db[name]
  def var(self,name):
    return 



```

Normalized view

```sql
create view eadd select r1.y, r2.y, r3.y, from root as r1, root as r2, root as r3, add where r1.x = add.x, r2.x = add.y, r3.x = add.z

```

# Termination

This is Yihong's jam.

Two simple termination improvers:

- Do not allow make-set. Do not allow primitive functions? These can be written as rules with extra clauses in the body
- Yihong had some kind of depth tracking thing. track smallest term size in eclass. Refuse to build things that are too big. You run out of trees.

Stratification of types a la EPR. Why are functions to unit ok (datalog)? Bounded lattices.

# Rulesets

Not all rules are made a like

- Simp rules - (x + 0) = x. Not necessarily terminating even if they are in the term rewriting ocntext, which is distrubing.
- defintional rules. decreating abstraction, bit blasting.
- refold rules, decompilation. Increasing abstraction. Pattern finding.
- churn rules - like AC. Kind of not exploding, but not very goal directed.
- generative rules - building new objects for which there are often infinitely many

To what degree can these be automatically identified?

# Ideas

- IO functions. Communicate to port, pipe `(readline)` `(writeln)`. The _really_ crazy version would use eids as futures
- `eval` and Expr type.
- negation and unstable inequality
- primitive intervals
- multiprecision floats
- random number generator?
- Polynomials, semiring semantics? Quotient rings. polynomials as container.
- Talk to scryer
- subsumption
- python interop
- libloading
- a mode where no "new" thing are ever inserted. Similar to some kind of EPR condition? Stratified typing?

egraph decomp
rewrite imp

examples

- geom
- sharing logic min
- matrices
- category
- float
- first order interactive

asp - neighborhood
custom search for extreact (stochstic)
]

intgrals and sums. bound vars.
aegraph picat
egglog ocaml
theories? linear vectors

egraph isel

design a problem to thwart greedy

x = bar(x1, a)
y = biz(y1, a)
z = z1 + a

foo(x,y,z)

cost x y z : 10
cost x1 : 1
cost a : 10

x = x1(a)
y = y1(a)
z = z1(a)

extract foo(x,y,z)

Unison - hashes every construct to be globally accessible. For mutually recursive definitions, it tie breaks.

Egglog doesn't really allow recursive defintions (should it?)

```
(function zeros () List)
(union zeros (Cons 0 zeros))

(function zeros1 () List)
(union zeros1 (Cons 0 zeros1))

```

There is a loop here. `zeros1` is not dervied to be `zeros` because there is no isomorphism finder.
`zeros` is not really "defined" to be `cons 0 zeros`. It is "equal"

Backend issues
scan vs binary join vs gj
terms.
what about proofs via tracing
