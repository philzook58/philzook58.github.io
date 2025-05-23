---
title: Where are all the Rewrite Rules?
date: 2025-02-18
---

I think a thing that'd be nice is to have a databank of rewrite rules. Here's some of the ones I know about.

IF YOU HAVE ANY INTERESTING OR NOT SO INTERESTING RULES PLEASE DROP ME A LINE. You can email me at <philzuckerblog@gmail.com> or dm me on the various social medias.

I feel in particular I'm missing application oriented stuff. The easier thing to find is mathematical or theorem proving focussed in nature.

Maybe it'd be nice to collate these into a common format. Is this even possible really? As the XKCD goes:

![](https://imgs.xkcd.com/comics/standards.png)

Here is a vomit of what I could think of and remember today.

# Integer Properties

There are some common named properties of integers.

Actually very few of them are good as rewrite rules do to looping (associativity and commutativity). Hence you may want something like egraphs or ordered rewriting.

Fusing out constants in various ways or cancelling `n - n = 0` is a very common example of simplification rules.

```python
from kdrag.all import *

n, m, k = smt.Ints("n m k")
add_comm = kd.prove(smt.ForAll([n, m], n + m == m + n))
add_assoc = kd.prove(smt.ForAll([n, m, k], n + (m + k) == (n + m) + k))
add_zero = kd.prove(smt.ForAll([n], n + 0 == n))
add_inv = kd.prove(smt.ForAll([n], n + -n == 0))

add_monotone = kd.prove(kd.QForAll([n, m, k], n <= m, n + k <= m + k))

mul_comm = kd.prove(smt.ForAll([n, m], n * m == m * n))
mul_assoc = kd.prove(smt.ForAll([n, m, k], n * (m * k) == (n * m) * k))
mul_one = kd.prove(smt.ForAll([n], n * 1 == n))
mul_zero = kd.prove(smt.ForAll([n], n * 0 == 0))

mul_monotone = kd.prove(kd.QForAll([n, m, k], n <= m, k >= 0, n * k <= m * k))


le_refl = kd.prove(smt.ForAll([n], n <= n))
le_trans = kd.prove(kd.QForAll([n, m, k], n <= m, m <= k, n <= k))


lt_trans = kd.prove(kd.QForAll([n, m, k], n < m, m < k, n < k))
lt_total = kd.prove(kd.QForAll([n, m], smt.Or(n < m, n == m, m < n)))


distrib_left = kd.prove(smt.ForAll([n, m, k], n * (m + k) == n * m + n * k))
distrib_right = kd.prove(smt.ForAll([n, m, k], (m + k) * n == m * n + k * n))
```

<https://github.com/folivetti/srtree/blob/1c89c842cda13716214faf8dbf917c2f9fdbfe82/src/Algorithm/EqSat/Simplify.hs#L99>
Alcides Fonseca pointed out these rules in a haskell equality saturation fro symbolic regression library

# Differentiation

<https://www.philipzucker.com/z3_diff/>

There are different approaches to differentiation. Some make semantically very poor sense.

One way is to "yonedaify" and have X denote the identity function `fun x => x` and the functions `sin : (R -> R) -> (R -> R)` actually represent `sin : R -> R` precomposed with composition. Then the naive autodiff rules kind of work.

Another approach is to have "x" mean a real valued function on some unknown manifold `M`. `X : M -> R` . Then `d(X)` is actually a thing with smenatic meaning and you can track them around.
<https://github.com/nick8325/twee/blob/master/tests/deriv.p>

```python
from kdrag.all import *
import kdrag.theories.real as real

x,c = smt.Reals("x c")
f,g = smt.Consts("f g", real.RFun)
X = smt.Lambda([x], x)
deriv = real.deriv

rules = [
    deriv(X) == real.const(1),
    smt.ForAll([c], deriv(real.const(c)) == real.const(0)),
    smt.ForAll([f, g], deriv(f + g) == deriv(f) + deriv(g)),
    smt.ForAll([f, g], deriv(f * g) == deriv(f) * g + f * deriv(g)),
]

```

```python
M = smt.DeclareSort("M")
V = smt.DeclareSort("V") # tangent space
d = smt.Function("d", M >> real.R,  smt.ArraySort(M, V, real.R))
# I don't really have this hammered out.
```

# Sets

<https://en.wikipedia.org/wiki/Algebra_of_sets>
<https://en.wikipedia.org/wiki/List_of_set_identities_and_relations>

Kuratowksi closure axioms for topology <https://en.wikipedia.org/wiki/Kuratowski_closure_axioms>

```python
from kdrag.all import *
import kdrag.theories.set as set_

T = smt.DeclareTypeVar("T")
S = set_.Set(T)
A,B,C = smt.Consts("A B C", S)

union_comm = kd.prove(smt.ForAll([A, B], A | B == B | A))
union_assoc = kd.prove(smt.ForAll([A, B, C], (A | B) | C == A | (B | C)))
union_empty = kd.prove(smt.ForAll([A], A | S.empty == A))
union_full = kd.prove(smt.ForAll([A], A | S.full == S.full))
union_self = kd.prove(smt.ForAll([A], A | A == A))

inter_comm = kd.prove(smt.ForAll([A, B], A & B == B & A))
inter_assoc = kd.prove(smt.ForAll([A, B, C], (A & B) & C == A & (B & C)))
inter_empty = kd.prove(smt.ForAll([A], A & S.empty == S.empty))
inter_full = kd.prove(smt.ForAll([A], A & S.full == A))
inter_self = kd.prove(smt.ForAll([A], A & A == A))

diff_empty = kd.prove(smt.ForAll([A], A - S.empty == A))
diff_full = kd.prove(smt.ForAll([A], A - S.full == S.empty))
diff_self = kd.prove(smt.ForAll([A], A - A == S.empty))
```

# BitVectors

Booleans and bitvectors must have a pile of good rewrite rules. I think many of these may be useful in hardware compilers.

Surely the preprocessors of Boolector or Bitwuzla have some? <https://github.com/Boolector/boolector/blob/master/src/btorrewrite.c> <https://github.com/bitwuzla/bitwuzla/tree/main/src/rewrite> Very programmatic.

Rewriting rules for and inverter graphs (AIG)?

LLVM and ilk must have a bunch but where?

Bit twiddling hacks is a source of some fun ones <https://graphics.stanford.edu/~seander/bithacks.html>

Harald Aptroot pointed out some interesting rules he has <https://gitlab.com/haroldaptroot/haroldbot/-/blob/main/prooffinder.js?ref_type=heads>

```python
class BVTheory:
    def __init__(self, N):
        self.N = N
        x, y, z = smt.BitVecs("x y z", N)
        zero = smt.BitVecVal(0, N)
        self.zero = zero
        one = smt.BitVecVal(1, N)
        self.one = one

        self.bvadd_comm = kd.prove(smt.ForAll([x, y], x + y == y + x))
        self.bvadd_assoc = kd.prove(smt.ForAll([x, y, z], (x + y) + z == x + (y + z)))
        self.bvadd_id = kd.prove(smt.ForAll([x], x + zero == x))
        self.bvadd_neg = kd.prove(smt.ForAll([x], x + (-x) == zero))

        self.bvsub_self = kd.prove(smt.ForAll([x], x - x == zero))
        self.bvsub_def = kd.prove(smt.ForAll([x, y], x - y == x + (-y)))

        self.bvmul_comm = kd.prove(smt.ForAll([x, y], x * y == y * x))
        self.bvmul_assoc = kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
        self.bvmul_id = kd.prove(smt.ForAll([x], x * smt.BitVecVal(1, N) == x))
        self.bvmul_zero = kd.prove(smt.ForAll([x], x * zero == zero))

        self.bvand_comm = kd.prove(smt.ForAll([x, y], x & y == y & x))
        self.bvand_assoc = kd.prove(smt.ForAll([x, y, z], (x & y) & z == x & (y & z)))
        self.bvand_id = kd.prove(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
        self.bvand_zero = kd.prove(smt.ForAll([x], x & zero == zero))

        self.bvor_comm = kd.prove(smt.ForAll([x, y], x | y == y | x))
        self.bvor_assoc = kd.prove(smt.ForAll([x, y, z], (x | y) | z == x | (y | z)))
        self.bvor_id = kd.prove(smt.ForAll([x], x | zero == x))
        self.bvor_neg = kd.prove(smt.ForAll([x], x | ~x == smt.BitVecVal(-1, N)))

        self.bvxor_comm = kd.prove(smt.ForAll([x, y], x ^ y == y ^ x))
        self.bvxor_assoc = kd.prove(smt.ForAll([x, y, z], (x ^ y) ^ z == x ^ (y ^ z)))
        self.bvxor_id = kd.prove(smt.ForAll([x], x ^ zero == x))
        self.bvxor_self = kd.prove(smt.ForAll([x], x ^ x == zero))

        self.bvshl_zero = kd.prove(smt.ForAll([x], x << zero == x))
        self.bvshr_zero = kd.prove(smt.ForAll([x], smt.LShR(x, zero) == x))

        # Bitwise simplification rules
        self.bvand_self = kd.prove(smt.ForAll([x], x & x == x))
        self.bvor_self = kd.prove(smt.ForAll([x], x | x == x))
        self.bvxor_zero = kd.prove(smt.ForAll([x], x ^ zero == x))
        self.bvnot_self = kd.prove(smt.ForAll([x], ~x == -x - 1))

        # Rules for shifting and rotating
        self.bvshl_self = kd.prove(
            smt.ForAll([x, y], x << y == x * (one << y))
        )  # Left shift as multiplication
        # bvshr_self = kd.prove(smt.ForAll([x, y], smt.LShR(x, y) == x / (one << y)))  # Logical right shift as division
        # bvashr_self = kd.prove(smt.ForAll([x, y], smt.AShr(x, y) == smt.If(x >> 31 == 0, smt.LShR(x, y), ~smt.LShR(~x, y))))  # Arithmetic right shift rule

        # Simplification with negation and subtraction
        self.bvsub_zero = kd.prove(smt.ForAll([x], x - zero == x))
        self.bvsub_id = kd.prove(smt.ForAll([x], zero - x == -x))
        self.bvadd_sub = kd.prove(smt.ForAll([x, y], x + (-y) == x - y))
        self.bvsub_add = kd.prove(smt.ForAll([x, y], x - (-y) == x + y))

        # Bitwise AND, OR, and XOR with constants
        self.bvand_allones = kd.prove(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
        self.bvor_allzeros = kd.prove(smt.ForAll([x], x | zero == x))
        self.bvxor_allzeros = kd.prove(smt.ForAll([x], x ^ zero == x))

        # Distribution and absorption laws
        self.bvand_or = kd.prove(
            smt.ForAll([x, y, z], x & (y | z) == (x & y) | (x & z))
        )
        self.bvor_and = kd.prove(
            smt.ForAll([x, y, z], x | (y & z) == (x | y) & (x | z))
        )
        self.bvand_absorb = kd.prove(smt.ForAll([x, y], x & (x | y) == x))
        self.bvor_absorb = kd.prove(smt.ForAll([x, y], x | (x & y) == x))

        # Shifting rules with zero and identity
        self.bvshl_zero_shift = kd.prove(smt.ForAll([x], x << zero == x))
        self.bvshr_zero_shift = kd.prove(smt.ForAll([x], smt.LShR(x, zero) == x))
        # bvashr_zero_shift = kd.prove(smt.ForAll([x], smt.AShr(x, zero) == x))  # Arithmetic right shift by zero is identity
        self.bvshl_allzeros = kd.prove(smt.ForAll([y], zero << y == zero))
        self.bvshr_allzeros = kd.prove(smt.ForAll([y], smt.LShR(zero, y) == zero))
        # bvashr_allzeros = kd.prove(smt.ForAll([y], smt.AShr(zero, y) == zero))  # Arithmetic right shift of zero is zero

        # Additional rules for combining operations
        # bvadd_and = kd.prove(smt.ForAll([x, y, z], (x & y) + (x & z) == x & (y + z)))  # AND distribution over addition
        self.bvor_and_not = kd.prove(smt.ForAll([x, y], (x & y) | (x & ~y) == x))
        # bvxor_and_not = kd.prove(smt.ForAll([x, y], (x & y) ^ (x & ~y) == y))  # Distribution of XOR and AND with negation

        # Properties involving shifts and bit manipulations
        self.bvshl_and = kd.prove(
            smt.ForAll([x, y, z], (x & y) << z == (x << z) & (y << z))
        )
        self.bvshr_and = kd.prove(
            smt.ForAll([x, y, z], smt.LShR(x & y, z) == smt.LShR(x, z) & smt.LShR(y, z))
        )
```

# Functional Programs

There are many interesting functional programs. Pure functional programs are a subset of term rerwiting systems. Functional programs are pretty natural feeling to me. Using general term rewriting systems to run functional programs is overkill and also inefficient. In any case, all pure functional programs can be seen as instances of term rewriting systems and used to asses some kind of performance.

- Evaluators
- peano arithmetic
- binary arithmetic
- list programs
- red black trees
- fibonacci, factorial, gcd, ackermann

Functional programs can be in the form of if-then-else chains, but they can also be specified as equations on the constructors. The second form is familiar from haskell.

# Lists

List functions
<https://ocaml.org/manual/5.3/api/List.html>

- `length`
- `rev`
- `append`
- `hd`
- `tl`
- `concat`
- `map`
- `fold`
- `mem`
- `forall`
- `exists`

## SKI Combinators

<https://en.wikipedia.org/wiki/SKI_combinator_calculus>

```python
TERM = smt.DeclareSort("TERM")
"""
Doesn't work without more tricks.
I = smt.Const("I", TERM >> TERM)
S = smt.Const("S", TERM >> (TERM >> (TERM >> TERM)))
K = smt.Const("K", TERM >> (TERM >> TERM))
"""

x,y,z = smt.Consts("x y z", TERM)
app = smt.Function("app", TERM, TERM, TERM)
I,S,K = smt.Consts("I S K", TERM)

kd.notation.getitem.register(TERM, app)

rules = [
    smt.ForAll([x], I[x] == x),
    smt.ForAll([x, y, z], S[x][y][z] == x[z][y[z]]),
    smt.ForAll([x, y], K[x][y] == x),
]
rules
```

    [ForAll(x, app(I, x) == x),
     ForAll([x, y, z],
            app(app(app(S, x), y), z) ==
            app(app(x, z), app(y, z))),
     ForAll([x, y], app(app(K, x), y) == x)]

# FOILing

Expanding out a polynomial by distributing. You may also want to sort all the terms.

## DNF

DNF is putting a boolean expression into a giant sum  of conjuctions, kind of the booolean analog of expanding out a polynomial

```python
from kdrag.all import *

p,q,r = smt.Bools("p q r")

# DNF
dnf = [
smt.ForAll([p], ~~(p) == p),
smt.ForAll([p,q], ~(p | q) == ~p & ~q),
smt.ForAll([p,q], ~(p & q) == ~p | ~q),
smt.ForAll([p,q,r], p & (q | r) == (p & q) | (p & r)),
smt.ForAll([p,q,r], (p | q) & r == (p & r) | (q & r)),
]

dnf = [kd.prove(f) for f in dnf]
dnf
```

    [|- ForAll(p, Not(Not(p)) == p),
     |- ForAll([p, q], Not(Or(p, q)) == And(Not(p), Not(q))),
     |- ForAll([p, q], Not(And(p, q)) == Or(Not(p), Not(q))),
     |- ForAll([p, q, r],
            And(p, Or(q, r)) == Or(And(p, q), And(p, r))),
     |- ForAll([p, q, r],
            And(Or(p, q), r) == Or(And(p, r), And(q, r)))]

# Eggiverse

There are a variety of projects in an around Egg and UW that have collections of rules.

- <https://github.com/egraphs-good/egg/tree/main/tests> people tend to take a look at eggs test examples, although I don't think they were meant to be the point
- <https://github.com/egraphs-good/egglog/tree/main/tests> egglog has a number of example files
- <https://github.com/egraphs-good/egglog-python/tree/main/python/egglog/examples>
- <https://github.com/herbie-fp/herbie/blob/main/src/core/rules.rkt> Herbie rules. Herbie is an optimizer for floating point calculations.
- <https://github.com/uwplse/ruler/tree/main/tests> Ruler rules. Ruler is a rule synthesis framework

- <https://github.com/egraphs-good/egglog/blob/main/tests/eqsolve.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/bdd.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/fibonacci.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/list.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/array.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/integer_math.egg>
- <https://github.com/egraphs-good/egglog/blob/main/tests/herbie.egg>

```python
%%file 
(
    datatype Math
  (Num i64)
  (Var String)
)


(datatype Array
  (Const i64)
  (AVar String)
)

(constructor add (Math Math) Math)
(constructor select (Array Math) Math)
(constructor store (Array Math Math) Array)

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
      ((union (select mem i2) e1)))
; aliasing writes destroy old value
(rewrite (store (store mem i e1) i e2) (store mem i e2))
; non-aliasing writes commutes
(rule ((= (store (store mem i2 e2) i1 e1) mem1) (neq i1 i2))
      ((union (store (store mem i1 e1) i2 e2) mem1)))

```

# Rubi Integration Rules

There is a set of integration rules that supposedly work really well. THey arte overfit to mathematica unforutnately and that makes them hard to port

<https://rulebasedintegration.org/>

<https://github.com/sympy/sympy/blob/master/sympy/integrals/manualintegrate.py>

Fourier transform rules? Laplace? `F[af + bg] = aF[f] + bF[g]`, `F[f ** g] = F[f] * F[g]`,  etc.? <https://en.wikipedia.org/wiki/Fourier_transform#Tables_of_important_Fourier_transforms>

# Vectors

- <https://en.wikipedia.org/wiki/Vector_algebra_relations>
- <https://en.wikipedia.org/wiki/Vector_calculus_identities>
- <https://en.wikipedia.org/wiki/Exterior_calculus_identities#Properties>
- geometric algerba

# "Math"

- <https://fungrim.org/>
- <https://dlmf.nist.gov/> NIST Digital Library of Mathematical Functions
- <https://personal.math.ubc.ca/~cbm/aands/>  Abramowitz and Stegun: Handbook of Mathematical Functions
- Concrete Mathematics book by Knuth et al
- Combinatorics?

# Hongguang Fu Trig

There is a paper and discussion in sympy about rules used for trig simplication

<https://docs.sympy.org/latest/modules/simplify/fu.html>
<https://github.com/sympy/sympy/blob/master/sympy/simplify/fu.py>

<https://github.com/sympy/sympy/blob/2ce85934406c08d16d98c68e50c6fad4fcabbde7/sympy/simplify/trigsimp.py#L812>

<https://en.wikipedia.org/wiki/List_of_trigonometric_identities>

# Summation

Moving summation symbols around.

- <https://en.wikipedia.org/wiki/Summation#Identities>
- <https://courses.cs.washington.edu/courses/cse373/19sp/resources/math/summation/>

```python
from kdrag.all import *
import kdrag.theories.real as real

Sum = smt.Function("Sum", real.RSeq, smt.IntSort(), smt.IntSort(), smt.IntSort())
f,g = smt.Consts("f g", real.RSeq)
c = smt.Real("c")
a,b = smt.Ints("a b")
rules = [
    smt.ForAll([f,a], Sum(f, a, a) == f[a]),
    smt.ForAll([f, g, a, b], Sum(f + g, a, b) == Sum(f, a, b) + Sum(g, a, b)),
    smt.ForAll([f, g, a, b], Sum(f - g, a, b) == Sum(f, a, b) - Sum(g, a, b)),
    smt.ForAll([f, g, a, b], Sum(f, a, b) == Sum(f, 0, b) - Sum(g, 0, a-1)),
    smt.ForAll([f, g, c, a, b], Sum(smt.K(smt.IntSort(), c) * f, a, b) == c * Sum(f, a, b)),
    smt.ForAll([c], Sum(smt.K(smt.IntSort(), c), a, b) == c * (b - a + 1)),
]



```

# Algebra

Universal algerba can be a source of equations.
<https://en.wikipedia.org/wiki/Algebraic_structure>

- Group, Ring, Monoid, Lattice.

# Kleene Algebra

<https://en.wikipedia.org/wiki/Kleene_algebra>
Kleene algebra is nearly an algebraic theory of pure equations (a couple are conditional equations). And yet it describes processes and regular expressions. Pretty cool!

- <https://www.philipzucker.com/bryzzowski_kat/>
- <https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/kleene.egg>
- <https://github.com/mgree/katbury>

# Category Theory

You can make a nearly equational theory for basic category by judicious placement of `cod` and `dom` to make sure the equations are unconditionally well sorted.

- <https://www.philipzucker.com/rust-category/>
- <https://github.com/philzook58/Catlab.jl/blob/master/src/theories/Monoidal.jl>
- <https://github.com/philzook58/egg-smol/tree/scratchpad2/tests/catlab>

# Associating

Left and right associating are useful operations. It's nearly trivial. But still a good example.

```python
T = smt.DeclareSort("T")
binop = smt.Function("binop", T, T, T)
kd.notation.mul.register(T, binop)
x,y,z = smt.Consts("x y z", T)

assoc_right = smt.ForAll([x,y,z], x * (y * z) == (x * y) * z)

assoc_left = smt.ForAll([x,y,z], (x * y) * z == x * (y * z))

```

# Rewrite Engine Competition

- <https://sourcesup.renater.fr/scm/viewvc.php/rec/2019-CONVECS/>
- <https://github.com/philzook58/egglog-rec>

# Termination Competition

The termination competition has a couple formats for string and term rewriting systems.

- <https://github.com/TermCOMP/TPDB> Termination competition database
- <https://github.com/philzook58/TPDB> exported into the more trs readable format
- <https://termination-portal.org/wiki/Termination_Competition>
- <https://www.cs.tau.ac.il/~nachum/papers/printemp-print.pdf> 33 examples of Termination by Dershowitz has some examples

There is also a confluence competition.

# TPTP UEQ

There is a category of the TPTP theorem proving compeition for Unit Equality Proofs.

- <https://www.tptp.org/>
- <https://www.philipzucker.com/notes/Logic/tptp/>
- <https://github.com/bytekid/mkbtt/tree/master/input>

There may be something similar in SMTLIB-Comp?

# Twee

Twee is an equational theorem prover based around knuth bendix completion.

It has some interesting stuff in its test directory

<https://github.com/nick8325/twee/tree/master/tests>

# GHC

The haskell compiler has a rules directive. Pretty cool.

<https://github.com/search?q=repo%3Aghc%2Fghc+%7B-%23+RULES&type=code>

These are interesting but not exactly concrete rule sets:

<https://downloads.haskell.org/~ghc/7.0.1/docs/html/users_guide/rewrite-rules.html>
<https://wiki.haskell.org/GHC/Using_rules>

Stream fusion rules. <https://www.cs.tufts.edu/~nr/cs257/archive/duncan-coutts/stream-fusion.pdf>
<https://www.isa-afp.org/browser_info/current/AFP/Stream-Fusion/document.pdf>

<https://dl.acm.org/doi/10.1145/3677999.3678275> Higher Order Patterns for Rewrite Rules. GHC

## Hlint

<https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml>

```yaml
    - warn: {lhs: compare x y == LT, rhs: x < y}
    - warn: {lhs: compare x y /= LT, rhs: x >= y}
    - warn: {lhs: compare x y == GT, rhs: x > y}
    - warn: {lhs: compare x y == EQ, rhs: x == y}
    - warn: {lhs: compare x y /= EQ, rhs: x /= y}
    - warn: {lhs: head (sort x), rhs: minimum x}
    - warn: {lhs: last (sort x), rhs: maximum x}
    - warn: {lhs: head (sortBy f x), rhs: minimumBy f x, side: isCompare f}
    - warn: {lhs: last (sortBy f x), rhs: maximumBy f x, side: isCompare f}
    - warn: {lhs: reverse (sortBy f x), rhs: sortBy (flip f) x, name: Avoid reverse, side: isCompare f, note: Stabilizes sort order}
    - warn: {lhs: sortBy (flip (comparing f)), rhs: sortBy (comparing (Data.Ord.Down . f))}
    - warn: {lhs: reverse (sortOn f x), rhs: sortOn (Data.Ord.Down . f) x, name: Avoid reverse, note: Stabilizes sort order}
    - warn: {lhs: reverse (sort x), rhs: sortBy (comparing Data.Ord.Down) x, name: Avoid reverse, note: Stabilizes sort order}
    - hint: {lhs: flip (g `on` h), rhs: flip g `on` h, name: Move flip}
    - hint: {lhs: (f `on` g) `on` h, rhs: f `on` (g . h), name: Use on once}
    - warn: {lhs: if a >= b then a else b, rhs: max a b}

    - warn: {lhs: findIndices (a ==), rhs: elemIndices a}
    - warn: {lhs: findIndices (== a), rhs: elemIndices a}
    - warn: {lhs: "lookup b (zip l [0..])", rhs: elemIndex b l}
    - hint: {lhs: "elem x [y]", rhs: x == y, note: ValidInstance Eq a}
    - hint: {lhs: "notElem x [y]", rhs: x /= y, note: ValidInstance Eq a}
    - hint: {lhs: "length [1..n]", rhs: max 0 n}
    - hint: {lhs: length x >= 0, rhs: "True", name: Length always non-negative}
    - hint: {lhs: 0 <= length x, rhs: "True", name: Length always non-negative}

    - hint: {lhs: pure x <* y, rhs: x Data.Functor.<$ y}
    - hint: {lhs: return x <* y, rhs: x Data.Functor.<$ y}
    - hint: {lhs: const x <$> y, rhs: x <$ y}
    - hint: {lhs: pure x <$> y, rhs: x <$ y}
    - hint: {lhs: return x <$> y, rhs: x <$ y}
    - hint: {lhs: x <&> const y, rhs: x Data.Functor.$> y}
    - hint: {lhs: x <&> pure y, rhs: x Data.Functor.$> y}
```

# Go Compiler Rules

The Go compiler has some declarative lowering rules.

<https://github.com/golang/go/tree/master/src/cmd/compile/internal/ssa/_gen>

```python
%%file 
// Shifts

// SLL only considers the bottom 6 bits of y. If y > 64, the result should
// always be 0.
//
// Breaking down the operation:
//
// (SLL x y) generates x << (y & 63).
//
// If y < 64, this is the value we want. Otherwise, we want zero.
//
// So, we AND with -1 * uint64(y < 64), which is 0xfffff... if y < 64 and 0 otherwise.
(Lsh8x8   <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg8  <t> (SLTIU <t> [64] (ZeroExt8to64  y))))
(Lsh8x16  <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg8  <t> (SLTIU <t> [64] (ZeroExt16to64 y))))
(Lsh8x32  <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg8  <t> (SLTIU <t> [64] (ZeroExt32to64 y))))
(Lsh8x64  <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg8  <t> (SLTIU <t> [64] y)))
(Lsh16x8  <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg16 <t> (SLTIU <t> [64] (ZeroExt8to64  y))))
(Lsh16x16 <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg16 <t> (SLTIU <t> [64] (ZeroExt16to64 y))))
(Lsh16x32 <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg16 <t> (SLTIU <t> [64] (ZeroExt32to64 y))))
(Lsh16x64 <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg16 <t> (SLTIU <t> [64] y)))
(Lsh32x8  <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg32 <t> (SLTIU <t> [64] (ZeroExt8to64  y))))
(Lsh32x16 <t> x y) && !shiftIsBounded(v) => (AND (SLL <t> x y) (Neg32 <t> (SLTIU <t> [64] (ZeroExt16to64 y))))
```

# Cranelift

Cranelift is a compiler backend written in rust. It's main purpose is to compile wasm, but I think that scope may be growing with time.
Cranelift has a rewrite rule language called isle that is uses to describe optimizations and lowerings

- <https://github.com/bytecodealliance/wasmtime/tree/main/cranelift/codegen/src/opts>
- <https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/codegen/src/isa/riscv64/inst.isle>
- <https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf>
- <https://cfallin.org/blog/2023/01/20/cranelift-isle/>

# SMT

CVC5 has a new rewrite rule engine RARE. There are theory specific files like <https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites> for bitvectors or <https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites> for arith. There is plenty that is programmatically rewritten too though. <https://github.com/cvc5/cvc5/blob/main/src/theory/arith/arith_rewriter.cpp>

```python
%%file
(define-cond-rule arith-div-total-real ((t ?) (s Real)) (not (= s 0/1)) (/ t s) (/_total t s))
(define-cond-rule arith-div-total-int ((t ?) (s Int)) (not (= s 0)) (/ t s) (/_total t s))
(define-rule arith-div-total-zero-real ((t ?)) (/_total t 0/1) 0/1)
(define-rule arith-div-total-zero-int ((t ?)) (/_total t 0) 0/1)

(define-cond-rule arith-int-div-total ((t Int) (s Int)) (not (= s 0)) (div t s) (div_total t s))
(define-rule arith-int-div-total-one ((t Int)) (div_total t 1) t)
(define-rule arith-int-div-total-zero ((t Int)) (div_total t 0) 0)

(define-cond-rule arith-int-div-total-neg ((t Int) (s Int)) (< s 0) (div_total t s) (- (div_total t (- s))))

(define-cond-rule arith-int-mod-total ((t Int) (s Int)) (not (= s 0)) (mod t s) (mod_total t s))
(define-rule arith-int-mod-total-one ((t Int)) (mod_total t 1) 0)
(define-rule arith-int-mod-total-zero ((t Int)) (mod_total t 0) t)

(define-cond-rule arith-int-mod-total-neg ((t Int) (s Int)) (< s 0) (mod_total t s) (mod_total t (- s)))

; Eliminations
(define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (<= t s)))
(define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))
(define-rule arith-elim-int-gt ((t Int) (s Int)) (> t s) (>= t (+ s 1)))
(define-rule arith-elim-int-lt ((t Int) (s Int)) (< t s) (>= s (+ t 1)))
(define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))
```

I think Z3's rules are mostly programmatic in theory files <https://github.com/Z3Prover/z3/tree/master/src/ast/rewriter>  

Other SMT solvers also have rewrite rules?

# Lean

You can search for the simp attribute on github. Is there a way to dump all the good simp rules? Will the typeclass abstractions get in the wya of this making any sense outside of lean?
<https://github.com/search?q=repo%3Aleanprover%2Flean4%20%22%5Bsimp%5D%22&type=code>

# ACL2

Good bitvector rules?

ACL2 is highly equational in many ways. Which files though

# Maude

Maude is a term rewriting engine and logic. <https://cseweb.ucsd.edu/~goguen/sys/obj.html> I haven't found many good files though?

K is a related system

- <https://github.com/kframework/c-semantics/blob/master/semantics/c/language/execution/stmt/block.k> C semantics
- x86 <https://github.com/kframework/X86-64-semantics/blob/master/semantics/registerInstructions/addq_r64_r64.k>
- <https://github.com/kframework/llvm-semantics/blob/master/semantics/llvm-branching.k> llvm
-

# Inductive theorem provers

<https://github.com/cole-k/cc-lemma/blob/icfp-24/examples/clam.ceg>

hipspec <https://github.com/danr/hipspec/tree/master/examples>

thesy

# Metatheory

- <https://github.com/JuliaSymbolics/Metatheory.jl/tree/master/test/tutorials>

```python
function ⋅ end
miu = @theory x y z begin
  x ⋅ (y ⋅ z) --> (x ⋅ y) ⋅ z
  x ⋅ :I ⋅ :END --> x ⋅ :I ⋅ :U ⋅ :END
  :M ⋅ x ⋅ :END --> :M ⋅ x ⋅ x ⋅ :END
  :I ⋅ :I ⋅ :I --> :U
  x ⋅ :U ⋅ :U ⋅ y --> x ⋅ y
end
```

# GCC

CF pointed out <https://github.com/gcc-mirror/gcc/blob/master/gcc/match.pd>

"The other rewrite rules for GCC are located in fold-const.cc, simplify-rtx.cc and combine.cc (the latter 2 are the RTL ones and the combine ones are only used in the combine pass and it does some complex stuff like rewriting into and out of bit extraction format). Match and fold-const.cc are the generic (and gimple) tree level ones."  <https://hachyderm.io/@pinskia/114038839027304872>

# LLVM

- Instcombine <https://github.com/llvm/llvm-project/tree/main/llvm/lib/Transforms/InstCombine>
- <https://mlir.llvm.org/docs/PDLL/> But where are they?
- <https://github.com/llvm/llvm-project/blob/main/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td> Canonicalizer files. Thanks Regehr for pointers!
- <https://github.com/EnzymeAD/Enzyme-JAX/blob/main/src/enzyme_ad/jax/Passes/EnzymeHLOOpt.cpp>
- xdsl ? The rules are scattered around? <https://github.com/xdslproject/xdsl/blob/main/xdsl/transforms/canonicalization_patterns/arith.py>  `RewritePattern` class

# rpython

- <https://github.com/pypy/pypy/blob/main/rpython/jit/metainterp/ruleopt/real.rules>
- <https://github.com/pydrofoil/pydrofoil/blob/3df78c7c9cdf1f3a732477dec0325a8b506c9fff/pydrofoil/ir.py#L2704> optimize_* functions

# Vectorizations Rules

Diospyros? <https://github.com/cucapra/diospyros/blob/master/src/dios-egraphs/src/rules.rs> I don't really understand how these are doing the vecotorization? Seem like basic arithmetic rules.

# Scheduling

Scheduling is the mushing around of loops.

- <https://github.com/halide/Halide/blob/2e36da4d7631464272640a2126854748da299d54/src/Simplify_Sub.cpp#L25> Halide has a number of src/Simplify_*.cpp files. I don't know if any of these do simplifcation of the schedules

```
             rewrite(x - x, 0) || // We want to remutate this just to get better bounds
             rewrite(ramp(x, y, c0) - ramp(z, w, c0), ramp(x - z, y - w, c0)) ||
             rewrite(ramp(x, y, c0) - broadcast(z, c0), ramp(x - z, y, c0)) ||
             rewrite(broadcast(x, c0) - ramp(z, w, c0), ramp(x - z, -w, c0)) ||
             rewrite(broadcast(x, c0) - broadcast(y, c0), broadcast(x - y, c0)) ||
             rewrite(broadcast(x, c0) - broadcast(y, c1), broadcast(x - broadcast(y, fold(c1/c0)), c0), c1 % c0 == 0) ||
             rewrite(broadcast(y, c1) - broadcast(x, c0), broadcast(broadcast(y, fold(c1/c0)) - x, c0), c1 % c0 == 0) ||
             rewrite((x - broadcast(y, c0)) - broadcast(z, c0), x - broadcast(y + z, c0)) ||
             rewrite((x + broadcast(y, c0)) - broadcast(z, c0), x + broadcast(y - z, c0)) ||
```

- <https://github.com/Bastacyclop/egg-sketches/blob/main/examples/bench_tiling.rs>
- <https://github.com/rise-lang/shine/blob/main/src/main/scala/rise/eqsat/rules.scala>
- <https://github.com/exo-lang/exo/blob/main/src/exo/rewrite/LoopIR_scheduling.py>

# Linear / Tensor / Matrix Algebra

- Tensat <https://github.com/uwplse/tensat/blob/master/src/rewrites.rs> Some of this is more programmatic than one might hope
- <https://github.com/gussmith23/glenside/blob/main/src/language/rewrites.rs> glenside. Extremely programmatic. Basically all custom appliers?
- <https://github.com/ADAPT-uiuc/TensorRight/tree/master/rules>  TensorRight: Automated Verification of Tensor Graph Rewrites
- <https://mathweb.ucsd.edu/~jwavrik/web00/Moldova.pdf> Rewrite Rules and Simplification of Matrix Expressions
- <https://math.mit.edu/~dyatlov/54summer10/matalg.pdf> Matrix identities
- <https://www.math.uwaterloo.ca/~hwolkowi/matrixcookbook.pdf> Matrix cookbook  <https://dustinstansbury.github.io/theclevermachine/linear-algebra-identities>
- Do APL like languages have rewrite rules?
- <https://github.com/mrocklin/matrix-algebra> matrix algerba in maude Rocklin <https://newtraell.cs.uchicago.edu/files/tr_authentic/TR-2013-07.pdf>
- <https://github.com/sympy/sympy/blob/930b991f260ddb50c66d8094a091750d742bbecc/sympy/matrices/expressions/matmul.py#L443>
- <https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/matrix.egg> <https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/matexpr.egg>

# Relation Algebra

# Relational Algebra

<https://github.com/risinglightdb/risinglight/blob/main/src/planner/rules/plan.rs> <https://github.com/risinglightdb/risinglight/blob/main/src/planner/rules/expr.rs>

```rust
    rw!("pushdown-filter-hashagg";
        "(filter ?cond (hashagg ?keys ?aggs ?child))" =>
        "(hashagg ?keys ?aggs (filter ?cond ?child))"
        if not_depend_on("?cond", "?aggs")
    ),
    rw!("pushdown-filter-inner-join";
        "(filter ?cond (join inner ?on ?left ?right))" =>
        "(join inner (and ?on ?cond) ?left ?right)"
    ),
    rw!("pushdown-filter-semi-join";
        "(filter ?cond (join semi ?on ?left ?right))" =>
        "(join semi (and ?on ?cond) ?left ?right)"
    ),
```

Where is SPORES?

# Hardware Compiler Rewrite Rules

Some overlap with bitvector rewrite rules

In Yosys? <https://yosyshq.readthedocs.io/projects/yosys/en/0.40/using_yosys/synthesis/opt.html> <https://github.com/YosysHQ/yosys/tree/main/passes/opt>  <https://github.com/YosysHQ/yosys/blob/main/passes/opt/opt_expr.cc>
<https://github.com/YosysHQ/yosys/tree/main/passes/pmgen> pattern match gen  <https://github.com/YosysHQ/yosys/blob/main/passes/pmgen/peepopt_muldiv.pmg>
<https://github.com/YosysHQ/yosys/tree/main/techlibs/ice40/tests> techlibs

ABC?
Bluespec <https://github.com/B-Lang-org/bsc>?

Gus Smith's stuff? Sam Cowards?

<https://github.com/XhenryZhang/loop_rerolling_egg/blob/master/src/main.rs>

<https://egraphs.zulipchat.com/#narrow/channel/328978-topic.2Fapplications/topic/Where.20are.20the.20rewrite.20rules.3F/near/504935962> a list of some hardware rule egraph papers

<https://github.com/Gy-Hu/E-Syn/blob/692c43a5491a72143d1d30ed320e9fcc1bfd01eb/e-rewriter/src/main.rs#L85>

<https://arxiv.org/pdf/2406.12421> ROVER table 2

<http://www-cad.eecs.berkeley.edu/~alanmi/publications/2006/dac06_rwr.pdf> AIG rewrite rules. You can brute enumerate also.

# Synthesis

You don't need a dataset persay of rules if you can synthesize them. But also some of these projects have stored their rule sets

- <https://users.cs.utah.edu/~regehr/generalization-oopsla24.pdf#subsection.8.7> Hydra: Generalizing Peephole Optimizations with Program Synthesis. A collection of output from hydra <https://gist.github.com/manasij7479/2ad0f7f058503ae60de30e4bfb30c917>
- <https://pypy.org/posts/2024/07/finding-simple-rewrite-rules-jit-z3.html>
- <https://dl.acm.org/doi/10.1145/3428234>  Verifying and improving Halide’s term rewriting system with program synthesis
- <https://repositum.tuwien.at/bitstream/20.500.12708/81336/1/Daly-2022-Synthesizing%20Instruction%20Selection%20Rewrite%20Rules%20from%20RTL%20using...-vor.pdf>  Synthesizing Instruction Selection Rewrite Rules from RTL using SMT <https://arxiv.org/abs/2405.06127> Efficiently Synthesizing Lowest Cost Rewrite Rules for Instruction Selection <https://github.com/rdaly525/MetaMapper>
- Ruler
- Isaria
- <https://jrmcclurg.com/papers/pact_2022_paper.pdf>  Optimizing Regular Expressions via Rewrite-Guided Synthesis

# Algebraic Graphs

- <https://www.philipzucker.com/tree_decomp_etudes/>

- <https://www.cs.tufts.edu/comp/150FP/archive/andrey-mokhov/algebraic-graphs.pdf> Algebraic Graphs with Class (Functional Pearl).
- <https://arxiv.org/abs/2202.09230> United Monoids: Finding Simplicial Sets and Labelled Algebraic Graphs in Trees
- <https://arxiv.org/abs/2403.02273> Let a Thousand Flowers Bloom: An Algebraic Representation for Edge Graphs
- <https://dl.acm.org/doi/abs/10.1145/3704892> Formalising Graph Algorithms with Coinduction
- <https://dl.acm.org/doi/10.1145/3473577> Algebras for weighted search
- <https://dl.acm.org/doi/10.1145/2500365.2500613> Fun with semirings: a functional pearl on the abuse of linear algebra

# Graph Rewriting

Sea of nodes? Is there a declarative file somewhere?

There is that Wolfram hypergraph stuff.

<https://github.com/zxcalc/quantomatic/tree/stable/examples>

<https://github.com/UoYCS-plasma/P-GP2/tree/master/programs/deterministic> GP2 example graph rewrite rules. Coloring, sorting, shortest path

Knots and braiding algebra <https://en.wikipedia.org/wiki/Braid_group>

# CAS

Mathematica, sympy, maxima, etc. Where are they? There must be ton?

<https://github.com/corywalker/expreduce/tree/master/expreduce/resources>

# Physics

Physics

- annihilation creation algebra `[adag, a] = adag a - a adag = 1`  `{cdag, c} = 1` and so on.
- gamma matrices   <https://en.wikipedia.org/wiki/Gamma_matrices>
- Pauli matrix commutators
- ZX calculus
- <https://arxiv.org/pdf/2310.14056>
- <https://lmcs.episciences.org/1570> Generator and relations for n-qubit clifford operators
- <https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/cliffordt.egg> <https://arxiv.org/pdf/2204.02217.pdf>

- <https://allofphysics.com/list_all_inference_rules> Ben writes in that he has a system for inferences in physics. I'm not sure this is the same sort of thing I was getting at, but it is an interesting perspective.
-

# Deobfuscation

Mixed boolean arithemtic. Used for obduscation and subsequent deobfuscation.

- <https://github.com/plzin/mba> <https://plzin.github.io/posts/mba>
- <https://arxiv.org/abs/2305.06763>
- <https://github.com/open-obfuscator/o-mvll/blob/main/src/passes/arithmetic/Arithmetic.cpp>
- <https://secret.club/2022/08/08/eqsat-oracle-synthesis.html>
- <https://github.com/fvrmatteo/ASMSimplifier/blob/master/Deobfuscator/peephole.new> peephole optimizations

- <https://github.com/fvrmatteo/oracle-synthesis-meets-equality-saturation> crazy big python file.

```python
  rules = [
    # Commutativity
    Rule((x*y), [(y*x)]),
    Rule((x+y), [(y+x)]),
    Rule((x&y), [(y&x)]),
    Rule((x^y), [(y^x)]),
    Rule((x|y), [(y|x)]),
    # Associativity
    Rule((x*(y*z)), [((x*y)*z)]),
    Rule((x+(y+z)), [((x+y)+z)]),
    Rule((x&(y&z)), [((x&y)&z)]),
    Rule((x^(y^z)), [((x^y)^z)]),
    Rule((x|(y|z)), [((x|y)|z)]),
    # Normalisation (pushing NotW to the leaves)
    Rule((~(x*y)), [(((~x)*y)+(y-1))]),
    Rule((~(x+y)), [((~x)+((~y)+1))]),
    Rule((~(x-y)), [((~x)-((~y)+1))]),
    Rule((~(x&y)), [((~x)|(~y))]),
    Rule((~(x^y)), [((x&y)|(~(x|y)))]),
    Rule((~(x|y)), [((~x)&(~y))]),
    # Normalisation (pushing NegW to the leaves)
    Rule((-(x*y)), [((-x)*y),  (x*(-y))]),
    # Equalities
    Rule((~x), [((-x)-1)]),
    Rule(((-x)-1), [(~x)]),
    Rule((-x), [((~x)+1)]),
    Rule(((~x)+1), [(-x)]),
    Rule((x-y), [(x+(-y))]),
    Rule((x+(-y)), [(x-y)]),
    # Inverse distributivity
    Rule(((x*y)+(x*z)), [(x*(y+z))]),
    Rule(((x*y)-(x*z)), [(x*(y-z))]),
    # Collapsing
    Rule(((x*y)+y), [((x+1)*y)]),
    Rule((x+x), [(2*x)]),
    Rule(((x^y)|y), [(x|y)]),
    # Swapping
    Rule((x*(-y)), [(-(x*y))]),
    # Distributivity
    Rule(((x+y)*z), [((x*z)+(y*z))]),
    Rule(((x-y)*z), [((x*z)-(y*z))]),
    # Additional rules
    Rule((-(x+y)), [((-x)+(-y))]),
    Rule(((x&y)<<z), [((x<<z)&(y<<z))]),
    Rule(((x>>z)<<z), [(x&(~((1<<z)-1)))]),
    Rule((y-((~x)&y)), [(x&y)]),
    Rule(((x<<z)+(y<<z)), [((x+y)<<z)]),
    Rule(((x<<y)<<z), [((x<<z)<<y)]),
  ]
  ```

# Bits and Bobbles

<https://github.com/philzook58/awesome-egraphs> Most of these projects must have rules in some form. Hard to find an collate them. Many go outside of a purely declarative subset.

If you want a concrete interesting project (for an undergrad say), consider taking one of these programmatic rewrite systems and convert it into a declarative form of your choice.

<https://news.ycombinator.com/item?id=43101449#43138696> Hacker news discussion of this post.

Like functional programming, many kinds of "grammars" are examples of rewrite rules.

Lean, Isabelle, Coq, ACL2 etc must have piles of rules but it's hard to know how to separate them from not rules. How to mine?

RRL rewrite rule laboratory <https://github.com/GunterMueller/RRL_Rewrite-Rule-Laboratory> <https://github.com/GunterMueller/RRL_Rewrite-Rule-Laboratory/tree/master/Sutra/examples> <https://www.sciencedirect.com/science/article/pii/089812219400218A>

<https://gappa.gitlabpages.inria.fr/gappa/theorems.html> Gappa for floating point reasoning. not exactly equational, but a nice set of rules.

Apache rewrite rules - <https://httpd.apache.org/docs/2.4/mod/mod_rewrite.html> Is this the same sort of thing? sed, awk, etc?

Deductive databases for geometry. The equational version.

inverses <https://en.wikipedia.org/wiki/Inverse_function> and Galois connections or pesudoinverses or left/right inverses. f(g(X)) = X but not g(f(Y)) = Y. Or `f(g(f(X))) = f(X)`. <https://en.wikipedia.org/wiki/Galois_connection> . Examples floor/ceiling/round, convex hull / interval closure , closure / interior,   `F x <= y == x <= G y` <https://link.springer.com/chapter/10.1007/3-540-47797-7_4> Galois Connections and Fixed Point Calculus - backhouse. Backhouse generally has some sweet stuff.

`cos(acos(cos(X))) = cos(X)`.  The fact that `acos` is partial makes the "inverse" relationship finicky `acos(7) = ?`. Also the multivaluedness `acos(cos(X)) != X` generally because cos(x + 2pi) = cos(x)` and `acos` picks a branch.

projections `p(p(X)) = p(X)`. idempotency. a way of defining a subset/ refinement . `prj(X) = X` means x is in the subset.

quotients and canonizers. <https://en.wikipedia.org/wiki/Quotient> `canon(X + 0) = canon(X)`. `canon(canon(X)) = X` Injections and projections. `canon(X) = prj(inj(X))` if we inject into some other domain to represent the quotient. For example if we use sets of equivalence classes to represent quotient, proj picks a special one. `inj : A -> Set(A), inj(x) = {y | eq(x,y)}` , `proj : Set(A) -> A` maybe `proj(S) = min x, x in S` as an example if A has total ordering. `canon(X) = canon(Y) <-> eq(X,Y)`

<https://agraef.github.io/pure-lang/>

<https://redex.racket-lang.org/> plt redex <https://docs.racket-lang.org/redex/index.html> Mostly evaluation rewriting rules? <https://github.com/racket/redex/tree/master/redex-examples/redex/examples>

<https://www.specware.org/research/specware/> category theory. Where's the meat?

dedukti is a rewrite engine. <https://github.com/Deducteam/Dedukti/tree/master/examples> There must be more somewhere?

Agda has a rewriting extension thing.

Explicit substitution calculi. sigma-rho <https://en.wikipedia.org/wiki/Explicit_substitution>

Algebraic graphs.

Relation Algebra <https://en.wikipedia.org/wiki/Relation_algebra>
<https://en.wikipedia.org/wiki/Relational_algebra>

Equational theories for parallelism? Process calculi?

Linear algebra
<https://www.cl.cam.ac.uk/~jrh13/papers/hol05.pdf> Robert Solovay decision procedure for linear algebra. Section 4.

```
% expanding out dot product
0vec . x = 0
x . 0vec = 0
(cx) . y = c(x . y)
x . (cy) = c(x . y)
-x . y = - (x . y)
x . -y = - (x . y)
(x + y) . z = x . z + y . z
x . (y + z) = x . y + x . z
(x - y) . z = x . z - y . z
x . (y - z) = x . y - x . z

```

<https://github.com/yihozhang/szalinski-egglog>

Caviar rules <https://github.com/caviar-trs/caviar/tree/main/src/rules> . Looks like mostly typical integer identity stuff?

Does Maude have good rule sets? K?

Where are the hardware compiler rules?

Ghidra decompiler has a rewrite rule file
<https://github.com/NationalSecurityAgency/ghidra/blob/2eff37f655159574593b15bc19273915fc780cf2/Ghidra/Features/Decompiler/src/decompile/cpp/rulecompile.cc>
<https://github.com/NationalSecurityAgency/ghidra/blob/2eff37f655159574593b15bc19273915fc780cf2/Ghidra/Features/Decompiler/src/decompile/cpp/rulecompile.cc>

- halide ruler
- herbie
- egg suite
- egglog suite
- termination-comp
- hlint
- metatheory
- <https://github.com/yihozhang/egglog-pointer-analysis-benchmark>
- KAT

- Lift/Rise?
- speq?
- Isaria
- casc ueq
- smtcomp maybe
- tensat
- glenside

- cvc5 has the RARE rule files <https://github.com/cvc5/cvc5/blob/main/src/theory/bv/rewrites>

- t/rewriter/rewriter.txt pretty interesting. Rewrite returns codes saying fail, done, rewritecdepth1 2 3 or full

- Geometric algebra
- div grad curl

- Concrete Mathematics

- Boolean Equations
- List Rules
- Arithmetic Rules
- Kleene Algebra
- Category Theory
-

- Egg examples
- Twee
- TPTP
- REC
- TermComp
- Cranelift
-

- SMT theory files

Rewrite rule synthesis <https://inst.eecs.berkeley.edu/~cs294-260/sp24/projects/charleshong/> "Theory exploration"

Halide
LLVM
PDDL and PDL for MLIR <https://mlir.llvm.org/docs/PDLL/>

Does sympy, mathematica, maxima, etc have piles of declarative rewrite rules?

<https://github.com/sdiehl/pyrewrite/tree/master/examples>
<https://dl.acm.org/doi/10.1145/3428234>  Verifying and improving Halide’s term rewriting system with program synthesis

<https://arxiv.org/pdf/2404.08106> KestRel: Relational Verification Using E-Graphs for Program Alignment

- Relation algebra
- peephole

- <https://leahneukirchen.org/caudex/equational-reasoning.html>
- <http://www.mathmeth.com/read.shtml>
- <https://inst.eecs.berkeley.edu/~cs294-260/sp24/2024-01-24-haskell-rewriting>
- deforestation

<https://leahneukirchen.org/caudex/equational-reasoning.html> This is a nice pile of links.

<https://www.cs.nott.ac.uk/~pszgmh/tpfa.pdf> Theorem Proving for All: Equational Reasoning in
Liquid Haskell (Functional Pearl)

Hutton calculating compiler

See hlint rules <https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml>

Quickspec <https://hackage.haskell.org/package/quickspec>

Algebra of programming

Bird and Gibbons Books <https://www.cs.ox.ac.uk/publications/books/functional/>

Something that sometimes holds me back in my enthusiasm for egraphs and other automated theorem proving technology lately is that I'm missing a nice databank of rulesets and compelling examples. Making examples or benchmarks is actually quite hard, extremely useful, and sometimes underappreciated work.

Upon self grilling myself on a walk, I can eventually remember a bunch of links and pointers and things.

It is not exactly clear if reifying some of these rule sets is useful in the context of knuckledragger. It is not that useful to reify into a lemma something that z3 has the baked in ability to prove. On the other hand, sometimes the external solvers do not have these baked in and need them as explicit lemmas. It may also be important if you want to some precise rewrite or apply manipulations.

I'm somewhat susceptible to existential crises like that. It's really important to stay grounded in actually trying to do, calculate, build something IMO. It can be easy to eventually be drawn into the technical stuff for it's own sake, or develop some nth degree unhinged abstractions, philosophy or design principles that ultimately apply to like 2 examples which are actually better dealt with via more elementary means.

There isn't and I'm not sure there could be a uber format to declaratively specify rewrite rules. As the XKCD classic goes

People need things tweaked.

Perhaps an important lesson is that many of the published egg papers do funky shit that isn't really a pure rewrite rule.

I pulled out some examples just to give a flavor of what you might find in these places.
