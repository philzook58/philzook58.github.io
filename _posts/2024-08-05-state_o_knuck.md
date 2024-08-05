---
title: State of Knuckledragger, a Semi-Automated Python Proof Assistant
date: 2024-08-05
---


I've been working on Knuckledragger, my Z3 based semi-automated python proof assistant, on and off for 6 months (or arguably [five years](https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/)). I've realized I've done a bunch of stuff and despite writing often, not written the slightest bit about much of it.

So here is a fast sketchy run down of:

- The basic design and kernel
- Ideas and starts on theories like intervals, complex numbers, set theory, groups, linear algebra, software verification
- Convenience systems like tactics, syntax, and systematic approaches to induction principles and refinements.

Repo is here <https://github.com/philzook58/knuckledragger>

Got a new logo! Been adding docs, tutorials, CI, etc. All that software jazz.

<img src="https://raw.githubusercontent.com/philzook58/knuckledragger/main/logo.webp" alt="drawing" width="400"/>

Previous posts in this vein:

- <https://www.philipzucker.com/python-itp/>
- <https://www.philipzucker.com/knuckledrag2/>

# Z3 Expressions Types

A design principle I've narrowed in on is piggy packing on the z3 AST datatypes for my theorem datatypes.

I [was toying](https://github.com/philzook58/knuckledragger/blob/c02b9521aafdc141364179119256955fcf37ef34/thoughts/knuckledrag2.py) with making my own first order logic / higher order logic AST in python and then interpreting it into Z3. So far, I think this is an unnecessary indirection and was just burning time, lines of code, and design energy to no benefit. Z3 already has a feature rich access api and maybe the only thing I would have added to my type is built in polymorphism/sort generics.

This has the benefit that if you know how to write z3 python, you know how to write knuckledragger. If you know smtlib, you know knuckledragger. And regardless of the fate of knuckledragger, these are useful skills.

This has the downside of me having no control over how Z3 did things. I'm monkey patching in new functions onto ExprRef pretty often, which isn't great for python tooling and maybe tougher for reading by humans. Things that I would make attributes of a custom class or wrapper I'm instead sometimes putting into a global dictionary to be looked up (single dispatch overloading in particular I'm thinking of).

On the whole I think the positives outweigh the negatives.

# The Kernel

<https://github.com/philzook58/knuckledragger/blob/main/knuckledragger/kernel.py>

The core principle of knuckledragger is that it is just as thin as possible framework to chain calls to automated theorem provers in a principled way. By restricting our logic to more or less what the solvers already offer, we get a lot of distance and usability for free. The less code I write the better.

I have a [lot of experience](https://colab.research.google.com/github/philzook58/z3_tutorial/blob/master/Z3%20Tutorial.ipynb) using z3 to model problems in python. I like it. However, there is a need to break it up. Z3 does not have a mechanism to distinguish between theorems to be proved and theorems proven.

I had been considering [signing Proofs cryptographically](https://www.philipzucker.com/python-itp/) or other scams, but I've reverted to a pretty straightforward protected Proof datatype.

The details of what follows have been simplified a bit from what is actually in the library, which has more convenience and safety checks <https://github.com/philzook58/knuckledragger/blob/main/knuckledragger/kernel.py>

```python
@dataclass(frozen=True)
class Proof(z3.Z3PPObject):
    thm: z3.BoolRef
    reason: list[Any]
    admit: bool
```

The proof datatype is constructed through two functions `axiom` and `lemma`. `Proof` itself is made difficult to get at outside of the kernel module (although not impossible). You are not supposed to directly construct `Proof` itself. It isn't _really_ protected from construction, since you are always free to call `axiom`, but that is on you.
All interactive theorem provers also have the ability to introduce axioms.

```python
def axiom(thm: z3.BoolRef, by=[]) -> Proof:
    return Proof(thm, by, admit=True)

def lemma(thm: z3.BoolRef, by: list[Proof] = []) -> Proof:
    s = z3.Solver()
    for hyp in by:
        assert isinstance(hyp, Proof)
        s.add(hyp.thm)
    s.add(Not(thm))
    assert unsat == s.check()
    return Proof(thm, by, admit)
```

Also important though is the ability to make new definitions. Without this, you can't ever abstract much of anything or you need to introduce your new definitions as raw `axiom` calls every time.

```python
defns: dict[z3.FuncDecl, Defn] = {}
def define(name: str, args: list[z3.ExprRef], body: z3.ExprRef) -> z3.FuncDeclRef:
    assert f not in defns # no redefinitions allowed
    f = z3.Function(name, *[arg.sort() for arg in args])
    ax = axiom(ForAll(args, f(*args) == body))
    defns[f] = ax
    f.defn = ax
    return f
```

You also are going to often to want to make recursive definitions. `define` should check if you are making a recursive definition, but does not currently.

My current idea about `define_fix` is to write your definition body in the fixpoint style using a python lambda. I can record all the subcalls easily, which I prefer to digging through the AST. The termination could be discharged via default measure relations or by a call to aprove or similar termination checker.

```python
def define_fix(name: str, args: list[z3.ExprRef], retsort, fix_lam) -> z3.FuncDeclRef:
    sorts = [arg.sort() for arg in args]
    sorts.append(retsort)
    f = z3.Function(name, *sorts)

    # wrapper to record calls
    calls = set()

    def record_f(*args):
        calls.add(args)
        return f(*args)

    defn = define(name, args, fix_lam(record_f))
    # TODO: check for well foundedness/termination, custom induction principle.
    return defn
```

Having these global `lemma` / `define` functions and global `defns` dictionaries is a bit goofy. It might be nice to separate into different contexts.

# Applications and Theories

I think it is very very important to be example driven. I could definitely spend all my time on making cute little syntax or logic gizmos. Some of that is good, but only when informed by actual problems.

These are the sorts of theories I've been attacking to varying success.

## Nats

A basic datatype that you expect in a theorem prover is the natural numbers. There is a school of thought that the naturals are the root of mathematics ("God made the integers; all else is the work of man.").

From my perspective, it is unfortunate that smtlib does not offer a built in natural type. Instead it offers an integer type. So two different options for naturals are to cut them out of the built in integers or to use a Peano algerbaic datatype.

### Peano

We can model Naturals using an algebraic datatype consisting of a zero and successor constructor  `type nat = Zero | Succ of nat`.

This is a principled way of constructing them via a textbook style. It was by first inclination but now I have my doubts.

<https://www.philipzucker.com/sqrt2_2/> I wrote a bit about this here. I also toyed with an interesting style of defining via reflection into the Ints using `reflect` `reify` combinators.

You can define arithmetic (plus, times, etc) on these things via structural indiction.

You need to define an induction principle, more on how to do this generally later. For Nats it's easy to do by hand as an axiom schema (an axiom parametrized by data, in this case the data is a python or z3 lambda specifying a predicate `P`)

```python
Nat = Datatype("Nat")
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()

def induct(P):
    return kd.axiom(
            Implies(And(P(Nat.zero), ForAll([n], Implies(P(n), P(Nat.succ(n))))),
                   #-----------------------------------------------------------
                   ForAll([n], P(n))))
```

I've been finding this kind of clunky to work with.

Or similarly to this a binary datatype (a list of bits `type nat = list bool`)

### Nats as subsets

Nats can be perceived as part of a general phenomenon of a sort that is a subset of another sort, namely the integers. More on doing this generally in the refinement section.

Nats a subset of Ints, but ints are in turn a subset of the reals. There is also utility in considering the nonnegative reals as an entity of interest (real induction).

There are "induction" principles that directly work over Ints, like two sided induction. Maybe these are useful. <https://math.stackexchange.com/questions/4867269/how-does-one-perform-induction-on-integers-in-both-directions>

```python
# something like this cutting out the integers and getting a result statement as weakened to integers
def induct(P):
    return kd.axiom(And(P(0), kd.QForAll([n], n >= 0, P(n), P(n+1))) == kd.QForAll([n], n >= 0, P(n)))
# or this assuming P is true for all values <= 0
def induct2(P):
    return kd.axiom(And(kd.QForAll([n], n <= 0, P(n)), kd.QForAll([n], n >= 0, P(n), P(n+1))) == ForAll([n, P(n)]))
#or this double sided induction moving outward from 0 rather than just forward.
def induct3(P):
    return kd.axiom(And(P(0), ForAll([n], P(n) == P(n+1))) == ForAll([n], P(n)))
```

## Lists

Lists are a useful and prominent type. We can define an induction principle similar to the above. Everything needs to be parametrized on the sort in question.

Sequences are a built in that may serve better <https://microsoft.github.io/z3guide/docs/theories/Sequences/> . They are basically a free monoid type but with some useful stuff that you'd need to define for your own list type.

A suggested induction principle for sequences.

```python
def induct(T: z3.SortRef, P) -> kd.kernel.Proof:
    z = z3.FreshConst(T, prefix="z")
    sort = z3.SeqSort(T)
    x, y = z3.FreshConst(sort), z3.FreshConst(sort)
    return kd.axiom(
        z3.And(
            P(z3.Empty(sort)),
            kd.QForAll([z], P(z3.Unit(z))),
            kd.QForAll([x, y], P(x), P(y), P(z3.Concat(x, y))),
        )  # -------------------------------------------------
        == kd.QForAll([x], P(x))
    )
```

## Reals

I've been thinking about the reals a lot because I want knuckledragger to be good at the kinds of things I would do in an engineering or physics context.
Also I want to do basic calculus.

Lots and lots of junk on the reals.

Avoiding all the epsilon-delta calculus pain seems desirable, so I've been considering alternatives.

- formal power series, streams, Nat -> R
- Real induction. These might be useful axiom schema to throw in as a version of completeness of the reals. <https://math.stackexchange.com/questions/4202/induction-on-real-numbers>
- sequences
- convergence
- intermediate value theorem. Axiomatizing that bisection means something is a relative of completeness.
- extended reals. <https://en.wikipedia.org/wiki/Extended_real_number_line> Make an algebraic datatype with special +- infinity constructors. Relatedly can work with projectively extended <https://en.wikipedia.org/wiki/Projectively_extended_real_line> with only a single infinity
- Try Eudoxus reals?
-

### Formal Power Series

[Formal power series](https://en.wikipedia.org/wiki/Formal_power_series) are "just" `N >> R`. They have pointwise addition and a convolutional multiplication. These are normal perfectly computable things. Also division, composition, and inversion. You can also define operations analogous to differentiation and integration. So they're a cool algebraic thing. You need to show they converge if you want to connect back to more ordinary definitions

<https://www.cs.dartmouth.edu/~doug/powser.html> My all time favorite pearl about power series in haskell.

Sympy and sage also have support for these power series like things.

Streams are supported in cvc5 <https://cvc5.github.io/docs/cvc5-1.0.0/api/python/pythonic/dt.html> . This could be an alternative encoding. Or perhaps take coinduction as an inspiration for our modelling.

```python
# a sketch. Doesn't really work yet.
import knuckledragger as kd
from z3 import *
Powser = IntSort() >> RealSort()
n,m = Ints("n m")
a,b,c = Consts("a b c", Powser)
x,y,z = Reals("x y z")
fP0 = kd.define("P0", [], K(IntSort(), RealVal(0)))
P0 = fP0()
P0.defn = fP0.defn
series = kd.define("series", [x], Store(P0, IntVal(0), x)) #Lambda([n], If(n == 0, x, 0))
add = kd.define("add", [a,b], Lambda([n], a[n] + b[n]))
kd.notation.add.register(Powser, add)
add_comm = kd.lemma(ForAll([a], a + P0 == a), by=[add.defn, P0.defn])
add_assoc = kd.lemma(ForAll([a,b,c], a + (b + c) == (a + b) + c), by=[add.defn])
add_series = kd.lemma(ForAll([x,y], series(x) + series(y) == series(x + y)), by=[add.defn, series.defn, P0.defn])


# tail?
shift = kd.define("shift", [a], Lambda([n], a[n+1])) # Lambda([n], If(n >= 1, a[n + 1], 0))
mul = Function("mul", Powser, Powser, Powser)
kd.notation.mul.register(Powser, mul)
#mul = kd.define("mul", [a,b], Lambda([n], If(n == 0, a[n] * b[n], 
#                                                     shift(a) * b + series(a[0]) * shift(b))))
#mul = kd.define("mul", [a,b], Lambda([n], Sum([m], a[m] * b[n-m]))
# could use smul(a[0], b) instead of series(a[0]) * shift(b)

# a projection
powser = kd.define("powser", [a], Lambda([n], If(m < 0, RealVal(0), a[m])))
is_powser = kd.define("is_powser", [a], powser(a) == a)
powser_idem = kd.lemma(ForAll([a], powser(powser(a)) == powser(a)), by=[powser.defn])

def powser_induct(P):
    return kd.axiom(Implies( ForAll([a], Implies(is_powser(a) & P(a), P(shift(a)))),
                             #----------------------------------
                             ForAll([a], Implies(is_powser(a), P(a)))))
```

### Differentiation

I think the seeds of an approach can be found here <https://www.philipzucker.com/z3_diff/>

We can axiomatize a reasonable syntactic-ish differentiation operation. It isn't connected automatically to the analytic definition, and it can't be since differentiation is not a total operation on functions.

A "yoneda-like" trick is useful to define a `sin = sinR . : (R -> R) -> (R -> R)` function because it automatically associates all `compose` to the right.

```python
# sketch
RFun = ArraySort(R,R)
derive = Function("derive", RFun, RFun) #diff?
sin,cos,exp = Consts("sin cos exp", RFun)

dsin = derive(sin) == cos
dcos = derive(cos) == -sin
dexp = derive(exp) == exp

chain = ForAll([f,g], derive(comp(f,g)) == derive(g) * comp(derive(f),g))
dsum = ForAll([f,g], derive(f + g) == derive(f) + derive(g))
dmul = ForAll([f,g], derive(f * g) == derive(f) * derive(g))
c = Real("c")
dconst = ForAll([c], derive(K(R,c)) == K(R,0))
dx = derive(Lambda([x], x)) == K(R,1)
```

### Rounding

Convergence is a painful thing to deal with. A bit surprising to me, but obvious in hindsight is that you need a good theory of rounding/floor. That's how you derive the appropriate N for proofs of convergence. <https://www.philipzucker.com/analysis_knuckle/>

Rounding is actually kind of tricky. The z3 built ins `ToReal` and `ToInt` are a start, but they don't have that strong of reasoning power. They need to be helped along a little. This s actually evidence I think of the utility of knuckledragger. I could not get some basic theorems to go through in one shot through z3, but with some guidance I could. This probably has to do with seeding the ematching mechanism or preventing z3 from using some built in theory where it can't make use of the appropriate high level reasoning.

```python
import knuckledragger as kd
from z3 import *
x,y = Reals("x y")
floor = kd.define("floor", [x], z3.ToReal(z3.ToInt(x)))
n, m = Ints("n m")
int_real_galois = kd.lemma(ForAll([x,n], (x < ToReal(n)) == (ToInt(x) < n)))
int_real_galois_ge = kd.lemma(ForAll([x,n], (ToReal(n) <= x) == (n <= ToInt(x))))
_2 = kd.lemma(ForAll([x], z3.ToInt(floor(x)) == z3.ToInt(x)), by=[floor.defn])

floor_idem = kd.lemma(ForAll([x], floor(floor(x)) == floor(x)), by=[floor.defn, _2]) # nice. got it. Needed lemma _2
floor_le = kd.lemma(ForAll([x], floor(x) <= x), by=[floor.defn])
floor_gt = kd.lemma(ForAll([x], x < floor(x) + 1), by=[floor.defn])

toreal_mono = kd.lemma(ForAll([n,m], (n <= m) == (z3.ToReal(n) <= z3.ToReal(m))))

# The definitional property of floor. If n <= x then n <= floor(x)
c = kd.Calc([n,x], z3.ToReal(n) <= x)
c.eq(n <= z3.ToInt(x))
c.eq(z3.ToReal(n) <= floor(x), by=[floor.defn])
floor_minint = c.qed()


```

### HyperReals

Sequences of R can have an equivalence structure put on them that gives you infinitesimals.

Or can directly axiomatize it and directly build a transfer schema. Doing this makes me uncomfrotable. The schema to do this requires traversal of the ast and tracking of which definitions are tainted by the `std` predicate.

acl2(R) uses the hyperreals.

- <https://www.researchgate.net/publication/220532005_Nonstandard_analysis_in_ACL2> Gamboa thesis Hyperreals in ACL2 acl2(r). There's also a chapter in Applications of ACL2 book. Some follow up works. I saw someone
- <https://www.youtube.com/watch?v=U-y8UNccnIw&t=909s&ab_channel=Galois> max von hippel is using acl2(r)

There is a line of older automated reasoning work claiming the hyperreals makes problems way easier (Bledsoe and Ballantyne). The Hyperreals kind of algebrize calculus.

- <https://www.cs.utexas.edu/ftp/techreports/atp71.pdf> [3] W. W. Bledsoe. Some automatic proofs in analysis.
- <https://www.sciencedirect.com/science/article/abs/pii/0004370272900410> computer assisted limit theorems 9172 bledsoe
- <https://link.springer.com/article/10.1023/A:1005843328643>  The Heine–Borel Challenge Problem. In Honor of Woody Bledsoe
- Bledsoe, W.: Challenge problems in elementary analysis, Journal of Automated Reasoning 6 (1990),
- Bledsoe, W. W.: Heine–Borel Theorem Analogy Example, Technical Report Memo ATP 124, University of Texas Computer Science Dept., Austin, TX, 1994.
- <https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=70050293723ef74d0747323be1cd06eabe5ebbc5> Non resolution theorem proving
- Ballantyne, M. and Bennett, W., Graphing methods for topological proofs, The University of
Texas at Austin Math. Dept. Memo ATP-7 (1973).
- Ballantyne, A. M. and Bledsoe, W. W., Automatic proofs of theorems in analysis using nonstandard techniques, The University of Texas at Austin Math. Dept. Memo ATP-23 (July
1975); J. ACM, to appear, July 1977. -
- A. Michael Ballantyne: The Metatheorist: Automatic Proofs of Theorems in Analysis Using Non-Standard Techniques, Part II.
- Isabelle Hyperreals <https://isabelle.in.tum.de/library/HOL/HOL-Nonstandard_Analysis/Hyperreal.html>
- <https://www.cl.cam.ac.uk/~lp15/papers/Isabelle/fleuriot-princip-CADE.pdf> hyperreals applied to newton

### Complex

Defining a complex number as a record of its real and imaginary part is very natural.

```python
import knuckledragger as kd
import z3

C = kd.notation.Record("C", ("re", z3.RealSort()), ("im", z3.RealSort()))

z, w, u, z1, z2 = z3.Consts("z w u z1 z2", C)
add = kd.define("add", [z1, z2], C.mk(z1.re + z2.re, z1.im + z2.im))
kd.notation.add.register(C, add)
mul = kd.define(
    "mul", [z1, z2], C.mk(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
)
kd.notation.mul.register(C, mul)
conj = kd.define("conj", [z], C.mk(z.re, -z.im))


div = kd.define(
    "div",
    [z1, z2],
    C.mk(
        (z1.re * z2.re + z1.im * z2.im) / (z2.re**2 + z2.im**2),
        (z1.im * z2.re - z1.re * z2.im) / (z2.re**2 + z2.im**2),
    ),
)
kd.notation.div.register(C, div)

C0 = C.mk(0, 0)
C1 = C.mk(1, 0)

add_zero = kd.lemma(z3.ForAll([z], z + C0 == z), by=[add.defn])
mul_zero = kd.lemma(z3.ForAll([z], z * C0 == C0), by=[mul.defn])
mul_one = kd.lemma(z3.ForAll([z], z * C1 == z), by=[mul.defn])
add_comm = kd.lemma(z3.ForAll([z, w], z + w == w + z), by=[add.defn])
add_assoc = kd.lemma(
    z3.ForAll([z, w, u], (z + (w + u)) == ((z + w) + u)), by=[add.defn]
)
mul_comm = kd.lemma(z3.ForAll([z, w], z * w == w * z), by=[mul.defn])

# unstable perfoamnce.
# mul_div = kd.lemma(ForAll([z,w], Implies(w != C0, z == z * w / w)), by=[div.defn, mul.defn], timeout=1000)
##mul_div = Calc()
div_one = kd.lemma(z3.ForAll([z], z / C1 == z), by=[div.defn])
div_inv = kd.lemma(z3.ForAll([z], z3.Implies(z != C0, z / z == C1)), by=[div.defn])

# inv = kd.define("inv", [z], )

# conjugate
# polar
norm2 = kd.define("norm2", [z], z * conj(z))
```

### Powers

While z3 has good built in powers `x**4`, it does not have great reasoning principles for abstract powers `x**n`

There is reason to believe I may have to axiomatize it. Power is kind of special. It is a homomorphism between the group of addition and multiplication. <https://en.wikipedia.org/wiki/Exponential_field>

```python
x = Real("x")
n, m = Reals("n m")
pow2 = kd.define("pow2", [x], 2 ** x)
pow2_add_raw = kd.axiom(ForAll([n,m], (2**n) * (2 ** m)  == 2**(n + m))) # z3 can't derive this :(
pow2_add = kd.lemma(ForAll([n,m], pow2(n) * pow2(m) == pow2(n + m)), by=[pow2.defn, pow2_add_raw])
pow2_1 = kd.lemma(ForAll([n], pow2(1) == 2), by=[pow2.defn])
kd.lemma(ForAll([x], x**2 * x**3 == x ** 5))
kd.lemma(ForAll([n,m], (2**(n + 1)) * (2 ** m)  == 2**(n + m + 1)), by=[pow2_add_raw])
c = kd.Calc([n], 2 * 2 ** n)
c.eq(RealVal(2) ** 1 * 2 ** n )
c.eq(pow2(1) * pow2(n) , by=[pow2.defn])
c.qed()
c.eq(pow2(n + 1), by=[pow2_add])
c.eq(2 ** (n + 1), by=[pow2.defn])
c.lemmas
# c.qed() #fails. Yikes.

c = kd.Calc([n], 
     pow2(n + 1) - pow2(n))
c.eq(pow2(1) * pow2(n) - pow2(n), by=[pow2_add])
c.eq(2 * pow2(n) - pow2(n),       by=[pow2_1])
c.eq(pow2(n))
pow2_diff = c.qed()
```

z3 really doesn't like reasoning over its native powers. It's best to wrap them in definitions.

### Exp, Sine, Cosine

They're tricky. Basically they kind of need calculus.

Sine and cosine don't actually because the addition formula (which are relatives of the summation formula for powers)

Would it be good to define sine and cosine through the complex numbers? Maybe.

An interesting option is bolting in bounds from flint, which I think are as trustworthy as anything I'm doing.

```python
import flint
def flint_schema(z3_fun, flint_fun):
    def res(x):
        x = flint_fun(flint.arb(x))
        mid = RealVal(x.mid().str(5, radius=False))
        rad = RealVal(x.rad().str(5, radius=False))
        kd.axiom(And(mid - rad < z3_fun(RealVal(x)), z3_fun(RealVal(x)) < mid + rad))
    return res

cos_bnd = flint_schema(cos, flint.arb.cos)
cos_bnd(1)
```

rational trignometry. <https://web.maths.unsw.edu.au/~norman/Rational1.htm>
<https://www.cut-the-knot.org/pythagoras/RationalTrig/CutTheKnot.shtml>
"angles don't exist" Only the combo sin(theta) not raw theta.
<https://en.wikipedia.org/wiki/List_of_trigonometric_identities>

A simple but good test problem is bounding the value of `e` from first principles.

## Sets

Attempting a ZF like set theory. We can postulate a undefined sort `Set` and give it some properties. Everything is defined by it's relation to `elem` which is awkward. `ArraySort(Set,BoolSort())` is a useful stand-in for classes.

There are still kinks to work out for sure.

This is interesting <https://lawrencecpaulson.github.io/2022/02/02/Formalising_Math_Set_theory.html> in particular Art Quaife. Automated Deduction in von Neumann–Bernays–Gödel Set Theory. <https://rdcu.be/cJtDU>

```python
import knuckledragger as kd
from z3 import *
Set = DeclareSort("Set")
x,y,z,A,B,C = Consts("x y z A B C", Set)
Class = Set >> BoolSort()
P,Q,R = Consts("P Q R", Class)
elem = Function("elem", Set, Set,BoolSort())
Set.ext = kd.axiom(ForAll([A,B], (A == B) == ForAll([x], elem(x,A) == elem(x,B))))
emp = Const("emp", Set)
Set.emp = emp
emp_def = kd.axiom(ForAll([x], ~elem(x, Set.emp)))
emp.defn = emp_def


upair = Function("upair", Set, Set, Set)
upair_def = kd.axiom(ForAll([x,y,z], elem(z, upair(x,y)) == ((z == x) | (z == y))))

sep = Function("sep", Set, Class, Set)
sep_def = kd.axiom(ForAll([P,x,z], elem(z, sep(x,P)) == (elem(z,x) & P[z]), patterns=[elem(z,sep(x,P))]))


#biginter, biginter_def = define("biginter", [A], sep(A, ))


le = kd.notation.le.define([A,B], ForAll([x], Implies(elem(x,A), elem(x,B))))

le_eq = kd.lemma(ForAll([A,B], (A <= B) & (B <= A) == (A == B)), by=[le.defn, Set.ext])

# kuratowski
pair = kd.define("pair", [A,B], upair(upair(A,A),upair(A,B)))

bigunion = Function("bigunion", Set, Set)
# hmm. using a existnetial. I don't love that.
# The skolem is similar to choice, except it takes in the element and the big set. choice takes in big set and set in big set and gives element it chose.
bigunion_def = kd.axiom(ForAll([x,A], elem(x, bigunion(A)) == Exists([y], elem(x,y) & elem(y,A))))

union = kd.define("union", [A,B], bigunion(upair(A,B)))
union_elem = kd.lemma(ForAll([x,A,B], elem(x, union(A,B)) == (elem(x,A) | elem(x,B))), by=[union.defn, upair_def, bigunion_def])

union_comm = kd.lemma(ForAll([A,B], union(A,B) == union(B,A)), by=[union_elem, Set.ext])
union_idem = kd.lemma(ForAll([A], union(A,A) == A), by=[union_elem, Set.ext])

klass = kd.define("class", [A], Lambda([x], elem(x,A)))

elem_klass = kd.lemma(ForAll([A,x], klass(A)[x] == elem(x,A)), by=[klass.defn])

inter = kd.define("inter", [A,B], sep(A, klass(B)))

elem_inter = kd.lemma(ForAll([A,B,x], elem(x, inter(A,B)) == (elem(x,A) & elem(x,B))), by=[inter.defn, elem_klass, sep_def])

elem_inter2 = kd.lemma(ForAll([A,B,x], elem(x, inter(A,B)) == elem(x,A) & elem(x,B)), by=[inter.defn, elem_klass, sep_def])

# and so on

```

Alternative set theories are intriguing <https://plato.stanford.edu/entries/settheory-alternative/> <https://en.wikipedia.org/wiki/List_of_alternative_set_theories> . Mizar is supposedly based around Tarski Grothedieck

## Linear Algebra

Linear algebra is ubiquitously useful and an algebraic theory. I want to attack numpy problems. I the ability to make correctness bounds on numpy operations.

### Fixed Dimension

A simple but useful thing to do is worry about low dimensional vectors spaces. Dimension 2,3,4 have all sorts of geometric utility.

```python
def RN(N):
    RN = Datatype("R^" + str(N))
    RN.declare('make', *[('x' + str(i), RealSort()) for i in range(N)])
    RN = RN.create()
    x,y,z = Consts('x y z', RN)
    a,b,c = Reals("a b c")
    RN.x = lambda v,n: RN.accessor(0,n)(v) 
    RN.vadd = kd.define("vadd", [x,y], RN.make(*[RN.x(x,i) + RN.x(y,i) for i in range(N)]))
    notation.add.register(RN, RN.vadd)
    RN.vadd_comm = kd.lemma(ForAll([x,y], x + y == y + x), by=[RN.vadd.defn])
    RN.vadd_assoc = kd.lemma(ForAll([x,y,z], (x + y) + z == x + (y + z)), by=[RN.vadd.defn])

    RN.vsub = kd.define("vsub", [x,y], RN.make(*[RN.x(x,i) - RN.x(y,i) for i in range(N)]))
    notation.sub.register(RN, RN.vsub)
    RN.smul = kd.define("vmul", [x,a], RN.make(*[a * RN.x(x,i) for i in range(N)]))
    notation.mul.register(RN, RN.smul)

    RN.vdot = kd.define("vdot", [x,y], Sum([RN.x(x,i) * RN.x(y,i) for i in range(N)]))
    # @ overload
    return RN

R1 = RN(1)
R2 = RN(2)
R3 = RN(3)
R4 = RN(4)
```

### Finite Dimension

A more mathy thing to do is consider all finite vector spaces.

Lists seemed somewhat natural, but actually were a bit awkward.

A universe to work in for finite dimensional algebra is using `Z >> R == ArraySort(IntSort(), RealSort())` as a vector space. This has all finite dimensional subspaces in it.

There is a theme of needing to subset of finite Support (indices for which a vector is possibly non zero) in an infinite space. Sequences / Lists of Nats can supply a way of specifying a support.

### Geometry

I have experimented with a purely logical form of postulating an undeclared sort called `Point` and the Point pairs as a directed segment, then undirected segment as a quotient of this, then lines as a quotient of this, and so on. Probably this is a goofy kind of hard mode. A tower of refining equivalences is an interesting pattern.

More straightforward is to define `Point = Record(("x", RealSort()), ("y", RealSort()))`. We can construct `Set(Point)` such as lines and circles using algebraic constraints `line = kd.define("line", [a,b,c] Lambda([p], a * p.x + b * p.y == c))` and `circle = kd.define("circle", [c,r], Lambda([p], (p.x - c.x)**2 + (p.x - c.y) ** 2 == r))`. `is_line` can be constructed requiring the Set be affine

## Group Theory

Group theory is a nice one because it's very algebraic. The homomorphism theorems are a fairly elementary thing that can be considered real abstract math. It is also difficult to see how to formulate the homomorphism theorem in a meaningful way into ATPs.

Individual finitely presentable groups seem easy enough to axiomatize directly. Declare sorts and constants and multiplication/identity/inverse functions with the appropriate properties. The `Calc` macro is nice for proofs. Using sage and hence GAP/Magma can help automatically discharge

A theme I've seen is it is nice to have a "Universe" datatype. I think here, permutations on the integers (a subset of Nat -> Nat) is an interesting and rich Universe in which we can embed all countable groups (The content of the Cayley representation). All finite groups are isomorphic to some subset of this object. This is a metafact which maybe we can't express, because what exactly _is_ a group in the first place? A sort that posesses functions that fit the axioms?

We could also declare some uninterpreted sort called `Grp`

## Category Theory

In some respects, there are roots in this project in my experiences trying to use Z3 and other ATPs as a category theory prover.

- <https://www.philipzucker.com/category-theory-in-the-e-automated-theorem-prover/>
- <https://www.philipzucker.com/theorem-proving-for-catlab-2-lets-try-z3-this-time-nope/>

I think I knew how to write fully safe axioms, but they had lots of side conditions I thought were redundant. Knuckledragger is principled enough that I could prove these side conditions are unneeded.

Some general helper/tactic framework for embedding Generalized Algebraic theories into z3 seems possible. Discharging typing obligations early, since they are fairly automatic. Help to write/generate the right typing assumptions.

## Software

### Modelling CPUs

Two things systems I think are interesting are modelling the Nand2Tetris CPU and RiscV cpus. The first for educational value, the second maybe could actually be useful.

The general plan is to define instruction datatypes, a state datatype,

```python
# a sketch

import knuckledragger as kd
from z3 import *

RVInsn = Datatype("RVInsn")
RVInsn.declare("ADD", ("rd", BitVecSort(5)), ("rs1", BitVecSort(5)), ("rs2", BitVecSort(5)))
RVInsn = RVInsn.create()

RVState = Datatype("RVState")
RVState.declare("mk", ("reg", ArraySort(BitVecSort(5), BitVecSort(32))), ("pc", BitVecSort(32)), ("mem", ArraySort(BitVecSort(32), BitVecSort(8))))
RVState = RVState.create()

insn = Const("insn", RVInsn)
st = Const("st", RVState)
addr = Const("addr", BitVecSort(32))

load32 = kd.define("load32", [st, addr], 
  Concat(Select(st.mem, addr + i) for i in range(4))
)
reg = Const("reg", )

regwrite = kd.define("regwrite", [st, reg, addr],
                       If(reg == 0, st, # r0 is not a real register.
                       
                       )
  Store(st.reg, insn.rd, load32(st, st.reg[insn.rs1]) + load32(st, st.reg[insn.rs2]))
)

exec_insn = kd.define("exec_insn", [insn,st],
  If(insn.is_ADD, 
                RVState.mk(
                Store(st.reg, insn.rd, st.reg[insn.rs1] + st.reg[insn.rs2]),
                st.pc + 1,
                st.mem
                ),
)

```

Some nand2tetris circuitry buildup

```python
import knuckledragger as kd
from knuckledragger import lemma, axiom, define

from z3 import *

B = BoolSort()
BV1 = BitVecSort(1)
x,y,z,w,u,v = Consts("x y z w u v", BV1)
"""
CNand = Function("Nand", B,B,B,B)
nand_def = axiom(ForAll([x,y,z], CNand(x,y,z) == 
     Or(And(x == True,  y == True,  z == False),
        And(x == True,  y == False, z == True),
        And(x == False, y == True,  z == True),
        And(x == False, y == False, z == True))))
"""

CNand = define("CNand", [x,y,z], Or(
    And(x == 1, y == 1, z == 0),
    And(x == 1, y == 0, z == 1),
    And(x == 0, y == 1, z == 1),
    And(x == 0, y == 0, z == 1)))


test1 = lemma(CNand(True,True,False), by=[CNand.defn])

nand_fun = lemma(ForAll([x,y,z], CNand(x,y,z) == (~(x & y) == z)), by=[CNand.defn])
nand_fun

CNot = define("CNot", [x,y], CNand(x,x,y))
lemma(ForAll([x,y], CNot(x,y) == (~x == y)), by=[CNand.defn, CNot.defn])

cnot_fun = lemma(ForAll([x,y], CNot(x,y) == (~x == y)), by=[nand_fun, CNot.defn])


CAnd = define("CAnd", [x,y,z], Exists([w], And(CNand(x,y,w), CNot(w,z))))

cand_fun = lemma(ForAll([x,y,z], CAnd(x,y,z) == (x & y == z)), by=[cnot_fun, nand_fun, CAnd.defn])


COr = define("COr", [x,y,z], Exists([w,u], And(CNot(x,w), CNot(y,u), 
                                                   CNand(w,u,z))))

cor_fun = lemma(ForAll([x,y,z], COr(x,y,z) == ((x | y) == z)), by=[cnot_fun, nand_fun, COr.defn])

a,b,out,sel,sela,selb,notsel = Consts("a b out sel sela selb notsel", BV1)
Mux = define("Mux", [a,b,sel,out], Exists([sela,selb,notsel], And(
    CNot(sel, notsel), 
    CAnd(notsel, a, sela),
    CAnd(sel, b, selb),
    COr(sela, selb, out))))

mux_fun = lemma(ForAll([a,b,sel,out], Mux(a,b,sel,out) == (out == If(sel == 0, a, b))), by=[Mux.defn, cnot_fun, cand_fun, cor_fun])

```

### Hoare and WP

I could perhaps make Hoarse as a new judgement, a different kind of `Proof`. I can also deeply internalize into the system. This might be necessary to use cvc5 separation logic too.

I've done deeply internalized WP in smtlib before. It's kind of clunky.

### Metatheory

On thing people do in proof assistants is logical or programming language metatheory. They want to prove their language is type safe or terminating or that their logic is sound or has other interesting properties.

I need serious investment into the inductive relations subsystem before this becomes more tractable.

## Numerical Computation

### Intervals

I spent some nice time on a plane doing interval arithmetic.
It is tempting to do intervals over the extended reals.

That intervals can be improper is discomfitting.

```python
import knuckledragger as kd
import knuckledragger.theories.Real as R
import z3

Interval = kd.notation.Record("Interval", ("lo", kd.R), ("hi", kd.R))
x, y, z = z3.Reals("x y z")
i, j, k = z3.Consts("i j k", Interval)

setof = kd.define("setof", [i], z3.Lambda([x], z3.And(i.lo <= x, x <= i.hi)))

meet = kd.define("meet", [i, j], Interval.mk(R.max(i.lo, j.lo), R.min(i.hi, j.hi)))
meet_intersect = kd.lemma(
    z3.ForAll([i, j], z3.SetIntersect(setof(i), setof(j)) == setof(meet(i, j))),
    by=[setof.defn, meet.defn, R.min.defn, R.max.defn],
)

join = kd.define("join", [i, j], Interval.mk(R.min(i.lo, j.lo), R.max(i.hi, j.hi)))
join_union = kd.lemma(
    z3.ForAll([i, j], z3.IsSubset(z3.SetUnion(setof(i), setof(j)), setof(join(i, j)))),
    by=[setof.defn, join.defn, R.min.defn, R.max.defn],
)


width = kd.define("width", [i], i.hi - i.lo)
mid = kd.define("mid", [i], (i.lo + i.hi) / 2)

add = kd.notation.add.define([i, j], Interval.mk(i.lo + j.lo, i.hi + j.hi))
add_set = kd.lemma(
    z3.ForAll([x, y, i, j], z3.Implies(setof(i)[x] & setof(j)[y], setof(i + j)[x + y])),
    by=[add.defn, setof.defn],
)

sub = kd.notation.sub.define([i, j], Interval.mk(i.lo - j.hi, i.hi - j.lo))

# and so on
```

I'm particular interested in the ability of interval analysis to give verified bounds on differential / integral equations. There is a fixed point procedure for iteratively improving an approximate solutions to an ODE  $y'(t) = Ly(t)$,   $y_{n+1}(t) = y(0) + \int y'_{n}(t)dt = y(0) + \int Ly_{n}(t)dt $. This is picard-lindelof iteration / born approximation / other names. If you lift this to intervals, the integral of intervals is seinsibly over approximable. If you can find a interval approximation of y that maps into itself, you can eventually show the true solution must lie within there. A neat kind of bootstrapping.

- <https://www.philipzucker.com/z3_diff/>
- <https://www.philipzucker.com/z3-cegar-interval/>
- <https://www.philipzucker.com/more-stupid-z3py-tricks-simple-proofs/>

- Computational Functional Analysis by Moore <https://www.amazon.com/Computational-Functional-Analysis-Mathematics-Applications/dp/1904275249>
- Introduction to Interval Analysis  <https://epubs.siam.org/doi/10.1137/1.9780898717716> <http://www-sbras.nsc.ru/interval/Library/InteBooks/IntroIntervAn.pdf>
- methods and applications of inverval analysis <https://epubs.siam.org/doi/book/10.1137/1.9781611970906>
- Interval Analysis: Application in the Optimal Control Problems
- Real Analysis: A Constructive Approach Through Interval Arithmetic - bridger
- Interval Methods for Systems of Equations
- <https://fab.cba.mit.edu/classes/S62.12/docs/Hickey_interval.pdf>
- bishop
- Constructive functional analysis

### Fixed

SMT fixed point airthmetic theory. <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324132/>

`ToInt` and `ToReal` give a theory of rounding. Want to actually work with bitvectors too though.

### Floats

I left off last month a bit stumped on the floats.
The built in support for Real <-> Float reasoning is pretty weak. I'm not comfortable axiomatizing it. So not super sure how to continue, but I haven't attacked it recently.

# Features

Moving on from applications, we can discuss the niceties of syntax or general modelling problems of being in multi-sorted first orderlv logic.

## Overloading

This is honestly one of the most useful things knuckledragger offers right now.

Python has single dispatch in the standard library. <https://peps.python.org/pep-0443/> <https://docs.python.org/3/library/functools.html#functools.singledispatch> Hence, I consider this to be an accepted python pattern.

But I can't dispatch on the python class because z3 python does not produce different classes for different sorts. So the thing needs to be modified slightly to dispatch on sorts. This is not too hard to achieve. By monkey patching these dispatch objects onto the operators for `ExprRef`, we can overload the operators.

 <https://github.com/philzook58/knuckledragger/blob/c02b9521aafdc141364179119256955fcf37ef34/knuckledragger/notation.py#L54>

```python
class SortDispatch:
    """
    Sort dispatch is modeled after functools.singledispatch
    It allows for dispatching on the sort of the first argument
    """

    def __init__(self, default=None, name=None):
        self.methods = {}
        self.default = default
        self.name = name

    def register(self, sort, func):
        self.methods[sort] = func

    def __call__(self, *args, **kwargs):
        return self.methods.get(args[0].sort(), self.default)(*args, **kwargs)

    def define(self, args, body):
        assert isinstance(self.name, str)
        defn = kd.define(self.name, args, body)
        self.register(args[0].sort(), defn)
        return defn


add = SortDispatch(z3.ArithRef.__add__)
z3.ExprRef.__add__ = lambda x, y: add(x, y)
```

There is a question whether the overloading mechanism should do interesting search. Multiple dispatch could be nice. Typeclasses could be nice, Oleg style.

### Datatype fields

It is an extremely useful overload to enable getting the fields of z3 datatype via dot notation rather that getting at the accessors through the . It really really makes expressions easier to read, and easiness to read is part of what makes it more likely what you write is what you meant.

Python `__getattr__` is what gets called when a field is not found on the class as a fallback. The following snippet then searches through

<https://github.com/philzook58/knuckledragger/blob/c02b9521aafdc141364179119256955fcf37ef34/knuckledragger/notation.py#L103>

```python
def lookup_cons_recog(self, k):
    """
    Enable "dot" syntax for fields of z3 datatypes
    """
    sort = self.sort()
    recog = "is_" == k[:3] if len(k) > 3 else False
    for i in range(sort.num_constructors()):
        cons = sort.constructor(i)
        if recog:
            if cons.name() == k[3:]:
                recog = sort.recognizer(i)
                return recog(self)
        else:
            for j in range(cons.arity()):
                acc = sort.accessor(i, j)
                if acc.name() == k:
                    return acc(self)


z3.DatatypeRef.__getattr__ = lookup_cons_recog
```

### Notation

Syntax via <https://github.com/lark-parser/lark> . lark is a very nice arser generator framework. You actually can mix and match parser fragments. In this way, we could offer a framework for custom syntaxes, including unicode. I have not explored this direction much, as it isn't really to my taste.

## Tactics

### Calc

A thing I really like is calc tactics. These let you write an equational proof. I've moved over to using a Calc python class as it enables better syntax.
It can be used either by chaining or by mutation.
It is not part of the kernel. It discharges it's obligations through the kernel function `lemma`. When you call `c.qed()` it takes all the equational step lemmas it has found and asks the kernel if they combine from the total left hand side to right hand side.

<https://github.com/philzook58/knuckledragger/blob/c02b9521aafdc141364179119256955fcf37ef34/knuckledragger/tactics.py#L5>

```python
class Calc:
    """
    calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    """

    def __init__(self, vars, lhs):
        # TODO: hyps=None for conditional rewriting. assumpt, assume=[]
        self.vars = vars
        self.terms = [lhs]
        self.lemmas = []

    def ForAll(self, body):
        if len(self.vars) == 0:
            return body
        else:
            return z3.ForAll(self.vars, body)

    def eq(self, rhs, by=[]):
        self.lemmas.append(kd.lemma(self.ForAll(self.terms[-1] == rhs), by=by))
        self.terms.append(rhs)
        return self

    # TODO: lt, le, gt, ge chaining. Or custom op.

    def __repr__(self):
        return "... = " + repr(self.terms[-1])

    def qed(self):
        return kd.lemma(self.ForAll(self.terms[0] == self.terms[-1]), by=self.lemmas)
```

### Simp

A simplification tactic is at the core of a good experience. You hammer on these in lean, coq, or isabelle.

I thought maybe I'd need an extensive metaprogramming system to do this but now I'm not so sure.

Actually for the first time I found the z3 Tactic system super useful. I can give a `Goal` the defns database or maybe other simp databases and use demodulator, simplify, elim-predicates, macro-finder as promising simplifiers. By making a dummy variable "knuckle_goal" I can track what is my original term. This is not trusted kernel code. Once i have a suspected good simplified term, I can send it to `lemma` to actually confirm.

```python
def simp(t: z3.ExprRef) -> z3.ExprRef:
    expr = z3.FreshConst(t.sort(), prefix="knuckle_goal")
    G = z3.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = z3.Then(z3.Tactic("demodulator"), z3.Tactic("simplify")).apply(G)[0]
    # TODO make this extraction more robust
    return G2[len(G2) - 1].children()[1]


def simp2(t: z3.ExprRef) -> z3.ExprRef:
    expr = z3.FreshConst(t.sort(), prefix="knuckle_goal")
    G = z3.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = z3.Tactic("elim-predicates").apply(G)[0]
    return G2[len(G2) - 1].children()[1]
```

I should make a mechanism to store simp databases.

<https://github.com/AliveToolkit/alive2/blob/fc3ea52ba741306e1595d46753aa2795ca4aaab2/smt/solver.cpp#L584> tactic usage in alive2, the only place I've heard of it happening usefully.

### Other

- Backwards
- Mizar / Isar combinstors
- Unification helper for z3 ast might be nice
- Binders
- Egraph - Maybe my external z3 egraph <https://www.philipzucker.com/ext_z3_egraph/> is good for a tactic. There is also a z3 tactic "euf-completion" which is intriguing

## Alternative Solvers

`lemma` has an extra keyword parameter `solver` which defaults to z3. By mocking out other solvers, cvc5, vampire etc to match the z3 Solver python interface, they should also be supported. This is a work in progress. There are a variety of utility functions for printing tptp and smtlib. <https://github.com/philzook58/knuckledragger/blob/main/knuckledragger/utils.py>

## Lemma Database

Something I resist is requiring you to give the system a name for every lemma. It would be kind of nice, but then you'ld have to write the names twice `my_good_lemma = lemma("my_good_lemma", ...)`. In other languages like Julia, they have macros for this kind of thing `@lemma my_good_lemma. I kind of hate (other people's) macros though.

Python is super duper dynamic and introspectable though. A kind of fiendish but cool thing is that I can scan the entire system for `Proof` objects. Imported modules are just another python object , so by looking into the `__dict__`, I can find the name you used. This is super hacky just to avoid doing this in a boring way. I'm not sure.

```python
def lemma_db():
    """Scan all modules for Proof objects and return a dictionary of them."""
    db = {}
    for modname, mod in sys.modules.items():
        thms = {name: thm for name, thm in mod.__dict__.items() if is_proof(thm)}
        if len(thms) > 0:
            db[modname] = thms
    return db
```

These databases might be useful for machine learning training sets and for extracting theorem prover competition benchmarks. By erasing intermediate nodes in the proof tree, you can make a sequence of harder and harder problem, until you ask for the top level theorem given only the leaf axioms of the proof.

## Refinement and Partiality

This is a complicated subject and needs to be a post in its own right.

It is a consistent need to have a good mechanism to talk about subsets of some sort. Dependent type theories use sum types for this. This isn't quite an option.

One low effort thing that helps is a notion of quantified forall and exists combinators. These get you a lot of distancew for not too much. If I tag sorts with a special property `wf` for their well formedness condition, these combinators automatically add that upon quantifying over a variable of that sort.

```python
def QForAll(vs, *hyp_conc):
    """Quantified ForAll

    Shorthand for `ForAll(vars, Implies(And(hyp[0], hyp[1], ...), conc))`

    If variables have a property `wf` attached, this is added as a hypothesis.

    """
    conc = hyp_conc[-1]
    hyps = hyp_conc[:-1]
    hyps = [v.wf for v in vs if hasattr(v, "wf")] + list(hyps)
    if len(hyps) == 0:
        return z3.ForAll(vs, conc)
    elif len(hyps) == 1:
        return z3.ForAll(vs, z3.Implies(hyps[0], conc))
    else:
        hyp = z3.And(hyps)
        return z3.ForAll(vs, z3.Implies(hyp, conc))


def QExists(vs, *concs):
    """Quantified Exists

    Shorthand for `ForAll(vars, And(conc[0], conc[1], ...))`

    If variables have a property `wf` attached, this is anded into the properties.
    """
    concs = [v.wf for v in vs if hasattr(v, "wf")] + list(concs)
    if len(concs) == 1:
        z3.Exists(vars, concs[0])
    else:
        z3.Exists(vars, z3.And(concs))
```

- Free logic <https://plato.stanford.edu/entries/logic-free/> . The `E` predicate is much like my `wf`. Identical maybe.

There are some design choices for how to build refinement sorts/ subsets.

- predicates describing the subset. `Even(x) = Exists([y], x == 2*y)`
- Projection functions. These are the analog of choice functions to the predicate functions. A projection function is idempotent `proj(prof(x)) = x`. A projection function defines a subset such that `proj(x) = x`. Because of idempotency `proj(x)` always obeys this condition. `proj_even(x) = 2 * (x / 2)`
- New sorts by fiat `E = DeclareSort("Even"), inj = Function("inj", Int, E), proj = Function("proj", E, Int), Implies(Even(x), proj(inj(x)) == x)`
- Newtype sorts combined with projection functions. The newtypes can also contain useful witnesses. `type Even = Even {x : Int, y : Int}`  `wf(e) = e.x == 2*e.y`

## Existentials

Manual skolemization is probably wise. You can often find a natural candidate for naming these things when you do it manually. THis is important, because you can then help z3 along. Z3 is not strong at nested quantifiers. Maybe with Vampire coming online, I can suffer more quantifier nesting.

For example `even(x) = exists y, x == 2*y`. However, there is an obvious definition

## Lambdas

Use lambdas sparingly and defunctionalize immediately. You will be surprised by what things about lambdas z3 will understand and won't. It can normalize lambdas, but don't count on much beyond that. Perhaps when I have better support for using Vampire or Eprover I can amend this suspicion of using lambdas.

I've complained before that python doesn't have a good lambda manipulation library. Well, actually, z3 is not a bad version of that really. It has enough functionality that a locally nameless open_binder combinator is easy to write. Be forewarned, alpha equivalent lambdas are not `eq`.

```python
def open_binder(lam: z3.QuantifierRef):
    vars = [
        z3.Const(lam.var_name(i).upper(), lam.var_sort(i))
        for i in reversed(range(lam.num_vars()))
    ]
    return vars, z3.substitute_vars(lam.body(), *vars)
```

## Induction

Don't have a great answer. I have built wrappers around the z3 Datatype mechanism to derive induction and recursion definitions. Not in love with it.

A very preliminary prototype

```python
from knuckledragger.kernel import *
from z3 import *
class Datatype(z3.Datatype):
    def create(self):
        DT = super().create()  # z3 already checks for positivity.
        PredSort = ArraySort(DT, BoolSort())
        # construct an induction principle.
        P = FreshConst(PredSort, prefix="P")
        hyps = []
        for i in range(DT.num_constructors()):
            constructor = DT.constructor(i)
            args = [
                FreshConst(constructor.domain(j), prefix="a")
                for j in range(constructor.arity())
            ]
            acc = P[constructor(*args)]
            for arg in args:
                if arg.sort() == DT:
                    acc = QForAll([arg], P[arg], acc)
                else:
                    acc = ForAll([arg], acc)
            hyps.append(acc)
        x = FreshConst(DT, prefix="x")
        conc = ForAll([x], P[x])
        induct = Lambda([P], Implies(And(hyps), conc))
        induct_ax = trust(ForAll([P], induct[P] == True))

        # recursor

        # store inside the data type?
        DT.induct = induct
        DT.induct_ax = induct_ax
        #DT.rec = rec
        return DT

def recursor(name, *cases, DT):
    assert all(case.range() == DT for case in cases)
    f = z3.RecFunction(name, DT, )  # also freshness needs to be checked


def define_rec(name, args, body, measure=None):
    sig = [arg.sort() for arg in args]
    f = z3.RecFunction(name, *sig)  # also freshness needs to be checked. Yikes.
    # TODO check termination and totality of definition
    RecAddDefinition(f, body)
    fun_def = infer([], ForAll(args, f(*args) == body))
    return f, fun_def
```

### Inductive Relations

A useful modelling capability is inductive relations, which are served by dependent type definitions in systems like lean and coq.
Dependent types are not necessary for some version of inductive relations though.

In my Justified SMT post <https://www.philipzucker.com/minikanren_inside_z3/> , I discussed the basic idea of how I intend to encode this. You can use the clark completion to define all the ways a relation can become true. If you add an extra parameter to the relation that describes the tree and existential witnesses of the proof, these become well founded relations. Induction over the relation is really induction over this proof object.

These are related to refinements in that we need an extra consistency condition that the proof object attached to the relation actually checks.

## Generics

A big problem for smtlib is that you can't easily write sort generic/polymorphic definitions.
This can be got around by writing generic functions/definitions such that they take in the z3 sort as a parameter to a python function. This is analogous to using a module system to achieve

Another intriguing option is the addition of an open or closed `Any` universe. One can define a datatype `ClosedAny` or declare an uninterpreted sort `OpenAny` that has injectors and projectors from all other types. Things that have to be generic can work over this type sometimes. Without auto conversions, this may be rather clunky. It is interesting the relationship between this Any type and type theory universes.

Staging might be interesting to explore to remove overhead of the dynamic typing approach. Often the types will resaolve to something concrete.

## Context

It would be nice sometimes to not have to keep repeating `ForAll([x], foo, bar, biz)` all the time and keep some lemmas in the `by` clause by default. One solution is to make local lemma wrappers. Could do something trickier or more stateful though. Not sure.

```python
def local_lemma(thm,by=[]):
    return kd.lemma(kd.QForAll([x], foo, bar, thm), by=by + my_default_lemmas)
```

## Algebraic Hierarchy

An interesting and tough problem is building algebraic hierarchies in your system. The theories of monoids, groups, rings, fields, etc have a relation to one another. This relation is a quite possibly complicated partial order and there may be more than one may to interpret the naturals as a group for example. There are other less algebraic examples such as different strengths of continuity or differentiability in analysis.

I spent a bit of time thinking about this. It's tough and seemingly tied to generics. So far, it looks like it would require building a lot of metasystem in python. I'm punting on this one. Let's prove some concrete things before worrying about how to abstract them. I suspect the generic weakness of knuckledragger means it will never have an awesome solution to this problem. It's like trying to model Lean in C. You can probably do it in some sense, but at extreme encoding cost.

## Quotients

One thing the Lean folks claim is a big deal is that Lean has a culture of supporting quotients, possibly even in the core system.

Quotients do exist and are useful. They feel dual in some way to the problems of refinements

There are a couple strategies.

- canon function.
- Sets of equal elements
- By fiat declare new undefined quotient sort.

Z/2 is kind of the quotient analog of even/odd

## ite chains

It is unfortunate that the z3 python bindings do not offer a pattern matching construct even though the surface language of smtlib2 does. Big nested sequences of `If` are ugly, hard to read, and hence easy to get wrong.

<https://docs.pola.rs/api/python/stable/reference/expressions/api/polars.when.html> The dataframe ecosystem has a convention to solve a similar problem. I'm trying to use familiar python idioms when one can work.

I could do purely functional chaining or stateful. I'm kind of offering both here by returning `self`.

```python
class Cond():
    def __init__(self):
        self.clauses = []
        self.cur_case = None
        self.other = None
        self.sort = None
    def when(self,c : z3.BoolRef):
        assert self.cur_case is None
        assert isinstance(c, z3.BoolRef)
        self.cur_case = c
        return self
    def then(self,e):
        assert self.cur_case is not None
        if self.sort is not None:
            assert e.sort() == self.sort
        else:
            self.sort = e.sort()
        self.clauses.append((self.cur_case, e))
        self.cur_case = None
        return self
    def otherwise(self, e):
        assert self.otherwise is None
        assert self.sort == e.sort()
        self.otherwise = e
        return self.expr()
    def expr(self):
        assert self.otherwise is not None
        assert self.cur_case is None
        acc = self.otherwise
        for c, e in self.clauses:
            acc = z3.If(c,e,acc)
        return acc


c = Cond()
c.when(x.is_nil()).then(0)
c.when(x.is_cons()).then(1 + length(x.tail))
c.otherwise(-1) # case should never hit, this is the general issue with partiality
length = kd.define("length", [x], c.expr())
```

One possibility to sanity check the totality of your cases is to put a fresh variable in the otherwise and then do a relational check `prove(e1 == e2)` where `e1` and `e2` only differ by the fresh constant in the otherwise default case. If this check does not pass, your cases are not total. And you can achieve this without going to a Maybe or keeping aside some other special error value. Kind of cute.

## Speed

Am I hanging myself by being in python? I find myself worrying about eventually needing everything cached and how complicated that will be. So far, everything runs fast.

It would be good to line profile

## Machine Learning

I haven't done much of anything yet. Lemma databases might be helpful for this.

Copilot rules though. It does a decent job of filling in both my theorem statements and proofs.

# Bits and Bobbles

Gordon plotkin, decision procedure for partial derivatives <https://www.youtube.com/watch?v=j_w6GNUIQDo&ab_channel=AppliedCategoryTheory%40UCR>

Marshall <https://github.com/andrejbauer/marshall>  <https://dl.acm.org/doi/pdf/10.1145/3341703> MarshallB . Awesome exact real system. Based around a principle that refining reals don't have equality. So the language has a more pirmitve thing than Bools, the sierpinski truth value (a stream that eventually ends in Unit).

<https://codac.io/>  Interval tubes for robotics

# Meta Z3

# Skolem

<https://www.cs.utexas.edu/~moore/acl2/manuals/latest/index.html?topic=ACL2____DEFCHOOSE>

<https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php/ACL2____DEFUN-SK>

Can I use a z3 skolem tactic?

```python
def define_choose(name, all_args, ex_args, body):
    all_sorts = list(map(lambda x: x.sort(), all_args))
    sk = [Function(name + "_sk_" + e.decl().name(), *all_sorts, e.sort()) for e in ex_args] 
    kd.axiom(ForAll(all_args, Implies(Exists(ex_args, body), substitute(body))
    f = kd.define(name, all_args)
    f.wit = 

def define_herbrand(name, all_args):
    [FreshConst() for a in all_args]
    substitute()
    kd.axiom(Implies(body, ForAll([all_args], body)))
```

# Refinements

Replace with bounded quantifiers
forall x, P(x) ---> forall x, wf(x) -> P(x)
exists x, P(x) ---> exists x, wf(x) /\ P(x)

In what sense is this a sufficient alternative?

It's a design choice of refinement using newtype wrapper

Question is are there confusing situations where one might construct the record

Is any of this worth it though

Two big problems I have are representing quotients and refinements

- Make new sorts
- Parametrize them
- Meta records

Internalizing a refinement system using quotation.

What about Boole.

See we want variables to be tagged with their assumptions, which can be deischarged when we quantify over them. Maybe if I had a variation of first order logic.
 x|x>=0 |- t  -->  |- forall x, x >=0 => t
I could tuple ("x", x >= 0) and bubble up. But then I need to double everything
NatForAll(vars, f) = ForAll([vars], Implies(x >= 0, f))
NatExists(vars, f) = Exists([vars], And(x >= 0, f))

<https://isabelle.in.tum.de/~haftmann/pdf/data_refinement_in_isabelle_hol_haftmann_krauss_kuncar_nipkow.pdf> data refinement in isabelle 2013

<https://www.andreipopescu.uk/pdf/NF.pdf> non free datatypes

<https://www21.in.tum.de/~kuncar/huffman-kuncar-itp2012.pdf>  Lifting and Transfer: A Modular Design for
Quotients in Isabelle/HOL
4. Cezary Kaliszyk and Christian Urban. Quotients revisited for Isabelle/HOL. In
William C. Chu, W. Eric Wong, Mathew J. Palakal, and Chih-Cheng Hung, editors,
Proc. of the 26th ACM Symposium on Applied Computing (SAC’11), pages 1639–
1644. ACM, 2011.
5. Alexander Krauss. Simplifying Automated Data Refinement via Quotients. Technical report, Technische Universität München, July 2011. <http://www21.in.tum>.
de/~krauss/papers/refinement.pdf.
6. Lawrence C. Paulson. Defining functions on equivalence classes. ACM Trans. Comput. Logic, 7(4):658–675, October 2006.

Pos = DeclareType("Pos")
inj = DeclareFunction("inj", Pos, Int)

def pos_induct(P):
    ForAll([x], Implies(x >= 0, P(x))) == ForAll([y], P(y))

Is there a P(x,y) style "induction" principle that is natural?

 <https://arxiv.org/abs/2303.05244> Transport via Partial Galois Connections and Equivalences
Kevin Kappelmann

<https://z3prover.github.io/papers/z3internals.html#sec-refinement-types> refinment types in z3. Suggested to use user propagation

```python
wf = kd.notation.SortDispatch(default=lambda n: BoolVal(True), name="wf")
ExprRef.wf = property(lambda self: wf[self])

def Record(name, *fields, pred=None):
    rec = Datatype(name)
    rec.declare("mk", *fields)
    rec = rec.create()
    rec.wf = pred
    # Using projector for smart constructor.
    #rec._mk = rec.mk
    #rec.mk = lambda *args: rec._mk(proj(args))
    wf.register(rec, pred)
    return rec

Nat = Datatype("Nat", ("val", IntSort()), pred=lambda n: n >= 0)


def QConst(name, sort):
    c = Const(name, sort)
    c.wf = sort.wf(c)
    return c


# could just use record. This has the advantage of not using 
def Newtype(name, sort, pred=None):
    nt = Datatype(name)
    nt.declare("mk", ("val", sort))
    nt = nt.create()
    nt.wf = pred
    wf.register(nt, pred)
    return nt


```

```python
class RefineSort:
    def __init__(self, sort, pred):
        self.sort = sort
        self.pred = pred
    def Consts(self, names):
        vs = z3.Consts(names, self.sort)
        for v in vs:
            v.wf = self.pred(v)
        return vs
    def wf(self, e : ExprRed):
        """Is well formed"""
        return self.pred(e)
    def ForAll(self, vs, body):
        pass
    def Exists(self, vs, body):
        pass
```

This doesn't work for incoming assumptions. It can determine some expression is unconditionally positive.

```python
@dataclass 
class PosRecord():
    hyp : BoolRef
    x : ExprRef
    pf: kd.Proof # kd.Proof[hyp |- x >= 0]


```

A different style using projector functions.

```python
# projector functions
pos = define("pos", [x], If(x <= 0, 0, x))
# or abs
pos_idem = kd.lemma(pos(pos(x)) == pos(x), by=[pos.defn])
pos_id = kd.lemma(Implies(x >= 0, pos(x) == x)) # identity on appropriate subset

def pos_induct(P):
    return kd.axiom(
        Implies(P(0), ForAll([x], Implies(P(pos(x))), P(pos(x) + 1)))
    ForAll([x], P(pos(x)))_


# aka round
nat_proj = ToReal(ToInt(x)) 

Projection is the fusing of making a new sort and it's map back.

class Proj():
    p
    idem:Proof
    id_dom:Proof
m(m x) = m(x) 
Hmm. monadic?


# or as a schema.
proj_def(name, x, P)
    axiom idem



```

# Quotients

forall x ---> forall x
exists x ----> exists x, P(x)_/\ forall y, y = x -> P(y)

<https://arxiv.org/abs/1907.07591>  Defining Functions on Equivalence Classes

Canon functions.
We don't need a new sort if we can define a function that canonizes.

Can also directly axiomatize these functions.
Can also combine with a projection?

cauchy_canon_proj =
  eq(x,y) == (cauchy(x) == cauchy(y)) /\
  cauchy(x) => canon(x) ==

Seq

<https://en.wikipedia.org/wiki/Equivalence_class#canonical_surjection>

canon(canon(x)) = canon(x) # idem. is projection
eq(x,y) == (canon(x) == canon(y)) # reflect equiv
ForAll([y], Exists([x], Implies(canon(x) == canon(y), canon(x) == x))) # for all equiv class, there exists a self mapping element / fixed point. Is this a theorem or axiom?

Exists([x], canon(x) == x)

```python
canon_mod3 = define("canon_mod3", [x], x % 3)
canon_canon = kd.lemma(ForAll(canon(canon(x))) == canon(x), by=[canno.defn])
# kind of obvious by definition of eq.
eq_mod3 = define("eq_mod3", [x,y], x % 3 == y % 3)
# eq_mod3_2 = define("eq_mod3", [x,y], Exists([x], x == y + 3*z)) # less obvious
eq_mod_rel = define("eq_rel", [x,y,z], x == y + 3*z) # proof relevant.

proof relevant eq_mod factors into canon and proof

proof = define("z_rel", [x,y], (x - y) / 3)




eq(x,y,proof(x,y)) == (canon(x) == canon(y))
eq(x,y) == eq(x,y,proof(x,y)) # don't use existential. Use skolem.

even(x,y) == x == 2*y
even(x) == x == 2*(x / 2)

nat(x,y) = x == ToReal(y)
nat(x) = x == ToReal(ToNat(x))


# the quotient construction using sets
mod3 = define("qset", [x], Lambda([y], x % 3 == y % 3) 

# it's cute in a way, but lots of extra junk for no reason.

def quotient(eq):
    kd.lemma(trans(eq), sym(eq), refl(eq))
    inj = define("qset", [x], Lambda([y], eq(x,y)))
    proj = define("choice, [s], )
    axiom(Implies(choice(s) == x, s[x]))



I didn't equate x == y, so maybe this is justified?
Well, I'm working in domains that have an a priori equality relation.
Syntax -> semantics.
Or sem0 -> sem1 -> sem2 -> ... stratification

"dymamic" stratification
sem = ArraySort(IntSort(), Syntax , S)
or
a = ArraySort(IntSort, S)
b = ArraySort(Int, S)
c = 

Distinct(a[0], b[0], c[0])
ForAll([n], (a[n+1] == b[n+1]) == (a[n] == b[n] | prim_eq(a[n], c[n]) & c[n] == b[n])
f : (N -> S) -> (N -> S)
ForAll([n, a ,b], f(a)[n+1] == f(b)[n+1]) == ( f(a)[n] == f(b)[n] | 
                                               prim_eq(f(a), f(b)) |
                                               a[n] == b[n] )

prim_eq() 



sem[0]
 == n+1
or infinite stream if you have it. An egraph should stabilize into repetition.




```

# Inductive Relations

# Option / Parametric

```python
def Option(T : SortRef) -> SortRef:
    OT = Datatype(f"Option<{}>")
    OT.declare("some", ("val", T))
    OT.declare("none")
    OT = OT.create()
    def bind(o, f):
        return If(OT.is_none(o), OT.none, f(o))
    OT.bind = bind
    #bind = kd.define("bind", [o,f], If(OT.is_none(o), OT.none, f(o)))
    # support super goofy algebraic effects style.
    def run(gen):
        g = iter(gen)
        g.step(If(OT.is_none(o), OT.none, f(o)))
    OT.run

    return OT




```

# MultiSolver

Make solver objects. Mock z3 interface

monkey patch for pytest
kd.kernel.lemma = lambda *args, **kwargs: kd.kernel.lemma(kwargs["solver"]=VampireSolver)
kd.lemma =

```python
import z3
import knuckledragger as kd
class BaseSolver():
    def __init__(self):
        self.adds = []
        self.options = {}
    def add(self, thm):
        pass
    def assert_and_track(self, thm, name):
        pass
    def check(self):
        pass
    def unsat_core(self):
        pass
    def set(self, option, value):
        self.options[option] = value


import tempfile
import subprocess
class VampireSolver(BaseSolver):
    def __init__(self):
        super().__init__()
    def check(self):
        with open("/tmp/vampire.smt2", "w") as fp: #tempfile.NamedTemporaryFile() 
            fp.write(b";;declarations\n")
            for fp in kd.kernel.defns.keys():
                assert isinstance(f, z3.FuncDeclRef)
                fp.write(f.sexpr())
                fp.write("\n")
            fp.write(b";;axioms\n")
            for e in self.adds:
                fp.write("(assert " + e.thm.sexpr() + ")\n")
            fp.write(b"(check-sat)\n")
            fp.flush()
            #print(fp.readlines())
            res = subprocess.run(["vampire", fp.name, "--mode", "smtcomp","--input_syntax", "smtlib2", "-t", 
            str(self.options["timeout"]) +"d", "--output_mode", "smtcomp"], stdout=subprocess.PIPE).stdout
        if res == "unsat":
            return z3.unsat
        elif res == "sat":
            return z3.sat
        else:
            print(res)
            return z3.unknown
    def unsat_core(self):
        return self.solver.unsat_core()


s = VampireSolver()
s.add(z3.RealVal(1) == z3.RealVal(1))
s.set("timeout", 1000)
s.check()

```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[25], line 53
         51 s.add(z3.RealVal(1) == z3.RealVal(1))
         52 s.set("timeout", 1000)
    ---> 53 s.check()


    Cell In[25], line 26, in VampireSolver.check(self)
         24 def check(self):
         25     with open("/tmp/vampire.smt2", "w") as fp: #tempfile.NamedTemporaryFile() 
    ---> 26         fp.write(b";;declarations\n")
         27         for fp in kd.kernel.defns.keys():
         28             assert isinstance(f, z3.FuncDeclRef)


    TypeError: write() argument must be str, not bytes

```python
class Z3Solver(z3.Solver):
    pass
class VampireSolver():
    def __init__(self):
        self.asserts = []
        self.options = []
    def set_option(self, name, value):
        if name == "timeout":


    def add(self, thm):
        self.asserts.append(thm)
    def check(self):
        # export smt, make tmp, call vampire, return
        return z3.unknown 
    def assert_and_check(self, thm, name): #?
        assert False
    def get_model():
    def get_proof(self):


class SMTSolver():
class THFSolver():
class CVC5Solver(SMTSolver):
    pass
class TweeSolver(THFSolver):
    pass

def sledge():
    threading
    all_lemmas + defns
    for solver in [Z3Solver, TweeSolver, CVC5Solver]:
        lemma(thm, by=by, solver=solver)

def lemma(thm, by=[], solver=Z3Solver, get_proof=False, timeout=1000):
    s = solver()
    s.set_option("timeout", )
```
