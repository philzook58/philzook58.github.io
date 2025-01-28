---
date: 2025-01-20
title: "More Knuckledragger: Simp, Inductive Relations, Sympy NbE, and Software Foundations"
---

I've been hard at work plugging away at [Knuckledragger](https://github.com/philzook58/knuckledragger), my low barrier proof assistant.

Try it out! <http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb>

Look at my cute docs! <https://www.philipzucker.com/knuckledragger/>

It is an LCF style theorem prover using Z3py directly as it's core, enabling basically seamless interoperation with any other usage of z3py. I am really convinced this is a nice design I haven't seen before that gets me an insane amount for free.

Having a ball! I don't think I've been this intense and in flow for a while. Adding a tactics system really unleashed me <https://www.philipzucker.com/knuckle_lemma/>

There's a pile of new features and even more ideas coming, so it's good to discuss them in a blog post.

- simp and unfold
- inductive relations
- eval, reify and nbe
- Translating software foundations
- GenericProof

And away we go!

# simp and unfold

One of the points of knuckledragger is holding back theorems from z3 in order to guide it. But this is also annoying because now it is my job to find those theorems.

Z3 supplies a very nice simplify routine. But it can't simplify through user definitions.

User definitions are registered via `kd.define` and stored in the kernel. Unfold can access these and unfold them once. It also produces an optional proof trace. The unfolding should follow obviously via using this trace.

```python
from kdrag.all import *
def unfold(e: smt.ExprRef, decls=None, trace=None) -> smt.ExprRef:
    """
    Do a single unfold sweep, unfolding definitions defined by `kd.define`.
    The optional trace parameter will record proof along the way.
    `decls` is an optional list of declarations to unfold. If None, all definitions are unfolded.

    >>> x = smt.Int("x")
    >>> f = kd.define("f", [x], x + 42)
    >>> trace = []
    >>> unfold(f(1), trace=trace)
    1 + 42
    >>> trace
    [|- f(1) == 1 + 42]
    """
    if smt.is_app(e):
        decl = e.decl()
        children = [unfold(c, decls=decls, trace=trace) for c in e.children()]
        defn = kd.kernel.defns.get(decl)
        if defn is not None and (decls is None or decl in decls):
            e1 = smt.substitute(defn.body, *zip(defn.args, children))
            e = e1
            if trace is not None:
                if isinstance(defn.ax, smt.QuantifierRef):
                    trace.append((defn.ax(*children)))
                else:
                    trace.append(defn.ax)
            return e1
        else:
            return decl(*children)
    else:
        return e
```

```python
from kdrag.all import *
foo = kd.define("foo", [], smt.IntVal(42) + smt.IntVal(8))
trace = []
kd.rewrite.unfold(foo, trace=trace)
```

42 + 8

```python
trace
```

    [|- foo == 42 + 8]

Interleaving unfolding and z3's simplify should be able to evaluate for concrete arguments. This is not the final form of this, I can see there needs to be something smart to decided when to stop if the argument is not concrete.

```python
def simp(e: smt.ExprRef, trace=None, max_iter=None) -> smt.ExprRef:
    """
    Simplify using definitions and built in z3 simplifier until no progress is made.

    >>> import kdrag.theories.nat as nat
    >>> simp(nat.one + nat.one + nat.S(nat.one))
    S(S(S(S(Z))))

    >>> p = smt.Bool("p")
    >>> simp(smt.If(p, 42, 3))
    If(p, 42, 3)
    """
    i = 0
    while True:
        i += 1
        if max_iter is not None and i > max_iter:
            return e
        e = unfold(e, trace=trace)
        # TODO: Interesting options: som, sort_store, elim_ite, flat, split_concat_eq, sort_sums, sort_disjunctions
        e1 = smt.simplify(e)
        if e1.eq(e):
            return e1
        else:
            if trace is not None:
                trace.append(kd.kernel.lemma(e1 == e))
            e = e1
```

```python
trace = []
kd.simp(foo,trace=trace)
```

50

```python
trace
```

    [|- foo == 42 + 8, |- 42 + 8 == 50]

I was experimenting with RecFunction, which kind of let's z3 do the unfolding for you, but it infects the context and translating contexts was getting super fishy. So I'm happier with this design for the moment. It wasn't much code!

I should also enable registering theorems as rewrite rules, but I haven't go a system for that yet. I do have basic pattern matching / rewriting facilities though.

# Inductive Relations

In this post <https://www.philipzucker.com/minikanren_inside_z3/> I discussed how to encode prolog or minikanren programs into z3. There is a "leastness" to the intent of these definitions that you can encode using the "leastness" of the fixed point of algebraic datatypes.

I don't have dependent datatypes, becausre z3/smtlib2 do not directly support them.

But neither does Isabelle, and it does have an inductive relation facility. Inductive relations != dependent types. Dependent types are just one way of achieving the informal concept.

Basically you need to define a witness/trace datatype alongside a relation that confirms the witness is valid.

- The witness of inductive relation of evenness is the div2 divisor basically. `even(x) = exists y. x = 2 * y` or in open witness carrying form `even(wit, x) == Or(And(wit == 0, x == 0), And(even(wit.pred, x - 2)))`
- The witness of inductive relation describing operational semantics is a trace of execution (a list of labelled moves).
- And so on.

Note that you can do this transformation in lean or coq also, translating the dependent version of the inductive relation into a non dependent witness datatype and a function to `Prop` defined recursively over the witness.

There are probably examples that you can't factor out into a simple witness type and predicate, but I haven't gotten that far yet. We'll deal with it when we get to it.

So you can write this as a idiom in Knuckledragger, but it is burdensome and makes for annoying translation barrier from other system's tutorials.

I also wanted to nestle it nicely into Z3's existing pattern of datatype generation. Part of what makes it annoying is that you want to write it as if you are defining a witness datatype at the same time as defining a verifying relation, even though really the witness datatype is defined first.

Here's an example. It's a work in progress. I borrow the meta lambda to bind the parameters of the witness

```python
from kdrag.all import *
x = smt.Int("x")
Even = kd.InductiveRel("Even", x) # x is a parameter of the relation
Even.declare("Z",                           pred = x == 0)
Even.declare("SS", ("sub2_evidence", Even), pred = lambda sub2: sub2.rel(x-2))
Even = Even.create()
wit = smt.Const("ev", Even)
wit.rel(4)

```

even(ev, 4)

```python
kd.simp(Even.SS(Even.SS(Even.Z)).rel(4))
```

True

```python
kd.simp(Even.SS(Even.Z).rel(4))
```

False

# Eval_ and NbE

A natural thing to want is to interpret z3 expressions to python values. If I prove something about some z3 expression, maybe I want to actually extract it.
But also this is useful for evaluating z3 terms into domain specific libraries such as sympy.

Python has an `eval` function

```python
eval("1 + 1")
```

    2

And sympy has `sympify`  (a reify of strings and python objects into sympy) and `lambdify` (which is an eval from sympy terms to python).

```python
import sympy
from sympy.abc import x
sympy.sympify("1 + x")
```

$\displaystyle x + 1$

```python
sympy.lambdify(x, 1 + x)(smt.Int("z"))
```

z + 1

Well, one can build basically the same thing.

- operators sent into the overloadable pytohn equivalents
- `Lambda` becomes a python lambda, although I think I should make a custom `Closure` type.
- Rational reals are `fractions.Fraction` values.
- I chose to interpret z3 datatypes as namedtuples with the same name as the constructor and field names.

And a sort directed `reify` function

```python
from kdrag.all import *
import kdrag.theories.nat as nat
e0 = nat.Z + nat.S(nat.Z)
e0
```

add(Z, S(Z))

```python
e = kd.utils.eval_(e0)
e
```

    S(pred=Z())

```python
kd.utils.reify(nat.Nat, e)
```

S(Z)

Combining them we get a normalization routine <https://en.wikipedia.org/wiki/Normalisation_by_evaluation> . Because it goes through the metalayer though, I'm not sure how we could trace it. And the whole apparatus is a bit complicated to cover all the corner cases, so I don't think I can put this in the kernel.

I find this a very interesting perspective on normalization by evaluation, probably close-ish to the original Lisp version.

Some interesting aspects

- python is object oriented and the operators are late bound. We get lot's of interpretations for free by this
- When `value` is just another datatype in your language, operating kind of at the same level as `term`, it's a bit harder to see the distinction. My `value` is `python.object` and my `term` is `z3.ExprRef` which are wildly different. I find this to happen a lot that making things further apart makes it easier for me to ditinguish them. While having your object language and meta language be similar looking saves a lot of effort, it also makes it order to parse when you're in one vs the other if an author isn't super fastidious.

```python
def nbe(x):
    return kd.utils.reify(x.sort(), kd.utils.eval_(x))
nbe(e0)
```

S(Z)

Higher order functions or stuck terms are a lot fishier. I don't understand NbE well enough. I'm following my nose. It is interesting that z3 terms rae themselves python objects, so we can interpret into itself.

Currently, I choose to just fail.

```python
#kd.utils.eval_(smt.Int("x"))
```

You can add a binding to the context though

```python
kd.utils.eval_(smt.Int("x"), {"x": 42})
```

    42

We can also use this to interpret z3 expressions into sympy ones

```python
import sympy
import sympy.abc
x = smt.Int("x")
kd.utils.eval_(1 + x, {**sympy.__dict__, **sympy.abc.__dict__})
```

$\displaystyle x + 1$

```python
import kdrag.theories.real as real
def sympy_nbe(vs, e, globals={}):
    env = {**sympy.__dict__, **sympy.abc.__dict__, **globals}
    sympy_e = kd.utils.eval_(e, env)
    return sympy.lambdify([v.decl().name() for v in vs], sympy_e.simplify(), modules=[real])(*vs)
x = smt.Real("x")
sympy_nbe([x], 1 + 2 + real.sin(x)**2 + real.cos(x)**2)
```

    Admitting lemma ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x) >= 0))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x)**2 == x))


    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(sqr(x)) == x))





    4

Again, I don't even know how to get breadcrumbs out of sympy. So there is not proof object that `1 + 2 + sin(x)**2 + cos(x)**2 == 4`

One could choose to just admit this, build some tactics to try and do this sort of thing, or take it as a new proof obligation in a `Lemma` context.

I'm intrigued at using this technique <https://www.philipzucker.com/overload_bool/> to reify through control flow

More food for thought

- Sam Lindley's slides <https://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf>
- <https://williamjbowman.com/tmp/nbe-four-ways/>

# Software Foundations and Other Tutorials

A good thing to grind on is just translating other systems tutorials into knuckledragger to make sure I'm tutorial complete. I have found features missing and many bugs. I haven't yet run into a kernel bug though, which is nice (I'm sure they are there. I'm also programming the happy path).

I think once I'm confident you can do software foundations V1 and V2 I'll cut some kind of Knuckledragger release.

On the downside, the more I do this, the more knuckledragger loses some uniqueness as it is glomming on features that already exist.

It is however super important to keep actually trying to use knuckledragger, or any project one is writing. Inventing and proving new formulations of theories while also building the proof assistant is a lot to chew on, so I'm glad I have a pile of lazy already done theorems to copy. Like here <https://www.philipzucker.com/cody_sheffer/> .

I'm also looking at the lean and isabelle tutorials.

It's all going into the CI, but I'm not really cleaning up the text. Eventually, I'll write a more thorough custom tutorial for knuckledragger.

### Basics

```python
import kdrag as kd
from kdrag import smt

"""
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
"""

day = kd.Enum("day", "monday tuesday wednesday thursday friday saturday sunday")

d = smt.Const("d", day)
next_weekday = kd.define("next_weekday", [d], kd.cond(
    (d.is_monday, day.tuesday),
    (d.is_tuesday, day.wednesday),
    (d.is_wednesday, day.thursday),
    (d.is_thursday, day.friday),
    (d.is_friday, day.monday),
    (d.is_saturday, day.monday),
    (d.is_sunday, day.monday),
))
```

```python
""" Compute (next_weekday friday). """
kd.simp(next_weekday(day.friday))


# In[4]:


""" Compute (next_weekday (next_weekday saturday)). """
kd.simp(next_weekday(next_weekday(day.saturday)))


```

tuesday

```python
"""
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
"""
l = kd.Lemma(next_weekday(next_weekday(day.saturday)) == day.tuesday)
"""Proof. simpl. reflexivity.  Qed."""
l.auto(by=next_weekday.defn)
l.qed()
```

&#8870;next_weekday(next_weekday(saturday)) == tuesday

```python
bool = kd.Enum("bool", "true false")

b, b1, b2 = smt.Consts("b b1 b2", bool)


negb = kd.define("negb", [b], kd.cond(
    (b.is_true, bool.false),
    (b.is_false, bool.true),
))
andb = kd.define("andb", [b1, b2], kd.cond(
    (b1.is_true, b2),
    (b1.is_false, bool.false),
))
orb = kd.define("orb", [b1, b2], kd.cond(
    (b1.is_true, bool.true),
    (b1.is_false, b2),
))

negb1 = kd.define("negb1", [b], 
b.match_(
  (bool.true, bool.false),
  (bool.false, bool.true),
))

kd.lemma(smt.ForAll([b], negb(b) == negb1(b)), by=[negb1.defn, negb.defn])

kd.lemma(orb(bool.true, bool.false) == bool.true, by=orb.defn)
kd.lemma(orb(bool.false, bool.false) == bool.false, by=orb.defn)
kd.lemma(orb(bool.false, bool.true) == bool.true, by=orb.defn)
kd.lemma(orb(bool.true, bool.true) == bool.true, by=orb.defn)
```

&#8870;orb(true, true) == true

```python


"""
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
"""
kd.notation.or_.register(bool, orb)
kd.notation.and_.register(bool, andb)

"""
Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.
"""
kd.lemma(bool.false | bool.false | bool.true == bool.true, by=orb.defn)

```

&#8870;orb(orb(false, false), true) == true

```python
rgb = kd.Enum("rgb", "red green blue")
color = kd.Inductive("color")
color.declare("black")
color.declare("white")
color.declare("primary", ("p", rgb))
color = color.create()

c = smt.Const("c", color)
p = smt.Const("p", rgb)
monochome = kd.define("monochrome", [c],
                      c.match_(
                          (color.black, bool.true),
                          (color.white, bool.true),
                          (color.primary(p), bool.false)
                        )
                      )

isred = kd.define("isred", [c],
                      c.match_(
                          (color.primary(rgb.red), bool.true),
                        default=bool.false)
                      )
isred.defn
```

&#8870;ForAll(c,
       isred(c) ==
       If(And(is(primary, c), is(red, p(c))), true, false))

```python
bit = kd.Enum("bit", "B1 B0")
nybble = kd.Record("nybble", ("b0", bit), ("b1", bit), ("b2", bit), ("b3", bit))

nybble(
    b0=bit.B0,
    b1=bit.B1,
    b2=bit.B0,
    b3=bit.B1
)

```

nybble(B0, B1, B0, B1)

```python


Nat = kd.Inductive("Nat")
Nat.declare("O")
Nat.declare("S", ("n", Nat))
Nat = Nat.create()

otherNat = kd.Inductive("otherNat")
otherNat.declare("O")
otherNat.declare("S", ("n", otherNat))
otherNat = otherNat.create()

n = smt.Const("n", Nat)
pred = kd.define("pred", [n], n.match_(  
    (Nat.O, Nat.O),
    (Nat.S(n), n)
))
pred.defn

```

&#8870;ForAll(n,
       pred(n) ==
       If(is(O, n), O, If(is(S, n), n(n), unreachable!321)))

### Lists

```python
# Inductive natprod : Type :=
#   | pair (n1 n2 : nat).
# 
# (** This declaration can be read: "The one and only way to
#     construct a pair of numbers is by applying the constructor [pair]
#     to two arguments of type [nat]." *)
# 
# Check (pair 3 5) : natprod.
# 
# (** Functions for extracting the first and second components of a pair
#     can then be defined by pattern matching. *)
# 
# Definition fst (p : natprod) : nat :=
#   match p with
#   | pair x y => x
#   end.
# 
# Definition snd (p : natprod) : nat :=
#   match p with
#   | pair x y => y
#   end.
# 
# Compute (fst (pair 3 5)).
# (* ===> 3 *)
# 
# 

# In[2]:


import kdrag as kd
from kdrag import smt
import kdrag.theories.nat as nat
NatProd = kd.Record("NatProd", ("n1", nat.Nat), ("n2", nat.Nat))

q = NatProd(nat.from_int(3),nat.from_int(5))
print(q.sort())

n,m,k = smt.Consts("n m k", nat.Nat)
p = smt.Const("p", NatProd)
fst = kd.define("fst", [p], p.n1)
snd = kd.define("snd", [p], p.n2)

kd.simp(fst(q))
kd.simp(snd(q))

kd.utils.eval_(fst(q))
kd.utils.eval_(snd(q))

```

    NatProd





    S(pred=S(pred=S(pred=S(pred=S(pred=Z())))))

```python
# 
# (** **** Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
# Theorem fst_swap_is_snd : forall (p : natprod),
#   fst (swap_pair p) = snd p.
# Proof.
#   (* FILL IN HERE *) Admitted.
# (** [] *)

# In[4]:


swap_pair = kd.define("swap_pair", [p], NatProd(p.n2, p.n1))

nat_prod_surj = kd.lemma(smt.ForAll([n, m], swap_pair(NatProd(n, m)) == NatProd(m, n)), by=swap_pair.defn)


```

```python
NatList = kd.Inductive("NatList")
NatList.declare("Nil")
NatList.declare("Cons", ("head", nat.Nat), ("tail", NatList))
NatList = NatList.create()

def natlist(*args):
    if len(args) == 0:
        return NatList.Nil
    else:
        return NatList.Cons(args[0], natlist(*args[1:]))

natlist(nat.from_int(1), nat.from_int(2), nat.from_int(3))

```

Cons(from_int(1), Cons(from_int(2), Cons(from_int(3), Nil)))

```python
n,count = smt.Consts("n count", nat.Nat)
repeat = smt.Function("repeat", nat.Nat, nat.Nat, NatList)
kd.define("repeat", [n,count], smt.If(count.is_Z, NatList.Nil, NatList.Cons(n, repeat(n, count.pred))))

length = smt.Function("length", NatList, nat.Nat)
l = smt.Const("l", NatList)
kd.define("length", [l], smt.If(l.is_Nil, nat.Nat.Z, nat.Nat.S(length(l.tail))))

append = smt.Function("append", NatList, NatList, NatList)
l1,l2 = smt.Consts("l1 l2", NatList)
kd.define("append", [l1,l2], smt.If(l1.is_Nil, l2, NatList.Cons(l1.head, append(l1.tail, l2))))

kd.notation.add.register(NatList, append)

x = list(nat.from_int(i) for i in range(1,10))
kd.lemma(natlist(x[0], x[1], x[2]) + natlist(x[4], x[5]) == natlist(x[0], x[1], x[2], x[4], x[5]), by=append.defn)
kd.lemma(NatList.Nil + natlist(x[4], x[5]) == natlist(x[4], x[5]), by=append.defn)
kd.lemma(natlist(x[0], x[1], x[2]) + NatList.Nil == natlist(x[0], x[1], x[2]), by=append.defn)

```

&#8870;append(Cons(from_int(1),
            Cons(from_int(2), Cons(from_int(3), Nil))),
       Nil) ==
Cons(from_int(1), Cons(from_int(2), Cons(from_int(3), Nil)))

```python
head = kd.define("head", [l, n], smt.If(l.is_Nil, n, l.head))
tail = kd.define("tail", [l], smt.If(l.is_Nil, NatList.Nil, l.tail))

"""
Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.
"""
l = natlist(x[0], x[1], x[2])
kd.lemma(head(l , nat.Nat.Z) == x[0], by=head.defn)
kd.lemma(head(NatList.Nil, nat.Nat.Z) == nat.Nat.Z, by=head.defn)
kd.lemma(tail(l) == natlist(x[1], x[2]), by=tail.defn)


```

&#8870;tail(Cons(from_int(1),
          Cons(from_int(2), Cons(from_int(3), Nil)))) ==
Cons(from_int(2), Cons(from_int(3), Nil))

```python
# Theorem tl_length_pred : forall l:natlist,
#   pred (length l) = length (tl l).
# Proof.
#   intros l. destruct l as [| n l'].
#   - (* l = nil *)
#     reflexivity.
#   - (* l = cons n l' *)
#     reflexivity.  Qed.

# In[8]:


l = smt.Const("l", NatList)
nil_app = kd.lemma(smt.ForAll([l], append(NatList.Nil, l) == l), by=append.defn)


l = kd.Lemma(smt.ForAll([l], nat.safe_pred(length(l)) == length(tail(l))))
_l = l.fix()
l.cases(_l)
print(l.goals)
l.auto(by=[length.defn, tail.defn, nat.safe_pred.defn])
l.auto(by=[length.defn, tail.defn, nat.safe_pred.defn])


```

    [[l!465];
    [is(Cons, l!465) == True] ?|- safe_pred(length(l!465)) == length(tail(l!465)), [l!465];
    [is(Nil, l!465) == True] ?|- safe_pred(length(l!465)) == length(tail(l!465))]





    Nothing to do!

```python
#     eventually reaching [nil], these two arguments together establish
#     the truth of [P] for all lists [l].
# 
#     Here's a concrete example: *)
# 
# Theorem app_assoc : forall l1 l2 l3 : natlist,
#   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
# Proof.
#   intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
#   - (* l1 = nil *)
#     reflexivity.
#   - (* l1 = cons n l1' *)
#     simpl. rewrite -> IHl1'. reflexivity.  Qed.

# In[9]:


l1,l2,l3 = smt.Consts("l1 l2 l3", NatList)
l = kd.Lemma(smt.ForAll([l1,l2,l3], (l1 + l2) + l3 == l1 + (l2 + l3)))
_l1, _l2, _l3 = l.fixes()
l.induct(_l1)
#l.goals[-1]
#l.auto(by=append.defn)
l.unfold(append)
l.simp()
l.auto()

_tail = l.fix()
l.intros()
_head = l.fix()
l.unfold(append)
l.simp()
l.auto(by=[append.defn])
l.qed()
#l.unfold(append)
#l.auto(by=append.defn(NatList.Nil, _l2))
#l.auto(by=[append.defn(NatList.Nil, _l2), append.defn(NatList.Nil, _l2 + _l3)])
#l.auto(by=[append.defn])
#l.qed()


```

&#8870;ForAll([l1, l2, l3],
       append(append(l1, l2), l3) ==
       append(l1, append(l2, l3)))

```python
# (* ----------------------------------------------------------------- *)
# ## Reversing a List 
# 
# (** For a slightly more involved example of inductive proof over
#     lists, suppose we use [app] to define a list-reversing function
#     [rev]: *)
# 
# Fixpoint rev (l:natlist) : natlist :=
#   match l with
#   | nil    => nil
#   | h :: t => rev t ++ [h]
#   end.
# 
# Example test_rev1:            rev [1;2;3] = [3;2;1].
# Proof. reflexivity.  Qed.
# Example test_rev2:            rev nil = nil.
# Proof. reflexivity.  Qed.

# In[10]:


rev = smt.Function("rev", NatList, NatList)
l = smt.Const("l", NatList) 
rev = kd.define("rev", [l], smt.If(l.is_Nil, NatList.Nil, rev(l.tail) + natlist(l.head)))



append_Nil = kd.lemma(smt.ForAll([l], append(NatList.Nil, l) == l), by=append.defn)
append_Cons = kd.lemma(smt.ForAll([l1,l2, n], NatList.Cons(n,l1) + l2 == NatList.Cons(n, l1 + l2)), by=append.defn)

#rev_Nil = kd.lemma(rev(NatList.Nil) == NatList.Nil, by=rev.defn) # This doesn't work? What? Ematching failure. I see. No. Do I see?
rev_Nil = kd.lemma(rev(NatList.Nil) == NatList.Nil, by=rev.defn(NatList.Nil))
rev_Cons = kd.lemma(smt.ForAll([l,n], rev(NatList.Cons(n,l)) == rev(l) + natlist(n)), by=rev.defn) 

kd.lemma(rev(natlist(x[0], x[1], x[2])) == natlist(x[2], x[1], x[0]), by=[append_Nil, append_Cons, rev_Cons, rev_Nil])

# This should be less painful
l = kd.Lemma(rev(natlist(x[0], x[1], x[2])) == natlist(x[2], x[1], x[0]))
for i in range(4):
    l.unfold(rev,append)
    l.simp()
l.qed()

#l.rw(append_Cons)
#l.simp()
#print(l)
#l.auto(by=[append_Nil, append_Cons])
#l.auto()
#l
#l.qed()

#kd.lemma(rev(NatList.Nil) == NatList.Nil, by=rev.defn(NatList.Nil))


```

&#8870;rev(Cons(from_int(1),
         Cons(from_int(2), Cons(from_int(3), Nil)))) ==
Cons(from_int(3), Cons(from_int(2), Cons(from_int(1), Nil)))

```python
# (** For something a bit more challenging, let's prove that
#     reversing a list does not change its length.  Our first attempt
#     gets stuck in the successor case... *)
# 
# Theorem rev_length_firsttry : forall l : natlist,
#   length (rev l) = length l.
# Proof.
#   intros l. induction l as [| n l' IHl'].
#   - (* l = nil *)
#     reflexivity.
#   - (* l = n :: l' *)
#     (* This is the tricky case.  Let's begin as usual
#        by simplifying. *)
#     simpl.
#     (* Now we seem to be stuck: the goal is an equality
#        involving [++], but we don't have any useful equations
#        in either the immediate context or in the global
#        environment!  We can make a little progress by using
#        the IH to rewrite the goal... *)
#     rewrite <- IHl'.
#     (* ... but now we can't go any further. *)
# Abort.
# 
# (** So let's take the equation relating [++] and [length] that
#     would have enabled us to make progress at the point where we got
#     stuck and state it as a separate lemma. *)
# 
# Theorem app_length : forall l1 l2 : natlist,
#   length (l1 ++ l2) = (length l1) + (length l2).
# Proof.
#   (* WORKED IN CLASS *)
#   intros l1 l2. induction l1 as [| n l1' IHl1'].
#   - (* l1 = nil *)
#     reflexivity.
#   - (* l1 = cons *)
#     simpl. rewrite -> IHl1'. reflexivity.  Qed.

# In[11]:

l1 = smt.Const("l1", NatList)
length_Cons = kd.lemma(smt.ForAll([l1,n], length(NatList.Cons(n,l1)) == nat.Nat.S(length(l1))), by=length.defn)
length_Nil = kd.lemma(length(NatList.Nil) == nat.Nat.Z, by=length.defn(NatList.Nil))

l = kd.Lemma(smt.ForAll([l1,l2], length(l1 + l2) == length(l1) + length(l2)))
_l1, _l2 = l.fixes()
l.induct(_l1)
l.rw(length.defn(NatList.Nil))
l.simp()
#l.auto(by=[length.defn, append.defn, nat.add.defn]) # TODO: unstable
l.auto(by=[append_Nil, nat.add_Z])
_tl = l.fix()
l.intros()
_hd = l.fix()
l.rw(append_Cons)
l.rw(length_Cons)
l.rw(length_Cons)
l.auto(by=[nat.add.defn])
app_length = l.qed()
#l.unfold(nat.add)
#l.unfold(length)
app_length

```

&#8870;ForAll([l1, l2],
       length(append(l1, l2)) == add(length(l1), length(l2)))

# Generic Proof

Smtlib and Z3 (or basic multi sorted first order logic) have basically no parametric or generic types. This is kind of a problem when you want to copy things othert systems are doing. I'm not so sure it's that much of a problem if you are starting from scratch, working to the strengths and weaknesses of knuckledragger. Being generic is a sickness.

In any case, one panacea is to get a weaker external notion of generic in the metasystem, ie. python.

An extremely preliminary idea is `GenericProof`. This is basically a dicitonary keyed on anything (sorts, funcdecls, terms, tuples of these, whatever), with the caveat that when you register something to it

1. it checks it is a proof
2. it checks that the theorem of the proof matches the defined schema.

This is similar in some ways to `SortDispatch` which knuckledragger uses to overload on z3 sorts in a manner similar to python's singledispatch. The intent there was that SortDispatch returns a z3 term (and inspects the sort of the first argument to decide which one), but GenericProof returns a proof object.

GenericProof plays a role similar to modules or typeclasses.

You are welcome to bundle together GenericProof as members of a python class, like `Group`.

```python
class GenericProof:
    """
    GenericProof is a dictionary of proofs indexed on meta (python) information.

    Because z3 and hence knuckledragger does not have strong generic support inside its logic,
    we can borrow a bit of python to parametrize theorems over other data or over sorts.

    This has some of the flavor of single dispatch.

    It is similar to an axiom schema is some respects (in usage it takes in python data and outputs a `kd.Proof`) except that one must register
    the theorems as proven by other means.

    It is a way to refer to a collection of similar proofs akin to single entry typeclasses or modules in other theorem proving systems.

    >>> x = lambda T: smt.Const("x", T)
    >>> obvious = GenericProof(lambda T: smt.ForAll([x(T)], x(T) == x(T)) )
    >>> obvious.lemma(smt.IntSort(), by=[])
    >>> R = smt.RealSort()
    >>> obvious.register(R, kd.lemma(smt.ForAll([x(R)], x(R) == x(R))))
    """

    def __init__(self, f):
        self.wrapped = f
        self.data = {}

    def __call__(self, *args) -> kd.Proof:
        return self.data[args]

    def __getitem__(self, *args) -> kd.Proof:
        return self.data[args]

    def get(self, *args) -> Optional[kd.Proof]:
        return self.data.get(args)

    def lemma(self, *args, **kwargs):
        return self.register(*args, kd.kernel.lemma(self.wrapped(*args), **kwargs))

    def register(self, *args):
        args, pf = args[:-1], args[-1]
        if not kd.kernel.is_proof(pf):
            raise ValueError("Not a proof", pf)
        formula = self.wrapped(*args)
        if not kd.utils.alpha_eq(formula, pf.thm):
            raise ValueError("Proof does not match", formula, pf)
        self.data[args] = pf


@GenericProof
def assoc(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y, z = smt.Consts("x y z", T)
    return kd.QForAll([x, y, z], f(x, f(y, z)) == f(f(x, y), z))


@GenericProof
def comm(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y = smt.Consts("x y", T)
    return kd.QForAll([x, y], f(x, y) == f(y, x))


@GenericProof
def idem(f: smt.FuncDeclRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, x) == x)


@GenericProof
def runit(f: smt.FuncDeclRef, e: smt.ExprRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, e) == x)


@GenericProof
def inv(f: smt.FuncDeclRef, inv: smt.FuncDeclRef, e: smt.ExprRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, inv(x)) == e)


@GenericProof
def symm(R: smt.FuncDeclRef):
    x, y = smt.Consts("x y", R.domain(0))
    return kd.QForAll([x, y], R(x, y) == R(y, x))


@GenericProof
def trans(R: smt.FuncDeclRef):
    x, y, z = smt.Consts("x y z", R.domain(0))
    return kd.QForAll([x, y, z], R(x, y), R(y, z), R(x, z))
```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[38], line 1
    ----> 1 class GenericProof:
          2     """
          3     GenericProof is a dictionary of proofs indexed on meta (python) information.
          4 
       (...)
         19     >>> obvious.register(R, kd.lemma(smt.ForAll([x(R)], x(R) == x(R))))
         20     """
         22     def __init__(self, f):


    Cell In[38], line 32, in GenericProof()
         29 def __getitem__(self, *args) -> kd.Proof:
         30     return self.data[args]
    ---> 32 def get(self, *args) -> Optional[kd.Proof]:
         33     return self.data.get(args)
         35 def lemma(self, *args, **kwargs):


    NameError: name 'Optional' is not defined

# Bits and Bobbles

I've also been professionaliziong the repo a bit. pyright and ruff now run. Kind of a fun whackamole. Given python is so chaotic, I really ought to be using all the tools I can get. The doctests are really nice and make for good documentation too. Giving uv a spin. Seems nice so far

- How to get angr semantics. What meaning could they have?
- need lemma search. Can introspect to grab all Proof in module. Do pmatch over them
- LLM integration
- hypothesis integration. Super useful. I hope to derive a nitpick from this + `eval_`. Useful for testing axioms against reality also. Good for my general infrastuructre
- careful proof reconstruction instead of slamm z3
- monad support. Is it really needed? Single shot Algebraic effects using generators
- partiality. Relational vs option vs undefined style.
- Talking to and from
- floats. I really want floats to work.
- a cbv and cbn tactic might be nice. More controlled.
