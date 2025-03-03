---
title: Generics and Typeclasses in Knuckledragger
date: 2025-03-03
tag: knuckledragger
---

Some things that I've punted on for a while are overloading, typeclasses and algebraic hierarchies in [knuckledragger](https://github.com/philzook58/knuckledragger), my low barrier python proof assistant built around z3.

The proofs assistants I'm most familiar with have (multiple) mechanisms for some form of overloading and bundling of information.

One of the things I find the most interesting about building knuckledragger is playing with the distinction between metalayers. The two main layers are

- python programming ("compile time", static, meta)
- z3 expressions ("run time", dynamic, object)

For example, I can make a python dataclass to hold z3 expressions or I can make a z3 record datatype to hold them. It is typically easy to convert from the z3 level up to the python, but not so easy to convert from the python to z3. Conversely, the python layer is usually more ergonomic and familiar. It is kind of similar to things you can do generating C code from python or the [staged metaprogramming](https://okmij.org/ftp/meta-programming/index.html) game in general. As an example, you can have a meta `Forall` quantifier that unrolls a finite domain at "compile time" or you can let z3 handle it. This is akin to loop unrolling at compile time vs letting the C compiler handle it (probably better).

Here are some of the other layers. I don't think this is a linear ordering, maybe there are 2 or 3 axes in here.

- wacky python metaprogramming and metaclasses
- python types
- class definitions
- instances of classes
- regular python functions
- z3 sorts
- z3 expressions
- Proofs. A python object holding a z3 formula and recursively a subproof record of smt calls
- shallow embedding of logics inside z3 (direct semantic `and_` `or_` z3 funcdecls)
- deep embedding of logics inside z3 (make a z3 datatype with `And`, `Or`, etc constructors)

Part of the design game and confusion is which of these layers I want to associate with features in other systems. What pieces from which layer should I use to implement X feature from Lean? Copying features from dependent type systems clouds the waters, because they have punctured the metalayers in a particular way The very idea of putting values in types is a puncturing and also the idea of first class proof objects is a puncturing imo. To some extent, the whole game of foundations since Frege and Russell has been finding fun meta puncturings that retain soundness. [Quotation](https://arxiv.org/abs/1802.00405) or [modalities](https://plato.stanford.edu/entries/logic-provability/) are intriguing different forms of puncturing.

## SortDispatch

From very early on Knuckledragger has had SortDispatch, a variation on [functools.singledispatch](https://docs.python.org/3/library/functools.html#functools.singledispatch) for the purposes of overloading. I consider being in the standard library a stamp of idiomatic approval for the pattern.

The idea is simple enough. You can make a python object that you can register new supported types into, and has a `__call__` implementation that which lookups the python type / python sort of the first argument in the registry dictionary.

If we were collapsing the layer of z3 sorts and python types, which we aren't, one could use `functools.singledispatch` to dispatch on the type of the first argument. Instead we need to make a new dispatch that calls `registry[arg0.sort()]` rather than `registry[type(arg0)]` to figure out which function to call.

These registration dictionaries has developed as a common pattern. It is also what `functools.cache` is doing. Most of my mechanisms have something like this in them.

The first though on how to support operator overloading is to just make new clases. I don't think this works well because I don't want to associate z3 sorts with python classes.
Python supports operator overloading through implementing certain "dunder" methods like `__add__`. The most common and natural to achieve overloading is to make new classes or subclasses. But for the purposes of knuckledragger, I want overloading based on the `z3.SortRef` of the `z3.ExprRef`. One design choice could be to try an shallowly embed the z3 sorts into the python type system. You could do this my subclassing `ExprRef`, and this is what z3py itself does. However, I'd need to rewrap all z3 functionality to find the appropriate python class to subclass into. If I had the ability to change z3py maybe this is what I'd have done.
Another choice is to wrap z3py expressions as a data member in a another class. I think the shallow usage of z3py makes my life easier and is a valuable feature for users, so this is not great. Another choice might be to try and add a type parameter to `ExprRef[T]` where T is the z3 sort. Also weird and overwrought imo.

```python
# This code lives in kdrag.notation

class SortDispatch:
    """
    Sort dispatch is modeled after functools.singledispatch
    It allows for dispatching on the sort of the first argument

    >>> my_func = SortDispatch(name="my_func")
    >>> my_func.register(smt.IntSort(), lambda x: x + 1)
    >>> my_func.register(smt.BoolSort(), lambda x: smt.Not(x))
    >>> my_func(smt.IntVal(3))
    3 + 1
    >>> my_func(smt.BoolVal(True))
    Not(True)
    """

    def __init__(self, name=None, default=None):
        self.methods = {}
        self.default = default
        self.name = name

    def register(self, sort, func):
        self.methods[sort] = func

    def __getitem__(self, sort):
        return self.methods[sort]

    def __contains__(self, sort):
        return sort in self.methods

    def __call__(self, *args, **kwargs):
        if not args:
            raise TypeError("No arguments provided")
        sort = args[0].sort()
        res = self.methods.get(sort, self.default)
        if res is None:
            raise NotImplementedError(
                f"No implementation of {self.name} for sort {sort}. Register a definition via {self.name}.register({sort}, your_code)",
            )
        return res(*args, **kwargs)

    def define(self, args, body):
        """
        Shorthand to define a new function for this dispatch. Calls kdrag.define.
        """
        assert isinstance(self.name, str)
        defn = kd.define(self.name, args, body)
        self.register(args[0].sort(), defn)
        return defn


add = SortDispatch(name="add")
"""Sort based dispatch for `+` syntax"""
smt.ExprRef.__add__ = lambda x, y: add(x, y)  # type: ignore

# and so on...
```

# Dataclasses

I like dataclasses in python. It is a fairly low syntax way to defined structures and get some good default behavior. Dataclasses are a pretty decent way to cluster together properties. They give you capabilities that are similar to [modules](https://cs3110.github.io/textbook/chapters/modules/modules.html). A module system like OCaml's is a weak-ish functional language at the metalevel. "Functors" are are possibly higher order functions from modules to modules or functors to functors.

Python subclassing gives you something like an inclusion mechanism.

```python
from dataclasses import dataclass
from kdrag.all import *


@dataclass
class Semigroup:
    T: smt.SortRef
    f: smt.FuncDeclRef
    assoc: kd.Proof

    def __post_init__(self):
        x, y, z = smt.Consts("x y z", self.T)
        assert kd.utils.alpha_eq(
            self.assoc.thm,
            smt.ForAll([x, y, z], self.f(self.f(x, y), z) == self.f(x, self.f(y, z))),
        )


x, y, z = smt.Ints("x y z")
IntSemigroup = Semigroup(
    T=smt.IntSort(),
    f=(x * y).decl(),
    assoc=kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z))),
)


@dataclass
class Monoid(Semigroup):
    e: smt.ExprRef
    left_id: kd.Proof
    right_id: kd.Proof

    def __post_init__(self):
        super().__post_init__()
        x = smt.Const("x", self.T)
        assert kd.utils.alpha_eq(
            self.right_id.thm, smt.ForAll([x], self.f(x, self.e) == x)
        )
        assert kd.utils.alpha_eq(
            self.left_id.thm, smt.ForAll([x], self.f(self.e, x) == x)
        )


IntMonoid = Monoid(
    T=IntSemigroup.T,
    f=IntSemigroup.f,
    assoc=IntSemigroup.assoc,
    e=smt.IntVal(1),
    right_id=kd.prove(smt.ForAll([z], z * 1 == z)),
    left_id=kd.prove(smt.ForAll([z], 1 * z == z)),
)

# auto unpack
IntMonoid = Monoid(
    **{
    **IntSemigroup.__dict__,
    "assoc":IntSemigroup.assoc,
    "e":smt.IntVal(1),
    "right_id":kd.prove(smt.ForAll([z], z * 1 == z)),
    "left_id":kd.prove(smt.ForAll([z], 1 * z == z)),
    }
)
IntMonoid
```

Python typechecking does not work on the right level to see if you have passed in the appropriate data / proofs or not. Maybe you just passed in a proof of `"|- True" : kd.Proof`? A `__post_init__` function can check for the expected shape of things. Even if you don't pass in the right thing and it gets through, this is not a failure of soundness in one sense. The kernel won't work when you try to use the thing.

In another sense, it is a soundness failure. People will not always check the formulas themselves and not the ground truth of the actual z3 expression in the proofs. This problem exists in all ITPs. The elaborators and overloading mechanisms are pretty complex. They aren't part of the kernel typically and failures in them aren't soundness problems. However, if the user sees text that says something that is meaningfully different from what the kernel sees, you aren't proving what you thought you were.

Honestly, the ergonomics and HCI of a logic are part of of the trusted code base. [Human Factors of Formal Methods with Shriram Krishnamurthi](https://www.youtube.com/watch?v=vufM5G3QAYs&ab_channel=CUEngineeringAcademics). If your syntax is unreadable or it's semantics is nonintuitive, any formal proof is probably kind of worthless so far as trustworthiness goes. The trust won't survive the formal to informal transition.

Pollack inconsistency <https://www.cs.ru.nl/~freek/talks/rap.pdf>
<https://www.brics.dk/RS/97/18/BRICS-RS-97-18.pdf>  How to Believe a Machine-Checked Proof

```python
from kdrag.all import *
from dataclasses import dataclass

# A python level record
@dataclass
class Vec2_dc():
    x : smt.ArithRef
    y : smt.ArithRef

    # We can make an isomorphism between the internal and meta record
    @classmethod
    def of_kd(cls, vec2):
        return Vec2_dc(vec2.x, vec2.y)
    def to_kd(self):
        return Vec2_kd(self.x, self.y)
    
# an internalized knuckledragger version of the record
Vec2_kd = kd.Struct("Vec2", ("x", smt.RealSort()), ("y", smt.RealSort()))

print(Vec2_kd(1,2))
print(Vec2_dc.of_kd(Vec2_kd(1,2)))
```

    Vec2(ToReal(1), ToReal(2))
    Vec2_dc(x=x(Vec2(ToReal(1), ToReal(2))), y=y(Vec2(ToReal(1), ToReal(2))))

However, I can't have a `kd.Proof` inside a kd Struct in the current design of the system. It is perfectly fine to have them be in dataclasses.
Another thing I can do is bundle multiple kd.Proof up using `smt.And`. It's not terrible. I don't have have nice names though. One thing I could do there is to make named identity functions on the bools and use them to tag the different pieces.

```python
def AndBundle(*pfs : kd.Proof) -> kd.Proof:
    return kd.prove(smt.And(*[pf.thm for pf in pfs]), by=pfs)
def DeAndBundle(pf : kd.Proof) -> kd.Proof:
    assert smt.is_and(pf.thm)
    return [kd.prove(p, by=pf) for p in pf.thm.children()]

p = smt.Bool("p")
assoc_tag = kd.define("assoc", [p], p)
comm_tag = kd.define("comm", [p], p)

def BundleAC(assoc : kd.Proof, comm : kd.Proof) -> kd.Proof:
    return kd.prove(smt.And(assoc_tag(assoc.thm), comm_tag(comm.thm)), by=[assoc, comm, assoc_tag.defn, comm_tag.defn])

```

# GenericProof

GenericProof is a lightweight mechanism intended for proofs parametrized over data that can't be quantified over inside z3's logic (or at least not with extremely burdensome and fraught encoding effort).

Basically, I kind of want to be able to have things like `|- lambda A : Sort, Forall(x, x + 0 = x)` but Z3 doesn't support explicit abstraction over Sorts or FuncDecl (without conversion to an array). There may be other kinds of data I want to parametrize on.

Also, perhaps interestingly, if I'm doing ad-hoc polymorphism, I want this lambda to be partial not total. It shouldn't have a result on anything I haven't registered yet. It should throw an error.

So what we can do is kind of push the lambda out to the right of the turnstile `lambda A: |- Forall(x, x + 0 == x)`. We can use the python meta lambda when Z3's object lambda isn't workable.

It is nice to check that we are filling the GenericProof with the right thing. We do this by initializing it with a function that will take the parameters of the `GenericProof` and produce the syntactic formula. This is checked against the registered `Proof` object by alpha equivalence.

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
    >>> obvious.register(R, kd.prove(smt.ForAll([x(R)], x(R) == x(R))))
    """

    def __init__(self, f):
        self.wrapped = f
        self.data = {}

    def __call__(self, *args) -> kd.Proof:
        return self.data[args]

    def __getitem__(self, *args) -> kd.Proof:
        return self.data[args]

    def __contains__(self, *args) -> bool:
        return args in self.data

    def get(self, *args) -> Optional[kd.Proof]:
        return self.data.get(args)

    def lemma(self, *args, **kwargs):
        return self.register(*args, kd.kernel.prove(self.wrapped(*args), **kwargs))

    def register(self, *args):
        args, pf = args[:-1], args[-1]
        if not kd.kernel.is_proof(pf):
            raise ValueError("Not a proof", pf)
        formula = self.wrapped(*args)
        if not kd.utils.alpha_eq(formula, pf.thm):
            raise ValueError("Proof does not match", formula, pf)
        self.data[args] = pf

# Some example usage

@GenericProof
def assoc(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y, z = smt.Consts("x y z", T)
    return kd.QForAll([x, y, z], f(x, f(y, z)) == f(f(x, y), z))


x, y, z = smt.Ints("x y z")
assoc.register(
    (x + y).decl(), kd.prove(smt.ForAll([x, y, z], x + (y + z) == (x + y) + z))
)
assoc.register(
    (x * y).decl(), kd.prove(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
)
```

# TypeClass

People love and hate [typeclasses](https://en.wikipedia.org/wiki/Type_class).

The original design intent of typeclasses was to have a record of stuff keyed on a type. This has been generalized over the keys to more complex multi-key.

I found a lot of inspiration here (as I often do) from Oleg Kiselyov's discussion <https://okmij.org/ftp/ML/canonical.html> of canonical structures, a similar implicits mechanism. If you have extensible functions, you can implement typeclasses at the user level. If you have a staged metaprogramming system like MetaOcaml, you can do have this mechanism run at compile time. Pretty cool.

One might be inclined to say that typeclasses are a prolog-like solver happening at the meta layer to resolve implicits. I think the search and inference of types vs lookup in a registry aspects can be fruitfully uncoupled. I might still make some kind of prolog/minikanren available. That Z3 sorts are basically atomic takes a bit of the point out of it. The z3py bindings don't expose type parameters to datatypes, and getting the pieces of Seq or Array types is possible, but I'm not sure I need an open mechanism for just those two cases

I already have `SortDispatch` for operator overloading, so that isn't the point. There is a very limited number of overloadable operators in python, so I can enumerate them all and i don't need an open mechanism.

The strongest reason I need typeclasses is that in order to translate proofs or formalizations out of existing systems, it is crucial to have mechanisms close enough to the original system or the cognitive load explodes. I have found even changing names I don't like to be too much cognitive load. An accurate assessment of how many mental balls I can juggle is crucial. Once you do have enough stuff to make translation close to syntactic, you can get a lot more distance translating an existing formalization rather than trying to do it de novo, even if I have good grasp of the underlying math.

A distinction between typeclasses and modules is that they can synthesize stuff for you. They are more implicit. With the dataclass style, the user needs to find and plumb the dataclasses through. With typeclasses, as long as the users and producers have access to the typeclass definition, they can use it as an implicit channel of communication. In this way, tactics can access needed proofs without being explicitly plumbed them.

The constructor of TypeClass takes in the a key, and fills in data from the registry into the fields of the instance. There is a `classmethod` registry that allows you to register particular keys with a typeclass.

I may also end up adding an extensible `rules = []` fields which upon failure of lookup in `_registry` can try to programmatically generate the instance.

This design has not stabilized that much.

```python
class TypeClass:
    """
    Subclass this to define a typeclass. The class itself holds a registry of information
    The key can be any valid Python key, but the expected types are smt.ExprRef and smt.FuncDeclRef.
    When you instantiate the class as usual, you hand the key to the constructor and the class will
    look up the information in the registry and populate the fields in the returned instance .
    look up the information in the registry and populate the fields in the returned instance.
    See https://okmij.org/ftp/ML/canonical.html for more on the programmatic approach to typeclasses.

    >>> class Monoid(TypeClass):
    ...     def check(self, T):
    ...         assert isinstance(self.mappend, smt.FuncDeclRef) and self.mappend.arity() == 2
    ...         assert isinstance(self.mempty, smt.ExprRef)
    ...         assert self.mappend.domain(0) == self.mappend.domain(1) == self.mempty.sort() == self.mappend.range()
    ...
    >>> x = smt.Int("x")
    >>> Monoid.register(smt.IntSort(), mappend=(x + x).decl(), mempty=smt.IntVal(0))
    >>> Monoid(smt.IntSort())
    Monoid({'key': (Int,), 'mappend': +, 'mempty': 0})
    """

    # We need to lazily instantiate so different subclasses of TypeClass do not share the same registry.
    _registry = None

    def __init__(self, *L):
        self.key = L
        registry = self.get_registry()
        if L not in registry:
            raise ValueError("Not registered in typeclass", L)
        for k, v in registry[L].items():
            setattr(self, k, v)
        if hasattr(self, "check"):
            self.check(*L)  # type: ignore

    @classmethod
    def get_registry(cls) -> dict:
        if cls._registry is None:
            cls._registry = {}
        return cls._registry

    @classmethod
    def lookup(cls, *L):
        return cls.get_registry()[L]

    """
    @classmethod
    def __contains__(cls, L) -> bool:
        return L in cls.get_registry()
    """

    @classmethod
    def register(cls, *L, **kwargs):
        registry = cls.get_registry()
        if L in registry:
            raise ValueError("Already registered key", L)
        registry[L] = kwargs
        assert cls(*L) is not None  # perform check

    # If we have this stub, pyright complains about overloading
    # def check(self, *L):
    #    pass

    def assert_eq(self, propname, b):
        a = getattr(self, propname)
        if not kd.utils.alpha_eq(a.thm, b):
            raise ValueError(f"Property {propname}, does not match", a, b)

    def __repr__(self):
        return type(self).__name__ + "(" + repr(self.__dict__) + ")"
```

Some example usage

```python
class Semigroup(TypeClass):
    key: smt.SortRef
    assoc: kd.Proof

    def check(self, T):
        # All of these are kind of redundant
        # assert isinstance(T, smt.SortRef)
        # assert T in kd.notation.mul or hasattr(smt.FreshConst(T), "__mul__")
        # assert self.key in property.assoc
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(
            self.assoc.thm, smt.ForAll([x, y, z], x * (y * z) == (x * y) * z)
        )


n, m, k = smt.Ints("n m k")
Semigroup.register(
    smt.IntSort(), assoc=kd.prove(smt.ForAll([n, m, k], n * (m * k) == (n * m) * k))
)


class AbelSemiGroup(TypeClass):
    key: smt.SortRef
    comm: kd.Proof

    def check(self, T):
        self.Semigroup = Semigroup(T)
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(self.comm.thm, smt.ForAll([x, y], x * y == y * x))
        self.assoc = self.Semigroup.assoc
        self.left_commute = kd.prove(
            smt.ForAll([x, y, z], x * (y * z) == y * (x * z)),
            by=[self.comm, self.assoc],
        )


AbelSemiGroup.register(smt.IntSort(), comm=kd.prove(smt.ForAll([n, m], n * m == m * n)))


class Monoid(TypeClass):
    e: smt.ExprRef
    id_left: kd.Proof
    id_right: kd.Proof

    def check(self, T):
        self.Semigroup = Semigroup(T)
        self.assoc = self.Semigroup.assoc
        x = smt.Const("x", T)
        assert kd.utils.alpha_eq(self.id_left.thm, smt.ForAll([x], self.e * x == x))
        assert kd.utils.alpha_eq(self.id_right.thm, smt.ForAll([x], x * self.e == x))


Monoid.register(
    smt.IntSort(),
    e=smt.IntVal(1),
    id_left=kd.prove(smt.ForAll([n], 1 * n == n)),
    id_right=kd.prove(smt.ForAll([n], n * 1 == n)),
)


class Group(TypeClass):
    inv: smt.FuncDeclRef
    inv_left: kd.Proof
    inv_right: kd.Proof

    def check(self, T):
        self.Monoid = Monoid(T)
        self.e = self.Monoid.e
        self.assoc = self.Monoid.assoc
        x = smt.Const("x", T)
        assert kd.utils.alpha_eq(
            self.inv_left.thm, smt.ForAll([x], self.inv(x) * x == self.e)
        )
        assert kd.utils.alpha_eq(
            self.inv_right.thm, smt.ForAll([x], x * self.inv(x) == self.e)
        )

class SemiLattice(prop.TypeClass):
    key: smt.SortRef
    idem: kd.Proof

    def check(self, T):
        self.Group = group.AbelSemiGroup(T)
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(self.idem.thm, smt.ForAll([x], x * x == x))
        self.left_idem = kd.prove(
            smt.ForAll([x, y], x * (x * y) == x * y), by=[self.idem, self.Group.assoc]
        )
        self.right_idem = kd.prove(
            smt.ForAll([x, y], (y * x) * x == y * x), by=[self.idem, self.Group.assoc]
        )
```

# Z3 Parametric Types

Life is easier for me the more I can push onto preexisting functionality. That is the design principle of Knuckledragger, that I didn't want to recreate the universe.

Z3 somewhat recently received preliminary support for parametric type variables. The spec for [SMTLib 2.7](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf) recently was released and it includes support for lambdas and parametric types. Both of these seem to not be in a mature enough state that I'm able to easily use them, though I'll keep trying.

Even if I could use the, I'd still need some generic mechanisms for ad-hoc polymorphism or parametrizing over other kinds of non-internalizable data.

Parametric types is the main thing separating the object logic in Z3 to being basically the same as that in Isabelle HOL or HOL Light afaik. It is also maybe the deal breaker that has led to separate meta layers like boogie, why3, etc. This rhymes with other schisms in the programming world like C++ vs C.

<https://github.com/Z3Prover/z3/discussions/7562>

There is some funky behavior. When TypeVars go into datatypes, they become something like existentials.

```python
from z3 import *
T = DeclareTypeVar("T")
List = Datatype("List")
List.declare("nil")
List.declare("cons", ("car", T), ("cdr", List))
List = List.create()
ilist = List.cons(IntVal(3), List.nil)
rlist = List.cons(RealVal(3), List.nil)
assert ilist.sort() == rlist.sort() 
assert List.car(ilist).sort() == List.car(rlist).sort() # same sort = T. Odd. But reasonable maybe.
```

When they go into functions, they get implicitly foralled? Here is an attempt at defining a recursor on Nat.

```python
from z3 import *
Nat = Datatype("Nat")
Nat.declare("Z")
Nat.declare("S", ("pred", Nat))
Nat = Nat.create()

a = DeclareTypeVar("a")

x = Const("x", Nat)
base = Const("base", a)
f = Const("f", ArraySort(a, a))
rec = Function("rec", Nat, a, ArraySort(a, a), a)

rec(x, base, f) == If(x == Nat.Z, base, f[rec(Nat.pred(x), base, f)]) # This is fine

p = Array("p", Nat, Nat)
rec(Nat.Z, Nat.Z, p) # This is a Sort mismatch error
```

# Bits and Bobbles

I could probably unify GenericProof, SortDispatch, and TypeClass into a single umbrella superclass. They all maintain dictionaries. But they do it in slightly different ways.

Amusingly, what I might imply by the word "typeclass" is contextual. It's almost as if the concept is overloaded to different meanings in different situations :) . What I have here is a very nonstandard emphasis on what a typeclass is.

One design that is continually tempting, but I think is a trap is to try and collapse python types and z3 sorts. I think this is ultimately a bad idea because one needs to do quite a bit of metaprogramming of z3 sorts, which if you identify them, needs to become python type metaprogramming. This is an unergonomic and confusing environment and what is the actual gain? Python typechecking is best used as a light sanity check at the current state. It is nice, don't get me wrong.

In knuckledragger, my meta system is python. My object logic is SMTLib in the form of z3py. My Proof objects live in the python layer. Unless I start reflecting them into a Z3 sort `DeclareSort("Proof")` (an intriguing endeavor, see for example <https://isabelle.in.tum.de/dist/library/FOL/FOLP/index.html> ), I cannot have proofs be members of a z3 struct for example.

It is not however a problem at all to bundle up some associated proofs into a python dataclass

There is a connotation of "types" with static/compile time, or metaness.
Dependent type theory based systems from the get go puncture the meta barrier. Also importantly, they bake in the "meta" notion that propositions and proofs of those propositions are mathematical objects you may want to manipulate in your system.
In a different sense, they still maintain a meta barrier. Coq is implemented in the meta language OCaml. The vernacular commands are not natively discussable in the Coq logic itself.
Lean confuses the distinctions even more. Lean is indeed implemented in lean and yet the Lean that manipulates Lean I think is separate from the logic of lean in a sense similar to how Ocaml is separate from Coq. To pierce this barrier fully seems to lead to inconsistency.

Each `Sortdispatch` maintains a dictionary mapping the sort of the first argument to a specialized function.

In my opinion, shallow embeddings of type systems are a fun game to play, but ultimately not very good.

SMTLib itself is close to being a functional programming language. `define-fun` `define-const` and `define-fun-rec` are very much like programming declarations. A closed smtlib expression that doesn't have quantifiers or free variables in it is probably basically computable. CF was mentioning the idea of maybe applying partial evaluation to SMTLib. It sounds fun but I'm not sure I understand the use case. One is generating huge mostly constant smtlib expressions? Or maybe this is baked more deeply in the solver? The current model

A sanity checking mechanism I'd like to happen automatically is to define an abstract sort `DeclareSort("AbstractLattice")` , assert the axioms and show that anything that has the axioms works on the derivations.

You can include an entire other class by doing self.__dict__.update(other.__dict__)

Some typeclasses don't even make sense in my context

Decidable - z3 is classical and also I don't have a first class Prop.
Inhabited - all z3 sorts are inhabited

- <https://okmij.org/ftp/ML/canonical.html>
- <https://link.springer.com/chapter/10.1007/978-3-642-39634-2_5> Canonical structures for the working coq user

- <https://lawrencecpaulson.github.io/2022/03/23/Locales.html>
- <https://lawrencecpaulson.github.io/2022/03/02/Type_classes.html>

There is another layer. Python metaprograaming and python's type system

History is curious. The ocaml module system has historical roots in systems to organize algebraic structures

- <https://www.why3.org/stdlib/algebra.html>

- <https://arxiv.org/abs/2001.04301>  Tabled Typeclass Resolution

diamond problem

- <https://en.wikipedia.org/wiki/Algebraic_structure>

- <https://lftcm2023.github.io/slides/SlidesBuildingAlgebraicHierarchy.pdf>

Maybe my biggest complaint about python is that the whitespace rules make it too long.

```python
from  dataclasses import dataclass
import kdrag as kd
import kdrag.smt as smt
@dataclass(frozen=True)
class Group():
    T : smt.SortRef
    e : smt.ExprRef
    mul : smt.FuncDeclRef
    inv : smt.FuncDeclRef
    mul_assoc : kd.kernel.Proof
    left_unit : kd.kernel.Proof
    left_inv : kd.kernel.Proof
    def __post_init__(self):
        T, mul, inv, e = self.T, self.mul, self.inv, self.e
        assert mul.arity() == 2 and inv.arity() == 1
        assert mul.domain(0) == T and mul.domain(1) == T and self.mul.range() == self.T
        assert inv.domain(0) == T and inv.range() == T
        x,y,z = [smt.FreshConst(self.T, prefix=x) for x in "x y z".split()]
        kd.lemma(kd.QForAll([x,y,z], mul(mul(x,y),z) == mul(x,mul(y,z))), by=[self.mul_assoc])
        kd.lemma(kd.QForAll([x], mul(e,x) == x), by=[self.left_unit])
        kd.lemma(kd.QForAll([x], mul(inv(x),x) == e), by=[self.left_inv])

UGroupSort = smt.DeclareSort('G') # Uninterpreted Group
e = smt.Const('e', UGroupSort)
x,y,z = smt.Consts('x y z', UGroupSort)                
mul = smt.Function('mul', UGroupSort, UGroupSort, UGroupSort)
kd.notation.mul.register(UGroupSort, mul)
mul_assoc = kd.axiom(kd.QForAll([x,y,z], (x * y) * z == x * (y * z)))
inv = smt.Function('inv', UGroupSort, UGroupSort)
left_unit = kd.axiom(kd.QForAll([x], e * x == x))
left_inv = kd.axiom(kd.QForAll([x], inv(x) * x == e))
UGroup = Group(UGroupSort, e, mul, inv, mul_assoc, left_unit, left_inv)
x,y,z = smt.Reals('x y z')
Group(kd.R, 
      e=smt.RealVal(0), 
      mul=(x+y).decl(), 
      inv=(-x).decl(), 
      mul_assoc=kd.lemma(smt.BoolVal(True)), 
      left_unit=kd.lemma(smt.BoolVal(True)),
      left_inv=kd.lemma(smt.BoolVal(True))) 
```

A style of seperately making the group signature and its laws

```python
from  dataclasses import dataclass
import kdrag as kd
import kdrag.smt as smt
@dataclass(frozen=True)
class Group():
    T : smt.SortRef
    e : smt.ExprRef
    mul : smt.FuncDeclRef
    inv : smt.FuncDeclRef

class LawfulGroup(Group):
    mul_assoc : kd.kernel.Proof
    left_unit : kd.kernel.Proof
    left_inv : kd.kernel.Proof
    def __post_init__(self):
```
