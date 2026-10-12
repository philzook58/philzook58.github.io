---
title: Category Theory of Terms Emphasizes the Argument List
date: 2026-10-12 
---

Category theory. I dunno man.

I think I have a cute story about data structure refactoring that brings a standard Term data structure more in sync with the categorical presentation. The trick is to emphasis the argument list / forest (which in turn can be seen a substitution, which is a more standard thing to say).

# Basic Terms

A basic term datatype in python looks like this. This is the analog of the OCaml definition `type term = App of string * term list | Var of string`

```python
from dataclasses import dataclass, field
class Term: ...

@dataclass
class App(Term):
    f : str
    args : list[Term]

@dataclass
class Var(Term):
    name : str


App("f", [Var("X")]) # f(X)
```

    App(f='f', args=[Var(name='X')])

It's a natural shoot from the hip first pass.

As is often the case though, this shoot from the hip is probably not the form with the cleanest mathematical properties. I think it's generally good to seek that out and see what you see. <https://en.wikipedia.org/wiki/The_Unreasonable_Effectiveness_of_Mathematics_in_the_Natural_Sciences>

# Factoring Out the Arg List as Special

Because the language (python or ocaml) had a very nice default `list` type, we did not even really consider making a custom standalone type for the arguments.

This would look like so

```python
from dataclasses import dataclass, field
class Term: ...
@dataclass
class TermSeq:
    terms : list[Term]

@dataclass
class App(Term):
    f : str
    args : TermSeq

@dataclass
class Var(Term):
    name : str


App("f", TermSeq([Var("X")])) # f(X)
```

Yes, we've barely done anything. We're headed somewhere weird don't worry.

# Variables and Context

A slight change is the make the variables indexed by an number rather than by a string.

```python
from dataclasses import dataclass, field
class Term: ...

@dataclass
class App(Term):
    f : str
    args : list[Term]

@dataclass
class Var(Term):
    index : int


App("f", [Var(0)]) # f(V0)
```

    App(f='f', args=[Var(index=0)])

I am inclined to say that this representation is "ill-specified" in the sense it is easier to give a clean semantics to variables (<https://www.philipzucker.com/assets/thin_talk.pdf> slide "compositional pointwise semantics") if we make sure we always know how many variables are around. This is _not_ inferrable from the term imo. One can infer a minimum context from an unannotated term by collecting up the variables, but we cannot specifically state we are in a context of size 27, but only use `Var(3)`. The automatic inference would say we are in context of size 4.

I feel like I've spoken at great length about this concept of the "dimension" being a necessary part of the term. <https://www.philipzucker.com/thin_term/>

```python
from dataclasses import dataclass, field
class Term: ...

@dataclass
class App(Term):
    ctx : int
    f : str
    args : list[Term]

@dataclass
class Var(Term):
    ctx : int
    index : int


App(27, "f", [Var(27,3)]) # f(V0)
```

    App(ctx=27, f='f', args=[Var(ctx=27, index=3)])

# Arguments as a Category

Combining these two ideas we can get something like this. I could also spray `ctx : int` into the other two, but I don't think it's necessary.

```python
from dataclasses import dataclass, field
class Term: ...

@dataclass
class TermSeq:
    ctx : int
    terms : list[Term]

@dataclass
class App(Term):
    f : str
    args : TermSeq

@dataclass
class Var(Term):
    index : int


TermSeq(27, [App("f", TermSeq(27, [Var(3)]))])
```

    TermSeq(ctx=27, terms=[App(f='f', args=TermSeq(ctx=27, terms=[Var(index=3)]))])

Now however, `TermSeq` has

- a natural domain (number of variables) and codomain (number of terms).
- a notion of composition as substitution
- two notions of product
  - a product over a common context <https://en.wikipedia.org/wiki/Product_(category_theory)>
  - a product where you contexts are kept separate (added) and terms are shifted <https://en.wikipedia.org/wiki/Monoidal_category>
- equalizers can explain unification <https://www.cs.man.ac.uk/~david/categories/book/book.pdf>

This is category stuff. It makes for some neat looking combinators in terms of the code though.

```python
@dataclass
class TermSeq:
    ctx : int
    terms : list[Term]

    def __post_init__(self):
        for t in self.terms:
            if not isinstance(t, Term):
                raise TypeError("All elements of terms must be Term instances")
            match t:
                case Var(i):
                    if i >= self.ctx:
                        raise ValueError(f"Variable index {i} out of bounds for context {self.ctx}")
                case App(f, args):
                    if not isinstance(args, TermSeq):
                        raise TypeError("Arguments of App must be a TermSeq")
                    if args.ctx != self.ctx:
                        raise ValueError("Context of arguments must match context of TermSeq")
                case _:
                    raise TypeError("Unsupported term type")

    @property 
    def dom(self):
        return self.ctx

    @property
    def cod(self):
        return len(self.terms)

    def __add__(self, other): 
        # pair(f,g) of morphisms. The categorical product of the morphisms
        if not isinstance(other, TermSeq):
            raise TypeError("Can only product TermSeq with TermSeq")
        if self.dom != other.dom:
            raise ValueError("Domains must match for product")
        return TermSeq(self.ctx, self.terms + other.terms)

    def __mul__(self, other):
        # shifting product
        if not isinstance(other, TermSeq):
            raise TypeError("Can only multiply TermSeq with TermSeq")
        return TermSeq(self.ctx + other.ctx, [extend(t, other.ctx) for t in self.terms] + [shift(self.ctx, t) for t in other.terms])

    def __matmul__(self, other):
        if not isinstance(other, TermSeq):
            raise TypeError("Can only matrix multiply TermSeq with TermSeq")
        if self.dom != other.cod:
            raise ValueError("Domain of first must match codomain of second for matrix product")
        return TermSeq(other.dom, [subst(t, other) for t in self.terms])


def subst(t : Term, s : TermSeq):
    match t:
        case Var(i):
            return s.terms[i]
        case App(f, args):
            return App(f, args @ s)
        case _:
            raise TypeError("Unsupported term type")

def shift(n : int, t : Term):
    match t:
        case Var(i):
            return Var(i + n)
        case App(f, args):
            return App(f, TermSeq(args.ctx + n, [shift(n, t) for t in args.terms]))
        case _:
            raise TypeError("Unsupported term type")
def extend(t : Term, n : int) -> Term:
    match t:
        case Var(i):
            return Var(i)
        case App(f, args):
            return App(f, TermSeq(args.ctx + n, [extend(t, n) for t in args.terms]))
        case _:
            raise TypeError("Unsupported term type")



TermSeq(2, [Var(0)]) + TermSeq(2, [Var(1)])

TermSeq(2, [Var(0)]) @ TermSeq(2, [Var(1), Var(0)])

def id_(ctx: int) -> TermSeq:
    # identity 
    return TermSeq(ctx, [Var(i) for i in range(ctx)])
def proj(ctx: int, i: int) -> TermSeq:
    # projection
    if i >= ctx:
        raise ValueError(f"Projection index {i} out of bounds for context {ctx}")
    return TermSeq(ctx, [Var(i)])
def swap(ctx: int, i: int, j: int) -> TermSeq:
    # swap
    if i >= ctx or j >= ctx:
        raise ValueError(f"Swap indices {i}, {j} out of bounds for context {ctx}")
    terms = [Var(k) for k in range(ctx)]
    terms[i], terms[j] = terms[j], terms[i]
    return TermSeq(ctx, terms)
def delete(ctx : int) -> TermSeq:
    # The maps to terminal object
    if ctx < 0:
        raise ValueError(f"Cannot drop from context {ctx}")
    return TermSeq(ctx, [])
dup = TermSeq(1, [Var(0), Var(0)])

def Function(f : str, arity : int) -> TermSeq:
    return TermSeq(arity, [App(f, TermSeq(arity, [Var(i) for i in range(arity)]))])

a = Function("a", 0)
assert a.dom == 0 and a.cod == 1
f = Function("f", 1)
assert f.dom == 1 and f.cod == 1
g = Function("g", 2)


```

Some usage. It is interesting how you construct terms using composition and product. Shifting around variables to get them in the right spot can be annoying.

It's also interesting how `TermSeq` plays the role of the return type of `Function`, which I would usually make a special `Decl` type.

Note that a standard way of presenting ground terms is as a morphism from ctx 0. This is a typical categorical thingy.

```python
assert id_(1) + id_(1) == TermSeq(1, [Var(0), Var(0)])
assert id_(1) * id_(1) * id_(1) == id_(3)
assert swap(2, 0, 1) == TermSeq(2, [Var(1), Var(0)])
assert proj(2, 0) == TermSeq(2, [Var(0)])
assert proj(2, 1) == TermSeq(2, [Var(1)])
assert f @ a == TermSeq(0, [App("f", TermSeq(0, [App("a", TermSeq(0, []))]))])
assert g @ id_(2) == g
```

# Bits and Bobbles

Keyword argument dicts and named variables go hand in hand. Then we could {"x" : t1, "y" : t2}. Then the objects / context is a set of names.
Is this the case for other generalizations of terms? Params, generalized arity?

```
class KeyedTerms:
    data: dict[str, Term]
class Term:
    f : str
    args : KeyedTerms
class Var:
    str
```

Presenting TermSeq in this way is kind oif like presenting Lists/free monoid as Cons cells rather than Append chains. One could also make a "free category" data structures with Comp constructors. This is sort the the full right association of those Comp cells.

Another theme is that often when I talk about trees, I should probably have said "forest" because I don't care or explicitly want there to be multiple trees in play. This is the case in a union find where I describe it as "upside down trees (child to parent pointers)" but really it's an upside down forest.

This post is not radically different from <https://www.philipzucker.com/tele/> categorical substitution etudes, but the story is a bit different and being freed from the constraints of the z3 ast makes for cleaner things I can do. I also have developed a totally different feel for "context" and "term" for myself since I wrote that.

There are many ways of refactoring and formulating a datastructure.

- The "algebra of types" (tuple is product, disjoint union is sum) gives some nice intuition a about some of them.
- <https://en.wikipedia.org/wiki/AoS_and_SoA> Structure of Array transformations can be very effective changes of conceptual perspective and change performance.
- One can take a union type and convert it into a "fatty struct" that just has pieces for all of them options, some of which are sometimes unused.
- If you have a mutually defined recursive type, you can cycle around which one you consider to be the toplevel type. You can also flatten a mutually defined type into a single one maybe at the cost of some floppiness. Mutual recursion usually kind of sucks to analyze in proof assistants, and yet is a nice well typed trick  from type functional programmings perspective.

<https://research.manchester.ac.uk/en/publications/a-categorical-unification-algorithm/>
<https://www.cs.man.ac.uk/~david/categories/book/book.pdf> Burstall and rydeheard
<https://www.sciencedirect.com/science/chapter/edited-volume/abs/pii/B9780120463701500127> goguen what is unification

<https://www.philipzucker.com/proof_uf/>
categorcial substitution etuds

<https://ncatlab.org/nlab/show/Lawvere+theory>

<https://en.wikipedia.org/wiki/Operad> linear usage of variables?
PROP =

if we made Multiterm have non flat structure, maybe we could note interesting associative operaods?

<https://en.wikipedia.org/wiki/Clone_(algebra)> clones are allowing  equality fusion in asusmptions? The dual of dup

Unificiation is not a thing you do to term pairs. It is something you do to a set of equations.

I both find it useless and overwrought and yet I am also continually drawn into curiosity. Partly this is because is has a mystique to it. Fancy smart people do it or whatever. Don't I want to be fancy smart too? Yes and no. There is a certain beligerrant pride in all walks of life to exulting simplicity rather than sophistication.

Whenever I reference it, I have to preface with a warning that I'm not really pushing for it.

I think the angle on category theory that I kind of get is where it is just another twist on the typical algebraic story of group, ring, field etc. It's another abstract idea like that where the "multiplication" operation is partial-ish, only makes sense when the input of x matches the output of y.

It is also a generalization of the algebra of function composition / relation composition.

I appreciate the concept of Functor seems to be closely associated with the concept of "nice mapping" / homomorphisms / map that respects structure. At some points I've been into natural trasnformations as kind of a mind model of a subset of parametric type patterns, but that isn't really paged in to me anymore.

Likewise something I've been drawn to for unclear reasons is Type theory, and there is a connection there.

Substitutions are some kind of mapping and it is intuitively clear to me that there can be a notion of composition in there.

I think kind of the persepctive of the category of susbtitutions is that "substitutions are all you need" and that the original terms can be thought of as certain kinds of subsitutions.

While a standard category theory modeling move, this is also kind of fucking nuts. We only have subsitutions but they don't have terms in them? What do they substitute into? Get the fuck out of here.

There is a minimalism here which is very nice for proving properties. But it is also too minimalistic, stuffing conceptually distinct things into the same slot just because they are mechanistically redundant in a certain way. Concepts matter.

A similar thing occurs in ETCS vs set theory vs
<https://ncatlab.org/nlab/show/SEAR> . ECTS is kind of too bare bones to

```python
class TermSeq(TermSeq):
    def split(self):
        return TermSeq(self.ctx, self.terms[0]), TermSeq(self.ctx, self.terms[1:])

    def __call__(self, *args : TermSeq):
        return self @ (functools.reduce(lambda x, y: x + y, args))
    # lift ?

def unify(s : TermSeq, t : TermSeq) -> TermSeq:
    if s.dom != t.dom or s.cod != t.cod:
        raise ValueError("Domains must match for unification")
    dom, cod = s.dom, s.cod
    if cod == 0: # no equations
        return id_(dom)
    elif cod == 1:
        match s.terms[0], t.terms[0]:
            case Var(i), Var(j):
                if i != j:
                    raise ValueError("Cannot unify different variables")
                return id_(dom)
            case App(f, args), App(g, bargs):
                if f != g:
                    raise ValueError("Cannot unify different function symbols")
                return unify(args, bargs)
            case _, _:
                raise TypeError("Unsupported term type for unification")

    else:
        s0, s_rest = s.split()
        t0, t_rest = t.split()
        sol1 = unify(s0,t0)
        return unify(s_rest @ sol1, t_rest @ sol1)
    
```

```python
from dataclasses import dataclass
class Term:
    pass
@dataclass
class App(Term):  # Comp(f, args)  but specialize like Cons compared to append. ConsComp
    f : str
    args : MultiTerm
    def shift(self, d : int) -> App:
        return App(f=self.f, args=self.args.shift(d))
    def substitute(self, t : MultiTerm) -> App:
        return App(f=self.f, args=self.args.substitute(t))

@dataclass
class Var(Term):
    n : int
    def shift(self, d : int) -> Var:
        return Var(n=self.n + d)
    def substitute(self, t : MultiTerm) -> Var:
        return t.ts[self.n]
@dataclass
class MultiTerm:
    d :  int
    ts : list[Term]
    def __or__(self, other : MultiTerm) -> MultiTerm: # truly independet paralle compose
        return MultiTerm(d=self.d + other.d, ts=self.ts + other.shift(self.d).ts)
    def __mul__(self, other : MultiTerm) -> MultiTerm: # 
        assert self.d == other.d
        return MultiTerm(d=self.d, ts=self.ts + other.ts)
    def __matmul__(self, other : MultiTerm) -> MultiTerm: # sequential compose
        return self.substitute(other)
    def substitute(self, t : MultiTerm) -> MultiTerm:
        assert self.d == len(t.ts)
        return MultiTerm(d=self.d, ts=[s.substitute(t) for s in self.ts])
    def shift(self, d : int) -> MultiTerm:
        return MultiTerm(d=self.d + d, ts=[t.shift(d) for t in self.ts])
    def weaken(self, n : int) -> MultiTerm: # I guess we could weaken using a thinning.
        return MultiTerm(d=self.d + n, ts=self.ts)
    


def app(f: str, *args : MultiTerm) -> MultiTerm:
    d = args[0].d
    assert all(a.d == d for a in args) and all(len(a.ts) == 1 for a in args)
    return MultiTerm(d=d, ts=[App(f=f, args=MultiTerm(d=args[0].d, ts=list(args)))])
def const(f, d : int) -> MultiTerm:
    return MultiTerm(d=d, ts=[App(f=f, args=MultiTerm(d=d, ts=[]))])

def var(n : int, d : int) -> MultiTerm:
    return MultiTerm(d=d, ts=[Var(n)])

id_ = var(0, 1)

v0 = var(0, 1)
app("f", v0).substitute(app("g", v0))

swap = MultiTerm(d=2, ts=[var(1,2),var(0,2)])
swap
f = app("f", var(0,1)) # f(X) as representing f
g = app("g", var(0,2), var(1,2)) # g(X,Y) as representing g

fst = var(0,2)
snd = var(1,2)
proj = var

from pprint import pprint
pprint(g @ ((f @ f) * v0))


# | only maintains linear usage of variables.
# * let's you duplicate
delete = MultiTerm(d=1, ts=[])
dup = MultiTerm(d=1, ts=[var(0,1), var(0,1)])
```

```python
from dataclasses import dataclass

class Cat: ...

@dataclass
class Comp(Cat): 
    f : Cat
    g : Cat
    # or could flatten associativity?

@dataclass
class Id(Cat): # var
    pass

@dataclass
class Decl(Cat):
    f : str
    arity : int

@dataclass
class Fork(Cat):
    # same domain. but product over. Hmm. That's just the produce?
    f : Cat
    g : Cat


```
