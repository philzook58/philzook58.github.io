---
title: A Python frozenset interpretation of Dependent Type Theory
date: 2025-05-19
---

TLDR. Types are basically sets. Why not python sets?

I enjoy mixing the sacred and the profane. Making a python model clarifies complex topics for me and gives me something to do. The core intuition often comes from finitary computable examples.

As in any sound-ish model, anything you can prove in dependent type theory (DTT) ought to be true here, but some things that are true here are not provable in DTT.

I can see a theme with what I have done here and in the past. Other examples of me attempting a related kind of thing.

- <https://www.philipzucker.com/finiteset/> modelling some basic definitions using nested frozensets. This post is particularly modelled after that one
- <https://www.philipzucker.com/computational-category-theory-in-python-i-dictionaries-for-finset/> making a class to model categorical formulation of finite sets
- <https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/> algebra of programming / relation algebra using finite sets in haskell

Try this notebook yourself in colab <https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2025-05-19-frozenset_dtt.ipynb>

# Basic Types

While one may want to map dependent types into python types, the python type system is awkward, isn't that rich, and most importantly opens the door to considering objects that are too big to actually conclusively analyze and understand. A much simpler thing to attempt do is map dependent types into python sets, specifically frozensets.

The base sets are pretty straightforward

```python
type Type = frozenset

Void = frozenset({})
Unit = frozenset({()})
Bool = frozenset({True, False})

```

Note because I have made the choice of being extremely finite, I can't make a `frozenset` of all `int`. What I can do make finite sets of ranges of ints. The parameter `n` is a meta parameter. This does evoke the dependent type `Fin` <https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Fin> but maybe it isn't really

```python
def Fin(n : int) -> Type:
    return frozenset(range(n))
Fin(4)
```

    frozenset({0, 1, 2, 3})

# Judgements

A hallmark of Martin-Lof type theory is that it has a couple different judgements <https://ncatlab.org/nlab/show/judgment> .

- `A type`  - `A` is a type
- `t : A`  - `t` has the type `A`
- `A == B` - type `A` is equal to type `B` definitionally
- `x == y : A` -  `x` and `y` are definitionally equal terms of type `A`

These judgements in the model can be mapped to python functions that check that they hold in the model. THe claim of soundness of my model says that if you can derive the judgements syntactically using the appropriate inference rules, my python functions ought to return `True`.

```python
def is_type(A: Type) -> bool:
    return isinstance(A, frozenset)
assert is_type(Void)
assert is_type(Unit)
assert is_type(Bool)
assert not is_type(False)
assert not is_type(())
```

```python
def has_type(x: object, A: Type) -> bool:
    return x in A

assert has_type((), Unit)
assert not has_type((), Bool)
assert has_type(True, Bool)
assert not has_type(True, Void)
```

```python
def eq_type(A: Type, B: Type) -> bool:
    return A == B
def def_eq(x : object, y: object, A : Type) -> bool:
    return x == y and has_type(x, A) and has_type(y, A)
```

# Type constructors

Two canonical things you want to talk about in type theory are dependent sum $\sum$ <https://en.wikipedia.org/wiki/Dependent_type#%CE%A3_type> and dependent function $\Pi$ <https://en.wikipedia.org/wiki/Dependent_type#%CE%A0_type> types.

To build these things, you want the notion of a family of sets <https://en.wikipedia.org/wiki/Family_of_sets>, aka a function that returns a set. On this point I remain a little confused, but I chose to use python functions to describe my notion of `Family`.  "Type family" has a connotation to my ear of talking in type theory, but it is a perfectly valid topic in ordinary set theory as merely an indexed family of sets. You may want to union, interset, or cartesian product over this family. See Halmos Naive Set Theory Chapter 9 for example

The dependent aspect of this dependent type can be clearly see in `B(a)`. While dependent types may sound exotic, a python function that returns a set is not exotic. It is also not exotic to have nested `for` loops where the thing you search over has a dependency on the previous `for` loop parameters. One place this shows up is as a way to implement obvious pruning in a naive loop based brute force search.

```python
from typing import Callable
type Family = Callable[[object], Type]

def Sigma(A: Type, B: Family) -> Type:
    return frozenset({(a, b) for a in A for b in B(a)})
Sigma(Bool, lambda x: Unit if x else Void)
```

    frozenset({(True, ())})

`Pair` is the the version of this that doesn't use the dependency

```python
def Pair(A : Type, B: Type) -> Type:
    return Sigma(A, lambda x: B)
Pair(Bool, Fin(3))
```

    frozenset({(False, 0),
               (False, 1),
               (False, 2),
               (True, 0),
               (True, 1),
               (True, 2)})

For dependeent functions, we want to build a `frozenset` of something "functionlike". Dictionaries are basically functions with `foo(bar)` replace with `foo[bar]`. You can do this as long as the function has finite domain, which we do here.
While `frozenset` is a python built in, `frozendict` is not. There is a library though <https://pypi.org/project/frozendict/> . The reason I need frozen versions I because I want to hash these things and make them keys and elements of further dicts and sets.

The way `Pi` works is by selecting every possible choice for every value of the input. The fact that I use `itertools.product` makes sense because dependent functions are sometimes called dependent product and have a notation $\Pi_{x : A} B(x)$

```python
! python3 -m pip install frozendict
```

```python
from frozendict import frozendict
import itertools
def Pi(A : Type, B : Family) -> Type:
    Alist = list(A)
    return frozenset(frozendict({k:v for k,v in zip(Alist, bvs)}) for bvs in itertools.product(*[B(a) for a in Alist]))
Pi(Bool, lambda x: Bool if x else Fin(2))
```

    frozenset({frozendict.frozendict({False: 0, True: False}),
               frozendict.frozendict({False: 0, True: True}),
               frozendict.frozendict({False: 1, True: False}),
               frozendict.frozendict({False: 1, True: True})})

Non dependent functions just throw away the argument.

```python
def Arr(A : Type, B: Type) -> Type:
    return Pi(A, lambda x: B)
Arr(Bool, Fin(3))
```

    frozenset({frozendict.frozendict({False: 0, True: 0}),
               frozendict.frozendict({False: 0, True: 1}),
               frozendict.frozendict({False: 0, True: 2}),
               frozendict.frozendict({False: 1, True: 0}),
               frozendict.frozendict({False: 1, True: 1}),
               frozendict.frozendict({False: 1, True: 2}),
               frozendict.frozendict({False: 2, True: 0}),
               frozendict.frozendict({False: 2, True: 1}),
               frozendict.frozendict({False: 2, True: 2})})

We can also have sum types, which are pretty straightforward.

```python
def Sum(A : Type, B: Type) -> Type:
    return frozenset({("inl", a) for a in A} | {("inr", b) for b in B})
Sum(Bool, Fin(2))
```

    frozenset({('inl', False), ('inl', True), ('inr', 0), ('inr', 1)})

# Telescoped Contexts

The dependent typing context $\Gamma$ aka telescope <https://ncatlab.org/nlab/show/type+telescope> is a central piece of dependent type theory. While I could reify it as a data structure, I actually think there is a nice shallow version of it in the form of python set comprehensions.

The context here is then somewhat identified with the python context. We can reify this context using `locals` <https://docs.python.org/3/library/functions.html#locals> if we so choose, which is kind of an interesting feature from a PL perspective. It's a reification of a flavor akin to call/cc but maybe not discussed as much.

```python
def ctx_example():
    for x in Bool:
        for y in Unit if x else Fin(2):
            print(locals())
ctx_example()
```

    {'x': False, 'y': 0}
    {'x': False, 'y': 1}
    {'x': True, 'y': ()}

The telescoping character that the Types can depend on the previously bound variables in the telescope comes naturally with the structure of `for` loops. Syntactically, the order of the expressions in the comprehension is flipped compared to what is the typically convention in type theory. It looks more like `A type -| Gam` than `Gam |- A Type`

Iin other words, I am for serious interpreting the telescope context $x : A, y : B(y), z : C(x,y)$ with the python textual code `for x in A for y in B(x) for z in C(x,y)`

All the judgments can be extended to being hypothetical judgements by making a comprehension wrapped in an `all`

```python
assert all(is_type(Void if x else Unit) for x in Bool) # x : Bool |- ite(x,Void,Unit) Type
assert all(has_type(y, Unit) for x in Bool for y in (Void if x else Unit)) # x : Bool, y : ite(x,Void,Unit) |- y : Unit
```

# Vec

Vec is a common example of a dependent type.

```python
def Vec(A : Type, n : int) -> Type:
    return frozenset(itertools.product(A, repeat=n))

Pi(Fin(3), lambda x: Vec(Bool, x)) # Functions that can returns lists less than size 3
```

    frozenset({frozendict.frozendict({0: (), 1: (False,), 2: (False, False)}),
               frozendict.frozendict({0: (), 1: (False,), 2: (False, True)}),
               frozendict.frozendict({0: (), 1: (False,), 2: (True, False)}),
               frozendict.frozendict({0: (), 1: (False,), 2: (True, True)}),
               frozendict.frozendict({0: (), 1: (True,), 2: (False, False)}),
               frozendict.frozendict({0: (), 1: (True,), 2: (False, True)}),
               frozendict.frozendict({0: (), 1: (True,), 2: (True, False)}),
               frozendict.frozendict({0: (), 1: (True,), 2: (True, True)})})

```python
Sigma(Fin(3), lambda x: Vec(Bool, x)) # A sum over all lists of size less than 3
```

    frozenset({(0, ()),
               (1, (False,)),
               (1, (True,)),
               (2, (False, False)),
               (2, (False, True)),
               (2, (True, False)),
               (2, (True, True))})

# Identity

Everything is too decidable and makes the distinction between propositional and definitional equality too hard to notice. Also it is quite extensional.

Nevertheless, we can construct a type family akin to an Identity type. <https://ncatlab.org/nlab/show/subsingleton>

```python
def Id(A : Type, x : object, y : object) -> Type:
    return frozenset({"refl"}) if x == y else frozenset()
```

```python
Pi(Bool, lambda x: Pi(Bool, lambda y: Id(Bool, x, y))) # forall x y, x = y There is no such function
```

    frozenset()

```python
Pi(Bool, lambda x: Pi(Bool, lambda y: Pi(Id(Bool, y, x), lambda p: Id(Bool, x, y)))) # forall x y : Bool, forall p : Id(Bool, y, x), Id(Bool, x, y)
```

    frozenset({frozendict.frozendict({False: frozendict.frozendict({False: frozendict.frozendict({'refl': 'refl'}), True: frozendict.frozendict({})}), True: frozendict.frozendict({False: frozendict.frozendict({}), True: frozendict.frozendict({'refl': 'refl'})})})})

```python
all([has_type(p, Id(Bool,y,x)) for x in Bool for y in Bool for p in Id(Bool,x,y)])
```

    True

```python
all([has_type(p, Id(Bool,y,x)) for x in Bool for y in Bool for p in Id(Bool,x,y)])
```

    True

```python
def BasedId(A : Type, x : object) -> Family:
    return lambda y: Id(A, x, y)
```

# Universes

Universes are big. They are the things that contains Types. <https://ncatlab.org/nlab/show/type+universe> <https://en.wikipedia.org/wiki/Universe_(mathematics)> <https://en.wikipedia.org/wiki/Constructible_universe>

Note that frozensets can't have a set be an element of itself without trickery. So we need a universe level for that so we can quantify over types and types of types, etc. <https://agda.readthedocs.io/en/latest/language/universe-levels.html> <https://lean-lang.org/functional_programming_in_lean/dependent-types/indices-parameters-universes.html> <https://en.wikipedia.org/wiki/Axiom_of_regularity> <https://ncatlab.org/nlab/show/axiom+of+foundation> <https://en.wikipedia.org/wiki/System_U> <https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox>

But also if we include all applications of `Arr` and `Pair` etc in our smallest universe, then it isn't a finite set. So another parameter that controls the depth of applications of the constructors also seems like a reasonable thing to do.

```python
def U(n : int, l : int) -> Type:
    if l > 0:
        u = U(n, l-1)
        return u | frozenset([u]) # Cumulative
    elif n > 0:
        u = U(n-1, 0)
        # TODO also the Pi and Sigma
        return u | frozenset([Arr(A,B) for A in u for B in u]) | frozenset([Pair(A,B) for A in u for B in u]) | frozenset([Fin(n)])
    else:
        return frozenset([Unit, Bool, Void])
    
U(0,0) # base universe
```

    frozenset({frozenset(), frozenset({False, True}), frozenset({()})})

```python
U(0,1) # One level up.
```

    frozenset({frozenset(),
               frozenset({False, True}),
               frozenset({()}),
               frozenset({frozenset(),
                          frozenset({False, True}),
                          frozenset({()})})})

```python
has_type(U(0,0), U(0,1)) # U(0,0) : U(0,1)
```

    True

```python
U(1,0)
```

    frozenset({frozenset(),
               frozenset({((), False), ((), True)}),
               frozenset({()}),
               frozenset({frozendict.frozendict({False: (), True: ()})}),
               frozenset({frozendict.frozendict({(): False}),
                          frozendict.frozendict({(): True})}),
               frozenset({False, True}),
               frozenset({((), ())}),
               frozenset({frozendict.frozendict({})}),
               frozenset({frozendict.frozendict({False: False, True: False}),
                          frozendict.frozendict({False: False, True: True}),
                          frozendict.frozendict({False: True, True: False}),
                          frozendict.frozendict({False: True, True: True})}),
               frozenset({(False, ()), (True, ())}),
               frozenset({(False, False),
                          (False, True),
                          (True, False),
                          (True, True)}),
               frozenset({frozendict.frozendict({(): ()})}),
               frozenset({0})})

Here is an example of a polymorphic construction. Note that in this model, we don't have only the functions that obey parametricity. Does this mean the model is "wrong"? No, I don't think so. It just isn't a complete model. The properly parametric functions are going to be a subset of the things returned.

```python
Pi(U(0,0), lambda A: Arr(A,A)) # forall a, a -> a
```

    frozenset({frozendict.frozendict({frozenset(): frozendict.frozendict({}), frozenset({False, True}): frozendict.frozendict({False: False, True: False}), frozenset({()}): frozendict.frozendict({(): ()})}),
               frozendict.frozendict({frozenset(): frozendict.frozendict({}), frozenset({False, True}): frozendict.frozendict({False: False, True: True}), frozenset({()}): frozendict.frozendict({(): ()})}),
               frozendict.frozendict({frozenset(): frozendict.frozendict({}), frozenset({False, True}): frozendict.frozendict({False: True, True: False}), frozenset({()}): frozendict.frozendict({(): ()})}),
               frozendict.frozendict({frozenset(): frozendict.frozendict({}), frozenset({False, True}): frozendict.frozendict({False: True, True: True}), frozenset({()}): frozendict.frozendict({(): ()})})})

```python
Pi(U(0,0), lambda A: Pi(U(0,0), lambda B : Unit)) # forall a b, Unit
```

    frozenset({frozendict.frozendict({frozenset(): frozendict.frozendict({frozenset(): (), frozenset({False, True}): (), frozenset({()}): ()}), frozenset({False, True}): frozendict.frozendict({frozenset(): (), frozenset({False, True}): (), frozenset({()}): ()}), frozenset({()}): frozendict.frozendict({frozenset(): (), frozenset({False, True}): (), frozenset({()}): ()})})})

```python
Pi(U(0,0), lambda B : B) # forall a. a
```

    frozenset()

```python
all([has_type(Arr(A,B), U(2,0)) for A in U(1,0) for B in U(1,0)])
```

    True

# Bits and Bobbles

Some useful resources on dependent types are

- <https://arxiv.org/abs/2212.11082> Introduction to Homotopy Type Theory
- <https://www.cse.chalmers.se/research/group/logic/book/book.pdf>  Programming in Martin-Lof ’s Type Theory
- <https://www.danielgratzer.com/papers/type-theory-book.pdf>
- <https://homotopytypetheory.org/book/>
- <https://www.youtube.com/playlist?list=PLtIZ5qxwSNnzpNqfXzJjlHI9yCAzRzKtx> HoTTEST Summer School 2022
- <https://www.cs.uoregon.edu/research/summerschool/summer14/rwh_notes/ssdt.pdf> Syntax and Semantics of Dependent Types -Martin Hofmann
- <https://people.cs.nott.ac.uk/psztxa/publ/ydtm.pdf> Why Dependent Types Matter
- <https://www.kleene.church/tt-notes> Cody's notes

Python comprehesions are modelled after set comprehensions. I think this means that has_type is something like the axiom of collection / replacement <https://en.wikipedia.org/wiki/Axiom_schema_of_replacement> , a connection I hadn't ever really considered before. Telescopes are telescoped because it models the scoping structure of quantifiers.

Having a notion of execution by using generators or dictionairyes that key on which time a thing enters the set might be interesting. Maybe a more faithful model of constructive principles / enables Int.

Maybe using quoting of code / partial evaluation / bytecode normalization might be a way to get at definitional equality.

Cody pointed out that `Fin` is totally cursed. The parameter coming in is an int and I vaguely silently cast between int and all the versions of Fin.

Sympy, Z3, step indexing, actually using python functions as functions, hypothesis generators generate `stream A` and check `A -> Bool` pairs as types and just sort of randmize test it rather than enumerate it. Contracts.

I kept getting surprised by the stuff that is actually empty vs stuff that had non parametric solutions. Is there something interesting there?

Maybe interpret identity types into

- Code string equality
- bytecode equality
- z3 smt equality
- egraph equality
- paths in a graph
- permutations
- isomorphisms
- simplicial complexes something somethjing (simplical sets really probably)
- sympy equality (t - t1).simplify().is_zero
- proof terms from something?
- `is` equality
- `==` equality

Maybe finite models like this are useful for counterexample finding or attempting to generalize/antiunify into suggested terms. <https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/mace4.html> Mace4 is a cool model enumerator for first order logic

Rather than use frozendict and frozenset, using BDD like structures could be useful <https://en.wikipedia.org/wiki/Binary_decision_diagram> . We are kind of model checking type thoery

Subsets, proof irrelevance, predicativity, quotients

<https://lawrencecpaulson.github.io/2022/02/23/Hereditarily_Finite.html>  <https://en.wikipedia.org/wiki/Hereditarily_finite_set> What I am doing is the analog of hereditarily finite set theory. Cody claims makes sense because DTT interpeters into set theory, and there are finite set models of the appropiate set theories. <https://eprints.illc.uva.nl/id/eprint/1769/1/wehr.pdf> <https://www.sciencedirect.com/science/article/abs/pii/S0049237X0871989X> The Type Theoretic Interpretation of Constructive Set Theory - Aczel. <https://www.lix.polytechnique.fr/~werner/publis/tacs97.pdf>  Sets in Types, Types in Sets - Benjamin Werner

Classes ~ functions.

parameters vs indices. Python functions vs ?

<https://golem.ph.utexas.edu/category/2022/07/identity_types_in_context.html>
<https://cs.stackexchange.com/questions/20100/what-are-the-difference-between-and-consequences-of-using-type-parameters-and-ty>
<https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/>

The fiber perspective. Hmm. If I want to be categorical about it. Actually implement telescoped substitution. But this is way more deeply embedded than what I've done here.

Refinement typing discipline vs dependent typing discipline. Related. What does the telescoping really achieve? Is it more or less powerful than binding all variables at once and then `forall x y z, P(x,y,z), Q(x,y,z), R(x,y,z) => Foo` which is more like Isabelle Pure. Triangularity is reminscent of triangular matrices but also triangular substitutions from minikanren implementations. Any connection?

Do the parametricity relational model finitely. Explain its relationshiop to information hiding of the universe and oninterference. Run a program twice on some unchanged and some changfed inpputs as a method to detect leakage. Fuzzing the universe might also work, since that can expose information hiding problems. Information hiding and staged metaprogramming also. Kind of you can't leak information from runtime to compile time.

One way for a topic to have meaning is to explain how to map it into another thing you're already comfortable in. For some new programming language, a way to do this is to give an interpreter of the new programming language inside a programming language you already know. An example of this in the context of a formal logic is to give a way to translate the syntax of your logic into a description of a thing metatheory you're working in, which might be some set theory or lean or isabelle or whatever. <https://plato.stanford.edu/entries/model-theory/> . You then also want to find an instance of this thing.

I've become used to saying the phrase "python is my metatheory". This is true because in Knuckledragger <https://github.com/philzook58/knuckledragger> , I metaprogram my higher order logic in python, doing the sorts of things a metalogic does. It is also true because I only feel comfortable that a mathematical topics makes sense if I can see something to do or compute with it. A model, however janky, finitized, or lightly unsound, inside of python can help strip away a befuddling aura of mysticism around a topic. Maybe from a fancier perspective, python is an interesting dirty place to put realizability <https://en.wikipedia.org/wiki/Realizability> <https://ncatlab.org/nlab/show/realizability> models, which I think are models with a notion of computation baked in.

I can see a theme.

- <https://www.philipzucker.com/finiteset/> modelling some basic definitions using nested frozensets
- <https://www.philipzucker.com/computational-category-theory-in-python-i-dictionaries-for-finset/> making a class to model categorical formulation of finite sets
- <https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/> algebra of programming / relation algebra using finite sets in haskell

In the typical arch of understanding , there is a naive version, then sophisticated, and then you appreciate the naive version again.

On a first pass, types are basically sets. The type `int` is basically interpretable as the set of all integers and the type `bool -> bool` is interpretable as the set of all functions from `bool` to `bool`  (of which there are `2^2 = 4`).

On a second pass, types aren't sets <https://dl.acm.org/doi/pdf/10.1145/512927.512938> . Sets do a bad job of explaining parametricity for example, for which a relational interpretation is more appropriate. <https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf> Parametricity is basically the same idea as information flow security.

On a third pass, types aren't not sets.

![](/assets/type_sets.jpg) Using this meme is a bit propaganda-y. It is implocitly calling you a bespectacled midwit if you think types are not sets. Maybe I'm using the wrong meme. Maybe I should use the brain exploding one? There are probably more passes beyond 3 and I think types are not sets is a perfectly valid viewpoint. Moreso than projecting this meme onto others, I mean it to explain how I currently see my own history of understanding.

Static vs dynamic. Type judgements are the string of python?
x : Fin(5), y : Fin(x) |- x + y : Fin(x)

The interpretation of contexts is sets of environments.

dependency shows up naturally in the ordering of loops. what's up with that?

## Quotient / Subset

```python
def Quot(A : Type, R) -> Type:
    return frozenset(frozenset({y for y in A if R(x,y)}) for x in A)

Quot(Bool, lambda x,y: Id(Bool, x, y))
```

    frozenset({frozenset({True}), frozenset({False})})

```python
# # Note because of pythion truthiness, this also accepts ordinary bool value predicates. Feature or misfeature?
Quot(Fin(6), lambda x, y: x == y % 3)
```

    frozenset({frozenset(),
               frozenset({1, 4}),
               frozenset({2, 5}),
               frozenset({0, 3})})

```python
def SubSet(A :  Type, P : Family) -> Type: # very much like Sigma
    return frozenset({(x, ()) for x in A if P(x)}) # Note because of pythion truthiness, this also accepts ordinary bool value predicates.

SubSet(Bool, lambda x: Id(Bool, x, True))

```

    frozenset({(True, ())})

```python
SubSet(Fin(7), lambda x: x < 3)
```

    frozenset({(0, ()), (1, ()), (2, ())})

```python
def Not(A : Type) -> Type:
    return Arr(A, Void)
def Decidable(A : Type) -> Type:
    return Sum(A, Not(A))

```

## Sympy

Sympy set module seems too weak to do families. Maybe it could be extneded?  <https://docs.sympy.org/latest/modules/sets.html>

```python
# sympy Set module
import sympy
x,y,z = sympy.symbols("x y z")
sympy.ConditionSet(x, x > 0, sympy.S.Reals)
sympy.Contains(x, sympy.UniversalSet)
x in sympy.UniversalSet
sympy.Contains(x, sympy.FiniteSet(1,2)) # in doesn't work. Needs to evlauates to Bool

#def Arr(A,B):
#def Pi(A,B):

Contains(x, sympy.UniversalSet), Contains(y, FiniteSet(1,2)(x), Contains(z, FiniteSet(1,2)(x,y))
                                          ImageSet().Contains()
                                        
```

## Gassed

How to include integers?
Lets everything become generators. Allow semidecidable sets.
Marshall  <https://github.com/andrejbauer/marshall>
<https://dl.acm.org/doi/abs/10.1145/3209108.3209193>

Maybe a kripke model version with just N steps allowed. Then could index what is in set by integer is appears at. Monotonic set growth.

```python
# Gassed version of Pi using generatyors? 
# Step indexing.

# gas parameter
def Pi(A,B,gas):
    # all steps < gas
    Alist = list(functools.reduce(operator.or_, A(i) for i in range(gas)))
    return frozenset(frozendict({k:v for k,v in zip(Alist, bvs)}) for bvs in itertools.product(*[B(a,gas) for a in Alist]))

# generator style.
# B is generator of families.
def Pi(A,B):
    Biter = B()
    B.next() # B is one ahead of A
    for An in A:
        Bn = B.next()
        yield frozenset(frozendict({k:v for k,v in zip(An, bvs)}) for bvs in itertools.product(*[Bn(a) for a in An]))


```

```python
from collections import defaultdict
def tset(vs):
    d = {}
    for v,t in vs:
        d[v] = min(d.get(v, float("inf")), t)
    return frozendict(d)

tset([("x",1), ("y",2), ("x", 3), ("z",4)])
```

```python
import itertools
def delay(t, v):
    for i in range(t):
        yield
    yield v
    #return v

list(delay(4, 2))

x = delay(4,3)
next(x)
next(x)
next(x)
next(x)
next(x)


def pair(x,y):
    for i in x:
        yield (i,None)
    for j in y:
        yield (i,j)
list(pair(delay(2,42), delay(1, "hello")))

def Pair(A,B):
    return [pair(i,j) for i in A for j in B]
def Pi(A,B):
    pass
```

## Z3

Z3 can describe finite sets as models. A Pi constructor akin to kd.QForAll.

```python
def Pi(*vs, body): # TeleForAll. # Pi?
    acc = body
    # TODO: maybe compress stretches of unquantified.
    for v in reversed(vs):
        if isinstance(v, tuple):
            #acc = kd.QForAll([v[0]], v[1], acc) # this is more refinement style. Strictly speaking B can still contain x in other ways.
            acc = kd.QForAll([v[0]], v[1][v[0]], acc)
        else:
            acc = kd.QForAll([v], acc)
    return acc

IntT = smt.K(smt.IntSort(), True)
#Pos = smt.Lambda([x], x > 0)
def GT(x):
    return smt.Lambda([y], y > x)
def Fin(n): # meta Fin
    return smt.Lambda([x], smt.And(0 <= x, x < n))
# Internal-ish Fin
Fin = kd.define("Fin", [n], smt.Lambda([x], smt.And(0 <= x, x < n)))
#Fin2 = smt.Lambda([x], smt.Lambda([y], smt.And(0 <= x, x < 2))
Turnstile([(x, Fin(3)), (y, Fin(x))], )

type Type = smt.ArraySortRef
def Pi(A : smt.ArraySortRef, B : smt.ArraySortRef) -> Type:
    return smt.Lambda([f], kd.QForAll([x], A[x], B(x)(f[x])))
def Arr(A : Type, B : Type) -> Type:
    return smt.Lambda([f], kd.QForAll([x], A[x], B(f[x])))
def Pair(A : Type, B : Type) -> Type:
    return smt.Lambda([p], smt.And(p.is_pair, A(p[0]), B(p[1])))
def Sigma(A : Type, B : Type) -> Type:
    return smt.Lambda([p], smt.And(p.is_pair, A(p[0]), B(p[0])(p[1])))
```

```python
Term0 = smt.DeclareSort("Term0")
Term = smt.Datatype("Term")
Term.declare("TT")
Term.declare("BoolVal", ("bval", smt.BoolSort()))
Term.declare("IntVal", ("ival", smt.IntSort()))
Term.declare("PairVal", ("fst", Term), ("snd", Term))
Term.declare("OtherVal", ("val", Term0)) # Functions, etc. We only separate out primitives for fun.

Type = smt.SortSort(Term)
Family = smt.ArraySort(Term, Type)
Bool = smt.Lambda([t], t.is_BoolVal)
Void = smt.Lambda([t], False)
Unit = smt.Lambda([t], t.is_TT)

Arr = smt.Function("Arr", Type, Type, Type)
apply = smt.Function("apply", Term, Term, Term)
lam = smt.Function("lam", smt.ArraySort(Term, Term), Term)
kd.axiom(kd.QForAll([a,b], apply(lam(a), b)) == a[b])
# extensionality forall x, apply(t1, x) == apply(t2, x) == (t2 == t1)


kd.define("Arr", [A,B], smt.Lambda([t], smt.And(t.is_OtherVal, kd.QForAll([x], A[x], B[apply(t, x)]))))
kd.define('Pi', [A,B], smt.Lambda([t], smt.And(t.is_OtherVal, kd.QForAll([x], A[x], B[x][apply(t, x)]))))
def Pi(A, B):
    return smt.Lambda([t], smt.And(t.is_OtherVal, kd.QForAll([x], A(x), B(x, apply(t, x)))))
# comp = smt.Function("comp", Type, Term)
# This might be ok, but the reverse,   Term, Type or asking if Term in Term requires carefulness.

lamB = smt.Function("lamB", smt.ArraySort(smt.BoolSort(), Term), Term)




Univ = smt.Const("Univ0", Type)


```

## Terms

I have been very vague what my allowed terms are.

```python
tt = ()
false = False
true = True

def ite(c, t, e):
    return t if c else e
def rec_unit(x, a):
    assert x == tt
    return a
def rec_void(x, a):
    assert False
```

```python
import dis

f = lambda x: x + 1
f1 = lambda y: y + 1
dis.dis(f)
dis.dis(f1)
```

      3           0 RESUME                   0
                  2 LOAD_FAST                0 (x)
                  4 LOAD_CONST               1 (1)
                  6 BINARY_OP                0 (+)
                 10 RETURN_VALUE
      4           0 RESUME                   0
                  2 LOAD_FAST                0 (y)
                  4 LOAD_CONST               1 (1)
                  6 BINARY_OP                0 (+)
                 10 RETURN_VALUE

```python

def inter(F : Family):
    return functools.reduce(lambda x,y: x.intersection(y), F.values())
def union(F : Family):
    return functools.reduce(lambda x,y: x.union(y), F.values())
def prod(F : Family):
    pass
```

```python
def Id(A : Type) -> Type:
    return Pi(A, lambda x: frozenset([frozendict({x : "refl"})]))

Id(Bool)
[p for x in Bool for y in Bool for f in Id(Bool) for p in f[x][y]] in Id(Bool)

all(has_type(Id(Bool)[x], Pi(Bool, Id(A,x,y)) for x in Bool))



def id_rec(motive, a, p, x):
    assert p == "refl"
    assert has_type(x, motive())
    return x

```

      Cell In[35], line 7
        all(has_type(Id(Bool)[x], Pi(Bool, Id(A,x,y)) for x in Bool))
                                  ^
    SyntaxError: Generator expression must be parenthesized

<https://github.com/Marco-Sulla/python-frozendict>

<https://en.wikipedia.org/wiki/Family_of_sets>

A graph neighborhood map V -> edges

Anytihng A -> [B]

relation to the finite parametricity idea.

Internalized == frozendict
Meta = python fun

Finite dependent type theory in python.

groupoid model? paths on a graph?

isomorphisms?

The is basically model checking of dependent type theory?
Which is easier.
We get a little bit of jimmies by fiddling with the universe.

step indexed relatiobns. Maybe there's some way to use computation bounding to model check.

indices vs parameters and meta vs other

inference rule form vs internialize pi form of induction

quotient types
extensional equality

Yes, this is a logical relation.
<https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf>
I am being vague what the actual syntactic language I'm working in.
Also the caveat that everything is a frozenset before I even get to it somehow is the intution behind termination.

Another axis to finitize on ot number of computational steps allowed and to have partial functions

defaultdict can do more but still not everything.
You can have a defaultdict from the integers.
BDDs are interesting also but just as a compression.

are types sets?
<https://bsky.app/profile/hillelwayne.com/post/3lms36j275s26>

Trying to make a sound model of dependent type theory
If you can derive a judgement (which I am not doing) or if there is a derivation of a judgement, the corresponding python statement should return true

`[[x : A]] ----->  "for x in [[A]]"`

Model checking dependent type theory
A python frozenset model of dependent type theory

How does one build a finite model of first order logic for example

Translate |- forall x, p(x,y) into
Picking p, A etc
all(p(x,y) for x in A)

string codes
z3 ast codes

z3 egraph somehow?

Graham suiggested "dispaly indexing". Represent Family as it's sigma type + a projector?
<https://ncatlab.org/nlab/show/displayed+category> ?
[for x in A for base, totpoint in B if base == x]

def ITE(A : Type, B : Type) -> Family:
    return frozenset({(True, A), (False, B)})

but again this is kind of a poor mans frozendict?

def ITE(A : Type, B : Type) -> Family:
    return frozendict({True : A, False : B})

That telescopes turn into foralls is interesting.
And it does make sense from a finitrary efficiency standpoint to not do a big non dependent loop and then cut out. You want to generate only that which is obvious plausible

Z3 model. Internal SetSort()
f = Function vs f = Array("f", , ) as internal vs external.
Universes.

```
for x in A:
    for y in B:
        if cond(x,y):
            yield yada
```

vs

```
for x in A:
    for y in B(x):
        yield yada
```

vs

```
for x in A:
    if cond(x):
        for y in B:
            if cond2(x,y):
                yield yada
```

vs
for x in A:
    if cond(x):
        for y in B(x):
            if cond2(x,y):
                yield yada

althouggb basically cond(x) can be fused into B by returning null iterator.

I've been playing the same game for so long
<https://www.philipzucker.com/finiteset/>
<https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/>

hmm. Using quickcheck. That's intriguing.
hypothesis. quickcheck over different universes or interpretations.

quickcheck set theory statements too. Huh.
I wonder if quickchecks in lean or quickchick have something like this

Krivine realizability models
What does this say about the sympy thing. Why isn't it working? No notion of set?

```python
from frozendict import frozendict
type Family[X] = frozendict[Type, X]
type MArr[A,B] = frozendict[A, B] # meta arrow
type MSet[A] = frozenset[A] # meta set

def Id(A : Type) -> Family[Family[Type]]:
    return frozendict({a : frozendict({b : ITE(Unit, Void)(a == b) for b in A}) for a in A})
```

```python
def Quot(A : Type, P : Family[Family[Type]]) -> Type:
    #groupby?
    #frozenset({frozenset(a for a in A if P(a)) for p in P})
    #itertools.groupby(A, lambda a)
    # union find?
    uf = {}
    def union(a, b):
        pass
    for a in A:
        for b in A:
            if find(a) == find(b):
                continue
            if P(a)(b):
                union(a, b)


# basically Sigma?
# def Subset(A : Type, P : Family)
```

```python
from frozendict import frozendict
import functools
import itertools
from typing import Callable


type Term = object
type Type = frozenset

Void : Type = frozenset()
tt : Term = () # could use Void?
Unit : Type = frozenset({tt})
Bool : Type = frozenset({True, False})


# pointed power



# frozen set vs frozendict(A,Bool)
# Set vs A -> Prop
"""
def telescope(ctx):
    if len(ctx) == 0:
    A = ctx[0]
    for a in A:
        for rest in ctx[1](a):
            yield (a, rest)
"""

# telescopes are generators.

# we are somewhat confusing the definition and an algorithm for proving the judgements.

"""
Or are contexts the _python_ context?
for x in A:
    # is_type(B(x))
    for y in B(x):
        #we are in context x : A, y : B(x) here
        q in Q # ctx |- q : Q

could we introspect the context?

"""

# extend a context
def extend(ctx, A):
    is_type(ctx, A)
    for ts in ctx:
        for a in A(*ts):
            yield (a, *ts)


# interpretation of judgements
def is_type(ctx, A):
    for ts in ctx:
        assert isinstance(A(*ts), frozenset)
def has_type(ctx, a, A):
    for ts in ctx:
        A1 = A(*ts)
        assert a(*ts) in A1
        #assert isinstance(A1, frozenset)
def eq_type(ctx, A, B):
    for ts in ctx:
        A1 = A(*ts)
        B1 = B(*ts)
        # is_type
        assert A1 == B1
        #assert isinstance(A1, frozenset)
def def_eq(ctx, a, b, A):
    pass

#Family = frozendict
Type = frozenset
Family = Callable[..., Type]
# Family = frozendict[object, Type]
#Tele = list[Family]

# but this is really one step less shallow
# Tele = frozenset[frozendict[str,object]]
#def sing(A):
#    # singleton family
#    return frozendict({a : frozenset({a}) for a in A})
# 
#sing(Bools)
def Eq(A : Type, a) -> Family:
    assert a in A
    def res(b):
        assert b in A
        return Unit if b == a else Void # frozenset({a})?
    return res

    #return frozenset(frozendict({a : frozenset({a})})

def Fin(n) -> Type:
    return frozenset({i for i in range(n)})
# Int is not a type. It's metalevel
# so Fin isn't a family. It's a meta family. yikes

# This is a family. Still pretty confused. We're conflating the different fins with each other and with int.
def Fin2(max : int) -> Family[Type]:
    return frozendict({i : Fin(i) for i in range(max)})

# This is more like saying all these types exist
# Fin is kind of like a cumulative universe
def FinU(max : int) -> Type: # l : int   universe level
    return frozenset([Fin(i) for i in range(max)])
# A : FinU 10, x : A, y : Fin2(10)(x) |-


# This vserion we can see we can't plug x : Fin(i) into Fin(x)
def Fin3(n : int) -> Type:
    return frozenset({(f"Fin{n}", i) for i in range(n)})


def Vec(max : int, A : Type):
    # max is an upper bound on the size of the Vec. This is not usually a thing.
    def fix(n):
        if n == 0:
            return Unit
        else:
            return Pair(A, fix(n-1))
    return Pi(Fin(max), fix)

# is there something less restrictive than Vec?
#def MaxList(max : int, A : Type):


# Inductive types are defined by recursion.
# Could use haskell style Free? Fix?
def Inductive(f):
    pass



Type = frozenset
Family = Callable[Type, Type]

def Fin(n : int) -> Type:
    return frozenset({i for i in range(n)})

def Pi(A : Type, B : Family) -> Type:
    Alist = list(A)
    return frozenset(frozendict({k:v for k,v in zip(Alist, bvs)}) for bvs in itertools.product(*[B(a) for a in Alist]))

def Arr(A : Type, B : Type) -> Type:
    return Pi(A, lambda a: B)

def Not(A : Type) -> Type:
    return Arr(A, Void)

def Sigma(A : Type, Bx : Family) -> Type:
    return frozenset([(a,B(a)) for a in A])

def Pair(A : Type, B : Type) -> Type:
    return Sigma(A, lambda a: B) 

def Sum(A : Type, B : Type) -> Type:
    return frozenset(("left", a) for a in A) | frozenset(("right", b) for b in B)

#@functools.cache
def Univ(i,j):
    if i == 0 and j == 0:
        # or make extra random types. Then polymorphic stuff can't rely on exact struxcture of U0.
        # Gives a feel for an "open" U0 rather than closed. U0 contents shouldn't leak.
        return frozenset([Bool, Unit, Void]) # base types
    # iterate constructions
    if j > 0:
        return frozenset({Univ(i,j-1)}) #, Fin(i), Eq(Univ(i,j-1), i), Sing(Univ(i,j-1))})
    elif j == 0:
        res = []
        for A in Univ(i, j-1):
            res.append(A) # cumulative
            for B in Univ(i, j-1):
                res.append(Arr(A,B))
        return frozenset(res)

# These are all not in contexts...
Arr(Bool,Bool)
Pi(Bool, Eq(Bool, True))
Sum(Bool, Bool)
Sum(Bool, Void)
Sum(Unit, Unit)
def Or(A,B): return Sum(A,B)
def And(A,B): return Pair(A,B)
def Implies(A,B): return Arr(A,B)
def Iff(A,B): return And(Implies(A,B), Implies(B,A))


#Eq(Bool, True)(False)

def Decidable(A : Type) -> Type:
    return Sum(A, Not(A))
Pi(Bool, lambda y: Sum(Eq(Bool, True)(y), Not(Eq(Bool, True)(y))))


def lam(A, f):
    return frozendict({a : f(a) for a in A})

lam(Bool, lambda x: x) in Arr(Bool, Bool)

lam(Univ(0,0), lambda A: A) in Pi(Univ(0,0), lambda A : A)
Pi(Univ(0,0), lambda A : A)
Univ(0,0)
```

```python
# a simple family
def ITE(A : Type, B : Type) -> Family:
    return lambda c: A if c else B

# an even simpler family
def Const(A : Type) -> Family:
    return lambda x: A
```

## Codes and Tarski Universes

Comprehensions are modelled after set comprehensions. Are has_type judgements like set comprehensions?

|- A type  is say the set exists
|- t : A   is like using seperation on a type that exists?. But we generate t, not cut it out. Seperation ought to look more like this.
[t == x + y for x in Fin(5) for y in Fin(x) for t in Fin(5 + y) ] ?

Maybe it's more like replacement? <https://en.wikipedia.org/wiki/Axiom_schema_of_replacement>
predciates A -> Bool as classes. Set[A] as sets. Converting is not obvious.
|- A type  is more like asserting a class expression is well formed?
|- t : A   is using (hypothetical?) axiom of collection?

|-

<https://ncatlab.org/nlab/show/Tarski+universe>
You have |- T : type and then |- t : El(T)
T is code

Cody points out Fin is an abomination because it takes Fin as a parameter.
But it always terminates at meta Nat.

families could be codes of families?

`El` family is a meta function. is it `eval`? And codes = str

<https://okmij.org/ftp/Haskell/TypeClass.html#Haskell1> only 1 typeclass Oleg

```python
#Family = Type # a set of codes
Code = str
Type = frozenset
Family = frozenset[Code]
El = eval
#def El(t : Code) -> Type:
#    # yada?
#    # But I probably want El to be extensible?
    
```

vytecode equality as definitional equality. A little strong than string equality of code. Would normalize withspace, parens. But also maybe names? Maybe not
<https://arxiv.org/abs/1805.08106>  The sufficiently smart compiler is a theorem prover
<https://dl.acm.org/doi/10.1145/3611643.3616357> Speeding up SMT Solving via Compiler Optimization

I could do fstring stuff to partially eval.
`lam(lambda xlambda x: f"{x}" ==  lambda y:

Code string equality
bytecode equality
z3 smt equality
egraph equality
paths in a graph
permutations
simplicial complexes something somethjing (simplical sets really probably)
sympy equality (t - t1).simplify().is_zero
proof terms from something?
`is` equality
`==` equality
