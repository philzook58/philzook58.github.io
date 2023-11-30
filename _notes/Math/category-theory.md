---
layout: post
title: Category Theory
---


- [Axioms](#axioms)
- [Examples](#examples)
  - [Groups and Monoids](#groups-and-monoids)
  - [PoSet](#poset)
  - [FinSet](#finset)
  - [FinVect](#finvect)
  - [FinRel](#finrel)
  - [LinRel](#linrel)
- [Categories and Polymorphism](#categories-and-polymorphism)
- [Combinators](#combinators)
- [Encodings](#encodings)
- [Diagram Chasing](#diagram-chasing)
- [Constructions](#constructions)
  - [Products](#products)
  - [CoProducts](#coproducts)
  - [Initial Objects](#initial-objects)
  - [Final](#final)
  - [Equalizers](#equalizers)
  - [Pullbacks](#pullbacks)
  - [PushOuts](#pushouts)
- [Functors](#functors)
  - [Adjunctions](#adjunctions)
- [Natural Transformations](#natural-transformations)
- [Monoidal Categories](#monoidal-categories)
- [String Diagrams](#string-diagrams)
- [Higher Category](#higher-category)
- [Topos](#topos)
- [Presheafs](#presheafs)
  - [Sheaves](#sheaves)
- [Profunctors](#profunctors)
- [Optics](#optics)
- [Logic](#logic)
  - [Poly](#poly)
- [Internal Language](#internal-language)
- [Combinatorial Species](#combinatorial-species)
- [Applied Category Theory](#applied-category-theory)
  - [Categorical Databases](#categorical-databases)
  - [Computational Category Theory](#computational-category-theory)
    - [Catlab](#catlab)
- [Resources](#resources)

EPR?

[Resources on Lenses](https://github.com/bgavran/Lens_Resources)

Doctrines

Abstract Finite categories
Kind of like a graph data structure.
Kind of like a finite group.
A list of objects, a list of morphisms with domain and codomain, and a multiplication table.
Any particular question can be answered via enumeration

Finitely Generated Categories

# Axioms

Category is objects and morphisms. Morphisms have a partial operation called composition and there is an identity morphism for every object

# Examples

## Groups and Monoids

The algebraic laws of monoid basically work for a category with one object, where multiplication is composition

A group can be modeled as a category with one object, where ever morphism has an inverse. Then the axioms of cateogory corresponds to the axioms of a group

## PoSet

partially ordered sets. There is at most one morphism between each object

Lattices are an interesting further subcase.

<https://en.wikipedia.org/wiki/Partially_ordered_set>

## FinSet

Finite sets as objects, finite maps (dicitonaries) as morphisms

Can also consider partial finite maps.

## FinVect

vector spaces are objects (dimensionality or labelled). Linear maps are morphisms (~ matrices)

## FinRel

## LinRel

# Categories and Polymorphism

Part of the appeal of category theory comes from it's relationship to polymorphism. Polymorphism is counterintuitive really in regards to the simple model of types being sets.

<https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/>

<https://arxiv.org/pdf/2209.01259.pdf> Category Theory for Programming

```haskell
class Functor f where
  map : (a -> b) -> f a -> f b
```

`f` is type mapping. Types are objects. map transfers morphisms

`forall a, f a -> g a` is a natural transformation. Polymorphism means you can't really look at / create elements, only swap, duplicate, and forget them.

`forall a. f a <~> Id a -> f a`  is a limit (do i remember that right?)

Yoneda lemma
[Reverse Engineering Machines with the Yoneda Lemma - Piponi](http://blog.sigfpe.com/2006/11/yoneda-lemma.html)

```
forall b. (a -> b) -> f b <~> f a
to y = y id
from fa = \f -> fmap f fa
```

Relation to CPS

Functor composition `Comp f g`

Representable Functors

Types are objects. Type derivations are morphisms.

Saying "functions' are morphisms is a bit confusing because what do we mean by function? The naive set model of functional programming? We're gonna get lost in the polymorphism stuff

idea: T,E |- T,R  as the morphism. "type evaluation" and "term checking" happneing in parallel.

[categorical models of polymorphism](https://core.ac.uk/download/pdf/81193164.pdf)

Fibration model

# Combinators

<https://en.wikipedia.org/wiki/Combinatory_logic>

Combinators are little functional pieces you can combine like lego blocks. When you have a language of combinators, variable binding issues are gone. They are hard to program with

Combinators are not synonymous with categories, but categories can inform a particular style of combinators

# Encodings

Encoding category theory to first order, higher order logic, and dependent type theory. Generalized algebraic theories.

Relational Composition
comp(F,G,H)

Comp as Partial function
comp(F,G) = Some(H)

Objects as Sort

Blog posts

- Egglog 2: Automatically Proving the Pullback of a Monic is Monic <https://www.philipzucker.com/egglog2-monic/>
- Egglog Examples: Pullbacks, SKI, Lists, and Arithmetic <https://www.philipzucker.com/egglog-3/>
- [Rewriting Monoidal Categories in the Browser with Egg](https://www.philipzucker.com/rust-category/)

# Diagram Chasing

# Constructions

## Products

## CoProducts

## Initial Objects

## Final

## Equalizers

## Pullbacks

## PushOuts

# Functors

Functors are mappings between categories. This means they are a  tuple of map from objects to objects and morphism to morphism such that composition plays nice (commutes sort of)
Functors are mappings between categories (a object to object map and morphism to morphism map) that plays nice with composition and identity. F(id) = id. F(f.g) = F(f) . F(g)

F = (Fo, Fm)
Fm(f . g) = Fm(f) . Fm(g)

Representations of groups. Functor from group as a category to

## Adjunctions

Free/Forgetful

Galois Connections. Abstraction and concretization

Closure/Rounding and lift

Abstract interpretation
Intervals <-> sets
polytopes
convexsets <-> sets

# Natural Transformations

A "natural" notion of morphisms between functors : C -> D.
Morphims in D indexed by objects in C.

# Monoidal Categories

Vect

# String Diagrams

[string diagrams for computer scientists](https://twitter.com/rwolffoot/status/1658383020473176064?s=20)

# Higher Category

<https://en.wikipedia.org/wiki/Higher_category_theory>

Morphisms go between objects
2-morphisms go between morphisms

An example I like is Rel. Morphisms are binary relations. binary relations can be compared via inclusion (they form a partial order themselves).

# Topos

<https://twitter.com/johncarlosbaez/status/1461346819963686920?s=20> John Baez
[topos theory in a nutshell baez](https://math.ucr.edu/home/baez/topos.html)
Use functions instead of a notion of element being member of set.
functions can essentially select elements.
functions into "truth value" set (indicator functions) are analogs of subsets.

<https://jonsterling.notion.site/Topoi-inside-and-out-7b0b86e39eeb43aeaee3c3af1dd91f2a> jon sterling blog post

To say something is a topos is to say it is

1. a category
2. a special category with some special constructs

Weird notions of truth value are fun.

Concepctual mathematics
Categories and Sets
Goldblatt
Maclane and Moerdijk

retract & section as notions of division / pseudo inverse

"variable sets"?

# Presheafs

Some "pattern" category indexing a set. One set per objects, one function per morphisms. i.e. a functor.

Some examples of this are models of algebraic structures. Simple algebraic structures (monoid, group) are modelled as single objects where arrows are the operations. A preseaf.

We sometimes say stuff like a group is a set with some structure. This is kind of the same thing.

A process is a set with a time stepping map.
A multigraph is a set of edges with source and target arrows. You can make it symmettric by insisting that flipping soruce and target is the same thing.

Presheafs are also like schema.

Presheafs are also like "action" like a group action on a set. Sometimes they are called C-sets.

Simplicial sets are indexed by a simplex with face inclusion relations. <https://en.wikipedia.org/wiki/Simplicial_set>

## Sheaves

# Profunctors

# Optics

# Logic

<https://mikeshulman.github.io/catlog/catlog.pdf> Categorical logic from a categorical point of view Mik Shulman
Scott and Lambek book

Rising Sea

A proof of `A |- B` is the basic "morphism". A proof is a tree. We can perhaps annotated this sequent with free variables and unification variables in play (signature). This makes this morphism floating over some kind of variable set, something sheafy? Or a set floats of variables floats over the proof

- Objects are propositions.
- Cut is compose.
- Axiom is id.
- Existentials and universals as adjunctions
  Different proofs are different morphisms between the same objects.

`x | A |- B` is kind of expressing $A \subset B$ where the sets A and B live in `x` space (the number of free variables describes the number of ). Because logic and set theory kind of reflect each other by the comprehension principle, formula and sets are quite similar. This is probably decribable as a functor of some kind.
Coordinates and coordinate changes are interesting to consider.
universal and existential quantifiers are kind of projectons combined with coordinatre transform. Weakening is like lifting a low-d set to a high-d set by just allowing the column above it. If you do existential and then lift, you get an outer approximation of original set. If you do
Sets and predicates are also akin to indicator functions. We are well aware that coordinate changes sort of require changing functions contravariantly.
A finitary version of coordinates is considering a representation of finset where you need to just label wth integers. Tupling can be collapsed to indices in column major, row major, or zigzag quite naturally. These are different cooridnate schemes.

```python
# finset

def idd(n):
  return (n,n,[i for i in range(n)])
DOM = 0
COD = 1
def compose(f,g):
  assert f[DOM] == g[COD]
  return (g[DOM], f[COD], [f[2][t] for t in g[2]]) 

def rowmajor(n,m,(i,j)):
  return i + n*j
def undorowmajor(n,m,k):
  return (k % n, k // n)

def colmajor(n,m,(i,j)):
  return j + m*i


def kron_row(f,g):
  pass
def kron_col(f,g):
  pass
def kron_zigzag(f,g):
  pass

# permutations are interesting subcase. These form groups at each object.
# when we define a pullback, we pick some ordering. There are others.

INITIAL = 0
FINAL = 1
OMEGA = 2

true = (FINAL, OMEGA, [1])
false = (FINAL, OMEGA, [0])

# a subset morphism of the finset n. It is indexed by the a set the size of the subset
def subset(n, s):
  return (len(s), n, [i for i in s]) 

def is_mono(f):
  pass
def is_epi(f):
  pass



```

Using integers as objects is a skeletal category. Using python sets as objects would not be. Lots of isomorphic objects. Integers are kind of beautiful in a way. Let's us use arrays.

```python
'''
use integers to mark variables, tuples and strings for function symbols / constants
objects are numbers of variables
morphisms are subsitutions
We also should case the domain and codomain
'''
def idd(n):
  return (n,n,[i for i in range(n)])
DOM = 0
COD = 1
def apply(subst, term):
  if isinstance(term, int):
    return subst[term]
  elif isinstance(term, tuple):
    return tuple(apply(subst, t) for t in term)
  elif isinstance(term, str):
    return term
  else:
    raise Exception("bad term")

def compose(f,g):
  assert f[DOM] == g[COD]
  return (g[DOM], f[COD], [apply(f[2], t) for t in g[2]])

def lift(t,n):
  if isinstance(t, int):
    return t+n
  elif isinstance(t, tuple):
    return tuple(lift(t, n) for t in t)
  elif isinstance(t, str):
    return t
  else:
    raise Exception("bad term")

def kron(f,g):
  return (f[DOM]+g[DOM], f[COD]+g[COD], f[2]+[lift(t, f[COD]) for t in g[2]])

fuse = (2,1,[0,0])

print(compose(idd(2), idd(2)))
print(compose(fuse, kron(fuse,fuse))) # (4, 1, [0, 0, 0, 0])
# equalizer

# pullback

# 
```

[Finite Limits and Anti-unification in Substitution Categories Wolfram Kahl](https://inria.hal.science/hal-02364568/document)

```python
# predicates are again represented using tuples, integers, and strings
# object are now predicates
# morphisms are proof trees with the root as `a |- b` which is a symbolic version of subset
def idd(p):
  return (p,p, "id")
DOM = 0
COD = 1
def compose(f,g):
  assert f[DOM] == g[COD]
  return (g[DOM], f[COD], ("cut", f[2], g[2]))

# conjuction
#def prod(f,g):
  
# disjunction

# implication

# a subsitution defines a functor
def instan(subst, pf):
  objmap = lambda ob: apply(subst, pf[DOM])
  arrmap = lambda arr: ("instan", subst[2], arr)
  return (objmap(pf[DOM]), objmap(pf[COD]), arrmap(pf[2]))

# adjoint
def exists(subst, pf):
  pass


```

Polynomials semialgebraic
Z3 impl
Linear numpy
Modules
Convex
Polytope
marshall
sympy

## Poly

```python
import sympy
from sympy import poly
from sympy import symbols
# a category of polynomial substutiton
# actually this is just sympy substitution.
def idd(n):
  x = sympy.MatrixSymbol('x', n, 1)
  x = [symbols(f"x{i}") for i in range(n)]
  return (n, x)

def cod(f):
  return len(f[1])
def dom(f):
  return f[0]

def comp(f,g):
  assert dom(f) == cod(g)
  sub = {symbols(f"x{i}") : e for i,e in enumerate(g[1])}
  return (dom(g), [y.subs(sub)  for y in f[1]])

print(comp(idd(3),idd(3)))

def kron(f,g):
  shift_sub = {symbols(f"x{i}") : i + dom(f) for i in range(dom(g))}
  gshift = [e.subs(shift_sub) for e in g]
  return (dom(f) + dom(g), f + gshift)

dup = [symbols("x0"), symbols("x0")]

```

# Internal Language

What is this? Cody talks about this a lot.

# Combinatorial Species

Brent Yorgey thesis
<https://en.wikipedia.org/wiki/Combinatorial_species>

# Applied Category Theory

[Compositional Modeling with Decorated Cospans - Baez](https://www.youtube.com/watch?v=skEsCiIM7S4&ab_channel=GReTASeminar)

<https://act2023.github.io/> International Conference on Applied Category Theory

[polynomil functors book](https://github.com/ToposInstitute/poly)
<https://github.com/ToposInstitute/polytt> a type theory implementation?

## Categorical Databases

schema is a finite category
Data lives over it
Mappings between schema describe

```python
# table for dom, cod, and one per each morphism.
# some knd of codd normal form
"create table people(val)"
"create table dog(val)"
"create table strings(val)"

# "Set" == Sql strings

# create table mymorph(unique src, dst);
# functional dependency
"create table owner(primry key src, dst)"
f = ("dogs", "people", "owner")
dog_name = ("dogs", "strings", "dog_name")
people_name = ("people", "strings", "people_name")

def idd(a):
  return (a,a, f"select {a} as src, {a} as dst from {a}")
def compose(f,g):
  (f[0], g[1], f"select {f[2]}.src as src, {g[2]}.dst as dst from {f[2]} join {g[2]} on {f[2]}.dst = {g[2]}.src")

class Schema():
  objs = []
  morphs = []
  eqs = []

def check_schema():
  for (dom,cod,t) in morphs:
    "select f.src not in {dom}"
    "select f.dst not in {cod}"
  for eq in eqs:

# a functor from one shcema to another
class FinFunctor():
  objmap = {}
  arrmap = {}

def check_functor(functor):

class NatTrans():
  pass

class Adjunction():
  pass


```

The chase for reapir -> datalog / egglog?

## Computational Category Theory

<https://x.com/AlexisToumi/status/1726528031584636953?s=20> <https://arxiv.org/abs/2311.10608> DisCoPy: the Hierarchy of Graphical Languages in Python

Hypergraph equality using networkx

```python
from discopy.monoidal import Ty, Box, Layer, Diagram
x, y, z = Ty('x'), Ty('y'), Ty('z')
f, g, h = Box('f', x, y @ z), Box('g', y, z), Box('h', z, z)
assert f >> g @ h == Diagram(
dom=x, cod=z @ z, inside=(
Layer(Ty(), f, Ty()),
Layer(Ty(), g, z),
Layer(z, h, Ty())))

from discopy import monoidal, python
from discopy.cat import factory, Category
@factory # Ensure that composition of circuits remains a circuit.
class Circuit(monoidal.Diagram):
  ty_factory = monoidal.PRO # Use natural numbers as objects.
  def __call__(self, *bits):
    F = monoidal.Functor(
    ob=lambda _: (bool, ), ar=lambda f: f.data,
    cod=Category(python.Ty, python.Function))
    return F(self)(bits)
class Gate(monoidal.Box, Circuit):
  """A gate is just a box in a circuit with a function as data."""
NAND = Gate("NAND", 2, 1, data=lambda x, y: not (x and y))
COPY = Gate("COPY", 1, 2, data=lambda x: (x, x))
XOR = COPY @ COPY >> 1 @ (NAND >> COPY) @ 1 >> NAND @ NAND >> NAND
CNOT = COPY @ 1 >> 1 @ XOR
NOTC = 1 @ COPY >> XOR @ 1
SWAP = CNOT >> NOTC >> CNOT # Exercise: Find a cheaper SWAP circuit!
assert all(SWAP(x, y) == (y, x) for x in [True, False] for y in [True, False])

from discopy import ribbon, drawing
from discopy.cat import factory, Category
x = ribbon.Ty('x')
cup, cap, braid = ribbon.Cup(x.r, x), ribbon.Cap(x.r, x), ribbon.Braid(x, x)
link = cap >> x.r @ cap @ x >> braid.r @ braid >> x.r @ cup @ x >> cup
@factory
class Kauffman(ribbon.Diagram):
  ty_factory = ribbon.PRO
class Cup(ribbon.Cup, Kauffman): pass
class Cap(ribbon.Cap, Kauffman): pass
class Sum(ribbon.Sum, Kauffman): pass
Kauffman.cup_factory = Cup
Kauffman.cap_factory = Cap
Kauffman.sum_factory = Sum
class Variable(ribbon.Box, Kauffman): pass
Kauffman.braid = lambda x, y: (Variable('A', 0, 0) @ x @ y)\
+ (Cup(x, y) >> Variable('A', 0, 0).dagger() >> Cap(x, y))
K = ribbon.Functor(ob=lambda _: 1, ar={}, cod=Category(ribbon.PRO, Kauffman))
#drawing.Equation(link, K(link), symbol="$\\mapsto$").draw()


from discopy.symmetric import Ty, Box, Swap, Diagram
x, y, z = Ty('x'), Ty('y'), Ty('z')
f = Box('f', x, y @ z)
g, h = Box('g', z, x), Box('h', y, z)
diagram_left = f >> Swap(y, z) >> g @ h
diagram_right = f >> h @ g >> Swap(z, x)
assert diagram_left != diagram_right
with Diagram.hypergraph_equality:
  assert diagram_left == diagram_right
```

- [Computational Category Theory](https://www.cs.man.ac.uk/~david/categories/book/book.pdf)
- [evan patterson](https://www.epatters.org/wiki/algebra/computational-category-theory.html)

<https://github.com/homalg-project/CAP_project> GAP package. Homological algebra focus

[hey I got on hacker news](https://news.ycombinator.com/item?id=23058551)

[catlab.jl](https://www.algebraicjulia.org/)

[gatlab](https://www.youtube.com/watch?v=Jdl2dh_hY3c&ab_channel=AppliedCategoryTheory)

homotopy.io
globular

cartographer

From a programming perspective I think there are a couple contributions:

- Category theory has a number of very intuitive looking graphical notations which nevertheless translate to very exact algebraic expressions. This is pretty dang nice. Category theory is a road to a very principled formulation of things that are already done in dataflow languages, tensor diagrams, and UML and things like that. These graphical languages are a reasonable user facing interface.

- Empirically in mathematics, category theory has been found to be a flexible and "simple" language to describe and interconnect very disparate things. In programming terms that means that it is a plausible source of inspiration for consistent interfaces that can do the same.

- Point free DSLs are really nice to work with as library/compiler writer. It makes optimizations way easier to recognize and implement correctly. Named references are phantom links attaching different points in a syntax tree and make it hard to manipulate them correctly. In slightly different (and vague) terms, category theory gives a methodology to turn abstract syntax graphs into trees by making all links very explicit.

I can't comment much on what category theory contributes to mathematics, but I think there are similar points. I think category theory can make precise analogies between extremely disparate fields like logic, set theory, and linear algebra. I think categorical intuitions lead to clean definitions when specialized to some particular field. Combinatory categorical logic does make some aspects of logic less spooky.

### Catlab

# Resources

[Nice list of resources](https://www.logicmatters.net/categories/)

- Bartosz Milewski
- Computational Category Theory
- Maclane

- [Rosetta stone](https://math.ucr.edu/home/baez/rosetta.pdf)

- [A Categorial Theory of Objects as Observed Processes](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.158.6803&rep=rep1&type=pdf)
- [You know more about presheaves than you think](https://www.hedonisticlearning.com/posts/you-know-more-about-presheaves-than-you-think.html) sheaves are databases
The underlying category is a schema. It maps up to FinSet.
Processes are a timey database.

- [Temporal type theory](https://arxiv.org/abs/1710.10258)

- Sheaves in Geometry and logic

- [Seven Sketches in Compositionality: An Invitation to Applied Category Theory](https://arxiv.org/abs/1803.05316)

- [pattern matching: a sheaf theortic approach thesis](https://escholarship.org/content/qt3t59q0pp/qt3t59q0pp_noSplash_8827b78a6461f58bc090a563888ef7fe.pdf)

[category theory carlo youtube](https://twitter.com/carloangiuli/status/1587467571737120769?s=20&t=rPY3oIv7e70HfT_mJgeYuA)

[topology a category theory approach](https://topology.mitpress.mit.edu/) <https://news.ycombinator.com/item?id=33601318>

[Category Theory Illustrated](https://github.com/abuseofnotation/category-theory-illustrated)

[sheaf theory through examples](https://mitpress.mit.edu/9780262542159/sheaf-theory-through-examples/)

[chyp](https://github.com/akissinger/chyp)interactive string diagram prover. Also graph rewrite system... hmmmmmm.

[Categorical diagram editor](https://www.youtube.com/watch?v=iWSw4RK8wEk&list=PLGAzEMA0TM_WxCnc__yLOFoS0_k-liev0&index=4&ab_channel=GReTASeminar)

[ghica keynote ICGT](https://www.youtube.com/watch?v=adHzaC5vVDg&ab_channel=GReTASeminar)
[Hierarchical string diagrams and applications](https://arxiv.org/abs/2305.18945)
Greta. See Graphs. See term rewriting.

Cartographer
globular
quantomatic
chyp
homotopy.io

```vampire
% clark completion

fof(mytheory, axiom,

%((dom(F) != cod(G)) => (comp(F,G) = junk)) &

%((dom(F) != cod(G)) => (comp(F,G) = junk(comp(F,G)))) &



%comp(junk(G),F) = junk(comp(junk(G),F)) &
%comp(G,junk(F)) = junk(comp(G,junk(F))) &
%(((dom(F) != cod(G)) | F = junk | G = junk) <=> (comp(F,G) = junk)) &
%comp(junk,F) = junk &
%comp(G,junk) = junk &

dom(id(A)) = A &
cod(id(A)) = A &

comp(id(A), F) = F &
comp(F, id(A)) = F &

cod(comp(F,G)) = cod(F) &
dom(comp(F,G)) = dom(G) 

%(monic(F) <=> ( ![X,Y] : ((comp(F,Y) = comp(F,X)) => X = Y)))

% junk(A,B) junk(comp(F,G)) keep junk intference seperated. Dunno.


).
cnf(noncollapse, axiom, junk != nonjunk).
```

`comp(id(dom(F)), F) = some(F)`
only use intrinsically well typed expressions.
`comp(F,comp(G,H)) = comp(comp(F,G),H)`
right, as I said 3 years ago, this doesn't work unguarded.

```vampire

fof(mytheory, axiom,

% unconditional
dom(id(A)) = A &
cod(id(A)) = A &
% I almost feel like unguarded assoc might be ok.
% possibly important for special AC support
% comp(F,comp(G,H)) = comp(comp(F,G),H) 

((dom(F) = A & cod(F) = B & cod(G) = A & dom(G) = C & cod(H) = C & dom(H) = D) => 
(
comp(id(B), F) = F &
comp(F, id(A)) = F &

cod(comp(F,G)) = cod(F) &
dom(comp(F,G)) = dom(G) &
comp(F,comp(G,H)) = comp(comp(F,G),H) 
)
)


).
cnf(noncollapse, axiom, junk != nonjunk).
```

How about this principle: We can unguard axioms that can never equate a well typed to an un well typed term.
