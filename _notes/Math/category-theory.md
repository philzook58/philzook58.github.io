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
- [Processes](#processes)
- [Categorical Databases](#categorical-databases)
- [Sheaves](#sheaves)
- [Profunctors](#profunctors)
- [Optics](#optics)
- [Logic](#logic)
- [Computational Category Theory](#computational-category-theory)
- [Internal Language](#internal-language)
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

Use functions instead of a notion of element being member of set.
functions can essentially select elements.
functions into "truth value" set (indicator functions) are analogs of subsets.

<https://jonsterling.notion.site/Topoi-inside-and-out-7b0b86e39eeb43aeaee3c3af1dd91f2a> jon sterling blog post

To say something is a topos is to say it is

1. a category
2. a special category with some special constructs

Weird notions of truth value are fun.

# Processes

Time

# Categorical Databases

schema is a finite category
Data lives over it
Mappings between schema describe

# Sheaves

# Profunctors

# Optics

# Logic

Rising Sea

A proof of `A |- B` is the basic "morphism". A proof is a tree. We can perhaps annotated this sequent with free variables and unification variables in play (signature). This makes this morphism floating over some kind of variable set, something sheafy? Or a set floats of variables floats over the proof

- Objects are propositions.
- Cut is compose.
- Axiom is id.
- Existentials and universals as adjunctions
  Different proofs are different morphisms between the same objects.

# Computational Category Theory

- [Computational Category Theory](https://www.cs.man.ac.uk/~david/categories/book/book.pdf)
- [evan patterson](https://www.epatters.org/wiki/algebra/computational-category-theory.html)

[hey I got on hacker news](https://news.ycombinator.com/item?id=23058551)

[catlab.jl](https://www.algebraicjulia.org/)

homotopy.io
globular
dicopy
cartographer

From a programming perspective I think there are a couple contributions:

- Category theory has a number of very intuitive looking graphical notations which nevertheless translate to very exact algebraic expressions. This is pretty dang nice. Category theory is a road to a very principled formulation of things that are already done in dataflow languages, tensor diagrams, and UML and things like that. These graphical languages are a reasonable user facing interface.

- Empirically in mathematics, category theory has been found to be a flexible and "simple" language to describe and interconnect very disparate things. In programming terms that means that it is a plausible source of inspiration for consistent interfaces that can do the same.

- Point free DSLs are really nice to work with as library/compiler writer. It makes optimizations way easier to recognize and implement correctly. Named references are phantom links attaching different points in a syntax tree and make it hard to manipulate them correctly. In slightly different (and vague) terms, category theory gives a methodology to turn abstract syntax graphs into trees by making all links very explicit.

I can't comment much on what category theory contributes to mathematics, but I think there are similar points. I think category theory can make precise analogies between extremely disparate fields like logic, set theory, and linear algebra. I think categorical intuitions lead to clean definitions when specialized to some particular field. Combinatory categorical logic does make some aspects of logic less spooky.

# Internal Language

What is this? Cody talks about this a lot.

# Resources

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
