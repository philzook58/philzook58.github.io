---
layout: post
title: Category Theory
---

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

https://en.wikipedia.org/wiki/Partially_ordered_set
## FinSet
Finite sets as objects, finite maps (dicitonaries) as morphisms

Can also consider partial finite maps.
## FinVect
vector spaces are objects (dimensionality or labelled). Linear maps are morphisms (~ matrices)
## FinRel
## LinRel



# Encodings
Encoding category theory to first order, higher order logic, and dependent type theory. Generalized algebraic theories.

Relational Composition
comp(F,G,H)

Comp as Partial function
comp(F,G) = Some(H)

Objects as Sort

Blog posts
-  Egglog 2: Automatically Proving the Pullback of a Monic is Monic https://www.philipzucker.com/egglog2-monic/
- Egglog Examples: Pullbacks, SKI, Lists, and Arithmetic https://www.philipzucker.com/egglog-3/
- [ Rewriting Monoidal Categories in the Browser with Egg](https://www.philipzucker.com/rust-category/)
# Diagram Chasing

# Functors
Functors are mappings between categories. This means they are a  tuple of map from objects to objects and morphism to morphism such that composition plays nice (commutes sort of) 
Functors are mappings between categories (a object to object map and morphism to morphism map) that plays nice with composition and identity. F(id) = id. F(f.g) = F(f) . F(g)

F = (Fo, Fm)
Fm(f . g) = Fm(f) . Fm(g)


Representations of groups. Functor from group as a category to 

## Adjunctions
Free/Forgetful

Galois Connections. Abstraction and concretization
Abstract interpretation
Intervals <-> sets
polytopes 
convexsets <-> sets



# Natural Transformations

# Monoidal Categories
Vect



# String Diagrams


# Topos

https://twitter.com/johncarlosbaez/status/1461346819963686920?s=20 John Baez

Use functions instead of a notion of element being member of set.
functions can essentially select elements.
functions into "truth value" set (indicator functions) are analogs of subsets.

# Processes
Time

# Categorical Databases
schema is a finite category
Data lives over it
Mappings between schema describe 

# Sheaves

# Logic


Rising Sea

A proof of `A |- B` is the basic "morphism". A proof is a tree. We can perhaps annotated this sequent with free variables and unification variables in play (signature). This makes this morphism floating over some kind of variable set, something sheafy.
Objects are propositions.
Cut is compose.
Axiom is id.
Different proofs are different morphisms between the same objects.
Existentials and universals as adjunctions



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

