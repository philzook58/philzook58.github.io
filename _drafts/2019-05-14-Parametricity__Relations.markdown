---
author: philzook58
comments: true
date: 2019-05-14 15:01:50+00:00
layout: post
link: https://www.philipzucker.com/?p=1009
published: false
slug: Parametricity / Relations
title: Parametricity / Relations
wordpress_id: 1009
---

Relations

Profunctors as relations. Does consatrained profunctor help? Then there are so ort sets of type variables that can actually be in the profunctor. Not sure why I would want to guarantee that we can bimap?

Pandas?

I've been reading some of the work on the claculation of programs.

There is the textbook the Algebra of Programming by Bird and de Moor. Roland Backhouse seems to be a name strongly associated. J.N. oliveira has a textbook and some recent work

https://themattchan.com/docs/algprog.pdf

JN Oliveria program Design by calculation

http://www4.di.uminho.pt/~jno/ps/pdbc_part.pdf

Relations are a superset of functions.

Category theory is the abstract theory of functions.

"Allegories" and perhaps Topoi are the abstract theory of relations.

From a soft intuition perspective, it doesn't hurt much, or perhaps is better to rapidly shift between Set like, categorical, point-free and pointful thinking.

Specifications are often declarative, not functional or imperative. As in they don't have an immediately obvious calculation or constructive flavor. Usually they are a random bag of conditions that feel right, at least on first pass.

So the game is stating your requirement in a way that is relatively painless (allowing some magic) and then transforming it in a principled way to something that is executable.

Categorical/Functional constructs are too constructive by default.

Allegorical/Relational constructs might be the right wya to go

Prolog has the declarative feel

Point-free languages side step the infinite pain of variables and binding, which from a toy language or perhaps IR perspective is very inviting.

Upon first learning of how to use typeclasses for programming, I was told it is typelevel prolog. This is correct in the sense that there does not have to be an input out output character to the parameters, but incorrect in the sense that prolog is strongly associated with backtracking search in my mind, of which the typeclass resolution mechanism has none.

Multiparameter typeclasses can be faked using tuples.

We can use typeclasses as a search mechanism using Lists of results.

Relational programming

https://en.wikipedia.org/wiki/Relational_algebra

the relational algebra is taught as a mathemtical model for relational databases. The intent there is that the relations are finite

The Relation Algebra is an algerba fro mathemtics.

type Rel a b = Set (a,b)

type Rel1 = a -> Set b

type Rel2 = {a -> Set b, b -> Set a}

What is the the point?

Free Theorems

Why would you even conceive of using relations

Relations are sets of tuples {(a,b)}.

Composition of  relations is given by A\cdot B = {(a,c) | \exists b (a,b) \in A, (a,b') \in B,  }

This is a generalization of composition for functions. For functions, the b that exists is given by evaluating A.

Relations also inherit intersection, union, and inclusion since they are sets.

The way this is discussed has a very category theory flavor. It is defined as universal properties.

X \subset A \and B \equiv X \subset A and X \subset B

Composition is given by the joins of databases.

Most of these operations have a very simple implementation using list comprehensions.



* * *



Old 3/8/18

I have found parametricity theorems very confusing (theorems for free)

I think that paramtricity is a system for taking assumed conclusions about inputs to a function and inferring conclusions about the outputs

for example, suppose I have x < x'. And then I apply the parametric function forall a. a -> a to both a and a', do i get a conclusion about the output y and y'?

Yes, y < y'

Alright. We know by rote that is id. So it returns x and x'. and then x is still < x'.

what is x = x'? Again, we can pull that relationship through.

What if x' = show x? Then the result is still the y' = show y. Like if

data Color = Blue | Red

show Blue = "blue"

show Red = "red"

and so on for all the relationships we can cook up.

Relations mathematically can be described as ordered pairs (x,y) from two sets X and Y. In most of my cases X=Y. But in the last case Y = String and X is some Showable set.

The free theorem system is a way to recursively deconstruct the type of the expression and find out what relationships get pulled through.

forall a. a -> a -> a

What can this do?

We get that if x < x', and y < y' then f x y < f x' y'. Which is true since it can only pick the first or second. similarly if we use show. x' = show x, y' = show y then show (f x y) = f x' y'.

let's suppose we hand it x in a relationship with x' and y in a relationship with y'.

Paramtrcitiy says that we can use two sets themselves in some kind of realtionship. Like A is a subset of A' is a relationship. Or A = A' is a relationship

or A and the subset of String that holds the string reps of A.

We only have the freedom to choose the relationship when it is a universalized type variable.

Paramatrized type variables can only be rearranged, duplicated, and dropped, intuitively. This relation mechanism is a way to talk about that without explicitly mentioning shapes. Two things that are a in a relationship and then rearranged in exactly the same way will stay in that relationship. Or if you apply the same function to them both, however the intial relationship going into the function is transfromed into some new realtionship, they have the be transfromed at the same time in the same way.

I think < is a verty useful relationship because function relations and equality relations already have notation in the thing we're talking about, so it is very easy to get confused.

For functions types two functions are related if they map related values into related values

For example if x < x' then f' x' < f x then f and f' are related. In particular this means that

f :: * -> * is a higher kinded type.

What it does in terms of relations is it converts one relation into another. Maybe it converts < to > for example. Or it converts . It is sort of some kind of relation function (which is a subset of relations of relations). If we quantify over f though we cannot assume any particular form of f. The theorem will work for all f.

Its a category where the Objects are relations. and the morphisms are relation functions.

The subcategory where the relation function satisfiy the Functor constraint is Cat. Where objects are categories and Functors are the morphisms

So it seems to be the idea is to not talk about shapes but relations between the objects in them.

WHy can't we formalize the notion of "what else could you do" or hidden information about the type?
