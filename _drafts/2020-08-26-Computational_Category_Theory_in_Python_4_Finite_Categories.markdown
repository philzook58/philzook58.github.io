---
author: philzook58
comments: true
date: 2020-08-26 16:47:00+00:00
layout: post
link: https://www.philipzucker.com/?p=2760
published: false
slug: 'Computational Category Theory in Python 4: Finite Categories'
title: 'Computational Category Theory in Python 4: Finite Categories'
wordpress_id: 2760
---




I find it always illuminating to try and find the most finite example of a mathematical concept I can. The infinite is a very weird place. It can be quite difficult to understand how to reason or compute on it, and surprising curveballs show up out of nowhere. Very often one can find examples where any possible question one could possibly ask is solvable by brute force.







Brute force is the master algorithm. British museum. Knowing how to brute force something is a starting point for more efficient methods. Want to solve sudoku? Well, in principle you can just try every combo of numbers and easily check that they are a sudoku answer.







I started with FinSet and FinVect because they are more applicable and probably more familiar. Have you ever come across the notion of a finite field? They are way simpler than the rational numbers in many ways and yet it isn't usually where we start teaching things. More niche application wise, less intuitive despite being simpler.







Finite categories are actually important and interesting in and of themselves too. Finite categories can encapsulate the notion of a diagram. When we draw a diagram, we're drawing a very finite example of something we expect to find inside a possibly quite large category. One can describe this within the framework of category theory as a functor going from the category that describes the diagram into the category in which you want to find examples of that diagram. Each individual functor will be another example of that diagram appearing in the target category.







Finite categories can also be used to encapsulate schema of databases.







  * Countermodels to things you think might be true
  * Diagrams
  * Indices into other categories






#### The Empty Category







The simplest number is zero, the simplest set is the empty set, and the simplest category is the category with no objects and no morphisms, the [empty category](https://ncatlab.org/nlab/show/empty+category)






    
    <code>from enum import Enum
    
    # https://ncatlab.org/nlab/show/empty+category
    class EmptyCat():
       objs = {}
       morphs = {}</code>







#### The Trivial Category







Ok, that was cute. Too simple though. What's the next rung up? A category with a single object. If we have an object, by the axioms of what it means to be a category, we have an identity arrow. So that's the next one. A sinlge Object with the identity arrow.







This is a general problem. We are always going to have an identity arrow for every object. 






    
    <code>@dataclass
    class Idd():
       obj
    
    class One():
       objs = { () }
       morphs = { Idd(()) }</code>







### Categories as Graphs







The mental python-category dictionary I've been building in the last couple posts is







  * Python Class ~ Category
  * Instance of class ~ Morphism of Category 






However, this is not the only way to encode categories. Abstract mathematical objects tend to have many equivalent ways of encoding them. I could encode the mathematical notion of the natural number 4 as the python integer 4, or as the list [(),(),(),()], or as an instance of a Natural python class, or as the [church numeral](https://en.wikipedia.org/wiki/Church_encoding) `lambda f: lambda x : f(f(f(f(x))))`







One nice structure available in python to use to encode a finite category is as a networkx graph. Networkx is the canonical python graph library. We can use a new dictionary.







  * NetworkX Graph ~ Category
  * NetworkX Vertex ~ Object of Category
  * NetworkX Edge ~ Morphism of Category












In addition, the graph structure is not sufficient to specify the category. It only lists the objects, morphisms, and the domain/codomain relationship between objects and morphisms. It does not specify composition. For that we in addition need a composition table from pairs of morphisms to their resulting morphism, which is akin to a multiplication table.







Note that not every possible Networkx graph will be capable of satisfing the axioms of a category. At minimum, there will always have to be edges pointing from a vertex to itself to be available as an identity morphism, and there will have to be a morphism available with the proper domain and codomain.













### One Object, Many Arrows: Monoids and Groups as categories







See previous post. However we can show an explicit group presented in the style we've chose







#### Many objects few arrows, Preorders







See previous post













#### Multi-Object Multi-Arrow







Graph







Span







Commuting Box







Schema













### Representation Choices







The correspondence that we're roughly developed in FinVect and FinSet is that a category is represented by a python class and an instance of that class has the data associated with a morphism in that category.  We may want to break away from that metaphor here. The main way of making data structures in python is the class system so we have to use it in other ways.







FinCat is not intended to be a category. It is a thing that when given data, produces a finite category. An instance of FinCat is a category.






    
    <code>class FinCat():
       def __init__(self, objs, morphs, cod_table, dom_table, comp_table ):
       def compose(self,f,g):
       def idd(self,obj):
           
       
       
    </code>







Presentations. A fairly general purpose way to describe an algebraic object like a group or ring is to describe it's generators and relations. For example, the group of the integers could be described at generated by (+1) (-1) (+0) with the relation (+1)(-1)=+0. Or the category of all paths in a graph could be described by it's edges.







A useful hack is to use identity morphisms to represent objects or objects to represent identity morphisms. Because of the axioms of a category, they are in a 1-1 correspondence with each other. Alternatively, we can use the objects to denote the identity morphisms on that object. Or we can wrap the object in Idd class. Pick your poison.







Using the python Enum class gives us so nice stuff. First off, it's a nice convention for finitely enumerable objects. Secondly, it gives us a built in iterator, so we can ask for all morphisms in a category easily.







The next simplest is the category with 1 object. It has to have an identity morphism, so we add this and nothing else.






    
    <code></code>







In addition, for finite algebraic structures, you can store a concrete multiplication table. Lookup tables are a very powerful technique and in fact can often be the best computational method to small sized problems, especially in embedded systems. See some cool examples at bit hacks [https://graphics.stanford.edu/~seander/bithacks.html](https://graphics.stanford.edu/~seander/bithacks.html) or in this talk [https://hackaday.com/2020/01/10/using-lookup-tables-to-make-the-impossible-possible/](https://hackaday.com/2020/01/10/using-lookup-tables-to-make-the-impossible-possible/)






    
    <code>times_table = {
       0 : {0 : 0, 1 : 0, 2 : 0 ... },
       1 : {0 : 0, 1 : 1, 2 : 2 ... },
       2 : {0 : 0, 1 : 2, 2 : 4, .. }
    }</code>







As a simple example, consider the symmettry group of a triangle. You can keep the triangle the same, rotate a triangle 120, 240, or flip it and rotate it. 







[https://en.wikipedia.org/wiki/Dihedral_group_of_order_6](https://en.wikipedia.org/wiki/Dihedral_group_of_order_6)



















Functors from a group to FinVect are finite dimensional representations







Functors from a group to FinSet are perumtation represenations (everything has to be invertible). Morphisms from a set to itself, such that every function is invertible. This functor does not have to exactly capture the group. It could have many copies of the group or subgroups. An example is that it could map to the 1-element set {()}. Every morphism maps to the identity morphism. The Cayley representation of a group is a mapping of the group into a permutation representation. The set it maps to is the set of all the morphisms of the group. Then the morphisms get mapped to a function that corresponds to right or left multiplication by that elements.







For example, the two morphism  group id, a,   a. a = id. Then the set we map the single object to is {id, a }. The morphism id maps to is {id : id, a : a} and the morphism a maps to is {id : a, a : id}.







An involution on a set 







### Presheaves







We can use a category as a pattern to look for in another. 







A transition system is a category that corresponds to the NatMonoid (PlusNatCat) being mapped into  . A reversible transition system PlusIntCat   







A DFA is indexed by a single object with mutiple arrows, one per symbol of the alphabet. The morphisms in the







[https://github.com/epatters/Catlab.jl/issues/154](https://github.com/epatters/Catlab.jl/issues/154) Interesting discussion here. So a discrte system takes Nat -> Functions.   Take R,+ to functions is too unconstrained. They should be smooth in the sense that the system is defined by a differential equation. 







Is this what is meant by a "lens" being an open dynamical system? That the index category has morphisms that correspond to S -> I, OxS -> S'  or the differential version?













This can also be considered a control system.







The trivial category mapping into FinSet is just a selecting a finite set in FinSet







Want to check that a circuit never does something bad? Give it every input.  There, you verified it.







Want to check that a numerical function is always ok? In principle, you can just try every floating point value through it. 







Want to find roots of a polynomial? Well, there are interesting things called finite fields. You can just goddamn try them all.







Ok, so we can see that we should be more clever in those situations. Brute force becomes unacceptable pretty fast.







An alternative







Presheaves and database scheme. A very small category serves as a pattern. A functor from this categroy is often called a presheaf. In particular, into set.







Computational Group Theory. Is concerned with solving problems related to  finitely presented groups.







#### Representation and the Finite Yoneda Lemma







The set $latex Hom(a,b)$ is defined to be the set of all morphisms from object a to object b. In a finite category this has to be a finite set. 







It turns out that we can use the machinery of FinSet we built in the first part of this series to represent this set and in fact reflect any finite category in it's entirety into FinSet. This fact is the finite Yoneda Lemma.







I like to think of the Yoneda lemma as a way of stating a mostly trivial observation. If you have a path from a to b,  You can also view it as a way of transforming paths from s to a to paths from s to b. This transformation is achieved by pasting your path at the end.













  * Monoids as Notions of Computation
  * Math3ma yoneda [https://www.math3ma.com/blog/the-yoneda-embedding](https://www.math3ma.com/blog/the-yoneda-embedding)
  * 

