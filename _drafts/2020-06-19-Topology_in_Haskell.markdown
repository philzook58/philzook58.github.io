---
author: philzook58
comments: true
date: 2020-06-19 15:54:38+00:00
layout: post
link: https://www.philipzucker.com/?p=2680
published: false
slug: Topology in Haskell
title: Topology in Haskell
wordpress_id: 2680
---




In order to do geometry on a computer you have to discretize it in some sense. One way of doing so is very familiar, you make meshes. Meshes are graph-like structures. They have vertices, edges, faces and so on. One way of  going about this is to give vertices arbitrary labels, consider edges as pairs of vertices, and faces as sets of edges. Then maybe we associated coordinates with the vertices and we can draw them.







Once you have this concrete structure in mind, we can ask questions about topology. Given a mesh, is it connected? Does it have holes like a donut? Are two meshes equivalent to each other in some sense? Is a path on the mesh "deformable" into another path? These clearly must be algorithmic questions we could define and ask about this finite discrete structure even isn't if it isn't immediately obvious how to do so.







One might try to build combinators for parametrized paths as functions. `type Path x = Double -> x`. Doubles are a stand in for the real numbers. You can manipulate functions like these and build new functions, but it's pretty hard to enforce and analyze such things however. What functions do can be pretty opaque.







Category theory is kind of a synthetic theory of paths. [https://www.youtube.com/watch?v=L4S-E85Dq4U&list=PL4FD0wu2mjWOtmhJsiVrCpzOAk42uhdz8&index=10](https://www.youtube.com/watch?v=L4S-E85Dq4U&list=PL4FD0wu2mjWOtmhJsiVrCpzOAk42uhdz8&index=10) [https://alhassy.github.io/PathCat/](https://alhassy.github.io/PathCat/)







If we have a data type that represents the Vertices






    
    <code>data Vertex = V0 | V1 | V2 | V3 | V4</code>







We can list the generating paths 






    
    <code>data Edge a b where
       E1 :: Edge 'V0 'V1
    
    data FreePath e a b where
       Compose :: FreePath e b c -> FreePath e a b -> FreePath e a c
       Id :: FreePath e a a
       Inv :: FreePath e b a -> FreePath e a b
       Pure :: e a b -> FreePath e a b
    -- These properties of paths make FreePath the same as a FreeGroupoid
    
    type FreeGroupoid = FreePath </code>







FreePath is a well-typed analog of a list of edges. We could also use an intrinsically right associated version of it, like we usually do with list.







FreePath should obey associativity of composition, the identity, and double inversion undoes it. This can be achieved in the Eq instance for the type







Being able to use GADTs and the category theory pattern actually feels pleasant here. While a weaker typed representation of paths would be [Vertex] or [Edge], this does not enforce that the path is actually built out of appropriately adjacent edges or vertices. This is exactly what the type system achieves for morphism composition.







Two paths are homotopically equivalent if they can be wiggled over into each other. In doing so, they are traversing over faces. These faces therefore are commuting ways of getting from a to b, which in turn is basically describing their boundary in terms of edges.







Homotopy type theory is from one perspective playing games with with equality, from the topology side I think it is a system for more shallowly embedding a design similar to the above into the language, allowing the compiler to more intrinsically understand these constructions.







Collapsing the groupoid of paths to a group is a functor. A group is a single object category where every arrow has an inverse.













Side idea: Homotopy via polynomial paths. You can describe a path on a sphere parametrzied by t. This lives in polynomial land. How can you use grobner bases?







Side idea: Can we encode homotopy to SAT? Is there a brute force algorithm on a finite simplex?



