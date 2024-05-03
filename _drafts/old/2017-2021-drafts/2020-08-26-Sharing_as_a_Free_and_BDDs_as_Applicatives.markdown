---
author: philzook58
comments: true
date: 2020-08-26 15:53:56+00:00
layout: post
link: https://www.philipzucker.com/?p=2923
published: false
slug: Sharing as a Free and BDDs as Applicatives
title: Sharing as a Free and BDDs as Applicatives
wordpress_id: 2923
---





https://youtu.be/RG3J1RQqwXU














Some Lean talkin about shared data structures. They mention this having a hash field inthe tree thing.








https://youtu.be/i9wgeX7e-nc?t=4144














Algebraic data types are perfect for describing trees. Absolutely gorgeous. However, there really are some data types that are graphs or DAGs.







There is some use in making a recursive type explicit by factoring out that fixed point in the same way one might factor out recursion from a factorial function.







Wren Ng Thornton has an interesting library where Fix is replaced by a version of Fix that can also achieve unification, (which is in some respects the dual of sharing? Am I full of shit?)







There is an interesting approach







Binary decision diagrams are a data structure for describing a boolean valued function of bools, or equivalently a set of bools.







The way one can describe sharing is somewhat obvious. In many languages you get access to references which are machine addresses of pieces of data, pointers. This is not very much in the Haskell style however.







You can sort of build your own machine independent pointer system by instead making it explicit you're using an IntMap for the indirections.







From a certain perspective and model, the shared and unshared version of a data structure are the same thing right? However, from an operational perspective they are vastly different.







Binary Decision Diagrams rely crucially on sharing. The sharing is the only thing that gives any hope that the data structure won't have 







If you can get a BDD in hand, and that is a big if, you can answer insane questions about the function. You can do all kinds of SAT finding, counting, and quantifier questions.







BDDs are constructed from a boolean formula by just interpreting the formula into a BDD. The sharing is found at every operation. This generic operation is called `apply` in the BDD world and in fact it corresponds to  an Applicative instance for the BDD data type.







BDDs are interesting from a functional programming perspective because they are a way of reifying functions as a data structure. Perhaps connections to representable functors.







There are also a wide class of BDD-like structures for which



