---
author: philzook58
comments: true
date: 2020-04-07 03:40:41+00:00
layout: post
link: https://www.philipzucker.com/computational-category-theory-in-python-i-dictionaries-for-finset/
slug: computational-category-theory-in-python-i-dictionaries-for-finset
title: 'Computational Category Theory in Python I: Dictionaries for FinSet'
wordpress_id: 2730
categories:
- Formal Methods
tags:
- categorytheory
- python
---




[Category theory](https://en.wikipedia.org/wiki/Category_theory) is a mathematical theory with reputation for being very abstract. 







Category theory is an algebraic theory of functions. It has the flavor of connecting up little pipes and ports that is reminiscent of dataflow languages or circuits, but with some hearty mathematical underpinnings.







So is this really applicable to programming at all? Yes, I think so.







Here's one argument. Libraries present an interface to their users. One of the measures of the goodness or badness of an interface is how often you are inclined to peek under the hood to get it to do the thing that you need. Designing these interfaces is hard. Category theory has taken off as a field because it has been found to be a useful and uniform interface to a surprising variety of very different mathematics. I submit that it is at least _plausible_ that software interfaces designed with tasteful mimicry of category theory may achieve similar uniformity across disparate software domains. This is epitomized for me in Conal Elliott's Compiling to Categories. [http://conal.net/papers/compiling-to-categories/](http://conal.net/papers/compiling-to-categories/)







I think it is easy to have the miscomprehension that a fancy language like Haskell or Agda is necessary to even begin writing software that encapsulates category theory based ideas, but this is simply not the case. I've been under this misapprehension before. 







It just so happens that category theory is _especially useful_ in those languages for explaining some programming patterns especially those concerning polymorphism. See Bartosz Milewski's [Category theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/). 







But this is not the only way to use category theory.







There's a really delightful book by Rydeheard and Burstall called [Computational Category Theory](http://www.cs.man.ac.uk/~david/categories/book/book.pdf). The first time I looked at it, I couldn't make heads or tails of it, going on the double uphill battle of category theory and Standard ML. But looking at it now, it seems extremely straightforward and well presented. It's a cookbook of how to build category theoretic interfaces for software.







So I think it is interesting to perform some translation of its concepts and style into python, the lingua franca of computing today.







In particular, there is a dual opportunity to both build a unified interface between some of the most commonly used powerful libraries in the python ecosystem and also use these implementations to help explain categorical concepts in concrete detail. I hope to have the attention span to do this following:







  * Numpy - Let's compute a pullback in FinVect!
  * Pandas - There are couple different options here. [Relation Algebra](http://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/) or The Spivak [Categorical Databases crew ](http://www.appliedcategorytheory.org/wp-content/uploads/2018/03/Ryan-Wisnesky-Categorical-Databases.pdf)
  * Sympy - The category of substition into terms as mentioned in R&B. Also in this [very excellent paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.48.3615).  Also [modules](https://en.wikipedia.org/wiki/Module_(mathematics))
  * [Z3py](https://github.com/philzook58/z3_tutorial_2020/blob/master/Z3%20Tutorial.ipynb) - Categorical Logic
  * Networkx - Graph stuff. Surely got some categories there
  * [Hypothesis](https://hypothesis.readthedocs.io/en/latest/) - Property based testing of universal properties






A very simple category is that of [finite sets](https://en.wikipedia.org/wiki/FinSet). The objects in the category can be represented by python sets. The morphisms can be represented by python dictionaries. Nothing abstract here. We can rip and tear these things apart any which way we please. 







The manipulations are made even more pleasant by the python features of set and dictionary comprehension which will mimic the definitions you'll find on the wikipedia page for these constructions quite nicely.







Composition is defined as making a new dictionary by feeding the output of the first dictionary into the second. The identity dictionary over a set is one that has the same values as keys. The definition of products and coproducts (disjoint union) are probably not too surprising.







One really interesting thing about the Rydeheard and Burstall presentation is noticing what are the inputs to these constructions and what are the outputs. Do you need to hand it objects? morphisms? How many? How can we represent the universal property? We do so by outputting functions that _construct_ the required universal morphisms. They describe this is a kind of [skolemization ](https://en.wikipedia.org/wiki/Skolem_normal_form). The constructive programmatic presentation of the things is incredibly helpful to my understanding, and I hope it is to yours as well.







Here is a python class for FinSet. I've implemented a couple of interesting constructions, such as pullbacks and detecting monomorphisms and epimorphisms.







I'm launching you into the a deep end here if you have never seen category theory before (although goddamn does it get deeper). Do not be surprised if this doesn't make that much sense. Try reading Rydeheard and Burstall chapter 3 and 4 first or other resources.





[gist https://gist.github.com/philzook58/b50720436e45a134bab2976c4c04b46e#file-finset-py]





Here's some fun exercises (Ok. Truth time. It's because I got lazy). Try to implement [exponential](https://en.wikipedia.org/wiki/Exponential_object) and [pushout](https://en.wikipedia.org/wiki/Pushout_(category_theory)) for this category.



