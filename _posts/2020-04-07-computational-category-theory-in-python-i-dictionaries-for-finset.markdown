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






```python
from collections import Counter
class FinSet():
    def init(self, dom ,cod , f):
        '''  In order to specify a morphism, we need to give a python set that is the domain, a python set 
        that is the codomain, and a dictionary f that encodes a function between these two sets.
        We could by assumption just use f.keys() implicitly as the domain, however the codomain is not inferable from just f.
        In other categories that domain might not be either, so we chose to require both symmettrically.
        '''
        assert( dom == set(f.keys())) # f has value for everything in domain
        assert( all( [y in cod for y in f.value()] )) # f has only values in codomain
        self.cod = cod
        self.dom = dom
        self.f = f
    def __getitem__(self,i):
        # a convenient overloading.
        return self.f[i]
    def compose(f,g):
        ''' Composition is function composition. Dictionary comprehension syntax for the win! '''
        return FinSet( g.dom, f.cod,  { x : f[g[x]]  for x in g.dom })
    def idd(dom):
        '''  The identity morphism on an object dom. A function mapping every x to itself'''
        return FinSet(dom, dom, { x : x for x in dom})
    def __equal__(f,g):
        assert(f.dom == g.dom) # I choose to say the question of equality only makes sense if the arrows are parallel.
        assert(f.cod == g.cod) # ie. they have the same object at head and tail
        return f.f == g.f
    def terminal(dom):
        ''' The terminal object is an object such that for any other object, there is a unique morphism 
        to the terminal object
        This function returns the object itself {()}  and the universal morphism from dom to that object'''
        return {()} , FinSet(dom, {()} ,  {x : () for x in dom} )
    def initial(cod):
        ''' The initial object is an object such that for any other object, there is a unique morphsm 
        from the initial object to that object.
        It is the dual of the terminal object.
        In FinSet, the initial object is the empty set set({}). The mapping is then an empty dictionary dict({})'''
        return set({}) , FinSet(set({}), cod, dict({}))
    def monic(self):
        ''' Returns bool of whether mapping is injective. 
            In other words, maps every incoming element to unique outgoing element.
            In other words, does `self @ g == self @ f`  imply  `g == f` forall g,f 
            https://en.wikipedia.org/wiki/Monomorphism
            Counter class counters occurences'''
        codomain_vals = self.f.values()
        counts = Counter(codomain_vals).values() # https://docs.python.org/3/library/collections.html#collections.Counter
        return all([count == 1 for count in counts]) # no elements map to same element
    def epic(self):
        ''' is mapping surjective? In other words does the image of the map f cover the entire codomain '''
        codomain_vals = self.f.keys() 
        return set(codomain_vals) == self.cod # cover the codomain
    def product(a,b): # takes a sepcific product
        ab = { (x,y) for x in a for y in b } 
        p1 = FinSet( ab, a, { (x,y) : x for (x,y) in ab } )
        p2 = FinSet( ab, b, { (x,y) : y for (x,y) in ab } )
        return ab, p1, p2 , lambda f,g: FinSet( f.dom, ab, { x : (f[x],g[x]) for x in f.dom  } ) # assert f.dom == g.dom, f.cod == a, g.cod == b
    def coproduct(a,b):
        ab = { (0,x) for x in a  }.union({ (1,y) for y in b  })
        i1 = FinSet( a, ab, { x : (0,x)  for x in a } )
        i2 = FinSet( b, ab, { y : (1,y)  for y in b } )
        def fanin(f,g):
            return { (tag,x) : (f[x] if tag == 0 else g[x]) for (tag,x) in ab }
        return ab, i1, i2, fanin
    def equalizer(f,g):
        ''' The equalizer is a construction that allows one to talk about the solution to an equation in a categorical manner
        An equation is f(x) = g(x). It has two mappings f and g that we want to somehow be the same. The solution to this equation
        should be a subset of the shared domain of f and g. Subsets are described from within FinSet by maps that map into the
        subset. 
        '''
        assert(f.dom == g.dom)
        assert(f.cod == g.cod)
        e = { x for x in f.dom if f[x] == g[x] }
        return e, FinSet(e, f.dom, {x : x for x in e})
    def pullback(f,g): # solutions to f(x) = g(y)
        assert(f.cod == g.cod)
        e = {(x,y) for x in f.dom for y in g.dom if f[x] == g[y]} # subset of (f.dom, g.dom) that solves equation
        p1 = FinSet( e, f.dom, { (x,y) : x for (x,y) in e } ) # projection 1
        p2 = FinSet( e, g.dom, { (x,y) : y for (x,y) in e } ) # projection 2
        
        def univ(q1,q2):
            ''' Universal property: Given any other commuting square of f @ q1 == g @ q2, there is a unique morphism
            that injects into e such that certain triangles commute. It's best to look at the diagram'''
            assert(q1.cod == p1.cod) # q1 points to the head of p1
            assert(q2.cod == p2.cod) # q2 points to the head of p2
            assert(q1.dom == q2.dom) # tails of q1 and q2 are the same
            assert(f @ q1 == g @ q2) # commuting square condition
            return FinSet( q1.dom, e ,  { z : ( q1[z] , q2[z] )    for z in q1.dom  }  )
        return e, p1, p2, univ  
```






Here's some fun exercises (Ok. Truth time. It's because I got lazy). Try to implement [exponential](https://en.wikipedia.org/wiki/Exponential_object) and [pushout](https://en.wikipedia.org/wiki/Pushout_(category_theory)) for this category.



