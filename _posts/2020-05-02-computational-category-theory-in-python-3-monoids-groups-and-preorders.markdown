---
author: philzook58
comments: true
date: 2020-05-02 14:36:29+00:00
layout: post
link: https://www.philipzucker.com/computational-category-theory-in-python-3-monoids-groups-and-preorders/
slug: computational-category-theory-in-python-3-monoids-groups-and-preorders
title: 'Computational Category Theory in Python III: Monoids, Groups, and Preorders'
wordpress_id: 2764
categories:
- Formal Methods
tags:
- categorytheory
- python
---




_Parts 1 and 2 are found [here](http://www.philipzucker.com/computational-category-theory-in-python-i-dictionaries-for-finset/) and [here](http://www.philipzucker.com/computational-category-theory-in-python-ii-numpy-for-finvect/)_







From one perspective, categories are just another algebraic structure, like [groups](https://en.wikipedia.org/wiki/Group_(mathematics)), [monoids](https://en.wikipedia.org/wiki/Monoid) and [rings](https://en.wikipedia.org/wiki/Ring_(mathematics)). They are these abstract things that have some abstract equational axioms and operations.  They are the next stop on our magnificent category journey.







![](/assets/monoidjourney-640x1024.png)







A monoid is a thing that has an associative operation with a unit. Addition and 0 make numbers a monoid. Multiplication and 1 are a separate monoid for numbers. Concatenation and empty lists make lists a monoid. Union and empty set make sets a monoid. We can encode this in python like so:






```python
class PlusIntMonoid(int):
    def mplus(self,b):
        return self + b
    def mzero():
        return 0

class TimesIntMonoid(int):
    def mplus(self,b):
        return self * b
    def mzero():
        return 1

class ListMonoid(list):
    def mplus(self,b):
        return self + b
    def mzero():
        return []

class UnionMonoid(set):
    def mplus(self,b):
        return self.union(b)
    def mzero():
        return set()

ListMonoid([1,2]).mplus(ListMonoid([1,2])) # [1,2,1,2]
UnionMonoid({1,2}).mplus(UnionMonoid({1,4})) # {1,2,4}
TimesIntMonoid(3).mplus(TimesIntMonoid.mzero()) # 3
```






What does this have to do with categories? Well, if some thing is a category, it obeys the axioms that define what it means to be a category. It has morphisms and objects. The morphisms compose if head meets tail on an object. There are always identity morphism.







The morphisms in a category with 1 object automatically obey the monoid axioms. In this case, the category axioms imply the monoid axioms. Everything composes because there is only one object. It's a kind of degenerate case where we are not using the partiality of the composition operator. There is automatically a unit for composition because the identity morphism is a unit. Composition is already required to be associative. Boom. The thing is a monoid.







Continuing with our representation from [previous](http://www.philipzucker.com/computational-category-theory-in-python-i-dictionaries-for-finset/) [posts](http://www.philipzucker.com/computational-category-theory-in-python-ii-numpy-for-finvect/), we make a python class for each category. An instance of this class is a morphism in this category. If you ask for the domain or codomain of any morphism, you always get back `()` because it is a single object category. Compare these classes with the above classes.






```python
class PlusIntCat(int):
    def compose(self,b):
        return self + b
    def idd():
        return 0
    def dom(self):
        return () # always return (), the only object
    def cod(self):
        return ()

class TimesIntCat(int):
    def compose(self,b):
        return self * b
    def idd():
        return 1
    def dom(self):
        return ()
    def cod(self):
        return ()

class ListCat(int):
    def compose(self,b):
        return self + b
    def idd():
        return []
    def dom(self):
        return ()
    def cod(self):
        return ()

class UnionSetCat(set):
    def compose(self,b):
        return self.union(b)
    def idd(self,b):
        return set()
    def dom(self):
        return ()
    def cod(self):
        return ()
    
PlusIntCat(3).compose(PlusIntCat.idd()) # 3
```






Some monoids are also groups if there is a natural inverse operation. The integers are a group under addition where the negative gives you the inverse. Some aren't though. The natural numbers (0,1,2...) aren't a group under addition though.







Similarly groups can be thought of as a category with one object, with the additional requirement that every morphism is invertible, that there is always a $ f^{-1}$ such that  $  f \circ f^{-1} = id$.







Sympy [has groups](https://docs.sympy.org/latest/modules/combinatorics/index.html) in it. We can make a wrapper of that functionality that looks like a categorical interface. To match our pattern of using python classes to represent categories, it is convenient to do the [slightly uncommon](https://www.python-course.eu/python3_classes_and_type.php) thing of making a class definition generator function `fp_group_cat`. Every time you call this function, it makes a different class and a different category. I have only here wrapped the finitely presented group functionality, but there are also free groups, permutation groups, and named groups available in sympy.






```python
from sympy.combinatorics.free_groups import free_group, vfree_group, xfree_group
from sympy.combinatorics.fp_groups import FpGroup, CosetTable, coset_enumeration_r


def fp_group_cat(G, catname):
    # A Category generator that turns a finitely presented group into categorical python class
    Cat = type(catname, (), vars(G))
    def cat_init(self,a):
        self.f = a
    Cat.__init__ = cat_init
    Cat.compose = lambda self,b : G.reduce(self.f * b.f)
    Cat.dom = lambda : ()
    Cat.cod = lambda : ()
    Cat.idd = lambda : Cat(G.identity)
    return Cat

F, a, b = free_group("a, b")
G = FpGroup(F, [a**2, b**3, (a*b)**4])
MyCat = fp_group_cat(G, "MyCat")
MyCat(a*a).compose(MyCat.idd())
MyCat.dom()
```






#### Many objects, at most one arrow per pair: Preorders







We can simplify the power of a category in a different direction. Instead of having only 1 object, we'll have few arrows. 







A category with many objects but at most a single morphism between a pair of them obeys the axioms of a [preorder](https://en.wikipedia.org/wiki/Preorder). In categorical terminology this is sometimes called a [thin category](https://en.wikipedia.org/wiki/Posetal_category) Any actual order like like $ \le$ on numbers is also a preorder, but preorders have slightly weaker requirements. Here is a categorical representation of the ordering on integers (although really the same implementation will work for any python type that implements <= and == )






```python
class IntOrderCat():
    def __init__(self, dom, cod):
        assert(dom <= cod)
        self.cod = cod
        self.dom = dom
        self.f = ()
    def idd(n):
        return IntOrderCat(n,n)
    def compose(f,g):
        assert( f.dom == g.cod )
        return IntOrderCat( g.dom, f.cod )
    def __repr__(self):
        return f"[{self.dom} <= {self.cod}]"
    
# our convention for the order of composition feels counterintuitive here.
IntOrderCat(3,5).compose(IntOrderCat(2,3)) # [2 <= 5]
IntOrderCat.idd(3) # [3 <= 3]
```






An example of a partial order is the subset relationship, which we can represent using python sets. This is an important but perhaps confusing example. Haven't we already defined FinSet? Yes, but these are different categories. In FinSet, morphisms are functions. In SubSetCat a morphisms is the subset relationship (of which there can either be one or not one). They just plain are not the same thing even though there are sets in the mix for both. The situation is made even more confusing by the fact that the subset relationship can be talked about indirectly inside FinSet using monic morphisms, which have as their image the subset of interest.






```python
class SubSetCat():
    def __init__(self,dom,cod):
        assert( dom.issubset(cod))
        self.cod = cod
        self.dom = dom
    def compose(f,g):
        assert(f.dom == g.cod)
        return SubSetCat(g.dom, f.cod)
    def idd(s):
        return SubSetCat(s,s)
    def __repr__(self):
        return f"[{self.dom} <= {self.cod}]"

SubSetCat(  {1,2,3} , {1,2,3,7} ).compose(SubSetCat( {1,2} , {1,2,3} )) # [{1, 2} <= {1, 2, 3, 7}]
```






Preorders are related to directed acyclic graphs (DAG), the directed graphs that have no loops.  If you give me a DAG, there is a preorder that is generated by that DAG.  Exercise for the reader (AKA I'm lazy): Can you turn a Networkx DAG into a category?







### Thoughts







This is nice and all just to explain categories in terms of some perhaps more familiar concepts. It feels a little ho-hum to me. We are not getting really any benefit from the concept of a category from this post. However, the examples of monoids, groups and preorders are always something you should think about when presented when a new categorical concept, because it probably reduces to something more familiar in this case. In addition, mappings to/from these simple objects to more complicated categories can be very interesting.







The methods of computational group theory are intriguing. It seems like some of them should extend to category theory. See this book by RFC Walters for example [https://www.cambridge.org/core/books/categories-and-computer-science/203EBBEE29BEADB035C9DD80191E67B1](https://www.cambridge.org/core/books/categories-and-computer-science/203EBBEE29BEADB035C9DD80191E67B1) A very interesting book in other ways too. (Thanks to Evan Patterson for the tip)







Next time I think we'll talk about finite categories and the finite Yoneda lemma. 







Artwork courtesy of [David](https://davidtersegno.wordpress.com/)







Edit: Hacker News discussion: [https://news.ycombinator.com/item?id=23058551](https://news.ycombinator.com/item?id=23058551)



