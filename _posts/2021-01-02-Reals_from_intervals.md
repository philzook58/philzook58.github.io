---
author: Philip Zucker
date: 2021-01-02
layout: post
categories:
- Formal Methods
tags:
- python
title: Sketchy Exact Reals from Interval Arithmetic
---

Exact reals are cool.

I've got piles of stuff to say, and there are tendrils that lead off in so many directions that I only cloudily understand, but it's nice to rip off a manageable chunk here.

Any system that allows for arbitrarily accurate calculations of a number can be considered a system of exact reals.

That means the object that represents the "real number" must not be just a pile of dead data like a float. It has to somehow be able to receive instruction about the precision required and then output the desired answer. There are different representation choices for this that may be natural depending on the facilities of your language and tastes.

One that is very natural to me though is to represent such a thing as a function that takes in a precision request and outputs something like a number `Precision -> Number`. This precision could be an integer specifying the number of digits of precision, and the Number could be a rational (a numerator and denominator) or some kind of arbitrary precision float data type from a library like MPFR, or perhaps an interval of these things.

How is an exact real different from an interval data type? This something I've wondered about. They do seem awfully similar. Well, I think I have a way to make an nonperformant exact real library from an interval library with a precision knob.

Here for example is an exact real in python that uses the [mpmath](https://mpmath.org/) library for all the heavy lifting. `mpmath` has an interval type which is controlled by a global variable `dps` holding digits of precision. By placing the computation of the interval into a thunk, we can compute an answer over and over at increasing precision. Even though you don't have to explicilty pass it, this global `dps` parameter can be thought of as a precision parameter to these thunked functions. The result of the thunk at each evaluation depends on it's current value.

```python
from mpmath import iv
from typing import Callable
import operator as op

# type definitions
interval = mpmath.ctx_iv.ivmpf
# thunked intervals that use dps ~ reals
real = Callable[[], interval]


# lifts a one argument interval function to a one argument thunked interval function
def lift(f : Callable[[interval], interval]) -> Callable[[real], real]:
    def res(x : real) -> real:
        return lambda : f(x())  
    return res

# lifts a one argument interval function to a one argument thunked interval function
def lift2(f : Callable[[interval, interval], interval]) -> Callable[[real, real], real]:
    def res(x : real, y: real) -> real:
        return lambda : f(x(), y())  
    return res

def const(x : str) -> real:
    return lambda : iv.mpf(x)

# some simple lifts of mpmath functions
rsin = lift(iv.sin)
rcos = lift(iv.cos)
rexp = lift(iv.exp)
rlog = lift(iv.log)
rneg = lift(op.neg)
radd = lift2(op.add)
rmul = lift2(op.mul)


# a random example calculation
third = const("1/3")
v = rmul( rexp( third) , rlog(third))

for i in range(10):
    iv.dps = i
    print(v())
'''
[-2.0, -1.0]
[-1.5625, -1.48438]
[-1.537109, -1.529297]
[-1.5339355, -1.5327148]
[-1.53326416, -1.53320313]
[-1.533239365, -1.533231735]
[-1.5332376957, -1.5332362652]
[-1.53323698044, -1.53323693573]
[-1.533236963674, -1.533236958086]
[-1.5332369611133, -1.5332369599491]
'''
```

If you want nice python operator overloading, it wouldn't be so difficult to wrap this thunk in a simple `Real` or `Refinable` wrapper class.

A different representation that might feel more natural is a stream of increasingly better answers. These two representations are basically equivalent. I can create a stream (a python generator in this case) from the function by applying it to a stream of precisions and a function from a stream by getting the nth element of the stream.

```python
def streamify(f : Callable[[precision],number]) -> Iterator[number]
    def res():
        n = 0
        while True:
            n += 1
            yield f(n)
    return res

def funcify(s : Iterator[number]) -> Callable[[precision],number]):
    def res(n):
        return s()[n]
    return res
```

The only functions that play nice with a notion of arbitrarily refinable calculation are continuous functions. If you have a discontinuity, then an arbitrarily small width interval input can create a finite width interval in the output, which breaks the contract of what the real is supposed to do. It is no longer an arbitrarily refinable number and the shell game we're playing where we pretend the intervals somehow are converging to a number go out the window.

### Predicates and Belnap Bools

So that's all cool, but what really gets me going is to start considering predicates on the real numbers and boolean operations. One representation of a decidable predicate for a computer's purposes is a function that takes in the object and gives you a boolean of the property holds on the object or not. 

But here is an example that calls for a richer notion of truth than just booleans.

Extending what you accept as a notion of truth is very similar to extending what you consider a notion of number.
The only actual numbers are the counting numbers. I do kind of believe that notions of truth = {true, false} is a fairly natural notion, more natural in some sense than others.  And yet, one can develop intuition and comfort with the truly bizarre concept of a complex number $a + ib$ and treat it the same or analogous to counting numbers for a restricted set of algebraic manipulations.
And these other notions of truth obey similar algebraic manipulations or notions of proof, typically just more restricted in some way. Doing quantum mechanics with the naturals would suck (if possible).

The `mpmath` library when you ask questions about intervals like `i1 < i2` operates under a three-valued logic. If the question is definitely true for every element in the intervals, it output `True`, definitely false it outputs `False`, but if there is overlap of the intervals it outputs `None` representing a "I'm not sure".

So intervals behave under a kind of [three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic). There actually is a default value `missing` in [Julia](https://docs.julialang.org/en/v1/manual/missing/) that behaves in this way, and it is also not an unknown conept in the context of databases with missing entries. This three-valued logic I'm going to call the Belnap booleans (I think this may be slightly inaccurate. The Belnap booleans are a four valued logic. )

For our use case, the `None` means "you need to refine the precision more to find out".

The refinables add an extra layer on this. The truth value used by predicates over exact reals is not a boolean, not is it even the three-valued logic of intervals. Instead it is a refinable three-valued logic.

The dependence of the interval on the precision is monotonic. If we increase the precision, the new interval must be a subset of the interval at less precision in order for everything to bve behaving consistently.  Similarly, these truth values can only increase in information. In some sense `None` represents a value of less information than the value `True` or `False`. As the computation gets refined the information content should only go up.

Through an accident of the short circuiting mechanism and falsity of `None` in python, the standard operations `and` and `or` are close to what we want for the Belnap booleans

```python
x = [True, False, None]
for i in x:
    for j in x:
        print( f"{i} or {j} = {i or j}" )
'''
True or True = True
True or False = True
True or None = True
False or True = True
False or False = False
False or None = None
None or True = True
None or False = False
None or None = None
'''

for i in x:
    for j in x:
        print( f"{i} and {j} = {i and j}" )
'''
True and True = True
True and False = False
True and None = None
False and True = False
False and False = False
False and None = False
None and True = None
None and False = None
None and None = None
'''

```

The one case that doesn't work is `(None,False)` in both cases. For `belor` we want `belor(None,False) = None` because it is not yet known what the truth value is. If the `None` refines to `True` it should be `True` but if `None` refines to `False` it should be `False`. Similarly we want `beland(None,False) = False` since we already know that regardless of the refinement value of `None`, the already known `False` kills it.
So we can just catch these two cases and fix them.

```python
belnap = Optional[bool]

def belor(x : belnap, y : belnap) -> belnap:
    if x == None and y == False:
        return None
    return x or y

def beland(x : belnap, y : belnap) -> belnap:
    if x == None and y == False:
        return False
    return x and y

def belnot(x : belnap) -> belnap:
    if x == None:
        return None
    return not x

```

These belnap operations can be lifted to refinable belnaps. The prefix "r" stands for "refinable". As the precision is increased, we can turn from unsure `None` values to certain `True/False` values.

```python
rbelnap = Callable[[], belnap]

# no actually. We actually need truth tables.
rnot = lift(belnot)
ror = lift2(belor)
rand = lift(beland)

# lifts a one argument interval function to a one argument thunked interval function
def lift2(f : Callable[[interval, interval], Optional[bool]]) -> Callable[[real, real], belnap]:
    def res(x : real, y: real) -> belnap:
        return lambda : f(x(), y())  
    return res


rlt = lift2(op.lt)
rgt = lift2(op.gt)
rne = lift2(op.ne)

# equality total poison. Do not use these. Uh... Wait. No just as good as inequality.
req = lift2(op.eq)
rge = lift2(op.ge)
rle = lift2(op.le)

third = const("1/3")
thirdish = const("0.3333")
v = rgt(third, thirdish)
for i in range(10):
    iv.dps = i
    print(f"Precision {i}: {v()}")
'''
Precision 0: None
Precision 1: None
Precision 2: None
Precision 3: None
Precision 4: True
Precision 5: True
Precision 6: True
Precision 7: True
Precision 8: True
Precision 9: True
'''
```

### Quantifiers

This section is a little sketchy. 

We can actually implement semidecision procedures for predicates represented as block box predicates.
Basically, the reals are searchable by making iteratively refined interval partitions. We can build a generator that builds a partition of the interval $$[0,1]$$ at the current precision level.

```python
def partition(): #paving?
    d = 10**iv.dps # denominator = number of partitions
    for i in range(d):
        yield iv.mpf( [f"{i}/{d}" , f"{i+1}/{d}" ])
```

Then we can use that to implement the `find` quantifier, which is a slightly less familiar one. `find` takes a predicate and returns not a truth value, but the actual value for which the predicate evaluates to true or any arbitrary element if none exists. Sometimes `find` is called the [Hilbert epsilon](https://en.wikipedia.org/wiki/Epsilon_calculus) and you'll find it in TLA+ as [`CHOOSE`](https://learntla.com/tla/sets/#choose) for example.

One can implement the other quantifiers `exists` and `forall` (perhaps with some inefficiency) in terms of `find`.

Note that `find` as I've built it here is not correctly obeying the refinement condition of the reals. I've done something wrong.

```python
predicate = Callable[[real], rbelnap]

def find( f : predicate ) -> real:
    def res():
        for i in partition():
            test = f(lambda : i)()
            if test == True:
                return i
        return iv.mpf(["0","1"]) # should we be more careful here?
    return res

def exists(f):
    return f(find(f))
def forall(f):
    return rnot( find( lambda x: rnot(f(x)) ) )

v = find( lambda x: rgt( rmul(x,x),  const("1/4")) )
#v = forall( lambda x: rgt( rmul(x,x),  const("1/4")) )
#v = exists( lambda x: rgt( rmul(x,x),  const("1/4")) )
for i in range(5):
    iv.dps = i
    print(f"Precision {i}: {v()}")
'''
Precision 0: [0.625, 0.875]
Precision 1: [0.59375, 0.703125]
Precision 2: [0.5097656, 0.5205078]
Precision 3: [0.50097656, 0.5020752]
Precision 4: [0.500099182, 0.500205994]
'''

```

Trying to write this made me miss types.


### Bits and Bobbles

- There's something to the notion of using semi intervals, intervals where one half lies at infinity. Regular intervals can be constructed out of them. There is this notion of Sierpinski space that the Marshall works use but I didn't find natural in the presentation above. Maybe using semi-intervals would make that more apparent.

- There are other formulations of exact reals that store a computation graph. This may be related in some sense, as the thunks are storing a hidden computation graph.

- Using python-flint bindings to Arb may be more appropriate than using mpmath

- How should one elegantly arrange the code so that we don't recheck partitions that have already been ruled out at coarser refinement. My guess is some generator sprinklings. I like generators.

- I clearly still have some conceptual confusion in this post.

Some thoughts for future posts:
- Lattices and Propagators
- ODEs, [Picard-Lindelof](https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem)
- Lipshitz bounds = intervals + automatic differentiation
- Continuity as a lens
- CEGAR, dReal, Z3


```python
def integral(f : Callable[[real], real]):
    def res():
        return sum([ f(lambda : i)() for i in partition() ]) * const(f"1/{10**iv.dps}")()
    return res

v = integral( lambda x : rmul(x,x) )
for i in range(3):
    iv.dps = i
    print(f"Precision {i}: {v()}")
```

### Links


[https://dl.acm.org/doi/abs/10.1145/3385412.3386037](https://dl.acm.org/doi/abs/10.1145/3385412.3386037) Toward an API for real numbers

MarshallB used for CAD [https://dl.acm.org/doi/pdf/10.1145/3341703](https://dl.acm.org/doi/pdf/10.1145/3341703)  [https://www.youtube.com/watch?v=h7g4SxKIE7U](https://www.youtube.com/watch?v=h7g4SxKIE7U) - Ben Sherman giving a talk on this [https://www.ben-sherman.net/publications.html](https://www.ben-sherman.net/publications.html)  some other related publications and thesis

[https://www.youtube.com/watch?v=f8fivVYdGlg](https://www.youtube.com/watch?v=f8fivVYdGlg) - Norbert Muller 

<https://github.com/dpsanders/ExactReals.jl>
< http://irram.uni-trier.de/ > iRRAM

<http://arblib.org/>
[http://fredrikj.net/calcium/](http://fredrikj.net/calcium/) [https://news.ycombinator.com/item?id=24700705](https://news.ycombinator.com/item?id=24700705)

Escardo posts
Seemingly Impossible Functional Programs  <http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/>
Searchable data types <https://lukepalmer.wordpress.com/2010/11/17/searchable-data-types/>
monad for infinite search in finite time <http://math.andrej.com/2008/11/21/a-haskell-monad-for-infinite-search-in-finite-time/>
synthetic topology of datatypes and classical spaces <https://www.cs.bham.ac.uk/~mhe/papers/entcs87.pdf> This really lays it all out
smythe 
vickers - Topology via Logic

<http://math.andrej.com/2008/08/24/efficient-computation-with-dedekind-reals/>

Abstract Stone Duality. [http://www.paultaylor.eu/ASD/intawi/intawi.pdf](http://www.paultaylor.eu/ASD/intawi/intawi.pdf) [http://www.paultaylor.eu/](http://www.paultaylor.eu/)

delay monad <https://www.cs.ox.ac.uk/ralf.hinze/WG2.8/22/slides/tarmo.pdf>

Theory of Approximation. Belnap [http://www.pitt.edu/~belnap/howacomputershouldthink.pdf](http://www.pitt.edu/~belnap/howacomputershouldthink.pdf)


[https://news.ycombinator.com/item?id=23797302](https://news.ycombinator.com/item?id=23797302) Seemingly impossible functional programs discussion


Differentiable Marshall B paper <https://arxiv.org/pdf/2007.08017.pdf> I guess this isn't differentiable marshallb. It's differentiable something

<https://fredrikj.net/> Fredrik Johansson is the man.
Arb, Calcium, mpmath, 
<https://arxiv.org/abs/2011.01728> calcium paper. It implements a mix of "effective" numbers and exact reals
