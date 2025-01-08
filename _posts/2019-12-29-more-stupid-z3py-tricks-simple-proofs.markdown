---
author: philzook58
comments: true
date: 2019-12-29 04:33:06+00:00
layout: post
link: https://www.philipzucker.com/more-stupid-z3py-tricks-simple-proofs/
slug: more-stupid-z3py-tricks-simple-proofs
title: 'More Stupid Z3Py Tricks: Simple Proofs'
wordpress_id: 2600
categories:
- Formal Methods
tags:
- z3
---

Edit 2024: See my project knuckledragger for more systematic work in this vein <https://github.com/philzook58/knuckledragger>

Z3 can be used for proofs. The input language isn't anywhere near as powerful as interactive theorem provers like Coq, Isabelle, or Agda, but you can ask Z3 to prove pretty interesting things. Although the theorems that follow aren't hard in interactive theorem provers, they would take beyond complete novice level skills to state or prove.

I like to think of the z3 proving process as "failing to find a counterexample". Z3py has supplies a function `prove` which is implemented like this.

```
#https://z3prover.github.io/api/html/namespacez3py.html#a2f0f4611f0b706d666a8227b6347266a
def prove(claim, **keywords):
     """Try to prove the given claim.
 
     This is a simple function for creating demonstrations.  It tries to prove
     `claim` by showing the negation is unsatisfiable.
 
     >>> p, q = Bools('p q')
     >>> prove(Not(And(p, q)) == Or(Not(p), Not(q)))
     proved
     """
     if z3_debug():
         _z3_assert(is_bool(claim), "Z3 Boolean expression expected")
     s = Solver()
     s.set(**keywords)
     s.add(Not(claim))
     if keywords.get('show', False):
         print(s)
     r = s.check()
     if r == unsat:
         print("proved")
     elif r == unknown:
         print("failed to prove")
         print(s.model())
     else:
         print("counterexample")
         print(s.model())
```

Basically, it negates the thing you want to prove. It then tries to find a way to instantiate the variables in the expression to make the statement false. If it comes back unsat, then there is no variable assignment that does it. Another way to think about this is rewriting the $ \forall y. p(y) $ as $ \neg \exists y \neg p (y)$.  The first $ \neg$ lives at sort of a meta level, where we consider unsat as a success, but the inner $ \neg$ is the one appearing in `s.add(Not(claim))`.

We can prove some simple facts. This is still quite cool, let's not get too jaded. Manually proving these things in Coq does suck (although is easy if you use the ring, psatz, and lra tactics [https://coq.inria.fr/refman/addendum/micromega.html](https://coq.inria.fr/refman/addendum/micromega.html), which you DEFINITELY should. It is a great irony of learning coq that you cut your teeth on theorems that you shouldn't do by hand).

```
from z3 import *
p = Bool("p")
q = Bool("q")
prove(Implies(And(p,q), p)) # simple destruction of the And
prove( And(p,q) == Not(Or(Not(p),Not(q)))) #De Morgan's Law

x = Real("x")
y = Real("y")
z = Real("z")
prove(x + y == y + x) #Commutativity
prove(((x + y) + z) == ((x + (y + z)))) #associativity
prove(x + 0 == x) # 0 additive identity
prove(1 * x == x)
prove(Or(x > 0, x < 0, x == 0)) #trichotomy
prove(x**2 >= 0) #positivity of a square
prove(x * (y + z) == x * y + x * z) #distributive law
```

Ok, here's our first sort of interesting example. Some properties of even and odd numbers. Even and Odd are natural predicates. What are possible choices to represent predictaes in z3?  
We can either choose python functions `IntSort -> BoolSort()` as predicates or we can make internal z3 functions `Function(IntSort(), BoolSort())`

```
x = Int("x")
y = Int("y")
def Even(x):
    q = FreshInt()
    return Exists([q], x == 2*q)
def Odd(x):
    return Not(Even(x))
prove(Implies( And(Even(x), Odd(y)) , Odd(x + y)))
prove(Implies( And(Even(x), Even(y)) , Even(x + y)))
```

All well and good, but try to prove facts about the multiplicative properties of even and odd. Doesn't go through. :(

Here's a simple inductive proof. Z3 can do induction, but you sort of have to do it manually, or with a combinator. Given a predicate f, inductionNat returns

```
def inductionNat(f): # proves a predicate f forall nats by building s simple inductive version of f.
    n = FreshInt()
    return And(f(IntVal(0)), ForAll([n], Implies(And(n > 0, f(n)),  f(n+1))))
'''
# doesn't solve
sumn = Function('sumn', IntSort(), IntSort())
n = FreshInt()
s = Solver()
s.add(ForAll([n], sumn(n) == If(n == 0, 0, n + sumn(n-1))))
claim = ForAll([n], Implies( n >= 0, sumn(n) == n * (n+1) / 2))
s.add(Not(claim))
s.check()
'''
# solves immediately
sumn = Function('sumn', IntSort(), IntSort())
n = FreshInt()
s = Solver()
s.add(ForAll([n], sumn(n) == If(n == 0, 0, n + sumn(n-1))))
claim = inductionNat(lambda n : sumn(n) == n * (n+1) / 2)
s.add(Not(claim))
s.check() #comes back unsat = proven
```

Here's another cute and stupid trick. Z3 doesn't have a built in sine or cosine. Perhaps you would want to look into [dreal](http://dreal.github.io/) if you think you might be heavily looking into such things. However, sine and cosine are actually defined implicitly via a couple of their formula. So we can instantiate
A slightly counterintuitive thing is that we can't use this to directly compute sine and cosine values. That would require returning a model, which would include a model of sine and cosine, which z3 cannot express.  
However, we can try to assert false facts about sine and cosine and z3 can prove they are in fact unsatisfiable. In this way we can narrow down values by bisection guessing. This is very silly.

```
sin = Function("sin", RealSort(), RealSort())
cos = Function("cos", RealSort(), RealSort())
x = Real('x')
trig =  [sin(0) == 0,
         cos(0) == 1,
         sin(180) == 0,
         cos(180) == -1, # Using degrees is easier than radians. We have no pi.
         ForAll([x], sin(2*x) == 2*sin(x)*cos(x)),
         ForAll([x], sin(x)*sin(x) + cos(x) * cos(x) == 1),
         ForAll([x], cos(2*x) == cos(x)*cos(x) - sin(x) * sin(x))]
s = Solver()
s.set(auto_config=False, mbqi=False)
s.add(trig)
s.add( RealVal(1 / np.sqrt(2) + 0.0000000000000001) <= cos(45))
s.check()
```

A trick that I like to use sometimes is embedding objects in numpy arrays. Numpy slicing is the best thing since sliced bread. A lot, but not all, of numpy operations come for free, like matrix multiply, dot, sum, indexing, slicing, reshaping. Only some are implemented in terms of overloadable operations. here we can prove the Cauchy Schwartz inequality for a particular vector and some axioms of vector spaces.

```
import numpy as np
import operator as op
def NPArray(n, prefix=None, dtype=RealSort()):
    return np.array( [FreshConst(dtype, prefix=prefix) for i in range(n)] )
v = NPArray(3)
w = NPArray(3)
l = Real("l")

prove( np.dot(v,w * l) == l * np.dot(v,w) ) # linearity of dot product
prove(np.dot(v, w)**2 <= np.dot(v,v) * np.dot(w,w)) # cauchy schwartz

def vec_eq(x,y): # a vectorized z3 equality
    return And(np.vectorize(op.eq)(x,y).tolist())

prove( vec_eq((v + w) * l, v * l + w * l)) # distributivity of scalar multiplication

z = NPArray(9).reshape(3,3) # some matrix
prove( vec_eq( z @ (v + w) , z @ v + z @ w )) # linearity of matrix multiply
prove( vec_eq( z @ (v * l) , (z @ v) * l))    # linearity of matrix multiply
```

Defining and proving simple properties of Min and Max functions

```
from functools import reduce
def Max1(x,y):
    return If(x <= y, y, x)
def Min1(x,y):
    return If(x <= y, x, y)
def Abs(x):
    return If(x <= 0, -x, x)

def Min(*args):
    return reduce(Min1, args)
def Max(*args):
    return reduce(Max1, args)
    
z = Real('z')
prove(z <= Max(x,y,z))
prove(x <= Max(x,y))
prove(Min(x,y) <= x)
prove(Min(x,y) <= y)
```

Proving the[Babylonian method](https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method) for calculating square roots is getting close to the right answer. I like the to think of the Babylonian method very roughly this way: If your current guess is low for the square root x/guess is high. If your guess is high, x/guess is low. So if you take the average of the two, it seems plausible you're closer to the real answer. We can also see that if you are precisely at the square root, (x/res + x)/2 stays the same. Part of the the trick here is that z3 can understand square roots directly as a specification. Also note because of python overloading, `babylonian` with work on regular numbers and symbolic z3 numbers. We can also prove that babylon_iter is a contractive, which is interesting in it's own right.

```
def babylonian(x):
    res = 1
    for i in range(7):
        res = (x / res + res) / 2
    return res    

x, y = Reals("x y")
prove(Implies(And(y**2 == x, y >= 0, 0 <= x, x <= 10), babylonian(x) - y <= 0.01))
```

A funny thing we can do is define [interval arithmetic](https://en.wikipedia.org/wiki/Interval_arithmetic)using z3 variables. Interval arithmetic is very cool. Checkout [Moore's book](http://www-sbras.nsc.ru/interval/Library/InteBooks/IntroIntervAn.pdf), it's good. This might be a nice way of proving facts related to real analysis. Not sure.  
This is funny because z3 internally uses interval arithmetic. So what we're doing is either very idiotically circular  or pleasantly self-similar.  
We could use a similar arrangement to get complex numbers, which z3 does not natively support

```
class Interval():
    def __init__(self,l,r):
        self.l = l
        self.r = r
    def __add__(self,rhs):
        if type(rhs) == Interval:
            return Interval(self.l + rhs.l, self.r + rhs.r)
    def __sub__(self, rhs):
        return Interval(self.l)
    def __mul__(self,rhs):
        combos = [self.l * rhs.l, self.l * rhs.r, self.r * rhs.l, self.r*rhs.r]
        return Interval( Min(*combos), Max(*combos))
    def fresh():
        l = FreshReal()
        r = FreshReal()
        return Interval(l,r)
            
    def valid(self): # It is problematic that I have to rememeber to use this. A way around it?
        return self.l <= self.r
    def __le__(self,rhs): # Or( self.r < self.l ) (ie is bottom)
        return And(rhs.l <= self.l, self.r <= rhs.r )
    def __lt__(self,rhs):
        return And(rhs.l < self.l, self.r < rhs.r )
    def forall( eq ):
        i = Interval.fresh()
        return ForAll([i.l,i.r] , Implies(i.valid(), eq(i) ))
    def elem(self,item):
        return And(self.l <= item, item <= self.r) 
    def join(self,rhs):
        return Interval(Min(self.l, rhs.l), Max(self.r, rhs.r))
    def meet(self,rhs):
        return Interval(Max(self.l, rhs.l), Min(self.r, rhs.r))
    def width(self):
        return self.r - self.l
    def mid(self):
        return (self.r + self.l)/2
    def bisect(self):
        return Interval(self.l, self.mid()), Interval(self.mid(), self.r)
    def point(x):
        return Interval(x,x)
    def recip(self): #assume 0 is not in 
        return Interval(1/self.r, 1/self.l)
    def __truediv__(self,rhs):
        return self * rhs.recip()
    def __repr__(self):
        return f"[{self.l} , {self.r}]"
    def pos(self):
        return And(self.l > 0, self.r > 0)
    def neg(self):
        return And(self.l < 0, self.r < 0)
    def non_zero(self):
        return Or(self.pos(), self.neg())
        
x, y = Reals("x y")
i1 = Interval.fresh()
i2 = Interval.fresh()
i3 = Interval.fresh()
i4 = Interval.fresh()

prove(Implies(And(i1.elem(x), i2.elem(y)), (i1 + i2).elem(x + y)))
prove(Implies(And(i1.elem(x), i2.elem(y)), (i1 * i2).elem(x * y)))

prove(Implies( And(i1 <= i2, i2 <= i3), i1 <= i3  )) # transitivity of inclusion

prove( Implies( And(i1.valid(), i2.valid(), i3.valid()),  i1 * (i2 + i3) <= i1 * i2 + i1 * i3)) #subdistributivty

# isotonic
prove(Implies( And( i1 <= i2, i3 <= i4  ),  (i1 + i3) <= i2 + i4 ))
prove(Implies( And(i1.valid(), i2.valid(), i3.valid(), i4.valid(), i1 <= i2, i3 <= i4  ),  (i1 * i3) <= i2 * i4 ))
```
