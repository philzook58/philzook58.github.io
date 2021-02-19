---
author: Philip Zucker
date: 2021-02-18 13:52:20+00:00
layout: post
title: CEGARing Exponentials into Z3 with Python Coroutines
tags:
- python
- category theory
- smt
- z3
---

Counter Example Guided Abstraction Refinement (CEGAR) is a search strategy for either making a solver more efficient or extending it's capabilities. One makes an abstracted problem (contains false solutions) of the problem at hand that a solver can handle more easily than the full problem. The solver returns a solution. Either this solution is a valid one with respect to the complete problem, or it falls in the gap of between the relaxed abstracted problem and the actual problem. In which case, one uses the solution to tighten up the abstraction to outlaw that solution (and other similar ones hopefully). Rinse and repeat.

(Side note: [CEGAR](http://www.cs.cmu.edu/~emc/papers/Conference%20Papers/Counterexample-guided%20Abstraction%20Refinement.pdf) in a stricter sense is a technique for model checking, but I tend to think of it as basically the previous paragraph )

[SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) itself can be considered an example of CEGAR from certain perspective. SMT solvers have sort of two layers: sort of a propositional layer and theory specific reasoning layer. One can abstract facts like $x \le 3$ as an opaque boolean variable $p$. Send it off to a SAT solver which only understand the logical propositional structure, it returns a solution. Either this solution is consistent with the actual interpretation of the propositional variables as linear inequalities or not. If not, there must be some subset of the inequalities that actually is not self consistent. This is a propositional clause that you can assert to the SAT model to refine the model. Rinse and repeat.


[Z3](https://github.com/Z3Prover/z3) is my favorite solver. It is very expressive, but it doesn't have everything. One omission that hurts for some applications is that Z3 does not understand transcendental functions like exp, sin, cos, etc. Other SMT solvers can handle these things, in particular [dReal](http://dreal.github.io/). Or perhaps your problem doesn't have a significant logical-ish/boolean flavor, in which case perhaps global non convex solvers or mixed integer solver can be the way to go.

But it is interesting to build a CEGAR loop involving Z3 to extend it to support them. What we can do is mash together a solving process ping ponging between Z3 and an interval arithmetic library, in this case [PyIbex](https://www.ensta-bretagne.fr/desrochers/pyibex/docs/pyibex/)



Python generators are neat. There is a rarely used feature of them that makes them even neater. It turns out, you can have the yield statement not only output a value to the outside, but also receive one via the function `send` which is a brother of `next`. See here for example usage <https://realpython.com/introduction-to-python-generators/#how-to-use-send)>. In this way, generators can be used not only to create values, but to transform a stream of them. They are a [coroutine](https://en.wikipedia.org/wiki/Coroutine).


A stratagem I use for organizing symbolic code involving constraint generation is to return not just an output variable, but also a list of side constraints that constrain the variable to the appropriate values. Then you just have to be careful to add the side constraints every time to a global constraint set every time you use one of these functions. For example as a toy example

```python
def add_7(x):
    y = Int("y")
    return y, [x + 7 == y]
```

Depending on your background, it may be illuminating to note this is basically a [Writer monad](http://learnyouahaskell.com/for-a-few-monads-more). If not, just ignore this comment.

Sometimes the style produces more variables than necessary, but it let's you describe things that aren't a strictly functional relationship. See for example these blog posts.

- <https://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/>
- <https://www.philipzucker.com/categorical-combinators-for-convex-optimization-and-model-predictive-control-using-cvxpy/>


A very slight change to this is to not produce a list of constraints, but instead a [generator](https://wiki.python.org/moin/Generators) of constraints. Basically it is the same thing. However, if we use the ability to send values into the [generator via `send`](https://realpython.com/introduction-to-python-generators/#how-to-use-send), now we have a richer family of things to express. Now we can have constraints depend on further information coming in down the line (spoiler alert: CEGAR counterexamples).

So here is a sketch of how this could be done putting an exponential function into z3. The initial constraints give just a very loose approximation of exponential, perhaps some linear inequality bounds on it's values. Perhaps just these constraints are sufficient ( or just the mere fact that exp is a function) for Z3 to show something is impossible/unsatisfiable. If not though, we can use to countermodel to refine the constraints in such a way that the solution is not longer valid. In this case, we refine the subdivision of the domain

The track the current approximation of exp by intervals, be use the concept of a Tube. [Tubex](http://simon-rohou.fr/research/tubex-lib/doc/index.html) is a cool library that builds up Ibex the ability to talk about tubes, which are an precise interval envelope of a function. You can think of this as an extension of discretizing a function the usual way. In usual discretization, you hold an array of values of the function. You tend to think of these as samples of the function at discrete points. You can't say anything about the values the function takes on outside the sample points. If instead you break up the domain of the function into interval regions, you can use interval arithmetic to store precision bounds on the value in each subdivision. This can be thought of as an [abstract domain](https://en.wikipedia.org/wiki/Abstract_interpretation) for real valued functions and you can use the idea to mechanically and numerically provide exact bounds on the solution of an ODE for example. Interesting stuff. Definitely checkout the Tubex lib for more

I made my own simple Tube class because Tubex did not seem to expose the functionality I wanted in terms of refinement. It's an interesting exercise in any case. My tube holds the current subdivision of the reasons in `self.ts` and a interval computing function `self.f` for example `exp` from pyIbex. It refines this subdivision at a point t by calling `refine`. These points will come from the z3 countermodel.

FYI, I'm not confident my refinement logic is very sound. It's kind of finicky to get it right in the presence in possibly infinite endpoints of intervals. `refine` returns the new facts (new domain-codomain interval pairs) that were learned because of the refinement in `fresh`. 

```python
from pyibex import * 
from z3 import *

class MyTube():
    def __init__(self, f):
        self.ts = [Interval(-oo,oo)] #[Interval(-oo,-10), Interval(-10,10) , Interval(10,oo)] #[Interval(-oo,oo)]#
        self.f = f
        self.ys = [f(t) for t in self.ts]
    def refine(self,t):
        fresh = []
        for i in range(len(self.ts)):
            if t in self.ts[i]:

                # rather than bisect use refinement exactly at.
                # hmm. what about a repeated refinement?
                # I guess we should bisect and sample
                # or we should only sample when semi infinite refinement
                tint = self.ts[i]
                #print(t, tint, t in tint)
                if tint.is_unbounded():
                    lt,ut =  Interval(tint.lb(), t), Interval(t, tint.ub())
                else:
                    lt,ut = tint.bisect()
                
                self.ts[i] = lt
                y = self.f(lt)
                self.ys[i] = y
                fresh.append((lt,y))
                
                self.ts.append(ut)
                y = self.f(ut)
                self.ys.append(y)
                fresh.append((ut,y))
        return fresh
    def __call__(self,t):
        for tt,y in zip(self.ts,self.ys):
            if t in tt:
                return y 
    def __repr__(self):
        return repr(list(zip(self.ts, self.ys )))

```

Here is a function that takes a z3 variable `x` and returns `exp(x)` where `exp` in an uninterpreted function. It also returns a second value which is a generator. This generator produces new Z3 constraints when it receives countermodels from Z3.

```python
# helper function. Builds constraint that x is in interval i which is possibly infinite.
def z3_in(x, i):
    # check for infinities
    c = []
    if i.ub() != oo:
        c += [x <= i.ub()]
    if i.lb() != -oo:
        c += [ i.lb() <= x]
    return And(c)

# returns a outer approximation of the exp(x) 
# second argument is a generator that receives models and outputs new constraints
def z3_exp(x):
    fexp = Function("exp", RealSort(), RealSort())
    def res():
        tube = MyTube(exp)
        m = yield [ fexp(x) >= 1 + x, fexp(x) >= 0 ] # The first thing it sends are just a couple useful facts
        while True:
            x0 = m.eval(x).numerator_as_long() / m.eval(x).denominator_as_long() 
            #refine tube at current model point
            f = tube.refine(x0) 

            # build refined constraints the fresh facts f returns from refine
            c = [ Implies( z3_in(x,t) ,  z3_in(fexp(x), y)) for t, y in f]
            m = yield c # yield and receive the countermodel
    return fexp(x), res
```

Here's some simple example usage.


```python
from z3 import *
x = Real("x")

y, c = z3_exp(x)

c = c()
s = Solver()
s.add(next(c))
s.add(Not( Implies( x >= 1, y >= 2.7 )))
s.check()
m = s.model()
for i in range(7):
     if s.check() == unsat:
            print("proved")
            break
     m = s.model()
     newcon = c.send(m) 
     s.add( newcon )
```


# Bits and Bobbles

You can extend this to other functions besides `exp`. In fact it is not hard to do so generically. It would look something like this.
I haven't checked this code.

```python
def z3_tube(name, x, f):
    f_z3 = Function(name, Realsort(), Realsort())
    def res():
        tube = MyTube(f)
        m = yield [ Implies( z3_in(x,t) ,  z3_in(fexp(x), y)) for t, y in tube]
        while True:
            if m[f_z3(x)] in tube(m[x]):
                c = []
            else:
                f = tube.refine(m[x])
                c = [ Implies( z3_in(x,t) ,  z3_in(fexp(x), y)) for t, y in f]
            m = yield c
            
    return f_z3(x), res
```

PyIbex is not intended as a precision interval library. Because of this, even if you polished this implem,entation more, it's not water tight. You should use a carefully rounded library like [mpmath](https://mpmath.org/) if you care about such things.

`send` is fascinating for other reasons. People have shown a pattern where you can use it to achiewve something like an algebraic effect system/free monad looking thing in python with decent syntax.

- <https://twitter.com/sigfpe/status/1274764185658769408?s=20>
- io.py [https://gist.github.com/alexknvl/e15ea9762a58935b28f2](https://gist.github.com/alexknvl/e15ea9762a58935b28f2)
- <https://github.com/alexknvl/ai-meetup/blob/master/19-09-26-ppl1/ppl-meetup.ipynb >probablistic programming
- <https://twitter.com/ezyang/status/1300278419188580353?s=20>
- [https://pypi.org/project/effect/#:~:text=Effect%20is%20a%20library%20for,It%20supports%203.6%20and%20above.](https://pypi.org/project/effect/#:~:text=Effect%20is%20a%20library%20for,It%20supports%203.6%20and%20above.) effect - as python library

- takafumi asrakaki using julia yieldto for a "callcc" <https://julialang.zulipchat.com/#narrow/stream/137791-general/topic/call.2Fcc.20for.20Julia.3F.20%28or.20how.20to.20use.20.60yieldto.60%29/near/218188425>
- [https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.398.9600&rep=rep1&type=pdf](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.398.9600&rep=rep1&type=pdf) Yield - mainstream delimitted continuations. slides [http://parametricity.net/dropbox/yield-slides.subc.pdf](http://parametricity.net/dropbox/yield-slides.subc.pdf)