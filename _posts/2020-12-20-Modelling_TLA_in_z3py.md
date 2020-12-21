---
author: Philip Zucker
date: 2020-12-20
layout: post
categories:
- Formal Methods
tags:
- python
- z3
title: Modelling TLA+ in Z3Py
---

It's that time of year again where I'm fiddling around with Z3Py. I'm booting it back up because I'm scheduled to do a [tutorial on Z3](https://fmie2021.github.io/agenda.html) on Feb 3. It's kind of silly because I probably already have too much content, and the tutorial is aimed at newbies, but there are some fun new things that I've learned in the last year I can do in Z3. As one example, it's not so hard to build a pretty reasonable simulacrum of TLA+ in Z3.

[TLA+](https://lamport.azurewebsites.net/tla/tla.html) is a modelling/specification language for computational processes. It is particularly useful for modeling concurrency, where our intuitions fail us <http://deadlockempire.github.io/>. It's the mind child of Leslie Lamport, the same guy behind [LaTex](https://en.wikipedia.org/wiki/LaTeX) and [Paxos](https://en.wikipedia.org/wiki/Paxos_(computer_science)). The language doesn't aim for deep verification of your actual code as is sometimes the goal with tools like Coq, but because of that it is significantly more lightweight and easy to use. 
The [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) is a freely available IDE and checker to TLA+, but I think it is kind of a neat idea to replicate something in the flavor of TLA+ in all too familiar python. By leveraging Z3, we can get a lot of logical mileage and solver power for free.

[Z3](https://rise4fun.com/z3/tutorial) is an SMT solver. Its input language [smtlib2](http://smtlib.cs.uiowa.edu/examples.shtml) is a kind of typed first order logic with special support for things like booleans, integers, reals, bitvectors, and algebraic datatypes. You can ask Z3 if propositions are valid, or if not it can provide a counterexample. It works pretty crazy good, especially if you work around its weaknesses (mostly quantifiers and nasty nonlinear stuff). Z3 has top class performance and its [python bindings](https://z3prover.github.io/api/html/namespacez3py.html) are widely regarded as very good.

The main unusual things TLA brings into play compared to bog standard logics is the primed variables $$x'$$, representing the values of variables at the next time step, and some temporal operators like always $$\Box$$ and eventually $$\Diamond$$.

We could mark primes by creating variables in pairs
```python
from z3 import *
x, xnxt = Ints("x x'")
```

But I've chosen to mark the prime variables using a special uninterpreted function, which we strip out later.

```python
def nxt(x): # next is a special function for generators in python, so we shouldn't use that name
    assert is_const(x)
    assert f.decl().kind() == Z3_OP_UNINTERPRETED:
    s = x.sort()
    return Function("nxt", s, s)(x)
```

One breakage here as compared to with TLA+ is the use of types. TLA+ curiously insists on a lack of intrinsic types and argues against them as a foundational feature. Types are instead propositions that are proved in the system. This just is really not convenient for using with Z3, so from the get-go I'm going to take liberties.

We can implement an `always` operator via a fairly simple procedure, we just roll out the execution of any formula for `n` time steps. This is the trick of bounded model checking. This rollout can be achieved by using the Z3 `substitute` function, a surprisingly useful little fellow.


```python
# collects up all the variable from a formula
# https://stackoverflow.com/questions/14080398/z3py-how-to-get-the-list-of-variables-from-a-formula
def get_vars(f):
    r = set()
    def collect(f):
      if is_const(f): 
          if f.decl().kind() == Z3_OP_UNINTERPRETED:
              r.add(f)
      else:
          for c in f.children():
              collect(c)
    collect(f)
    return r


#https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-bounded-model-checking
# rolls out the transition relation for n steps
# it replaces x with x_i and prime(x) with x_(i+1)
def always(p,n=20):
    orig_vs = get_vars(p)
    nextvs = orig_vs
    t = True
    for i in range(1,n):
        vs = nextvs
        nextvs =  [ Const( f"{str(v)}_{i}", v.sort()) for v in orig_vs  ]
        p1 = substitute(p, [ (nxt(v), nextv) for v, nextv in zip(orig_vs,nextvs)  ]) 
        p2 = substitute(p1, [ (orig_v, v) for orig_v, v in zip(orig_vs,vs)  ])
        t = And(t,p2)
    return t
```

Here for example is the specification of a clock from the [Specifying Systems](https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf) book. The clock starts with an hour between 0 and 12, and at each time step increases unless it's wrapped around 12.

```python
hr = Int("hr")
HCini = And(1 <= hr, hr <= 12)
HCnxt = nxt(hr) == If(hr != 12, hr + 1, 1)
HC = And(HCini, always(HCnxt)) 
prove(Implies(HC,  always(HCini))) # prove clock always stays between 0 and 12 (for 20 times steps)
```

You do have to be careful with using always. Arbitrarily nesting it's usage may give unexpected results. Lamport makes an argument that specs very rarely do or should make sophisticated use of the temporal operators. Maybe this is good enough or maybe there is a way to patch this up.

Here are some other useful TLA+ like features and functions transcoded.

```python
def elem(x,S):
    return Or([x == s for s in S])

def unchanged(*args):
    return And([prime(x) == x for x in args])

def eventually(p, n=20):
    return Not(always(Not(p),n=n))

def stutter(p, vars=None):
    if vars == None:
        vars = get_vars(p)
    return Or(p, unchanged(*vars))

def enabled(A):
    vs = get_vars(A)
    nxtvs =  [ FreshConst(  v.sort(), prefix=str(v) ) for v in vs]
    p1 = substitute(A, [ (nxt(v), nextv) for v, nextv in zip(vs,nxtvs)  ]) 
    return Exists(nxtvs, p1)

# backports useful logical operator notation for z3 that it does not have by default
BoolRef.__and__ = lambda self, rhs: And(self,rhs)
BoolRef.__or__ = lambda self, rhs: Or(self,rhs)
BoolRef.__xor__ = lambda self, rhs: Xor(self,rhs)
BoolRef.__invert__ = lambda self: Not(self)
BoolRef.__rshift__ = lambda self, rhs: Implies(self,rhs)
```


Here as another example is the [Die Hard puzzle](http://lamport.azurewebsites.net/video/video4.html)

```python
small, big = Ints("small big")

TypeOk = And(
   elem(small, range(4)),
   elem(big, range(6))
)
Init = And(
   big == 0,
   small == 0
)

FillSmall = And(prime(small) == 3, unchanged(big))
FillBig = And(prime(big) == 5, unchanged(small))
Goal = big != 4
SmallToBig = If(big + small <= 5,   
                 And( nxt(big) == big + small, nxt(small) == 0 ) , 
                 And(nxt(small) == small - (5 - big), nxt(big) == 5)
               )

BigToSmall = If( big + small <= 3,
                 And( nxt(small) == big + small, nxt(big) == 0),
                 And( nxt(small) == 3, nxt(big) == big - (3 - small) )
                )

EmptyBig = And(nxt(big) == 0,  unchanged(small)) 
EmptySmall = And(nxt(small) == 0,  unchanged(big)) 
Next = Or(FillSmall, FillBig, EmptySmall, EmptyBig, SmallToBig, BigToSmall)

Spec = Init & always(Next, n=8)
prove( Implies(Spec  , always(Goal, n = 8)))
```

Z3 does in fact return a counter model that fills the buckets up as desired.

TLA+ has a tendency to use functions/records which are not so obvious how to encode. There are different ways of going about this. One aspect of playing around with Z3py is that it makes extremely clear the existence of the logic language and a metalanguage. The logic is Z3 expressions, but the metalanguage is python and they are obviously very different. But there is often a choice of whether to encode things in the logic vs the metalanguage. It is usually better I think to encode as much in python as possible if you can get away with it. Z3 likes piles of simple constraints more than it likes complicated quantifiers and things.

For example, we can want to encode an Enum type in python or in Z3.

```python
from enum import Enum, auto
#python enum
class RMState(Enum):
     WORKING = auto()
     PREPARED = auto()
     COMMITTED = auto()
     ABORTED = auto()

# z3 enum
RMState = Datatype("RMState")
RMState.declare("working")
RMState.declare("prepared")
RMState.declare("committed")
RMState.declare("aborted")
RMState = RMState.create()
```

Or we can choose to encode records in Z3 vs python.

```python
#python record of z3 values
val = Int("val")
rdy, ack = Bools("rdy ack")
chan = {val : val, rdy : rdy, ack : ack}

# Z3 record of Z3 values
Chan = Datatype("Chan")
ChanCon = Chan.declare("constr", ("val", IntSort()) , ("rdy", BoolSort()),  ("ack", BoolSort()) )
Chan = Chan.create()
record = Chan.constr(val,rdy,ack)
chan = Const("chan", Chan)
```

Or we can choose to encode functions in z3 or python

```python
# python square. Works of Z3 values too
def square(x):
    return x*x

# Internalized Z3 square function
square = Function("square", IntSort(),IntSort())
x = Int("x")
square_axiom = ForAll([x], square(x) == x * x)
```



### Bits and Bobbles

Downsides:

* Very ad hoc. The use of special autogenerated names is a great way to inadvertently smash things together
* TLA syntax is designed to be readable. The python adds a lot of noise
* TLA toolbox can format specs nicely using latex.
* TLA has a lot of thought gone into it. Making changes to it in an afternoon of thought is probably not to be trusted

Upsides:
* Better fits Z3, so we get good automation from the get go
* python is lingua franca of computing. It is comforting compared to TLA+, even if Z3py might be discomfiting.
* Having to download the toolbox and figure out how to use it is always going to be a slight speedbump. There is a TLA+ vscode extension now though. That might help


Using Python ast parsing <https://greentreesnakes.readthedocs.io/en/latest/index.html>, we could probably use regular simple python syntax as a PlusCal like DSL and compile it into the above Z3-TLA+ hybrid.

I'm not sure if the CHOOSE operator of TLA+ will be easy to implement. It kind of seems like it requires nested solves? Can it be encoded using 

I don't particularly understand the TLA+ module system yet and I'm not so sure how to emulate it. Python modules might be one way, or perhaps classes.

Although I tried to copy exactly, perhaps one shouldn't spec in precisely the style of standard TLA+.

### Links

  * <https://www.learntla.com/introduction/> Hillel Wayne's tutorial
  * <https://www.microsoft.com/en-us/research/uploads/prod/2018/05/book-02-08-08.pdf> Specifying Systems
  * <https://pron.github.io/tlaplus>  Very impressive essays by Ron Pressler
  * <https://github.com/cobusve/TLAPLUS_DeadlockEmpire> Very neat way to learn TLA+
  * <https://github.com/tlaplus/Examples>
  * Apalache is a Z3 backed model checker for TLA+ <https://github.com/informalsystems/apalache>
  * <https://theory.stanford.edu/~nikolaj/programmingz3.html>
  * <https://github.com/philzook58/z3_tutorial_2020>
  * <https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/>
