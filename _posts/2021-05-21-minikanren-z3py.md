---
author: Philip Zucker
date: 2021-05-22 
layout: post
title: Making a "MiniKanren" using Z3Py
---

Relational/logic programming is quite cool. It let's you do things that sound impossible, like run a program backwards. Using [Z3py](https://github.com/philzook58/z3_tutorial)  to do a lot of heavy lifting, there's a cute, simple, and pretty powerful little [microkanren](http://minikanren.org/) you can make. You can have it answer queries like the following that run list append backwards.

```python
q = Const("q", List)
r = Const("r", List)
runq([q,r], appendo(q,r,cons(2,cons(42,cons(17,nil)))))
'''
Response:
[{q: nil, r: cons(2, cons(42, cons(17, nil)))},
 {q: cons(2, nil), r: cons(42, cons(17, nil))},
 {q: cons(2, cons(42, nil)), r: cons(17, nil)},
 {q: cons(2, cons(42, cons(17, nil))), r: nil}]
'''

```

Full (very short) implementation here <https://gist.github.com/philzook58/242961b16f0e04a731760ca8d272d91c>.

### A Short Spiel on Minikanren

The minikanren approach builds a embedded relational programming language out of 2 pieces

1. unification
2. Some kind of nondeterministic search

The microkanren paper is really good, if you can read a little scheme <http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf>. I talk more and have more links about microkanren here <https://www.philipzucker.com/yet-another-microkanren-in-julia/>

The non-deterministic search is structured around the concept of a "goal". A goal transforms a state into a set of possible refined states based on the assertions of the goal. In other words it can be modelled as a function `State -> [State]`.

The state of a minikanren search is described by the currently known unifications. [Unification](https://en.wikipedia.org/wiki/Unification_(computer_science)) is a sort of bidirectional pattern matching. You take two patterns and traverse down them to figure out what variables have to equal, or if it is impossible for them to match. I'm going to short circuit this entire piece to just lean on Z3. This has the upside of not need to implement it, and the downside of Z3 being rather less controlled / general in what it returns compared to using unification.

A term with variables, let's call it a pattern, is in some sense is a representation of a set of concrete terms with no variables. The patterns represents the set of terms with every possible term substitution into the variables of the pattern. Unification is a way of asking for the intersection of these term sets.

Z3 goes totally concrete though. So when minikanren returns a result that contains patterns, Z3 could return every possible instantiation (which is possibly infinite) of those patterns, depending on how we ask.

## Generators

I rather like python generators. You can do some pretty wacko control flow with them.

My internal model of what I am doing is the state of the program is a list of Z3 assertions and goals transform into new lists of z3 assertions. This form would allow for a more normal kanren interleaving search.

But, by using the internal state of the z3 `Solver` with the push/pop interface we get efficiency and convenience gains but what is left behind is a rather bizarre and very stateful program.

## Implementation

So let's write out the most basic goal for equality. The goal is parametrized by the left and right hand side of the equality. The goal itself is a generator that takes in a solver and yields with the solver in a new state with new assertions added. We add the `s.check() == sat` for early pruning of this branch of the search using Z3's solving capabilities. When the generator finally dies, the solver should be returned to it's original state. That is a contract that needs to be correctly implemented by every goal. It's a tightwire walk for sure, but if you build your goals using combinators, you're ok.

```python
from z3 import *
def eq(x,y):
    def goal(s):
        s.push()
        s.add(x == y)
        if s.check() == sat:
            yield
        s.pop()
    return goal
```

In fact we can abstract this to lift an arbitrary z3 assertion into a goal. via the same pattern basically. I change just `s.check() == sat` to `s.is_good()` because I'll want the flexibility later. You can think of them as the same.

```python
def lift(z3assert):
    def res(s):
        s.push()
        s.add(z3assert)
        if s.is_good():
            yield
        s.pop()
    return res
def lift2(op):
    def res(x,y):
        return lift(op(x,y))
    return res
import operator
eq = lift2(operator.__eq__)
```

Now we can define the kanren goal combinators `disj` and `conj` for disjunction (or) and conjunction (and). `conj1` basically runs two goals in sequence, the second one being in the scope of the first. `disj1` . `disj` and `conj` are the multiargument forms for convenience. The `*` are the wacky little notations for python varargs.

```python
def conj1(f,g):
    def res(s):
        for _ in f(s):
            if s.is_good():
                #print(s.model())
                yield from g(s)
    return res
import functools
def conj(*args):
    return functools.reduce( conj1 , args )
def disj1(f,g):
    def res(s):
        # itertools.chain(f(s), g(s))
        yield from f(s) 
        yield from g(s)
    return res
def disj(*args):
    return functools.reduce(disj1, args)
```

Anther convenience function is `conde` which operates like a scheme `cond` expression and also a bit like a pattern match.

```python
def conde(*args):
    return disj(*map(lambda l: conj(*l), args))
```

Some other helpful routines. `Zzz` makes a thunked goal. This is a confusing thing, but it is necessary when you define a recursive relation or else the thing will go into an infinite loop.
`mempty` is a failure and `printmodel` does not change the assertion state and can be useful for debugging.

```python
def Zzz(thunk_goal):
    def res(s):
        yield from thunk_goal()(s)
    return res
def printmodel(s):
    if s.is_good():
        print(s.model())
    yield
def mempty(s):
    if False:
        yield # trick into making it an iterator?

```

Finally we need a toplevel `run` function. There are some choices here. This version takes in the variables of interest in `qs` and projects them out of the model. This does not return every possible solution to the query just one per successful branch.

```python
def runq(qs, goal):
    s = Solver()
    s.is_good = lambda : s.check() == sat
    for _ in goal(s):
        m = s.model()
        yield {q: m.eval(q) for q in qs}
```

Here's a basic query. We have the full flexibility of Z3 available to us

```python
x, y = Ints("x y")
ex_goal2 = conde( [eq(x,3) , eq(y,4) ] ,
                  [eq(y,5) , eq(x,6) ] )
list(runq([x,y],ex_goal2))
# [{x: 3, y: 4}, {x: 6, y: 5}]
```
A more complex query. Note I had to use the `Zzz` combinator on the recursive call to `appendo` to stop the thing from going off the rails.

 ```python
# Declare a List of integers
List = Datatype('List')
# Constructor cons: (Int, List) -> List
List.declare('cons', ('car', IntSort()), ('cdr', List))
# Constructor nil: List
List.declare('nil')
# Create the datatype
List = List.create()
cons = List.cons
car  = List.car
cdr  = List.cdr
nil  = List.nil

def appendo(x,y,z):
    h = FreshInt()
    t = FreshConst(List)
    res = FreshConst(List)
    return conde( [ eq(x, nil), eq(y,z) ],
                  [ eq( x, cons(h,t)), eq(z, cons(h, res)) , Zzz( lambda : appendo(t,y,res ))] 
                )

q = Const("q", List)
r = Const("r", List)
x, y = Ints("x y")
list(runq([q,r], appendo(q,r,cons(2,cons(42,cons(17,nil))))))
 ```


And interesting alternative to `runq` is to use iterative deepening. This is a complete search method. This will return multiple times for the same path through the goals. We could avoid this by tracking known models and disallowing them as we go along.

```python
def run_iterative_deep(goal):
    s = Solver()
    s.is_good = lambda : s.num_scopes() < s.max_depth and s.check() == sat
    for depth in itertools.count(start=1):
        s.max_depth = depth
        for _ in goal(s):
            yield s.model()
```


### Kanren's Conj and Disj vs Z3's And and Or

I've been struck by the similarity of programming Z3 and macro programming / compile time programming.
Python in the use of Z3py is a macro level metalanguage for Z3. Sometimes you have a choice about whether to perform computation in the python layer or in the Z3 layer. Do you want to define a z3 `Function` or use a metalevel python function to define exponentiation? Do you want to use python records or Z3 records for your data types? You can use tricks of partial evaluation to do as much as possible at the python layer.
The two layers are not completely interchangeable though. Python lacks the solving/inference/reversible capabilities of Z3, and Z3 notably lacks recursion and iteration in full power.

Z3 queries are inflexible in certain senses. It feels like you need to kind of define a fixed universe over which Z3 is to search.
The two main sidesteppings of this restriction are the use of quantifiers and relatedly the fixedpoint engines, for both of which your mileage may vary.

It is probably desirable to use Z3 And/Or whenever possible to displace disj/conj. Z3 is going to do a much better job of searching than my junk, and it reduces the number of push/pop.

### A Quantified Z3 append for comparison

You can define append using quantifiers. This is a full definition. However, the use of quantifiers using the regular solving engine in Z3 usually means it will not be able to return a model because it can't in general figure out if it satisfied the entire quantified definition (quantification is in a sense asserting an infinite number of formula, which is hard to check in general). The fixedpoint solvers <https://rise4fun.com/z3/tutorialcontent/fixedpoints>  _can_ do something with this, but that is for another post someday.

```python
from z3 import *
# Declare a List of integers
List = Datatype('List')
# Constructor cons: (Int, List) -> List
List.declare('cons', ('car', IntSort()), ('cdr', List))
# Constructor nil: List
List.declare('nil')
# Create the datatype
List = List.create()
cons = List.cons
car  = List.car
cdr  = List.cdr
nil  = List.nil


append = Function("apppend", List, List, List)

q = Const("q", List)
r = Const("r", List)
l = Const("l", List)
h = Int("h")
t = Const("t", List)
append_def = [
    ForAll([l], append(nil, l) == l),
    ForAll([h,t,l], append(cons(h,t), l) == cons(h, append(t,l) ))
]
s = Solver()
s.add(append_def)
s.add( append(q,r)  == cons(2,cons(42,cons(17,nil))) )
s.check() # doesn't return
```

## Why the quotes around minikanren?
The Kanren family usually uses a complete search of some kind, interleaving the branches of the search tree. Since I'm abusing the push/pop mechanism of z3, it is most convenient to use a depth first search, which is incomplete. In this sense, what we have here is not really a Kanren.

And yet, I did reference the microkanren paper to write this and am building an embedded relational programming language with kanren-like surface syntax. So maybe this is still a Kanren.

### Bits and Bobbles

Use this for reachability analysis on programs (while loops, etc).

Make a version of run that exhausts a branch by asserting the model must change back to itself.

Compare and contrast with Z3 built-in fixed point solvers like BMC and Spacer.

Use unsat core to backjump more?

How to do full minikanren style interleaving search?

Combining logic programming with constraints/smt is not at all a new thing.
It goes under the name CLP (constraint logic programming) and CHC (constrained horn clauses).

<https://www.youtube.com/watch?v=KsC_9_-NuQg>

