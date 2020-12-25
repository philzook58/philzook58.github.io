---
author: Philip Zucker
date: 2020-12-25
layout: post
categories:
- Formal Methods
tags:
- python
- z3
title: Weakest Precondition with Z3Py
---

[Weakest Precondition](https://en.wikipedia.org/wiki/Predicate_transformer_semantics) is a technique to reason about imperative programs using logic. Instead of interpreting statements by their effect on one state, they define their action on predicates on states. It really isn't so hard to make this perfectly concrete and computational by using the syntax tree and solving capability of Z3 as exposed by the python bindings.

I was extremely surprised by this technique when I first saw it. The verification technique that is more obvious to me is to roll out a program execution, giving each new instance of a variable a new logical variable and making each statement a constraint between then. This is similar to the form you see for a trajectory optimization problem in control and is what you'll find in a bounded model checking verifier. This is more of the flavor of my previous [post on TLA+ in Z3Py](https://www.philipzucker.com/Modelling_TLA_in_z3py/). Instead, the weakest precondition technique tracks and manipulates a predicate over a single state as it traverse backwards through the program.

First, let's look at a simple sketch of an interpreter for a toy language based on interpreting statements as state transformers.

### Statements as State Transformers

I'm not exactly sure how one thinks while programming. I think when I'm programming, I sort of have this cloudy notion of variables existing and changing. Or course I know they are made of bits held in registers or memory which is made of flip flops which are made of transistors and so on, but I mostly don't think about this unless it seems relevant.

But if I start to nail down what that means, my first model of what a program does is that each statement changes the state of some abstract machine. The states are piles of variables holding values like integers, booleans, and arrays.

To pin this down even more concretely, we can build an interpreter. The state could be represented using a python dictionary holding the bindings from variable names to their values. Each statements has as its meaning a $$state \rightarrow state$$ function. This function takes in a dictionary (the state) of the current bindings of variables to values and changes the binding to a new value. Sequencing statements is composing these functions.

```python
# the set_ statement sets the value in the dictionary to a new one
def set_(x, e):
    def res(vars):
        vars[x] = evalexpr(e, vars) # assuming we've defined evalexpr somewhere
        return vars
    return res

def seq(stmt1, stmt2):
    def res(vars):
        vars1 = stmt1(vars)
        vars2 = stmt2(vars)
        return vars2
    return res
```


### Statements as Set Transformers


A related but subtly distinct model is to consider what the program does on sets of states. One way of representing finite sets is as a list. So for example our assignment statement could be replaced by

```python 
def set_(x, e):
    def res(set_of_vars):
        for vars in set_of_vars:
            vars[x] = evalexpr(e,vars)
        return set_of_vars
    return res
```

Finite sets are a very constrained family of sets however. What if we wanted to represent set of states where the x variable are positive. Well, we could start to add special sets that we know how to deal with like intervals. This `Interval` data structure could be represented by a class that holds the two endpoints of the interval. What about if now we want to represent the set of (`x <= 0` and `x >= 4`). Well of course we could add a special `Union` class that holds a list of intervals and manipulate that. But then what if we need to represent all even numbers? Well, maybe we could add a special class that... yada yada yada.

### Logic and Sets

What going down this road leads to is basically the language of logic. Logical expressions like those found in Z3Py can be interpreted as the sets of values of the free variables for which the expression evaluates to `True`. This is a powerful idea, especially when backed by the automation provided by Z3. By asking Z3 to check for satisfiability we can determine if sets are empty, if they intersect, whether one is a subset of the other, etc. The syntactic manipulation of Z3 logical expressions allows us to almost trivially _describe_ a reasonable and large class of set manipulations. Constructing these formula does almost no interesting work, but when we query the Z3 solver interesting questions are answered.

```python
# Some example set manipulations
x = Int("x")

set1 = x >= 2 # The set of all integers greater than or equal to 2
set2 = x < 0 # The set of all integers less than zero

union12 = Or(set1,set2)

intersection12 = And(set1,set2)

complement1 = Not(set1)


s1 = x > 0
s2 = x > 1
prove(Implies(  s2 , s1  )) # is s2 a subset of s1?

f = Function("f", IntSort(), IntSort())
y = Int("y")
preimage = substitute( set1  , x, f(y)) # the preimage of set1 under f.
image = Exists([x], And(set1, y == f(x) ) # the image of f on set1 


```

### Weakest Precondition

Predicate transformer semantics are a way of describing what programs statements do in terms of their effect on the syntactic logical expressions describing states of the program.

Weakest precondition (WP) makes the choice to "run" the program backwards. The weakest precondition of a statement and postcondition is the largest starting set that maps inside the postcondition set under that statement. You might think that this set would be hard to describe, but it is actually easily constructed by syntactic manipulation of the postcondition formula.

Here are some of the basic statements.

Assignment replaces wherever the assigned variable appears in the postcondition with the right hand side of the assignment statement. This is a little confusing but it makes sense after a while. Give it a minute and think about it.

```python
def set_(v, e):
    return lambda post: substitute(post,(v, e))
```

For example the simple program that sets `a` to 4.

```python
post = a == 4
prog = set_(a,IntVal(4))
pre = prog(post) # 4 == 4
prove(pre) # returns proved
```

As a side note, there is also Strongest Postcondition (SP) semantics. I think there is a good answer for why WP is more common/useful, but I don't know it. I think it may be that assignment takes a simpler form in WP than it does in SP.

But of course we want more complicated programs we need to sequence multiple statements. `seq` applies the statements in the reverse order to the post condition. `begin` does the same thing for many statements using python varargs. It gives us a convenient syntax for code blocks in which the commas of function arguments look something like the semicolons of an ordinary language. It's cute.

```python
def seq(s1,s2):
    return lambda post: s1(s2(post))

def begin(*args):
    def res(post):
        wp = post
        for s in reversed(args):
            wp = s(wp)
        return wp
    return res
```


`if_` statements encode that either one or the other branch is taken depending on the truth of the condition.

```python
def if_(cond, t, e):
    return lambda post: Or(Implies(cond, t(post)) , And(Not(cond), e(post)))
```

Some other helpful little combinators.


```python
# skip does nothing. Analogous to a python pass statement
skip = lambda post: post
# abort always fails
abort = lambda post: BoolVal(False)

# assert_ fails if prop not satisfied
def assert_(prop):
    return lambda post: And(post, prop)
# assume_ adds an assumption on the state
def assume_(prop):
    return lambda post: Implies(prop, post)

# debug is like skip expect it prints the postcondition so we can see it
def debug(post):
    print(post)
    return post

# verify takes a post and precondition and queries Z3 to see if the code will 
# satisfy the postcondition if run on an input state satisfying the precondition
def verify_fun(pre, post, body):
    prove(Implies(pre, body(post)))
```

### Some Examples

With that we can already do some interesting stuff.

Consider the following simple sorting program for 2-tuples

```python
def twosort(a,b):
    if b < a:
        temp = a
        a = b
        b = temp
    else:
        pass
    return a,b
```

Is it right? Does it always return a sorted pair?

We can encode the program
```python
a, b, temp = Ints("a b temp")
prog = \
if_(b < a,
    begin(
         set_(temp,a),
         set_(a, b),
         set_(b, temp)
         ),
    skip
   )
```

And then query with a sorted `a <= b` postcondition

```
verify_fun(True, a <= b, prog)
```

Not that this property alone does not tell us if it is a sorting function. Consider the following.

```python
prog = \
if_(b < a,
    set_(a,b),
    skip
   )

# also true, but not a sort.
verify_fun(True, a <= b, prog)
```

Another interesting thing to do is verify functional equivalence of two programs. We can do this via a neat trick. If we take the two programs and run them in an arbitrary sequential order, and if they operate over disjoint states, we can reduce the problem to a single program verification. Here we have two different swapping functions, one that uses a `temp` variable and one that does some clever arithmetic to avoid it. Tricks like this, or a similar thing using XOR, can sometimes help save a little memory.

```python
# Simple program equivalence

prog1 =  \
begin(
         set_(temp,a),
         set_(a,b),
         set_(b, temp)
         )

c, d = Ints('c d')
prog2 = \
begin(
    set_(c, d - c),
    set_(d, d - c),
    set_(c, c + d)
)

verify_fun( And(a == c, b == d), And(a == c, b == d), seq(prog1,prog2))
```

In some sense ALL verification is a comparison problem. There is no god given notion of what a program _should_ do. Verification is always with respect to a spec. Usually a spec if written in a different language than the program, a language built to be clear and expressive, but not necessarily efficiently executable. In this case our spec language and program language are identified.

### Loops 

That's all well and good, but to get really juicy, unfortunately we at least have to introduce loops.
The simplest of this is a fixed for loop with ahead of time bounds. In this case, we can just unroll the loop to execute it.

```python
# For a fixed for loop, just unroll it.
def for_(i, start,end, body):
    def res(post):
        wp = post
        for ival in reversed(range(start,end)):
            wp = seq( set_(i, IntVal(ival)), body )(wp)
        return wp
    return res
```

However, in many cases this is not possible. Very often we want the bound on the loop to depend on the incoming data. In order to verify properties of the loop, it requires an extra annotation that you don't typically see in everyday languages, the loop invariant. Because it isn't exactly clear how many times the loop will run, we need some kind of inductive argument. We can show that the loop invariant is true at the start of the loop, and that it is preserved after ever run of the loop body, then it will be true when the loop finally stops, if it stops.

It is a somewhat strange thing that the while loop when run on a single state does the same thing, regardless of the choice of invariant, but from the perspective of being a predicate transformer, different invariants lead to very different statements. They drastically change what states we can guarantee will land in the postcondition set.

```python
def while_(cond, inv, *body):
    def res(post):
        vs = list(get_vars(post))
        return And( inv , 
        ForAll(vs, And( Implies( And(cond, inv), begin(*body)(inv))
                        , Implies( And(Not(cond), inv), post) )))
    return res
```

This is actually what is known as weakest liberal precondition. It is also important to establish terminating of the loop, which is not obvious and a whole kettle of fish.

Here's a simple `square` function. The useful invariant in this case is that in every run of the loop, `a` holds larger multiples of `n`. In particular `a == n*u`. It is also convenient that we can directly encode the specification into Z3.

```python

def square(n):
    a = 0
    i = 0
    while i < n:
        assert a == n * i # invariant
        i = i + 1
        a = a + n
    return a

i, n = Ints("i n")
prog = begin(
    set_(a, IntVal(0)),
    set_(i, IntVal(0)),
    while_(i < n   , And(i < n + 1, 0 <= i, a == n*i),
         set_(i, i + 1),
         set_(a, a + n)
        )
)

verify_fun( n >= 0 , a == n * n,  prog )
```

Here's a different program for which we can't as directly encode the specification to Z3, summing all the numbers from 0 to n. Instead we can define a simple recursive definition to Z3 and then show that the imperative program computes the same values.

```python
sumn = Function("sumn", IntSort(),IntSort())
sumndef = ForAll([a], sumn(a) == If(a <= 0, 0, sumn(a-1) + a))

prog = \
begin(
set_(i, IntVal(0)),
while_(i != n+1,  a == sumn(i)  ,
      set_(i, i + 1),
      set_(a, a + i)
      )
)

verify_fun(And(sumndef, n >= 0), sumn(n) == a, prog )
```


### Links

Projects that are trying to do this for real
Are there nuances here? These projects are not exactly doing Weakest precondition maybe.

* [Dafny](https://rise4fun.com/Dafny/tutorial)
* [Spark](https://www.adacore.com/about-spark)
* WhyML http://why3.lri.fr/python/
* Frama-C <https://frama-c.com/>
* JML   <https://www.openjml.org/>
* Viper <https://www.pm.inf.ethz.ch/research/viper.html>


* <https://en.wikipedia.org/wiki/Predicate_transformer_semantics>
* [Discipline of Programming](https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf) - Edsger Dijkstra
* <https://www.cs.utexas.edu/~isil/cs389L/HoareLogic3-6up.pdf> Isil Dilig's course
* <https://www.cs.cmu.edu/~aldrich/courses/17-355-18sp/notes/notes11-hoare-logic.pdf>
* Winskel's book
* Software Foundations <https://softwarefoundations.cis.upenn.edu/plf-current/toc.html>
* Greg Andrew's concurrency
