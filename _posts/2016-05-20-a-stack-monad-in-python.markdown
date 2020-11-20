---
author: philzook58
comments: true
date: 2016-05-20 20:01:56+00:00
layout: post
link: https://www.philipzucker.com/a-stack-monad-in-python/
slug: a-stack-monad-in-python
title: A Stack Monad in Python
wordpress_id: 444
tags:
- monad
---

So I saw

http://learnyouahaskell.com/for-a-few-monads-more#state

where he uses a stack as an example of a state monad.

I get the Maybe monad I think and some others, but the State monad is one more level of abstraction that confuses me still. When I try to reason about it, I fail to see the point sometimes. Pure state to state functions are immediately composable. To also have a return value and return state usually doesn't seem necessary.

The actual monad is the full state transforming and value returning function. This is very abstract.

Most functions you'll be writing will return a function that takes state and outputs (val, state) pair. It's weird.

Though I'd try doing it in python. It is sticky. Maybe I need to churn through it a bit more. The fact that I need to keep putting those toss away functions in there seems strange. Perhaps I need a bit more think. Although the do notation does expand out to that often I think.

    
    # This is horrific
    
    #currying would help correspondence to haskell. Then push(a,stack): would be the same as push(a): return lambda stack
    def push(a):
    	return lambda stack: (None, [a] + stack)
    
    
    pop = lambda stack:  (stack[0], stack[1:])
    def myreturn(x):
    	return lambda stack: (x, stack)
    
    def runStackFunc(statefulstackfunc):
    	return statefulstackfunc([])
    
    #state -> (val ,state)
    def bind(statemanip, regtostatemanip):       #  return val  #state
    	return lambda state: regtostatemanip(statemanip(state)[0])(statemanip(state)[1])
    
    #Do notation is also pretty clutch. You need to toss the value a lot
    
    print runStackFunc(bind(bind(bind(push(1), lambda _ : push(2)), lambda __ :pop), push))
    # associativity?  The value tossing lambdas need to be switched outside of the binds. That seems weird
    print runStackFunc(bind(push(1), lambda _ :bind( push(2), lambda __: bind(pop, push))))
    
    print runStackFunc(bind(bind(push(1), lambda _: push(2)), lambda __: bind(pop, push)))


It is neato how the associativity kind of works.



Edit:

I later realized I had forgotten >> aka then

    
    '''
    def then(statemanip, dontneednothin):
    	return lambda state: (dontneednothin(statemanip(state)[1]))
    '''
    #More general 
    def then(statemanip, dontneednothin):
    	return bind(statemanip, lambda _: dontneednothin)
    
    print runStackFunc(bind(then(then(push(1), push(2)), pop), push))




Pretty straightforward. Just added in the throwaway lambda into a function. Can do this manually or by referring back to bind (which is better since then basically just has the logic of bind in it).


