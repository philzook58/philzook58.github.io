---
author: philzook58
comments: true
date: 2016-07-08 19:42:56+00:00
layout: post
link: https://www.philipzucker.com/python-generators-and-infinite-power-series/
slug: python-generators-and-infinite-power-series
title: python generators and infinite power series
wordpress_id: 470
---

So I found an interesting paper describing how to use lazy lists to represent infinite series and i thought I'd try to do the same thing in python using generators, which are similar.

It's cool but kind of a mess. I assume with more thought this could be tweaked into a clear thing. The thunking is especially gross. Maybe totally unnecessary? At some point I felt like it was the right thing to do for some reason and then I stuck with it.

The obvious simpler way would be to truncate the series at n=100 or something and just use lists. Why would I ever want terms higher than that anyhow? Interesting exercise though.



    
    # lazy evaluation
    # sometimes a problem can be simple if we're working in an insanely huge space.
    # if you can proceed thorugh the space lazily, this might be an acceptable strategy
    
    
    # decorator to convert function into a function that returns a thunk that will evelauted to the original function
    def thunkify(func):
    	def func_wrapper(*args, **kwargs):
    		return lambda: func(*args, **kwargs)
    	return func_wrapper
    
    #geometric series
    def geo():
    	while True:
    		yield 1
    
    #exponential expansion
    def exp():
    	num = 0.
    	fact = 1.
    	yield 1.
    	while True:
    		num += 1.
    		fact = fact * num
    		yield 1./fact
    
    @thunkify
    def const(c):
    	yield c
    	while True:
    		yield 0
    
    def oneX():
    	yield 0
    	yield 1
    	while True:
    		yield 0
    
    @thunkify
    def convertArray(myarray):
    	for i in myarray:
    		yield i
    	while True:
    		yield 0
    
    # oneX = convertArray([0,1])
    
    
    myexp = exp()
    print next(myexp)
    print next(myexp)
    print next(myexp)
    
    ''' #an old unthunked approach. I need to instantiate all generators before passing them.
    def add(a, b):
    	while True:
    		yield next(a) + next(b)
    
    mysum = add(oneX(), const(3))
    print next(mysum)
    print next(mysum)
    print next(mysum)
    '''
    
    
    #If i do this way, need to always returns thunks for all constructors.
    # such as const(3): def thunk
    @thunkify
    def add(a, b):
    	#could this be lazier? # do I want egnerator combinators to instantiate the genereators?
    	a = a()
    	b = b()
    	while True:
    		yield next(a) + next(b)
    
    
    mysum = add(oneX, const(3))
    mysum = mysum()
    print next(mysum)
    print next(mysum)
    print next(mysum)
    
    
    #I fear rethunking will lead to weird bugs. rehtunked guys might be linked to each other in ways you might not expect
    def rethunk(a):
    	return lambda: a
    
    @thunkify
    def constmult(c, a):
    	a = a()
    	while True:
    		yield c * next(a)
    
    
    
    @thunkify
    def mult(a,b):
    	abar = a()
    	bbar =b()
    	a0 = next(abar)
    	b0 = next(bbar)
    	bbar = rethunk(bbar)
    	abar = rethunk(abar)
    	yield a0 * b0
    	remainprod = add(constmult(a0, bbar), mult(abar,b))
    	remainprod = remainprod()
    	while True:
    		yield next(remainprod)
    
    @thunkify
    def integrate(C, a):
    	num = 0.
    	a = a()
    	yield C
    	while True:
    		num += 1.
    		yield next(a)/num
    
    @thunkify
    def differentiate(a):
    	a = a()
    	num = 0.
    	next(a) #toss away constant
    	while True:
    		num += 1.
    		yield num * next(a) 
    
    
    def evalseries(x, n, series):
    	pass
    
    def take(n, gen):
    	gen = gen()
    	arr = []
    	for i in range(n):
    		arr.append(next(gen))
    	return arr
    
    print take(5, exp)
    print take(5, mult(oneX, exp))
    print take(5, integrate(0,oneX))
    print take(5, differentiate(oneX))
    print take(5, differentiate(exp))
    
    
    
    
    
    



