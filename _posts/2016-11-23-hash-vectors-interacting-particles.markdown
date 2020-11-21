---
author: philzook58
comments: true
date: 2016-11-23 22:12:32+00:00
layout: post
link: https://www.philipzucker.com/hash-vectors-interacting-particles/
slug: hash-vectors-interacting-particles
title: Hash Vectors and Interacting Particles
wordpress_id: 568
---

An approach I don't see much is using a hash table for vectors. I have seen a key value pair list vector. It makes sense. I think it gives you more algorithmic flexibility in the indices. Typical vectors are encoded in contiguous arrays index by integers. But encoding things that way feels kind of rigid. Perhaps in some circumstances the flexibility is worth the performance hit?

Here's an implementation

    
    import copy
    
    
    
    class HashVect(dict):
    #	def __init__(self):
    #		self.v = {}
    
    	def __add__(self,b):
    		c = copy.copy(self)
    		return c.add_in_place(b)
    
    	def add_in_place(self,b):
    		for key, value in b.iteritems():
    			if key in self:
    				self[key] += value
    			else:
    				self[key] = value
    		return self
    
    	def s_mult_in_place(self,a):
    		for key,value in self.iteritems():
    			self[key] = value * a
    
    	def s_mult(self,a)
    		return HashVect(map(lambda (k,v): (k,v*a)  , self.iteritems()))
    		# also
    	def __rmul__(self, linOp):
    		return self.bind(linOp)
    
    	def bind(self, linOp):
    		newVect = HashVect()
    		for key,value in self.iteritems():
    				tempvec = linOp(key)
    				tempvec.s_mult_in_place(value)
    				newVect.add_in_place(tempvec)
    		return newVect
    
    




Basically it subclasses dict and overrides plus operator to do vector addition. Also scalar multiplication and bind is a monadic approach to linear operators.

Here is a requisite fermionic annihilation and creation operator example to see where I'm trying to go with this. I want to automatize interacting perturbation theory about a fermi surface (particle and hole creation). I think I see how I could derive interesting things like effective single particle Hamiltonians (perturbatively Schur complement out the higher particle number subspaces). I'd like to see how I can automatically or manually do infinite summations like RPA and others, but I don't yet.

    
    from hashvect2 import HashVect
    
    N = 10
    x1 = 1
    x2 = 3
    state = HashVect()
    
    state[()]=1.
    #state[(x1,x2)] = 1.
    
    def adag(x):
    	def adagfun(occupation):
    		if x in occupation:
    			return HashVect({})
    		else:
    			phase = (-1.) ** len(filter(lambda y: x < y, occupation))
    			temp = list(occupation)
    			temp.append(x)
    			newocc= tuple(sorted(temp))		
    			return HashVect({newocc: phase})
    	return adagfun
    
    def a(x):
    	def afun(occupation):
    		if x in occupation:
    			phase = (-1.) ** len(filter(lambda y: x < y, occupation))
    			newocc = filter(lambda y: y != x, occupation)	
    			return HashVect({newocc: phase})	
    		else:
    			return HashVect({})
    	return afun
    
    print state.bind(adag(1)).bind(adag(0))
    
    print adag(1) * (adag(0) * state)


I think that mostly I may not want to use the bind interface to do things. A lot of stuff is just index twiddling and it doesn't make much sense to use the full machinery. Building the Hamiltonian terms directly out of a  and adags will be ghastly inefficient.

I think to get the noninteracting green's functions to work I need to build a basis transformer into the noninteracting energy eigenbasis?

I'm working in a particle number emphasizing basis. This may be very bad.

Could I implement a renormalization procedure by Schur complementing out high frequency subspace then rescaling (this is loose talk. I'm not sure what I mean yet)?

$ J a^\dagger $ terms for injecting from external leads. Fully interacting Landauer-Buttiker conductance? Also connection to generating function techniques in QFT?

Maybe I should be doing this in Haskell? I like Haskell. I like types. I like persistence and non mutation. I think I'll want numpy facilities down the road though.

I am trying actively to avoid thinking about how unoptimized and slow this will be. Maybe Pypy or other accelerating compilers will help.
