---
author: philzook58
comments: true
date: 2017-08-31 17:15:14+00:00
layout: post
link: https://www.philipzucker.com/using-z3-solve-simple-logic-puzzle/
slug: using-z3-solve-simple-logic-puzzle
title: Using Z3 to solve a simple logic puzzle
wordpress_id: 850
---

I was checking out Smullyan's Lady of the Tiger. It starts with some very simple logic puzzles. Let's make Z3 do one for us!

There are 100 politicians

at least one is honest

for any two at least one is crooked

How many honest politicians are there?

And here is one way of encoding this into z3:

    
    from z3 import *
    
    politicians = [ Bool('x%s' % i) for i in range(100) ]
    #True is an honest politicians#false is a crooked one
    atleastonehonest = Or(politicians)
    
    forall2atleastonecrooked = And([ Or(Not(i), Not(j)) for i in politicians for j in politicians if not i is j])
    
    #sol, something = solve(forall2atleastonecrooked,atleastonehonest)
    s = Solver()
    s.add(forall2atleastonecrooked,atleastonehonest)
    #print(s.check())
    s.check()
    solution = s.model()
    #print dir(solution[0])
    #print solution
    #print map(solution)
    #print is_true(solution[0])
    #print bool(solution[0])
    solbool = [solution[pol] for pol in politicians]
    print "honest men:", len([x for x in solbool if x ])


Z3 is kind of a pain in that it won't immediately cast to bools when I want them. A mistake I made at first was missing that "not i is j" in the list comprehension. Also an unfortunate feature is that this does not make it clear that there is a unique answer, due to permutations of the variables. But if we just asked for the number of honest, it's not clear to me how to encode the forall2 constraint. Very curiously, z3 picks 'x18' to be the one honest man. I wonder why?
