---
author: philzook58
comments: true
date: 2017-02-08 22:37:32+00:00
layout: post
link: https://www.philipzucker.com/sat-solving-smt/
slug: sat-solving-smt
title: SAT solving and SMT
wordpress_id: 591
---

I've been playing around with Coq and Agda and Idris, doing the exercises in the Software Foundations book. These have similar flavor, using the Curry-Howard isomorphism to use the type system as a way of proving stuff. It may not be an entire coincidence that the systems put in place to tell when you have a float int smash can be extended to full proving systems. The property of never having a float int collision is a proposition that requires proof. And somehow the compiler systematically guarantees it when type checking, without exhaustively running the program.

I came across The Little Prover, which talks about ACL and Dracula, theorem provers in the tradition of Lisp. There is not obviously types involved. This feels like an alternative tradition. More ad hoc?

There is another approach. More automated and not type theory based. They limit themselves to specialized domains. SAT solvers tell whether there exists a set of vairable values that can make

SAT is how you

My impression is that surprisingly often you are better off mapping your problem to the SAT form and then handing it off to really good solvers.

Check out this sudoku solver.

https://www.continuum.io/blog/developer/sat-based-sudoku-solver-python

I brew installed minisat (it's not clear to me if this is a top of the line solver. The[ competition](http://www.satcompetition.org/) page pegs it as pretty old, which isn't necessarily bad) and pip installed satispy.

https://pypi.python.org/pypi/satispy



I've heard that Z3 can be used in capture the flag competitions and [cracking stuff ](https://rolandsako.wordpress.com/2016/02/17/playing-with-z3-hacking-the-serial-check/)

Z3 has a python interface.

This has an interesting

Liquid Types? I've heard that mentioned before. Some kind of merging of the type theory tradition and SMT. I wonder if guys in the know would not emphasize such a dichotomy.
