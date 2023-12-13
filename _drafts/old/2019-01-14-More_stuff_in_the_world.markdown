---
author: philzook58
comments: true
date: 2019-01-14 19:29:09+00:00
layout: post
link: https://www.philipzucker.com/?p=1539
published: false
slug: More stuff in the world
title: More stuff in the world
wordpress_id: 1539
---

1/14/19

Formal methods for C

Unfortunately, there isn't an obvious winner here. And there are a lot of derelict projects.

I think that frama-c, the coq ecosystem, and maybe ATS in that order seem the best?

Interesting experience report from 2014. Tried frama-c. Tried VST.

https://www.imperialviolet.org/2014/09/07/provers.html

https://www.imperialviolet.org/2014/09/11/moveprovers.html

https://cs.stackexchange.com/questions/13785/formal-program-verification-in-practice

Some blasting lists

https://github.com/stanislaw/awesome-safety-critical

https://github.com/mre/awesome-static-analysis

https://github.com/awesomo4000/awesome-provable

"Safe" subsets of C/ Recommendations

https://en.wikipedia.org/wiki/MISRA_C - a spec for a subset of C

https://ieeexplore.ieee.org/document/1642624 - 10 Rules from JPL

Frama-c http://frama-c.com/ Sometimes connects spec to code? Different sub pieces plugins that do different things.

https://alhassy.github.io/InteractiveWayToC/

http://www.cas.mcmaster.ca/~alhassm/#outline-container-orgb6e1d9c

ACSL

why3 - Seems to bind together a bumch of automated and interactive proversd somehow?

http://why3.lri.fr/

It is a language. Kind of ML-ish. Also kind of SMTLIB like.

https://arxiv.org/abs/1405.7615 - verification of control systems

SPARK - similar spec language for ADA

http://toccata.lri.fr/tools.en.html

ATS - It's own beast. A dependently typed programming language with tight c integration

The Coq universe:

http://vst.cs.princeton.edu/ - Appel coq project. Separation logic. Uses one of the internal languages of compcert. C minor?

http://compcert.inria.fr/ - verified c compiler. commercially connected to AbsInt now?

https://github.com/Microsoft/checkedc . checkedc just does out of bounds checking?

https://swt.informatik.uni-freiburg.de/teaching/SS2014/FormalMethodsforC

http://www.astree.ens.fr/

https://www.cprover.org/cbmc/ - c bounded model checker

Spec languages.

Promela, Spin, NuSMV, TLA+

alt-ergo - an smt solver like z3 or cvc4

http://gappa.gforge.inria.fr/ - gappa, floating point numeric solver

metitarski - https://www.cl.cam.ac.uk/~lp15/papers/Arith/

https://stp.github.io/

http://mathsat.fbk.eu/download.html - MathSAT. an SMT solver

http://www.cs.cmu.edu/~modelcheck/vcegar/ - verilog counter example guided refinement

https://rise4fun.com/

boogie, dafny

https://www.youtube.com/watch?v=V1rm2oMhdzc

https://en.wikipedia.org/wiki/BLAST_model_checker

http://cseweb.ucsd.edu/~rjhala/blast.html

Hmm. Rhanjit Jhala was on this project

https://cpachecker.sosy-lab.org/index.php

https://en.wikipedia.org/wiki/Category:Abstract_interpretation - has galois connection as a topic listed?

https://en.wikipedia.org/wiki/Cppcheck

https://en.wikipedia.org/wiki/ECLAIR



* * *



Knouth Bendix. Term Rewriting

http://www.jaist.ac.jp/~hirokawa/tool/

http://cl-informatik.uibk.ac.at/software/tct/

Maude

TTT

Vampire? E thoerem Prover. AProve

haskell temrination checking http://aprove.informatik.rwth-aachen.de/eval/Haskell/

https://github.com/haskell-rewriting

http://termination-portal.org/wiki/Termination_Competition

https://tacas.info/toolympics.php

http://www.tptp.org/CASC/

http://project-coco.uibk.ac.at/

http://www.wikicfp.com/cfp/servlet/event.showcfp?eventid=66746&copyownerid=60586

-----

Matlab:

YalMIP

Sostools

gloptipoly

mpt

POP - http://paroc.tamu.edu/Examples/index.php https://pubs.acs.org/doi/full/10.1021/acs.iecr.6b01913

octave control - https://octave.sourceforge.io/control/overview.html all sort of weird stuff

Cvxpy

dccp - convex concave programming

dmcp - multi convex - take variable sets on at a time. If some variables are fixed, is convex. Kind of a cooridnate descent heurstic

yalmip mentioned - MaxPlus control using tropical algebra?

unums - a flaoting point compettitor for interval artihmetic?

h-finity control

explicit mpc

model reduction

controller reduction

big m solver

MC++ mccormick envelopesm, polyhedral something, chebyshev something



 	    


MC++ (version 2.0) provides a collection of C++ classes for construction, manipulation and bounding of factorable functions. The bounding methods include interval bounds, spectral bounds, convex/concave relaxations, Taylor and Chebyshev model estimators, ellipsoidal bounds, and polyhedral relaxations.

https://omega-icl.github.io/mcpp/page_SPECBND.html

    
    from z3 import *
    import matplotlib.pyplot as plt
    import numpy as np
    s = Solver()
    
    
    T = 5.0
    N = 40
    dt = T/N
    
    thetas = [Real("th" + str(i)) for i in range(N)]
    omegas = [Real("dth" + str(i)) for i in range(N)]
    mods = [ToInt(thetas[i]) for i in range(N)]
    #mods = [Int("mod" + str(i)) for i in range(N)]
    abovevert = [Bool("vert" + str(i))for i in range(N)]
    rem = [Real("rem" + str(i)) for i in range(N)]
    
    s.add(thetas[0] == 1)
    s.add(omegas[0] == 0.0)
    
    
    for i in range(N):
    	#pass
    	#s.add(-1/4 <= rem[i])
    	#s.add(rem[i] <= 1/4)
    	#s.add(0 <= rem[i])
    	#s.add(rem[i] <= 0.5)
    	#s.add(
    	#	Or ( And(abovevert[i],     mods[i] == thetas[i] + rem[i]),
    	#		 And(not abovevert[i], mods[i] == thetas[i] + 0.5 + rem[i] )))
    	#s.add(If(abovevert[i]
    	#      , mods[i] == thetas[i] + rem[i]
    	#      , mods[i] == thetas[i] + 0.5 + rem[i] ))
    	s.add(If(Or(thetas[i] - mods[i] <= 0.25, thetas[i] - mods[i] >= 0.75),
    		abovevert[i] == True,
    		abovevert[i] == False))
    	#      , mods[i] == thetas[i] + rem[i]
    	#      , mods[i] == thetas[i] + 0.5 + rem[i] ))
    
    
    
    for t in range(N-1):
    	s.add(thetas[t+1] == thetas[t] + dt*omegas[t])
    	#.add(omegas[t+1] == omegas[t] + dt*(thetas[t] - k)   ) 
    	#.add(omegas[t+1] == omegas[t] - dt*(thetas[t] - k)   ) 
    	#s.add(Or([a != 0 for a in l]))
    	#s.add(
    	#      Or ( And(abovevert[t+1],     omegas[t+1] == omegas[t] + dt*rem[t+1] ),
    	#	       And(not abovevert[t+1], omegas[t+1] == omegas[t] - dt*rem[t+1] )))
    	#s.add(If(abovevert[i]
    	#	, omegas[t+1] == omegas[t] + dt*rem[t+1]
    	#	, omegas[t+1] == omegas[t] - dt*rem[t+1]))
    	s.add(If(abovevert[t]
    		, omegas[t+1] == omegas[t] - dt*(thetas[t+1] - mods[t+1])
    		, omegas[t+1] == omegas[t] + dt*(thetas[t+1] - (mods[t+1] - 0.25)) 
    		))
    
    print(s.check())
    
    m = s.model()
    print(m)
    
    def convert(x):
    	if is_int_value(x):
    		return x.as_long()
    	elif is_rational_value(x):
    		return x.numerator_as_long()/x.denominator_as_long()
    	elif is_algebraic_value(x):
    		return convert(x.approx(7))
    
    npthetas = np.array([convert(m[th])  for th in thetas])
    print([m[th]  for th in abovevert])
    plt.plot(npthetas)
    plt.show()
    
    print(npthetas)
    
    
    
    



    
    m = Model(solver=CbcSolver())
    N = 20
    @variable(m, -pi <= θ[1:N] <= pi)
    @variable(m, -pi <= ω[1:N] <= pi)
    @variable(m, -0.7 <= τ[1:N] <= 0.7)
    @variable(m, -1 <= s[1:N] <= 1)
    @variable(m, -1 <= c[1:N] <= 1)
    @constraint(m, θ[1] == -0.1)
    @constraint(m, ω[1] == 0.0)
    dt = 0.5
    xd = range(-pi, stop = pi, length = 5)
    for t in 1:(N-1)
        @constraint(m, s[t] == piecewiselinear(m, θ[t], xd, y -> sin(y)))
        @constraint(m, c[t] == piecewiselinear(m, θ[t], xd, y -> cos(y)))
        @constraint(m, θ[t+1] == θ[t] + ω[t] * dt)
        @constraint(m, ω[t+1] == ω[t] + (τ[t] - s[t+1]) * dt)
    end
    @objective(m, Min, sum(c)) # minimize f(x)


cassette?
