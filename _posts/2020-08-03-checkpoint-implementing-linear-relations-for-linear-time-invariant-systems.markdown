---
author: philzook58
comments: true
date: 2020-08-03 03:33:45+00:00
layout: post
link: https://www.philipzucker.com/checkpoint-implementing-linear-relations-for-linear-time-invariant-systems/
slug: checkpoint-implementing-linear-relations-for-linear-time-invariant-systems
title: 'Checkpoint: Implementing Linear Relations for Linear Time Invariant Systems'
wordpress_id: 2906
tags:
- categorytheory
- julialang
- WIP
---




I'm feeling a little stuck on this one so I think maybe it is smart to just write up a quick checkpoint for myself and anyone who might have advice.







The idea is to reimplement the ideas here computing linear relations [https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/](https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/) There is a lot more context written in that post and probably necessary background for this one.







Linear relations algebra is a refreshing perspective for me on systems of linear equations. It has a notion of composition that seems, dare I say, almost as useful as matrix multiplication. Very high praise. This composition has a more bidirectional flavor than matrix multiplication as it a good fit for describing physical systems, in which interconnection always influences both ways.







In the previous post, I used nullspace computations as my workhorse. The nullspace operation allows one to switch between a constraint (nullspace) and a generator (span) picture of a vector subspace. The generator view is useful for projection and linear union, and the constraint view is useful for partial-composition and intersection. The implementation of linear relation composition requires flipping between both views.







I'm reimplementing it in Julia for 2 reasons







  * To use the Julia ecosystems implementation of module operations
  * to get a little of that [Catlab](https://algebraicjulia.github.io/Catlab.jl/latest/).jl magic to shine on it.






It was a disappointment of the previous post that I could only treat resistor-like circuits. The new twist of using module packages allows treatment of inductor/capacitor circuits and signal flow diagrams. 







When you transform into Fourier space, systems of linear differential equations become systems of polynomial equations $latex \frac{d}{dx} \rightarrow i \omega$. From this perspective, [modules ](https://en.wikipedia.org/wiki/Module_(mathematics))seem like the appropriate abstraction rather vector spaces. Modules are basically vector spaces where one doesn't assume the operation of scalar division, in other words the scalar are rings rather than fields. Polynomials are rings, not fields. In order to treat the new systems, I still need to be able to do linear algebraic-ish operations like nullspaces, except where the entries of the matrix are polynomials rather than floats.







[Syzygies](https://en.wikipedia.org/wiki/Linear_relation) are basically the module analog of nullspaces. Syzygies are the combinations of generators that combine to zero. Considering the generators of a submodule as being column vectors, stacking them together makes a matrix. Taking linear combinations of the columns is what happens when you multiply a matrix by a vector. So the syzygies are the space of vectors for which this matrix multiplication gives 0, the "nullspace". 







Computer algebra packages offer syzygy computations. Julia has bindings to Singular, which does this. I have been having a significant and draining struggle to wrangle these libraries though. Am I going against the grain? Did the library authors go against the grain? Here's what I've got trying to match the catlab naming conventions:






    
    <code>using Singular
    
    import Nemo
    
    using LinearAlgebra # : I
    
    CC = Nemo.ComplexField(64)
    P, (s,) = PolynomialRing(CC, ["s"])
    i = Nemo.onei(CC) # P(i) ? The imaginary number
    
    #helpers to deal with Singular.jl
    eye(m) = P.(Matrix{Int64}(I, m, m)) # There is almost certainly a better way of doing this. Actually dispatching Matrix?
    zayro(m,n) = P.(zeros(Int64,m,n)) #new zeros method?
    mat1(m::Int64) = fill(P(m), (1,1) )
    mat1(m::Float64) = fill(P(m), (1,1) )
    mat1(m::spoly{Singular.n_unknown{Nemo.acb}}) = fill(m, (1,1))
    
    # Objects are the dimensionality of the vector space
    struct DynOb
        m::Int
    end
    
    # Linear relations represented 
    struct DynMorph
      input::Array{spoly{Singular.n_unknown{Nemo.acb}},2}
      output::Array{spoly{Singular.n_unknown{Nemo.acb}},2}
    end
    
    dom(x::DynMorph) = DynOb(size(x.input)[2])
    codom(x::DynMorph) = DynOb(size(x.output)[2])
    id(X::DynOb) = DynMorph(eye(X.m), -eye(X.m))
    
    # add together inputs
    plus(X::DynOb) = DynMorph( [eye(X.m) eye(X.m)] , - eye(X.m) )
    
    
    mcopy(X::DynOb) = Dyn( [eye(X.m) ; eye(X.m)] , -eye(2*X.m) ) # copy input
    
    delete(A::DynOb) = DynMorph( fill(P.(0),(0,A.m)) , fill(P.(0),(0,0)) )   
    create(A::DynOb) = DynMorph( fill(P.(0),(0,0)) , fill(P.(0),(0,A.m)) )
    dagger(x::DynMorph) = DynMorph(x.output, x.input)
    
    # cup and cap operators
    dunit(A::DynOb) = compose(create(A), mcopy(A))
    dcounit(A::DynOb) = compose(mmerge(A), delete(A))
    
    
    scale(M) = DynMorph( mat1(M),mat1(-1))
    diff =  scale(i*s) # differentiation = multiplying by i omega
    integ = dagger(diff)
    #cupboy = DynMorph( [mat1(1) mat1(-1)] , fill(P.(0),(1,0)) )
    #capboy = transpose(cupboy)
    
    #terminal
    
    # relational operations
    # The meet
    # Inclusion
    
    # I think this is a nullspace calculation?
    # almost all the code is trying to work around Singular's interface to one i can understand
    function quasinullspace(A)
       rows, cols = size(A)
       vs = Array(gens(Singular.FreeModule(P, rows)))
       q = [sum(A[:,i] .* vs) for i in 1:cols]
       M = Singular.Module(P,q...)
       S = Singular.Matrix(syz(M)) # syz is the only meat of the computation
       return Base.transpose([S[i,j] for j=1:Singular.ncols(S), i=1:Singular.nrows(S) ])
    end
    
    function compose(x::DynMorph,y::DynMorph) 
        nx, xi = size(x.input)
        nx1, xo = size(x.output)
        @assert nx1 == nx
        ny, yi = size(y.input)
        ny1, yo = size(y.output)
        @assert ny1 == ny
        A = [ x.input                x.output P.(zeros(Int64,nx,yo)) ;
              P.(zeros(Int64,ny,xi)) y.input  y.output    ]
        B = quasinullspace(A)
        projB = [B[1:xi       ,:] ;
                 B[xi+yi+1:end,:] ]
        C = Base.transpose(quasinullspace(Base.transpose(projB)))
        return DynMorph( C[:, 1:xi] ,C[:,xi+1:end] )
    end
    
    # basically the direct sum. The monoidal product of linear relations
    function otimes( x::DynMorph, y::DynMorph) 
        nx, xi = size(x.input)
        nx1, xo = size(x.output)
        @assert nx1 == nx
        ny, yi = size(y.input)
        ny1, yo = size(y.output)
        @assert ny1 == ny
        return DynMorph( [ x.input                P.(zeros(Int64,nx,yi));
                           P.(zeros(Int64,ny,xi)) y.input               ],
                          [x.output                P.(zeros(Int64,nx,yo));
                           P.(zeros(Int64,ny,xo))  y.output               ])
        
    end</code>







I think this does basically work but it's clunky.







### Thoughts







I need to figure out Catlab's diagram drawing abilities enough to show some circuits and some signal flow diagrams. Wouldn't that be nice?







![](https://www.philipzucker.com/wp-content/uploads/2020/08/Screenshot-from-2020-08-02-23-05-12.png)







I should show concrete examples of composing passive filter circuits together. 







There is a really fascinating paper by Jan Willems where he digs into a beautiful picture of this that I need to revisit [https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf](https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf)







[https://golem.ph.utexas.edu/category/2018/06/the_behavioral_approach_to_sys.html](https://golem.ph.utexas.edu/category/2018/06/the_behavioral_approach_to_sys.html)







Is all this module stuff stupid? Should I just use rational polynomials and be done with it? Sympy? $latex \frac{d^2}{dx^2}y = 0$ and  $latex \frac{d}{dx}y = 0$ are different equations, describing different behaviors. Am I even capturing that though? Is my syzygy powered composition even right? It seemed to work on a couple small examples and I think it makes sense. I dunno. Open to comments.







Because univariate polynomials are a principal ideal domain (pid), we can also use [smith form](https://en.wikipedia.org/wiki/Smith_normal_form)s rather than syzygies is my understanding. Perhaps AbstractAlgebra.jl might be a better tool?







Will the syzygy thing be good for band theory? We're in the multivariate setting then so smith normal form no longer applies.



