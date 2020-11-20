---
author: philzook58
comments: true
date: 2020-07-19 20:41:19+00:00
layout: post
link: https://www.philipzucker.com/a-buchberger-in-julia/
slug: a-buchberger-in-julia
title: A Buchberger in Julia
wordpress_id: 2876
tags:
- algorithm
- julialang
---




Similarly to how Gaussian elimination putting linear equations into LU form solves most linear algebra problems one might care about, Buchberger's algorithm for finding a [Grobner basis](http://www.scholarpedia.org/article/Groebner_basis) of a system of multivariate polynomial equations solves most questions you might ask. Some fun applications







  * Linkages
  * Geometrical Theorem proving. Circles are x^2 + y^2 - 1 = 0 and so on.
  * [Optics](https://www.philipzucker.com/grobner-bases-and-optics/)
  * Constraint satisfaction problems. x^2 - 1 = 0 gives you a boolean variable. It's a horrible method but it works if your computer doesn't explode.
  * Energy and momentum conservation. "Classical Feynman Diagrams" p1 + p2 = p3 + p4 and so on.
  * Frequency domain circuits and linear dynamical systems ;) more on this another day






To learn more about Grobner bases I highly recommend [Cox Little O'Shea](http://people.dm.unipi.it/caboara/Misc/Cox,%20Little,%20O%27Shea%20-%20Ideals,%20varieties%20and%20algorithms.pdf)







To understand what a Grobner basis is, first know that [univariate polynomial long division](https://en.wikipedia.org/wiki/Polynomial_long_division) is a thing. It's useful for determining if one polynomial is a multiple of another. If so, then you'll find the remainder is zero.







One could want to lift the problem of determining if a polynomial is a multiple of others to multivariate polynomials.  Somewhat surprisingly the definition of long division has some choice in it. Sure, x^2 is a term that is ahead of x, but is x a larger term than y? y^2? These different choices are admissible. In addition now one has systems of equations. Which equation do we divide by first? It turns out to matter and change the result. That is unless one has converted into a Grobner Basis.







A Grobner basis is a set of polynomials such that remainder under multinomial division becomes unique regardless of the order in which division occurs.







How does one find such a basis? In essence kind of by brute force. You consider all possible polynomials that could divide two ways depending on your choice.







Julia has packages for multivariate polynomials. [https://github.com/JuliaAlgebra/MultivariatePolynomials.jl](https://github.com/JuliaAlgebra/MultivariatePolynomials.jl) defines an abstract interface and generic functions. DynamicPolynomials gives flexible representation for construction.  TypedPolynomials gives a faster representation.







These already implement a bulk of what we need to get a basic Buchberger going: Datastructures, arithmetic, and division with remainder. With one caveat, there is already a picked monomial ordering. And it's not lexicographic, which is the nice one for eliminating variables. This would not be too hard to change though?







Polynomial long division with respect to a set of polynomials is implemented here







[https://github.com/JuliaAlgebra/MultivariatePolynomials.jl/blob/9a0f7bf531ba3346f0c2ccf319ae92bf4dc261af/src/division.jl#L60](https://github.com/JuliaAlgebra/MultivariatePolynomials.jl/blob/9a0f7bf531ba3346f0c2ccf319ae92bf4dc261af/src/division.jl#L60)







Unfortunately, (or fortunately? A good learning experience. Learned some stuff about datastructures and types in julia so that's nice) quite late I realized that a very similar Grobner basis algorithm to the below is implemented inside of of[ SemiAlgebraic.jl package](https://github.com/JuliaAlgebra/SemialgebraicSets.jl/blob/master/src/groebner.jl). Sigh.






    
    <code>using MultivariatePolynomials
    using DataStructures
    
    
    function spoly(p,q)
        pq = lcm(leadingmonomial(p),leadingmonomial(q))
        return div(  pq , leadingterm(p) ) * p - div(pq , leadingterm(q)) * q
    end
    
    function isgrobner(F::Array{T}) where {T <: AbstractPolynomialLike} # check buchberger criterion
        for (i, f1) in enumerate(F)
            for f2 in F[i+1:end]
                s = spoly(f1,f2)
                _,s = divrem(s,F)
                if !iszero(s)
                    return false
                end
            end
        end
        return true
    end
    
    function buchberger(F::Array{T}) where {T <: AbstractPolynomialLike}
        pairs = Queue{Tuple{T,T}}()
        # intialize with all pairs from F
        for (i, f1) in enumerate(F)
            for f2 in F[i+1:end]
                enqueue!(pairs, (f1,f2))
            end
        end
        
        # consider all possible s-polynomials and reduce them
        while !isempty(pairs)
            (f1,f2) = dequeue!(pairs)
            s = spoly(f1,f2)
            _,s = divrem(s,F)
            if !iszero(s) #isapproxzero? Only add to our set if doesn't completely reduce
                for f in F
                    enqueue!(pairs, (s,f))
                end
                push!(F,s)
            end
        end
    
        # reduce redundant entries in grobner basis.
        G = Array{T}(undef, 0)
        while !isempty(F)
            f = pop!(F)
            _,r = divrem(f, vcat(F,G))
            if !iszero(r)
                push!(G,r)
            end
        end
        
        return G
    end</code>







Some usage. You can see here that Gaussian elimination implemented by the backslash operator is a special case of taking the Grobner basis of a linear set of equations






    
    <code>
    using DynamicPolynomials
    @polyvar x y
    
    buchberger( [ x + 1.0 + y   , 2.0x + 3y + 7  ] )
    #= 
    2-element Array{Polynomial{true,Float64},1}:
     -0.5y - 2.5
     x - 4.0
    =#
    
    [ 1 1 ; 2  3 ] \ [-1 ; -7]
    #=
    2-element Array{Float64,1}:
      4.0
     -5.0
    =#
    
    
    buchberger( [ x^3 - y , x^2 - x*y ])
    #=
    3-element Array{Polynomial{true,Int64},1}:
     -xy + y²
     y³ - y
     x² - y²
    =#</code>













## Improvements







Many. This is not a good Buchberger implementation, but it is simple. See [http://www.scholarpedia.org/article/Buchberger%27s_algorithm](http://www.scholarpedia.org/article/Buchberger%27s_algorithm) for some tips, which include criterion for avoiding unneeded spolynomial pairs, and smart ordering. Better Buchberger implementations will use the f4 or f5 algorithm, which use sparse matrix facilities to perform many division steps in parallel. My vague impression of this f4 algorithm is that you prefill a sparse matrix (rows correspond to an spolynomial or monomial multiple of your current basis, columns correspond to monomials) with monomial multiples of your current basis that you know you might need.







In my implementation, I'm tossing away the div part of `divrem`. It can be useful to retain these so you know how to write your Grobner basis in terms of the original basis.







You may want to look at the julia bindings to [Singular.jl](https://github.com/wbhart/Singular.jl)







## Links







  * [https://mattpap.github.io/masters-thesis/html/src/groebner.html](https://mattpap.github.io/masters-thesis/html/src/groebner.html)
  * [https://www-polsys.lip6.fr/~jcf/FGb/index.html](https://www-polsys.lip6.fr/~jcf/FGb/index.html)
  * [https://github.com/wbhart/Singular.jl](https://github.com/wbhart/Singular.jl)
  * [https://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/](https://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/)
  * [https://www.philipzucker.com/computing-syzygy-modules-in-sympy/](https://www.philipzucker.com/computing-syzygy-modules-in-sympy/)
  * [https://www.philipzucker.com/grobner-bases-and-optics/](https://www.philipzucker.com/grobner-bases-and-optics/)
  * [https://scicomp.stackexchange.com/questions/21699/benchmarks-for-gr%c3%b6bner-bases-and-polynomial-system-solution](https://scicomp.stackexchange.com/questions/21699/benchmarks-for-gr%c3%b6bner-bases-and-polynomial-system-solution)
  * [https://mathoverflow.net/questions/322518/computing-groebner-basis-for-a-complicated-systems-of-polynomials](https://mathoverflow.net/questions/322518/computing-groebner-basis-for-a-complicated-systems-of-polynomials)
  * [https://cstheory.stackexchange.com/questions/12326/unification-and-gaussian-elimination](https://cstheory.stackexchange.com/questions/12326/unification-and-gaussian-elimination)
  * [https://homepage.divms.uiowa.edu/~fleck/181content/taste-fixed.pdf](https://homepage.divms.uiowa.edu/~fleck/181content/taste-fixed.pdf)
  * [http://www.scholarpedia.org/article/Buchberger%27s_algorithm](http://www.scholarpedia.org/article/Buchberger%27s_algorithm)
  * [https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/toy_buchberger.html](https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/toy_buchberger.html)
  * Operads grobner [https://www.maths.tcd.ie/~vdots/AlgebraicOperadsAnAlgorithmicCompanion.pdf](https://www.maths.tcd.ie/~vdots/AlgebraicOperadsAnAlgorithmicCompanion.pdf) What the heck. From Evan's site [https://www.epatters.org/wiki/algebra/computational-category-theory.html](https://www.epatters.org/wiki/algebra/computational-category-theory.html)
  * [https://github.com/tkluck/FGb.jl](https://github.com/tkluck/FGb.jl)








