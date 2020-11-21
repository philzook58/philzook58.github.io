---
author: philzook58
comments: true
date: 2020-03-23 03:29:00+00:00
layout: post
link: https://www.philipzucker.com/computing-syzygy-modules-in-sympy/
slug: computing-syzygy-modules-in-sympy
title: Computing Syzygy Modules in Sympy
wordpress_id: 2719
categories:
- Formal Methods
tags:
- math
- sympy
---




Reading about the methods of computational algebra is really compelling to me because some domains that seem like natural fits







  * Mechanisms
  * CAD (computed aided design)
  * Automated geometric theorem proving 
  * Optics - [http://www.philipzucker.com/grobner-bases-and-optics/](http://www.philipzucker.com/grobner-bases-and-optics/)
  * Sum of Squares techniques  [http://www.philipzucker.com/deriving-the-chebyshev-polynomials-using-sum-of-squares-optimization-with-sympy-and-cvxpy/](http://www.philipzucker.com/deriving-the-chebyshev-polynomials-using-sum-of-squares-optimization-with-sympy-and-cvxpy/)
  * Energy momentum conservation networks






I used to have no idea that multivariate polynomial equations had guaranteed methods that in some sense solve those systems. It's pretty cool.







However, when I was pouring over the two Cox Little O'shea volumes, the chapter on modules made my eyes glaze over. Who ordered that? From my perspective, modules are vector spaces where you cripple the ability to divide scalars. Fair enough, but the language is extremely confusing and off-putting. Syzygy? Free Resolution? Everything described as homomorphisms and exact sequences? Forget it. Why do this? This is too abstract. 







So I've been on the lookout for some application to motivate them. And I think I have at least one. Capacitor Inductor circuits.







A pure resistive circuit can be treated by linear algebra. The voltages and currents are connected by linear relations. [http://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/](http://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/)







The common way to describe inductor capacitors circuits is by using phasor analysis, where the resistances become impedances which have a frequency parameter in them. I'm not entirely convinced that it isn't acceptable to just use linear algebra over rational functions of the frequency, but I have some reason to believe more carefulness regarding division may bear fruit. I suspect that carefulness with division corresponds  to always sticky issues of boundary conditions.







On a slightly different front, I was very impressed by Jan Willems Open Dynamical systems. [https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf](https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf) In it, he talks about differential equations as describing sets of possible trajectories of systems. He uses module theory as a way to manipulate those sets and conditions from module theory to describe interesting qualitative features like controllability of those systems.







He sticks to the tools of Hermite and Smith forms of matrices, as he is mostly interested in single variable polynomials as the ring in question.  Here's my issues







  1. I'm not really familiar with these forms
  2. I can't find good implementations of these. Perhaps here [https://desr.readthedocs.io/en/latest/index.html](https://desr.readthedocs.io/en/latest/index.html) (Differential Equation Symmetry Reduction), which seems like an interesting project for other reasons as well. Maybe I'm a fool, but I'd like to stick to python for the moment.
  3. I also have an inkling that modules over multivariate polynomials will come in handy for playing around with band theory (or partial different equations for that matter). Maybe something interesting to be said regarding topological materials? 






It seems like Groebner basis techniques should acceptably solve these systems as well. Converting between the analog of range and nullspace representations as I did in my previous post corresponds to syzygy calculations in the terminology of modules







Sympy does supply a Groebner basis algorithm, but not much beyond that. The [AGCA module](https://docs.sympy.org/latest/modules/polys/agca.html) that should supply calculations over modules is mostly a lie. The documentation lists many functions that are not implemented. Which is too bad.







Edit: @isuruf claims that there is a syzygy calculation tucked away inside sympy that I had not discovered.  I haven't tried it. https://gist.github.com/philzook58/95b6b6ef97c4b2047d9833b7993fa1ef#gistcomment-3506126







However, you can can hack in syzygy calculation into a Groebner basis calculation. I started pouring over chapter 5 of Using Algebra again, and it really has everything you need.







When one converts a set of polynomials to a Groebner basis, one is getting an equivalent set of polynomials with excellent properties. A Groebner basis is an analog of reduced echelon form of a matrix (these rows are equivalent to the old rows), and Buchberger's algorithm is an analog of gaussian elimination. [https://mattpap.github.io/masters-thesis/html/src/groebner.html#special-case-1-gauss-algorithm](https://mattpap.github.io/masters-thesis/html/src/groebner.html#special-case-1-gauss-algorithm) . You can  find a decomposition of a polynomial in your ideal by a multivariate division algorithm with respect to the Groebner basis. This is the analog of the ability of an upper triangular matrix to be easily inverted.







You can perform a number of tricks by adding in dummy variables to the Groebner basis algorithm. The first thing you can do with this sort of trick is track how to write the Groebner basis in terms of the original basis. This is the analog of working with an augmented matrix during gaussian elimination. [https://en.wikipedia.org/wiki/Augmented_matrix](https://en.wikipedia.org/wiki/Augmented_matrix)







I found this Maple documentation helpful in this regard (although formatted horrifically)







[https://www.maplesoft.com/support/help/Maple/view.aspx?path=Groebner%2fBasis_details](https://www.maplesoft.com/support/help/Maple/view.aspx?path=Groebner%2fBasis_details)







We want to track a matrix A that writes the Groebner basis vector G to the original vector of polynomials F. $ G = AF$. We do it by attaching the each generator f of F a fresh marker variable f + m. Then the coefficients on m in the extended Groebner basis correspond to the matrix A. Think about it.







The other direction matrix can be found via the reduction algorithm with respect to the Grobner basis  $ F = BG$ . This is pretty straightforward given that sympy implemented reduction for us.







From these we determine that







G = GBA  
F = FAB







Finding the syzygies of a set of generators is the analog of finding a nullspace of a matrix. A syzygy is a set of coefficients to "dot" onto the generators and get zero. In linear algebra talk, they are sort of orthogonal to the generator set.







The ability to find a nullspace gives you a lot of juice. One can phrase many problems, including solving a $ Ax=b$ system of equations as a nullspace finding problem. 







Proposition 3.3 of Using Algebra tells us how to calculate the generators of a syzygy module for a Groebner basis. It's a little strange. The S-polynomial of two generators from the basis is zero after reduction by the basis. The S-polynomial plus the reduction = 0 gives us a very interesting identity on the generators (a syzygy) and it turns out that actually these generate all possible syzygies. This is still not obvious to me but the book does explain it.






```
import sympy as sy

def spoly(f,g,*gens):
    ltf = sy.LT(f,gens)
    ltg = sy.LT(g,gens)
    lcm = sy.lcm(ltf,ltg)
    s = lcm / ltf * f - lcm / ltg * g
    return s

#grobner tracking. Maintaining the relation of the grobner basis to the original
def extended_groebner(F, *gens):
    n = len(F)
    markers =  [sy.Dummy() for i in range(n)]
    Fext = [ f + a for a, f in zip(markers, F)]
    gen_ext = list(gens) + markers
    Gext = sy.groebner(Fext, gen_ext)
    A = [[g.coeff(m) for m in markers ] for g in Gext]
    G = [ sy.simplify(g - sum( [ m * aa  for m,aa in zip(markers, a)  ] )) for a,g in zip(A,Gext) ] #remove dummy parts
    assert( sy.simplify(sy.Matrix(G) -  sy.Matrix(A) * sy.Matrix(F)).is_zero )
    # maybe assert buchberger criterion
    return G, A
    
    
def reduce_basis(F,G,*gens):
    B,rems = list(zip(*[sy.reduced(f,G, gens) for f in F]))
    print(B)
    print(rems)
    assert( all([r == 0 for r in rems] )) # assuming G is a grobner basis
    assert( sy.simplify(sy.Matrix(F) - sy.Matrix(B) * sy.Matrix(G)).is_zero   )
    return B

# generators for the syzygies of G. Schreyer's Theorem. Cox Little Oshea Theorem 3.2 chapter 5
def syzygy(G,*gens): # assuming G is groebner basis
    n = len(G)
    basis = []
    I = sy.eye(n)
    for i, gi in enumerate(G):
        for j, gj in enumerate(G): 
            if i < j:
                s = spoly(gi,gj,*gens)
                print(s)
                a,r = sy.reduced( s , G, gens )
                assert(r == 0) # should be groebner basis
                lti = sy.LT(gi,gens)
                ltj = sy.LT(gj,gens)
                lcm = sy.lcm(lti,ltj)
                ei = I[:,i] 
                ej = I[:,j]
                basis.append(lcm / lti * ei - lcm / ltj * ej - sy.Matrix(a))
                assert( sy.simplify(sy.Matrix(G).T * basis[-1]).is_zero)  # should all null out on G
    return basis

x,y,z,s = sy.symbols("x y z s")
F = [x+y+z, x*y+y*z+z*x, x*y*z-1]
G, A = extended_groebner(F, x,y,z)
B = reduce_basis(F,G,x,y,z)
Gsyz = syzygy(G)
```






Proposition 3.8 of Using Algebra tells us how to get the syzygies of the original generators given the previous information. We map back the generators of G and append the columns I - AB  also







I - AB columns are syzygys of F. F (I - AB) = F - FAB = F- F = 0  using the equation from above F = FAB 







I'm still trying to figure out how to do calculations on modules proper. I think it can be done be using dummy variables to turn module vectors into single expressions. There is an exercise in Using Algebra that mentions this.






```
def matrix_to_eqs(m):
   nrows, ncols = m.shape
   gens = [sy.Dummy() for i in range(ncols)]
   eqs = m @ sy.Matrix(gens)
   return eqs, gens
def eqs_to_matrix(eqns, gens):
    return sy.Matrix( [[ eq.coeff(g) for g in gens] for eq in eqns])
```






Grobner basis reference suggestions:







  * The Cox Little O'Shea books 
  * [http://www.scholarpedia.org/article/Groebner_bases](http://www.scholarpedia.org/article/Groebner_bases)
  * There is a paper often referenced about applications of grobner basis to control theory. It's also a pretty excellent introduction to grobner bases period  [http://people.reed.edu/~davidp/pcmi/buchberger.pdf](http://people.reed.edu/~davidp/pcmi/buchberger.pdf)  [http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.205.1191&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.205.1191&rep=rep1&type=pdf)
  * The sort of side docs to the sympy grobner basis package are phenomenal [https://mattpap.github.io/masters-thesis/html/src/groebner.html](https://mattpap.github.io/masters-thesis/html/src/groebner.html)
  * Other piles of references here [http://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/](http://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/)


