---
author: philzook58
comments: true
date: 2019-10-21 04:12:17+00:00
layout: post
link: https://www.philipzucker.com/?p=1559
published: false
slug: Algebraic Numbers / Polynomial stuff / Convex stuff, Grobner pendulum
title: Algebraic Numbers / Polynomial stuff / Convex stuff, Grobner pendulum
wordpress_id: 1559
---




Polynomials. They are numbers unrealized. One can multiply them. divide them. 







Mutivariate polynomials can be thought of as univariate polys with polynomial coefficients. Suppose I had plugged in numbers. Then we'd just.







In order to satisfy mutiple polynomial equations, they need to share roots. And we can't proceed numerically, it has to be symbolic (we can only assume a ring, not a field for the coefficients). Shared symbolic roots is surprisingly a tractable problem. Why is that?







There is a similar question for shared common factors for integers. In that case the gcd is easily computed. The gcd is the shared factors of two integers. A piece of that is bezout's identity. [https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity](https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity) When two things have shared factors it is possible to combine them linearly to add up to zero.







[https://www3.risc.jku.at/people/buchberg/papers/2001-02-19-A.pdf](https://www3.risc.jku.at/people/buchberg/papers/2001-02-19-A.pdf)







polynomial mutiplication can be thought of as a matrix in V\otimesV -> V. A little peculair. V -> V \otimes V is  







Can I think of grobner basis calculation in a linear alegrba way?







The same thing is true of polynomials. If two polynomials have a shared factor, they can be linearly combined together to equal zero.







Linearity is a relative concept. Linear in what?







Polynomials are syntactic expressions (algebra). Polynomials are gemoetrical objects. Polynomials are functions. (Double -> Double). Polynomials are a vector space. The basis is tuples of integers corresponding to the powers.







I could have sworn I was writing some things about root finding. Strum sequences and stuff. And there was a book I had found from the lincoln library. Ok. It's in my nonlinear algerba dump.







[https://math.stackexchange.com/questions/2911256/a-way-to-represent-algebraic-numbers-in-a-computer](https://math.stackexchange.com/questions/2911256/a-way-to-represent-algebraic-numbers-in-a-computer)







Cool thing about algebraic numbers. Using the characteristic matrix to represent the polynomial sounds great. We could make a numpy library?







Interval Arithmetic + implicit polynomials







[https://www.researchgate.net/publication/329524513_A_Verified_Implementation_of_Algebraic_Numbers_in_IsabelleHOL](https://www.researchgate.net/publication/329524513_A_Verified_Implementation_of_Algebraic_Numbers_in_IsabelleHOL)







Verified implementation of algebraic numbers in Isabelle HOL







[https://github.com/uwplse/reincarnate-aec/blob/master/src/ExactArith.ml](https://github.com/uwplse/reincarnate-aec/blob/master/src/ExactArith.ml)







The hidden ExactNum library.







Michael Carbin Ben Sherman [https://dl.acm.org/citation.cfm?id=3341703](https://dl.acm.org/citation.cfm?id=3341703) There is a video. jesse michel.







Cyclotomic package - [http://hackage.haskell.org/package/cyclotomic](http://hackage.haskell.org/package/cyclotomic)













Indefinite summation can be solved with grobner basis? The second chapter of that paplications book. That sounds really cool.







Naturals are the example of an interesting thing to factor. We can always factor integers by brute force.







Factoring polynomials over then naturals can also done by brute force.







Factoring polynomials over finite fields can also be done by brute force.







[https://en.wikipedia.org/wiki/Factorization_of_polynomials](https://en.wikipedia.org/wiki/Factorization_of_polynomials)







Double roots are easier to find.







Galois theory is about factoring. The modern theory is about the connections between fields and groups








https://www.amazon.com/Lie-Groups-Physics-Geometry-Introduction/dp/0521884004








This book has a curious opener on galios theory







Modern Computer Algebra







Kronecker's method. Plug in, factor result. Try the different factorizations of the output







Vandermonde matrix.







Least suqares fitting. You evulate the nonlinear thing at points. Those become values. Then you can fit.







On the roots of a polynomial, nonlinear operations become linear. The quotient ring. x is linear by cheating, until we cap it at the end We're playing some kind of shell game. Forget x and x^2 are related at all and consider x^2 to just be a new variable. The eigenvectors of any f(x) are vandermonde vectors.







These are unfortunately not symmetric matrices. :(. But least squares is







Representiation theory for the roots.







We can do the same thing for multivariate polynomials







suggestion. Take a column vector of the generators. Then start adding x * f and so on the the column. How do we notice relations? Division I guess. Do we also want 1 x x^2 and so on? #gens kron var1pow kron var2pow ... schur reduction on gens goes to above form?






    
    <code>hstack 
    </code>







Envelope operations. Computing the envelope of a family of circles coming off of another circle. Could also try some wavy thing. This in principle is generating eikonals. We could revisit my sol le witt. sympy has a plotting thing.






    
    <code>from sympy import *
    
    x1, y1, x2, y2, dx, dy = symbols('x1, y1, x2, y2, dx, dy')
    
    def dist(x,y,d):
        return x**2 + y**2 - d**2
    
    e1 = dist(x1,y1,2)
    e2 = dist(x1-x2 ,y1 - y2 , 1)
    
    print(Poly(e1).coeffs())
    print(Poly(e1).terms())
    print(dir(Poly(e1)))
    e3 = diff(e1,x1)*dx + diff(e1,y1)*dy
    e4 = diff(e2,x1)*dx + diff(e2,y1)*dy
    #e3 = diff(e1,x1)*dx + diff(e1,y1)
    #e4 = diff(e2,x1)*dx + diff(e2,y1)
    # soluton by determinant of differentials
    #e3 = diff(e1,x1) * diff(e2,y1) - diff(e1,y1) * diff(e2,x1) 
    #e4 = 0
    #e4 = diff(e2,x1)
    #e3 = dist(x1 + dx,y1 + dy,2)
    #e4 = dist(x1 + dx - x2 , y1 + dy - y2 , 1)
    print(e1)
    print(e2)
    print(e3)
    print(e4)
    #print(solve(e1,e2,e3,e4))
    print(groebner([e1,e2,e3,e4], y1, x1, dx, dy, x2, y2, order='lex'))
    print(factor(groebner([e1,e2,e3,e4], y1, x1, dx, dy, x2, y2, order='lex')[-1]))
    
    '''
    Any line with dx dy is homogenous in them, which makes sense.
    The last equations is indeed the two new circles
    We can arbitrarily set dy = 1. Why is this okay?
    dx and dy do have 
    
    do a graph coloring?
    finite step a pendulum
    do fermats principle
    
    '''
    print(groebner([3*x1 + 7*y1 - 3, y1*2 + 4 *x1 - 8], x1, y1, order='lex'))
    
    print(groebner([dist(x1,y1,1), dist(x1-0.5,y1+.1,1)], x1, y1, order='lex'))</code>







Idea: How to make grobner out of gauss?







f \otimes x^n \otimes y^n mod {f}. These are all the possible derivations. (and inlcudes the s polynomials bucherberge produces.







## Algebraic numbers






More interesting books:




https://wstein.org/books/ant/




https://pseudoprofound.wordpress.com/2016/07/09/some-fun-with-algebraic-numbers/




https://perso.univ-rennes1.fr/marie-francoise.roy/bpr-ed2-posted2.html




Algebraic numbers.




Describe numbers by polynomials with integer coefficients.




Fractions are subclass (d*x-n = 0)




Can say which root with approximate numeric value.




Can turn approximate values back into representations using LLL. 1. possiblity for arithemtic. Use approximate arithemtic. Then perform LLL procedure. Verify that the answer is correct. Presumably easier? If fails: 1. Fall back to other method. Resultant / Grobner basis? 2. Just put a Nothing in the polynomial field of the number 3. Increase precision?




I don't understand the intuition behind the LLL polynomial finding algorithm.




Subset of this is to use trignometric numbers that just have cosines and sines. ExactNum Ocaml package




https://www.youtube.com/watch?v=pMDoNfKXYZg







Trigonometric numbers just need to apply the product and sum rules of angles. Then we can just work with the lowest common divisor of the angles we need.







As that julia article describes, negating and inverting are easy. And rooting.




The simplest way to add and multiply roots is to convert the coefficients of the polynomials, which are elem,entary symmettirc functions in the roots, to power sum's using Newton's indentities. Then convert the outer product or outer sum of all roots. This can be done using the binomial expansions. Then we can convert back to...




Why don't we just stay in the Power sum representation?






### Solving Pendulum with Grobner Bases 11/05/2018







Grobner bases are a cool tool. There are algorithms for computing them. They are the analog of Gaussian elminiation for polynomial equations, in the sense that they separate equations into a sequence that has increasing number of variables.







If we work in terms of the x and y of the pendulum, rather than the angle, we can get more algebraic looking equations (avoiding transcendental functions like sine and cosine). This is at the cost of a lgrange multiplier enforce the constraint that x and y lie on a circle.







$latex L = \dot{s}^2+\dot{c}^2- \frac{1}{2}\lambda (c^2 + s^2 - 1)$







The equations of motion from this Lagrangian are







$latex \ddot{c}=\lambda c$







$latex \ddot{s} = \lambda s$







$latex c^2 + s^2 - 1=0$







We haven;t added gravity yet. The solutiuon is constant angular velocity. A constant lambda is sufficient to achieve that. Lambda will be the angular velocity squared.







To discretize these equations, we have a couple choices. We can perform some kind of finite difference scheme. We can write the solutions as polynomials with some coefficients and select points (probably chebyshev) at which to enforce the equations of motion. We could try some kind of least squares.







We could also go whole hog into a least action formulation. This would turn it into a boundary value problem rather than initial value problem.







Another options may be to go to infinite series form.







An important and natural monomial ordering is one that respects time. Then the groebner subsitution process will solve the whole system.







For derivatives, one needs to be very careful. I think often you need to create a new dx variable for every variable. Then dot all the gradients of the constraints onto these variables to constraint them to stay within the surface. Then add addition constraints, often setting many of them to 0.







Sum of squares programming seem like an extra spice you may want.







Other interesting things: grobener refinement







Consider finding a minimizing polynomial for the circle x^2+y^=1.







So we use polynomials of the form $latex y - \sum a_n x^n $ which have to be SOS with the addition of $latex \lambda(x)(x^2 + y^2 - 1)$ or we can explicitly remove the y^2 term and replace it with an x^2 term. Doesn't really seem like what we'd want. I think we then minimize the constant offset term a_0 . This should give us a nice parabola that the circle sits on.







We could use a similar technique for The value function







Comparing the sampling method using LP and the SOS method verified for all points. We still get to use a weighting polynomial if we like.







### Sum of Squares Notes 11/06/2018







[http://whttps://laurentlessard.com/teaching/524-intro-to-optimization/ww.mit.edu/~parrilo/](http://whttps://laurentlessard.com/teaching/524-intro-to-optimization/ww.mit.edu/~parrilo/)







[http://www.mit.edu/~parrilo/sdocag/](http://www.mit.edu/~parrilo/sdocag/)







Holy shit. What a treasure trove.







[https://learning-modules.mit.edu/materials/index.html?uuid=/course/6/sp16/6.256#materials](https://learning-modules.mit.edu/materials/index.html?uuid=/course/6/sp16/6.256#materials)







[https://github.com/JuliaPolyhedra/Polyhedra.jl](https://github.com/JuliaPolyhedra/Polyhedra.jl)







Polyhedra projection methods for interval arithmetic. Fourier Motzkin eliminates variables kind of like gaussian elimination, Other method find all vertices, project and then take convex hull. Then create a convex hull over the range of the variables (linear approximation).







Could use this for extended interval airthmetic method, with small dividends for massively more computation. ;)







This is powerful, although probably does not scale.







Allows expression of alternating quantifier problems.







[https://www.juliaopt.org/meetings/mit2017/legat.pdf](https://www.juliaopt.org/meetings/mit2017/legat.pdf)







[https://github.com/JuliaOpt/SumOfSquares.jl](https://github.com/JuliaOpt/SumOfSquares.jl)







[https://github.com/JuliaAlgebra](https://github.com/JuliaAlgebra)







Applications to Control:







SDP as finding a quadratic lyapunov function







Groebner bases?







SOS and the NullStullensatz. The Nullstullensatz can be linearized. This is a way to prove the inconsistency of a set of equations. The Semidefinite approach is definitely a brother of this.







Why is SOS usually in terms of polynomials? The Sum of Squares of anything is manifestly positive. Polynomials are nice though. They are differentiable, integrable, and there is methodology for root finding / varieties available.







Continuum Network-Flow







Using Grobner basis to reduce the SOS problem. You can either directly remove those terms from the system, or you can add in terms that will be zero in a similar way to the previous procedure.







The edges of spectrahedra are where at least one eigenvalue is zero. Singularitites in that surface are where The rank of the matrix is even lower (sometimes rank 1). This helps explain why low rank is common.







"Semidefinite programing is nonabelian linear programming" -Bernd







Global polynomial optimization - find largest offset. We're finding a supporting plane in the direction of our measure. The dual solution is hopefully low rank. Then it can be factored and we can read off the optimal. If it is, the dual I think is in fact a certifcate of global optimality







Orbitopes - look at objects (points, equation sets) under all operations of some group. Permutahedra. Related to associahedra?







Projective duality and opitmization duality. A projective equation being greater than zero doesn't mean anything.







Two styles. The [1 x x^2] vector. and the putting linear stuff in the matirx and then thinking about the determinant.







Some pieces:






    
    x = Symbol('x')
    t = Symbol('t')
    tcvx = cvx.Variable()
    xs = Matrix([x**n for n in range(4)]); xs
    Qb = MatrixSymbol('Q', 4,4)
    Qcvx = cvx.Variable((4, 4), PSD=True); Qcvx
    Q = Matrix(Qb); Q
    p = (xs.T * Q * xs)[0]; p
    coeff = Poly(p-t,x).all_coeffs(); d
    #print(lambdify(Qb, Q[0,0])(X) <= 3)
    coeff_cvx = [lambdify((Qb,t), expr)(Qcvx, tcvx) for expr in d]; coeff_cvx
    
    #########
    
    def sospoly(n, x, varname):
        xs = Matrix([x**k for k in range(n)]); xs
        Qb = MatrixSymbol(varname, n,n)
        Qcvx = cvx.Variable((n, n), PSD=True); Qcvx
        Q = Matrix(Qb); Q
        p = (xs.T * Q * xs)[0]; p
        return p, Qb, Qcvx
    
    lam1p, lam1s, lam1c  = sospoly(3,x,'lam1')
    lam2p, lam2s, lam2c  = sospoly(3,x,'lam2')
    eq1p, eq1s, eq1c  = sospoly(3,x,'eq1')
    eq2p, eq2s, eq2c  = sospoly(3,x,'eq2')
    
    polcoeff = MatrixSymbol("p", 3,1)
    pol = sum([polcoeff[k] * x**k for k in range(n)]);
    t = Symbol('t')
    tcvx = cvx.Variable()
    eq1 = pol - t - lam1p * x*(x-1) - eq1p
    eq2 = t + pol + lam2p * x*(x-1) - eq2p
    
    # collectup oefficients from both, replace with cvx variables, and turn them into equalities.
    
    constraints += polcvx[3] == 1 # make highest coefficient = 1
    cvx.Minimize(tcvx)
    
    ############
    
    cvxdict = {}
    for expr in postorder_traversal(expr):
        if expr.func == SymbolMatrix:
            if expr.name not in cvxdict:
                cvxdict[expr] = cvx.Variable(expr.shape)
            
        elif expr.func == Symbol:
                cvxdict[expr] = cvx.Variable()
                
    def add2dict(cvxdict, expr):
        if expr.func == SymbolMatrix:
            cvxdict[expr] = cvx.Variable(expr.shape)        
        elif expr.func == Symbol:
            cvxdict[expr] = cvx.Variable()
    def cvxvar(expr):
        if expr.func == SymbolMatrix:
            return cvx.Variable(expr.shape)        
        elif expr.func == Symbol:
            return cvx.Variable()
        
    q = Symbol('q')
    cvxdict[q]= cvxvar(q)
    
    def cvxify(expr, cvxdict): # curried with cvxdict would be nice
         return lambdify(tuple(cvxdict.keys(), expr)(**cvxdict.values()) 
    
    
    
    
    
    
    
    
    
    







### Rationals








https://www.youtube.com/watch?v=qPeD87HJ0UA









https://www.youtube.com/watch?v=DpwUVExX27E








[https://github.com/mcgordonite/idris-binary-rationals](https://github.com/mcgordonite/idris-binary-rationals)







[https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree](https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree)







[https://www.cs.ox.ac.uk/jeremy.gibbons/publications/rationals.pdf](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/rationals.pdf)







functional pearl.







Concrete Mathematics is referenced.







Prime decomposition -> Rational is Z powers of primes







[https://en.wikipedia.org/wiki/Quote_notation](https://en.wikipedia.org/wiki/Quote_notation)







P-adics?







Homography and mobius tranformations . They are closed under composition. Similar in many ways to composition of linear or affine functions. Maybe exactly analogous in a projective sense.







Gosper algorithm







[https://perl.plover.com/yak/cftalk/INFO/gosper.txt](https://perl.plover.com/yak/cftalk/INFO/gosper.txt)







Every step of applying out a conitnued fraciton can be seen as applying a mobius transformation.







Convex in the variable. So once we know the integer part we can output it







Bihomography can implement addition.







Can we use Ratio composed with Polynomial type? Can use V2 to represent linear functions. Ratio [a]. Combined with gcd.







### Algebraic Geometry Notes 3/11/2018







Algebraic geometry studies the geoemtry of curves generated by polynomials basically.







A vairety is the solution of a set of equations as a geometric object.







Zero sets in particular. Zero for every polynomial in the polynomial set







Ideal = subset of Ring that absorbs multplication from outside the subset, like the evens







Intersection of sets maps to multpilcation of polynomials







and union of sets maps to sums







Zariski topology = closed sets are the sets that are zeros of some set of polynomials








https://youtu.be/ceAtMOmyu1A









https://www.youtube.com/watch?v=93cyKWOG5Ag




