---
author: philzook58
comments: true
date: 2019-08-11 17:47:28+00:00
layout: post
link: https://www.philipzucker.com/dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though/
slug: dump-of-nonlinear-algebra-algebraic-geometry-notes-good-links-though
title: Dump of Nonlinear Algebra / Algebraic geometry Notes. Good Links Though
wordpress_id: 1320
---

Old notes on nonlinear algebra. I dunno about the content but some very good links and book suggestions in here, so I'm gonna dump this one out there. Maybe it'll help someone.




---




Systems of multivariable polynomial equations are more solvable than people realize. There are algebraic and numeric methods. Look at Macaulay, Singular, Sympy for algebraic methods. phcpack and bertini  and homotopycontinuation.jl for numerical .




Algebraic methods are fixated on Groebner bases, which are a special equvialent form your set of equations can be manipulated to. You can disentangle the variables using repeated polynomial division (buchberger's algorithm) turning your set of equations into an equivalent set that has one more variable per equation. This is like gaussian elimination which is actually the extremely simple version of buchberger for linear equations.




The numerical methods use perturbation theory to take a system of equations you know how to solve and smoothly perturb them to a new system. Each small perturbation only moves the roots a little bit, which you can track with a differential equation solver. Then you can fix it up with some Newton steps. People who really care about this stuff make sure that there are no pathological cases and worry about roots merging or going off to infinity and other things.




You need to know how many roots to build and track in your solvable system. For that two theorems are important




bezout thereom - for dense systems, number of solutions is bound by product of total degree of equations.




bernstein bound - newton polytope gives bound of number of solutions of polynomial system. useful for sparse




One could make an argument for the homotopy continuation methods being the analog of iterative solutions for linear equations if grobner basis are gaussian elimibnation. Take equation we know how to solve (~preconditioner) and perform some iterative thing on it.




add enough random linear equations to make system full (points).




Then you have a membership algorithm due to sweeping of planes. Once you have points on actual varieites, pairwise compare them.




![](https://ofloveandhate-pybertini.readthedocs.io/en/feature-readthedocs_integration/_images/homotopycontinuation_generic_40ppi.png)




Cox OShea book is often reccomended. It's really good.




[https://www.springer.com/us/book/9781441922571](https://www.springer.com/us/book/9781441922571)




More advanced Cox et al book




[https://www.springer.com/us/book/9780387207063](https://www.springer.com/us/book/9780387207063)




Bernd Sturmfels,  Mateusz Michalek (including video lectures)




[https://personal-homepages.mis.mpg.de/michalek/ringvorlesung.html](https://personal-homepages.mis.mpg.de/michalek/ringvorlesung.html)




[https://personal-homepages.mis.mpg.de/michalek/NonLinearAlgebra.pdf](https://personal-homepages.mis.mpg.de/michalek/NonLinearAlgebra.pdf)




(Bernd is da man!)




[https://math.berkeley.edu/~bernd/math275.html](https://math.berkeley.edu/~bernd/math275.html)




Maculay 2 book




[https://faculty.math.illinois.edu/Macaulay2/Book/](https://faculty.math.illinois.edu/Macaulay2/Book/)




Singular books




[https://www.singular.uni-kl.de/index.php/publications/singular-related-publications.html](https://www.singular.uni-kl.de/index.php/publications/singular-related-publications.html)




[https://www.springer.com/us/book/9783662049631](https://www.springer.com/us/book/9783662049631)




[https://www.ima.umn.edu/2006-2007](https://www.ima.umn.edu/2006-2007)




Planning Algorithms, in particular chapter 6




[http://planning.cs.uiuc.edu/](http://planning.cs.uiuc.edu/)




https://oleksandrmanzyuk.wordpress.com/2012/10/25/grobner-bases-in-haskell-part-i/




Summer school on tensor methods




[https://www.mis.mpg.de/calendar/conferences/2018/nc2018.html](https://www.mis.mpg.de/calendar/conferences/2018/nc2018.html)




Extensions of




[https://ieeexplore.ieee.org/document/4399968](https://ieeexplore.ieee.org/document/4399968)




Numerical Polynomial Algebra by Hans Stetter




https://epubs.siam.org/doi/book/10.1137/1.9780898717976?mobileUi=0&




Introduction to Non-Linear Algebra V. Dolotin and A. Morozov. A high energy physics perspective




https://arxiv.org/pdf/hep-th/0609022.pdf




Nonlinear algebra can also be approach via linear algebra surprisingly. Resultants. As soon as you see any nonlinearity, the linear part of your brain shuts down, but a good question is linear in WHAT? Consider least squares fitting, which works via linear algebra. Even though you're fitting nonlinear functions, the expressions are linear in the parameters/coefficients so you're all good.




Similarly you can encode root finding into a linear algebra problem. A matrix has the same eigenvalues as it's characterstic polynomial $latex det(A - \lambda) $ has roots, so that already shows that it is plausible to go from linear algebra to a polynomial root finding problem. But also you can encode multiplying a polynomial by x has a linear operation on the coefficients. In this way we can .




[1 x x^2 x^3 ...] dot [a0 a1 a2 a3 ...] = p(x)




Multiplying by x is the shift matrix. However, we also are assuming p(x)=0 which gives use the ability to truncate the matrix. x * [1 x x^2 x^3 ...]  = Shift @ xbar. This is somewhat similar to how it feels to do finite differnce equations. The finite difference matrix is rectangular, but then boundary conditions give you an extra row. Multiplication by x returns the same polynomial back only when p(x)=0 or x = 0. The eigenvalues of this x matrix will be the value of x at these poisitions (the roots). This is the companion matrix [https://en.wikipedia.org/wiki/Companion_matrix](https://en.wikipedia.org/wiki/Companion_matrix)




We can truncate the space by using the zero equation.




It's a pretty funky construction, I'll admit.




To take it up to multivariable, we bring in a larger space [1 x y x^2 xy y^2 ...] = xbar kron ybar




We now need two equations to reduce it to points. The X matrix is lifted to X kron I. and we can pad it with ?




Multiplying by an entire polynomial. Sylvester matrix for shared roots. Double root testing.




Sylvester matrix is based on something similar to bezout's identity. To find out if some things p q has common factors you can find 2 things r s such that r*p + q*s = 0




https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#B%C3%A9zout's_identity_and_extended_GCD_algorithm




Sum of Squares is somewhat related material on systems of polynomial inequalities which can be translated to semidefinite matrix constraints. If you want to include equalities, you can use groebner bases to presolve them out.




Parrilo course material on Sum of Squares.




[https://learning-modules.mit.edu/materials/index.html?uuid=/course/6/sp16/6.256#materials](https://learning-modules.mit.edu/materials/index.html?uuid=/course/6/sp16/6.256#materials)




Paper on using greobner and CAD (cylindrical algebraic decomposition) for opitmization and control




[www.mit.edu/~parrilo/pubs/files/FRPM_IJC_preprint.pdf](http://www.mit.edu/~parrilo/pubs/files/FRPM_IJC_preprint.pdf)




 




Using groebner basis for constraint satisfaction problems: x^n=1 gives a root of unity. There are n solutions. This gives a finite set to work with. Then you can add more equations. This is related to the max-cut thing. I saw this on Cox webpage.




You can require neighbors to have different vertices by  0=(xi^k - xj^k)/(xi - xj). You can encode many constraints using clever algebra.




 




an example using the same technique to solve sudoku




[https://mathoverflow.net/questions/91666/gr%C3%B6bner-basis-for-sudoku](https://mathoverflow.net/questions/91666/gr%C3%B6bner-basis-for-sudoku)




 




[http://mattpap.github.io/scipy-2011-tutorial/html/groebner.html](http://mattpap.github.io/scipy-2011-tutorial/html/groebner.html)




Sympy tutorial solving geoemtric theorems and map coloring




 




[https://mattpap.github.io/masters-thesis/html/src/groebner.html](https://mattpap.github.io/masters-thesis/html/src/groebner.html)




explicitly mentions toric groebner as integer programming.




 




other interesting exmaples




[http://www.scholarpedia.org/article/Groebner_basis](http://www.scholarpedia.org/article/Groebner_basis)




Noncommutative grobner basis have application to solving differential equations? The differential operators are noncommutative. Not just silly quantum stuff. I mean the simple exmaple of non commutativty are the shcordinger momentum operators.




Automatic loop invariant finding




Geometric theorem rpvong




robotic kinematics




Optics? Envelopes, exchange of coordinates. Legendre transformations. Thermodynamics?




Global optimization? Find all local minima.




Nonlinear finite step.




Dynamic Prgramming. Add implicit V variab le for the vlaue function. Constrain via equations of modtion. Perform extermization keeping x0 v0 fixed. dx0=0 dv0=0 and dV=0. Grobner with ordering that removes x1 v1 V1. Iterate. Can keep dt as variable. Power series in t? Other integration schemes.




Probably need some method to simplify that left over relations so that they don't get too complex. Smoothing? Dropping terms? Minimization may require factoring to find global minimum.




Differentiation. Add to every variable a dx. Collect up first order as a seperate set of constraints. Add conditions df=0 and dy=0 for fixed variables to perform partial differentiation and extremization. A very similar feel to automatic differentiation. Functions tend to not be functions, just other wriables related by constraints




Variable ordering




lex - good for elimination




deglex - total degree then a lex to tie break




grevlex - total degree + reverse lexicographic. The cheapest variable is so cheap that it goes last




block ordering, seperate variables into blocks and pick orderings inside blocks




general matrix ordering. Apply a matrix to the exponent vectors and lex comparse the results. Others are a subset.




Can't I have a don't care/ partial order? would be nice for blockwise elimination I feel like.




Non-commutative




[http://sheaves.github.io/Noncommutative-Sage/](http://sheaves.github.io/Noncommutative-Sage/)




Physicsy




https://arxiv.org/pdf/hep-th/0609022




CAD book




[https://link.springer.com/book/10.1007%2F978-3-7091-9459-1](https://link.springer.com/book/10.1007%2F978-3-7091-9459-1)




Rings have addition and multiplication but not division necessarily. Polynomials, integers, aren't guarenteed to have inverses that remain polynomials or integers.




ideal = a subset of a ring that absorbs multiplication. Also closed under addition




All polynomial conseqeunces of a system of equations




HIlbert Basis theorem - all ideals are egenrated by a finite set




ideal generated from set - any element of ring that can be generated via addition and multiplication by arbitary element. Is ideal because if you multiplied it by another object, it is still and sum of multiples.




Ideals are sometimes kind of a way of talking about factors without touching factors. Once something is a multiple of 5, no matter what you multiply it with, it is still a multiple of 5. If (x - 7) is a factor of a polynomial, then no matter what you multiply it with, (x-7) is still a factor. Zeros are preserved.




Principal ideal domain - every ideal is generated by a single object




Prime ideal. if a*b is in ideal then either a or b is in ideal. Comes from prime numbers ideal (all number divislable by prime number). If ab has a factor of p then either a or b had a factor of p. whereas consider all mutiples of 4. if a = b =2 then ab is a mutiple of 4, but neither a nor b are a multiple of 4.




1d polynomials. Everything is easy.




Polynomial division is doable. You go power by power. Then you may have a remained left over. It's pretty weird.




You can perform the gcd of two polynomials using euclidean algorithm.




The ideal generated by a couple of them is generated by the multipolynomial gcd?




a = cx + dy + r




multivariate division: we can do the analog of polynomial division in the multivariate case. But we need an ordering of terms. reaminder is not unique.




But for certain sets of polynomials, remainder is unique.




Why the fixation on leading monomials?




The S-polynomial is the analog of one step of the euclidean algorithm. It also has the flavor of a wronskian or an anticommutator.




The bag euclidean algorithm. Grab the two things (biggest?). Take remainder between them, add remainder into bag.




This is the shape of the buchberger algorithm.




Finding homology or cohomology of solutions. Good question. One can see how this could lead to categorical nonsense since Category theory was invented for topological questions.




The variety is where a set of polynomials is 0. Roots and zero surfaces




List gives set of polynomials.




[forall a. Field a => (a,a,a) -> a ]




Or explicit




union and intersection can be achieved via multiplication and combining the sets




Krull dimension - Definition of dimension of algebraic variety. Maximal length of inclusion chain of prime ideals.




Ideals and Varieites have a relation that isn't quite trivial.




The ideal of a variety




Envelopes - parametrized set of varieties f(x,t)=0 and partial_t f(x,t)=0. Eliminate t basically to draw the thing. Or trace out t?




Wu's method for geometric theorem proving. You don't need the full power of a grobner basis.




Polynomial maps. Talk about in similar language to differential geometry.




Boxes are a simple way to talk about subsets. Or lines, planes. Or polytopes.




Also any function that gives a true false value. But this is very limited in what you can actually do.




Varieties give us a concrete way to talk about subsets. Grothendieck schemes give unified languages supposedly using categorical concepts. Sounds like a good fit for Haskell.




class Variety




use powser. Functor composition makes multivariable polynomials. Tuples or V3 with elementwise multiplication



    
    -- give variables names
    newtype X a = X [a]
    
    newtype Y a = Y [a]
    
    -- from k^n -> k^m
    type family PolyFun n m k where
       PolyFun n (S m) k = (PolyFun n 1, PolyFun n m)
       PolyFun (S n) 1 k = [PolyFun n 1 k] 
       PolyFun 1 1 k = k
    -- Gonna need to Make a typeclass to actually do this. Yikes
    -- it's just not as simple as Cat a b type. You really need to do computation
    -- and input a is not same as 
    class PolyF f where
       pcompose :: PolyFun b c k -> PolyFun a b k -> PolyFun a b k
       pid :: Num k => PolyFun b c k
    
    
    -- related to ideal of n generators on a space k^m
    -- this functions will compose some incoming 
    -- or is this better thought of as a variety?
    type Idealish :: (PolyFun n 1) -> PolyFun m 1
    makeidealish :: PolyFun m n -> Ideal
    makeidealish f = flip pcompose f
    
    -- apply turns polynomial into haskell function
    apply :: (PolyFun n m) -> V n -> V m
    
    -- somehow should be able to replace points with varieties. It's like a whole thing
    type VarietyFun = (PolyFun n 1 k) -> (PolyFun m 1 k)
    (PolyFun n 1 k -> PolyFun m 1 k) -> (PolyFun m 1 k -> PolyFun l)
    




The polynomial as a type parameter for agda. Regular Functions are functions from one variety to another. They are the same as the polynomial ring quotiented out by the ideal of the variety.




Ring Space and Geometric Space (affine space)




Maximal ideals can be thought of as points. (ideal of x-a, y-b, ...).




Free Polynomials ~ Free Num. Sparse representation. Uses Ordering of a. We should not assume that the are a power like in http://hackage.haskell.org/package/polynomial-0.7.3/docs/Math-Polynomial.html




Ord is monomial ordering. Think of a as [X,Y,X,X,X]




divmod :: (Integral a, Ord a) => Poly r a -> Poly r a -> Poly r a




newtype Monomial a = Monomial [a]




-- different monomial newtype orderings for lex, etc.




Monomial (Either X Y)




divmod as bs = remove bs from as. if can't remainder = as, div = 0




Intuition pumps : algebraic geometry, differential geoemtry, ctaegory theory, haskell agda.




In differential geometry, embedding sucks. We get around it by defining an atlas and differential maps.




There is a currying notion for polynomials. We can consider a polynomial as having coefficinets which themselves are polynomials in other variables or all at once.




What can be solved linearly? The Nullstullensatz certificate can be solved using linear equations




Resultants. What are they? Linear sums of monomials powers * the orginal polynomials. Det = 0 implies that we can find a polynomial combination




What is the deal with resultants




Toric Varieties. C with hole in it is C*. This is the torus because it is kind of like a circle. (Homologically?). There is some kind of integer lattice lurking and polytopes. Gives discrete combinatorial flavor to questions somehow. Apparently one of the more concrete/constructive arenas to work in.




binomaial ideals. the variety will be given by binomials




maps from one space to another which are monomial. can be implicitized into a variety. map is described by integer matrix. Integer programming?




Similar "cones" have been discussed in teh tropical setting is this related?




Algebraic statistics. Factor graph models. Probablisitc graphical models. Maybe tihs is why a PGM lady co taught that couse with Parillo




Modules




Tropical geometry




[http://www.cmap.polytechnique.fr/~gaubert/papers.html](http://www.cmap.polytechnique.fr/~gaubert/papers.html)




Loits of really intriguing sounding applications. Real time verification




gfan




How does the polynomial based optimization of the EDA course relate to this stuff? [https://en.wikipedia.org/wiki/Logic_optimizatio](https://en.wikipedia.org/wiki/Logic_optimization)n




Mixed volume methods? Polytopes.




cdd and other polytopic stuff. Integration of polynomials over polytopes




Software of interest




Sage




Sympy




Singular - Plural non-commutative?




FGb - Faugiere's implmentation of Grobner basis algorithms




Macaulay




CoCoa




tensorlab - [https://en.wikipedia.org/wiki/Tensor_software](https://en.wikipedia.org/wiki/Tensor_software)




sostools




PolyBori - polynomials over boolean rings [http://polybori.sourceforge.net/doc/tutorial/tutorial.html#tutorialli1.html](http://polybori.sourceforge.net/doc/tutorial/tutorial.html#tutorialli1.html)




LattE




4ti2




normaliz




polymake - [https://polymake.org/doku.php/tutorial/start](https://polymake.org/doku.php/tutorial/start) slick




[http://hep.itp.tuwien.ac.at/~kreuzer/CY/CYpalp.html](http://hep.itp.tuwien.ac.at/~kreuzer/CY/CYpalp.html) Calabi Yau Palp????




TOPCOM




frobby - can get euler charactersitics of monomial ideals? [http://www.broune.com/frobby/index.html](http://www.broune.com/frobby/index.html)




gfan




[https://www.swmath.org/browse/msc](https://www.swmath.org/browse/msc)




Homotopy continuation:




Bertini




[http://homepages.math.uic.edu/~jan/phcpy_doc_html/index.html](http://homepages.math.uic.edu/~jan/phcpy_doc_html/index.html)




phcpy and phcpack




hom4ps




[https://www.juliahomotopycontinuation.org/](https://www.juliahomotopycontinuation.org/)




certification:




[http://www.math.tamu.edu/~sottile/research/stories/alphaCertified/](http://www.math.tamu.edu/~sottile/research/stories/alphaCertified/)




cadenza




Jan




[http://homepages.math.uic.edu/~jan/mcs563s14/index.html](http://homepages.math.uic.edu/~jan/mcs563s14/index.html)




[www.math.uic.edu/~jan/tutorial.pdf](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=8&ved=2ahUKEwizrduPxZDeAhWxnOAKHb5XDGkQFjAHegQIBRAC&url=http%3A%2F%2Fwww.math.uic.edu%2F~jan%2Ftutorial.pdf&usg=AOvVaw2ro2rky2Y2Wg1bHAnrb0Cw)




bezout thereom - for dense systems, number of solutions is bound by product of total degree of equations.




bernstein bound - newton polytope gives bound of number of solutions of polynomial system. useful for sparse




One could make an argument for the homotopy continuation methods being the analog of iterative solutions for linear equations if grobner basis are gaussian elimibnation. Take equation we know how to solve (~preconditioner) and perform some iterative thing on it.




add enough random linear equations to make system full (points).




Then you have a membership algorithm due to sweeping of planes. Once you have points on actual varieites, pairwise compare them.




Suggestion that "linear program" form helps auto differentiation?




local rings. thickening? Infinite power series modded out by local relation. One maximal ideal.




differential geometry on algebaric surfaces.




modules are like vector spaces.




Ring linear




Canonical example, a vector of polynomials.




1-d space of polynomials.




Module morphism - respects linearity with sresepct to scalar multiplacation and addition Can be specified compoent wise. But has to be specified in such a way that resepct.




Basis - Linearly Independent set that spans the whole module. May not exist.




So were are kind of stuck always working in overcomplete basis to make thje vector space analogy. The generators have non trivial relations that equal zero. These coefficients form their own vector space. The space whole image is zero because of the relations is called the first syzygy module.




But then do we have a complete basis of all the relations? Or is it over complete?




If you ignore that the entries of a vectors are polynomials it becomes vector space. But but because they are they have secret relations.




even 1 dimensional vector space has some funky structure because of the polynomial nautre of the ring.




Somehow fields save us?




Paramaetrized vector curves, surfaces.




Parametrzied matrices.




Noncommutative polynomials. We could perhaps consider the process of normal ordering something related to a grobner basis calcaultion. Perhaps a multi polynomial division process? Consider the ordering where dagger is greaer than no dagger. Canonical basis also has i<j (more important for fermion).




SOS gives you the exact minimum of 1-d polynomial. You could also imagine encoding this as a semidefintier program. H-lam>=0. Min lam. Where H is the characterstic matrix.




We can diagonalize to the sos form, and then take each individual term = 0 to solve for x*.




While integer programming does that funky toric variety stuff with the objective vector deswcribing the grobner basis, binary programming is simple. x^2=x + linear eequations and constraints




haskell grobener




1. Monomials. Exponent vectors. Logarithmic representation. Mutiplication is addition. Composition is elementwise multiplication. Type level tag for ordering.




newtype Mon3 ord = V3 Int




data Lex




data DegLex




Ordering of monomials is important. Map is perfect




Map (Mon3 ord) ring




Groebner bases can be used to describe many familiar operations. Linear algerba, gaussian elminiation. Using commutators. Building power series assuming terms are relatively irrelevant.




Can I get a power series solution for x^2 + ax + 1=0 by using a negative ordering for a? I need another equation. x = \sum c_n * a^n. (x+dx)? How do I get both solutions?




Dual numbers for differential equations. dx is in a ring such that dx^n = 0.




Subset sum. Find some of subset of numebrs that add up to 0.




s um variables s_i




Solutions obey




s_0 = 0




(s_i - s_{i-1})(s_i - s_{i-1}-a_{i-1})=0




s_N = 0




Factors give OR clauses. Sepearte oplynomials give AND clauses. pseudo CNF form. Can't always write polys as factors though? This pattern also matches the graph coloring.




More interesting books:




[https://wstein.org/books/ant/](https://wstein.org/books/ant/)




https://pseudoprofound.wordpress.com/2016/07/09/some-fun-with-algebraic-numbers/






## Polynomial Factorization







[https://mattpap.github.io/masters-thesis/html/src/algorithms.html](https://mattpap.github.io/masters-thesis/html/src/algorithms.html)







[https://en.wikipedia.org/wiki/Factorization_of_polynomials](https://en.wikipedia.org/wiki/Factorization_of_polynomials)







Numerical vs Symbolic







Numeric







[https://en.wikipedia.org/wiki/Root-finding_algorithm](https://en.wikipedia.org/wiki/Root-finding_algorithm)







Pick a random point. Then apply Newton's method. Do this over and over. If you find N unique factors, you've done it. A little unsatisfying, right? No guarantee you're going to find the roots.







2. Perturbation theory / Holonomy continuation. Start with a polynomial with the same number of total roots that you know how to factor. x^N - 1 = 0 seems like an easy choice. Given $latex f(x)+\lambda g(x)=0$, $latex \partial g dx \lambda + \partial f dx +g(x){d\lambda}= 0$ . $latex \frac{dx}{d\lambda} = \frac{-g(x)}{\lambda \partial g + \partial f}$. You can use this ODE to track the roots. At every step use Newton's method to cleanup the result. Problems can still arise. Do roots collapse? Do they smack into each other? Do they run off to infinity?







3. The Companion matrix. You can convert finding the roots into an eigenvalue problem. The determinant of a (A - \lambda) is a polynomial with roots at the eigenvalues. So we need tyo construct a matrix whose deteerminant equals the one we want. The companion matrix simulates multiplication by x. That is what the 1 above the diagonal do. Then the final row replaces x^(N+1) with the polynomial. In wikipedia, this matrix is written as the transpose. https://en.wikipedia.org/wiki/Companion_matrix







4. Stetter Numerical Polynomial Algebra. We can form representations basically of the Quotient Rings of an Ideal. We can make matrices A(j) that implement multiplication by monomials x^j in F[x]/I. Then we can take joint eigensolutions to diagonalize these multiplications. Something something lagrange polynomials. Then if the solutions respect some kind of symmettry, it makes sense that we can use Representation theory proper to possibly solve everything. This might be the technique of Galois theory metnoined in that Lie Algebra book. This is not unconnected with the companion matrix technique above. These matrices are going to grow very higher dimensional.







Thought. Could you use holonomy continuation to get roots, then interpolate those roots into a numerical grobner basis? Are the Lagrange polynomials of the zero set a grobner basis?







Symbolic







Part of what makes it seem so intimidating is that it isn't obvious how to brute force the answer. But if we constrain ourselves to certain kinds of factors, they are brute forceable.







Given a suggested factor, we can determine whether it actually is a factor by polynomial division. If the remainder left over from polynomial division is 0, then it is a factor.







If we have an enumerable set of possibilities, even if large, then it doesn't feel crazy to find them.







Any root of a polynomial with rational coefficients can be converted to integer coefficients by multiplying out all the denominators.







Let's assume the polynomial has factors of integer coefficients.







Rational Root Test







Kronecker's method







Finite Fields. It is rather remarkable that there exists finite thingies that have the algerbaic properties of the rationals, reals, and complex numbers. Typically when discretizing continuum stuff, you end up breaking some of the nice properties, like putting a PDE on a grid screws over rotational symmetry. Questions that may be hard to even see how to go about them become easy in finite fields in principle, because finite fields are amenable to brute force search. In addition, solutions in finite fields may simply extend to larger fields, giving you good methods for calculations over integers or rationals or what have you.







SubResultant. A curious property that if two polynomials share roots/common factors, it is pretty easy to seperate that out. The GCD of the polynomials.







Kind of the gold standard of root finding is getting a formula in terms of square roots. This is an old question. Galois Theory is supposedly the answer.



