---
author: philzook58
comments: true
date: 2020-08-19 14:05:14+00:00
layout: post
link: https://www.philipzucker.com/?p=2659
published: false
slug: Applications of Modules
title: Applications of Modules
wordpress_id: 2659
---




Implementing Categorical Circuits with Catlab.jl and Singular.jl







Linear relations are really interesting and very applicable.







blast them with some use code and a diagram right here  so they don't get bored by the spiel







### A Spiel on Circuits







The behavior of a circuit is described by specifying a voltage variable to every node in the circuit, and a current variable to every edge. Ohm's law (V = IR) + [Kirkhoff's circuit laws](https://en.wikipedia.org/wiki/Kirchhoff%27s_circuit_laws) (current conservation and sum voltage drops = 0) give a pile of equations. These equations are linear (or affine really to be precise) in that the I/V variables never show up squared or anything weird. Because of this, this pile of equations can be collected into matrix form.







$latex \begin{bmatrix}  K \end{bmatrix} \begin{bmatrix} \vec{v} \\ \vec{i} \end{bmatrix} = \vec{j} $







For a closed circuit, this matrix can be made square, and hence solvable numerically or symbolically by Gaussian elimination (aka `K \ j` or `[scipy.linalg.solve(K,j)](https://docs.scipy.org/doc/scipy/reference/tutorial/linalg.html)` ).







Linear relations are an alternative definition to matrix multiplication for what one might mean by "matrix composition". Don't get me wrong, matrix multiplication is also da bomb. But this matrix $latex K $ does not make sense to matrix multiply. Why would you apply a constraint matrix K twice? What would that even mean? In addition, there are reasonable situations where you might not have a square matrix K. [Filters](https://en.wikipedia.org/wiki/Electronic_filter) are a common example where the circuit is left _open_, in other words we're missing pieces of information of the circuit. This implies that K isn't square and hence can't be multiplied by itself. 







Nevertheless, just because the circuit isn't completely specified doesn't mean you have no information or that there isn't anything interesting to compute or that there aren't meaningful notions of composition available. In mathematical terms, the structure of the known pieces of an open circuit tell us that the I,V vector lives in a particular affine subspace. This affine subspace is the nullspace of K, conjoined with a single inhomogenous solution.







The nullspace can be numerically or symbolically calculated (`[scipy.linalg.null_space](https://docs.scipy.org/doc/scipy/reference/generated/scipy.linalg.null_space.html)`). Wait, what? What does it even mean to "calculate" a nullspace? You give me a matrix and the nullspace is implicit in it? What more could I want?







Well, it's nice to have the nullspace represented in a canonical form. The nullspace calculation converts the implicit form of the nullspace into an explicit one by returning independent generators of the space. Why do we want these generators? 







The canonical form gives us







  * The dimensional of the nullspace. Maybe we had redundant constraints
  * How to take the linear summation of two nullspaces. This is a linear closure of the union under summation
  * How to project a nullspace into lower dimension.












There are [methods](https://en.wikipedia.org/wiki/Two-port_network#ABCD-parameters) (and this is a source of fascination for me) for treating the serial composition of passive filters via matrix multiplication, but getting things into and out of this form is awkward and puzzling how to generalize.







In a previous post, I described a methodology of how to think of open circuits as relations.







This is basically a reimplementation trying to follow the style and naming conventions set out by Catlab.jl







Julia is a step sidewise in mass appeal from Haskell. Both fall into the "Oh yeah, I've heard of that. Could be fun to learn." category of languages. Julia has the most exciting numerical and scientific computing projects/ideas that I'm aware of. It really is very intriguing to have a language that is nearly python like in it's simplicity, and yet have the possibility of fast native performance. This is always possible by writing meat in low level languages and then creating bindings, but this is a barrier that has often dissuaded me. It is important to not underestimate the value of convenience. If it was inconvenient for Alexander to conquer the known world, maybe he would've just stayed on his couch.







  * Catlab.jl is developing a critical mass. Evan and James in particular seem to have a great deal of energy and expertise. 
  * Haskell ultimately isn't a very friendly environment for numerical linear algebra or scientific computation.
  * Catlab has bindings to Singular module capabilities (although not fully fleshed out?)







https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/








#### Inductors and Capacitors need derivatives







One holy grail for me that I was missing was that really I wanted linear relations over polynomials.







The main applications that come to mind are linear signal flow diagrams, linear dynamical systems (like connected springs) and circuits. These systems are described by differential equations







The fundamental form if the inductance relation is $latex \Phi = LI$. The time derivative of this along with [Lenz's law](https://en.wikipedia.org/wiki/Lenz%27s_law) (changing magnetic flux = voltage), gives the more familiar relation $latex V = L \frac{dI}{dt}.







The fundamental relation of a capacitor is $latex Q = CV$. The derivative of this puts the equation in terms of current $latex I = C \frac{dV}{dt}$.







#### Phasor Analysis: Converting derivatives to polynomials







There are a couple ways of converting the description of the mathematical systems involving differentials and integrals into ones involving more mundane polynomials. In short this is the field of Fourier analysis.







However, the simplest most direct perspective is that taken by phasor analysis. The excitation of a linear time invariant system by a sinusoidal source can only result in sinsusoidal behavior at the same frequency. So we can make the ansatz that every variable has time dependence of the form $latex \tilde{V} = Re(V e^{j\omega t} ) = |V| \cos(arg(V) +  \omega t)$. When we supply this form into the relations for capacitors we get $latex I = j \omega V$ and for inductors we get $latex V = j \omega I$.







When we collect up all our linear equations What we have now though is that a circuit is no longer described by a matrix K with entries in the reals, but instead by entries that are complex polynomials. Ruh roh, Raggy.







#### Modules













#### Syzygies = Nullspaces







For my money, syzygies are basically nullspaces. Linear algebra packages offer nullspace functions. Given matrix A, they return a matrix N such that AN=0 and any v for which Av=0 can be expressed as v = Nw. In other words the columns of this matrix N span the nullspace of the matrix A.







The syzygy module of a pile of generators is the set of combinations of those generators that = 0. It is a module because it is closed under scalar multiplication and addition. If you add a zero combination to another, you get another zero combination. An element of the syzygy module can be represented by a vector with as many entries as there are generators. $latex s^T g = 0$. However, your generators are often given in terms of combinations of a free module. This is also true in regular linear algebra.  If you wanted to talk about a 2d subspace of a 3d vector space you give two generators that are embedded in the 3d space like [1 7 0] [2 5 9]. That means that each generator in turn is a linear combination of the free basis vectors e. $latex g_i = a_i ^T e$ or $latex g = Ge$. Hence getting all the generators of the syzygy module is giving a matrix S such that $latex SG = 0$  







Matrix multiplication can be descibred as taking the linear sum of the columns of the matrix. An element of nullspace from the perspective is describing a linear relationship between the columns of the matrix $latex \sum \vec{a}_j c_j = 0$.







The standard story of phasor 







The forced simple harmonic oscillator $latex \ddot{x} + \omega^2 x = f(t)$. Fourier analysis gives the steady state response of the system







Fourier transforming on the right vs the left. $latex f(t)=\int f(\omega)e^{i\omega t}d\omega$ vs. $latex F {L f = 0}$







The spectrum vs the fourier trasnform. The spectrum is the squared magntidue of the fourier transform. This is often what we physically measure. We see the brightness of the bands from the prism.







The first fourier trasnform device might be a prism. Why is this so? First off, the wavelength of light is related to it's frequency. \omega^2 = k^2. Second off, At interfaces, waves change diespersion relations. however the appropriate boundary conditions are (usually?) that the wavevector parallel to the interface must match in order to achieve continuity of the wave along the interface. 







Another natural forueir transform also occurs in optics.







Really, a very simple Fourier transform is just being far away from a dispersive system. Since the group velocity depends on the wavelength, The time of arrival will be connected to the frequency.







What I'm discussing is a way to correlate spatial extent of systems with their spectrum.







Sines and cosines are the eigenfunctions of differential operators. Eigendecompositions of matrices make solving them easy.







[https://see.stanford.edu/materials/lsoftaee261/book-fall-07.pdf](https://see.stanford.edu/materials/lsoftaee261/book-fall-07.pdf) The Fourier Transform book. Goddamn what a book







  * [https://web.stanford.edu/~boyd/ee102/](https://web.stanford.edu/~boyd/ee102/) Boyd signals and systems
  * Ogata and Nise
  * HAM books
  * [https://en.wikipedia.org/wiki/Network_analysis_(electrical_circuits)](https://en.wikipedia.org/wiki/Network_analysis_(electrical_circuits))
  * [http://www.cisl.columbia.edu/courses/spring-2002/ee6930/papers/00384428.pdf](http://www.cisl.columbia.edu/courses/spring-2002/ee6930/papers/00384428.pdf) efficient linear circuit analysis by pade
  * [https://www.win.tue.nl/analysis/reports/rana05-37.pdf](https://www.win.tue.nl/analysis/reports/rana05-37.pdf) modelling and discretization of circuit problems
  * [https://www.mathworks.com/help/control/index.html?s_tid=CRUX_lftnav](https://www.mathworks.com/help/control/index.html?s_tid=CRUX_lftnav) matlab control systems toolbox






The Laplce trasnform and Fourier trasnform are similar







The Fourier transform of the full -\inf to \inf solution of a time invaraint dynamical system usually doesn't exist. Why? Well, if the system is stable forward (decaying in some way due to friction) in time that means it is unstable going backwards in time. And vice versa. This isn't physically what is going on though. Actually there is some external force that started to system up or the system goes outside it's bounds of definition (your pendulum was forged and bolted together at some point). We can cook up forcing terms to make the fourier transform work, but it is a funny game we're playing. We replace nonhomogenous boundary conditions with a homogenous boundary condition going towards -\inf and a fictional bizarro forcing term.







However, the Laplace transform feels rather odd. It is somewhat surprising that is is invertible. Decomposing into decaying exponentials feels strange compared to decomposing into freqeuncies. The Laplace transform delves more into complex analysis, which has a beautiful internal coherence to it, but it also pretty bizarre.



















I would normally associate a resistor with a single current and two voltages. Voltages live on nodes, currents live on edges







03/20







Reading about algebraic geometry / algebra, the really compelling use case of these theorems and techniques is solving systems of polynomial equations. That is enough to get me interested.







Some domains that seem like natural fits







  * Mechanisms
  * CAD
  * Automated geometric theorem proving
  * Optics - see blog post
  * Sum of Squares techniques






In the book though they start talking about modules and I get lost. What the hell are those for. Who ordered that.







Modules are one possible weakening of Vector Spaces. They are vectors spaces where we can't divide scalars.







Vector spaces are also super duper useful. Over the many years of indoctrination I've received in our educational system, I have indeed been convinced that linear algebra is worth it.







Despite considering myself very comfortable with linear algebra and having an intuitive grasp of it, the way mathematicians talk about it, and their focus is very strange.







A vector space generated by a set of vectors.







The kernel of a matrix is a vector space. 







I have the tendency to think of this in terms of matrices. And I think of the kernel as being all the vectors who's dot product with the row of the matrix = 0. Likewise the condition for the generators and the kernel representing the same space is that all the dot products is 0. 







But it is interesting and useful to give up the dot product. 







Then the matrices of generators and the kernel matrix are linear maps rather than collections of vectors.







The is an example of a short exact sequences, which is a more generalizable replacement for some uses of inner product.







Exact sequences also form in vector calculus. The curl of a gradient is 0. I like to think of the finite difference matrices involved, but one can also consider these linear mappings between differently sized spaces. Taking the fourier of laplace transform of these equations converts them into polynomial equations.







Suppose you had a space described by cutting out polynomial sufraces or parametrized by polynomials. If you differentiate polynomial functions on the spaces would they have something like div grad curl. Could you find topological numbers of these surfaces from polynomial calculation. The Tangent spaces of these surfaces seem like natural modules. The tangent space of a sphere will be things in the kernel of the normal derivative function modulo the sphere function itself. x^2 + y^2 + z^2 = 1. A torus might be describable using polar coordinate and c^2 + s^2 = 1. That would cut it out from 4 dimensional space. (given fixed radii) . the inner ring is described by c^2+s^2 = 4 and then (c x + s y / () -  )^2 + z^2= 1. These spaces are an analog 







There is a theme here that making mathematical objects concrete means either discretizing or polynomializing. See finite difference vs spectral methods. Mesh /simplicial complex method vs Polynomial surfaces for geometry.







The inner product of these continuous spaces is the integral $latex \int v u dx.







On the other axis, modules are kind of a ring with more structure?













We can use the syzygies for subspace checks.







We can stack syzygies to meet







We can stack generators to join







Free Resoluitions might occur if we even needed some kind of duality in the linear case.







Hmm. Zach said something that makes sense to me (for once, sorry zach). I was thinking about tangent spaces by literally taking polynomials and differentiating them, getting gradients. The dot of the gradients onto a vector based at that position = 0 decsribes a cut away tangent space. From the more abstract persepctive, the coordinate ring is the quotient of the full set of polynomials by the cut away surfaces. It contains polynomials that can help tell where you are. If we quotient this ring by the point we are interested in at, this is a ring of things that are nonzero at that point, and nonzero on the surface?  The dimension of the tangent space. quotirnts and exact sequences are the same thing? Ok,I'm not actually pulling away much from this













One presents a vector subspace as a span of vectors







There is a ubiquitous pattern in mathemtics. Description by generators, Description by relations. Normlaized and unonnmoralize.







Grobner basis make division work good.







In linear algebra, I could give you a pile of vectors and say they generate a space. They may be extremely over complete and redundant, so maybe you want to put them into some normalized form. When you do this, for example, you can tell how big the dimension of your vector space is.







Eigenvalue, SVD, QR, and Gaussian Elimination all seem to do the job for a pile of vectors.







These normalized forms also make it easy to convert between a generator presentation and a relation presentation.







Gaussian elimination is similar in some respects to buchberger's algorithm. Gaussian elimination proceeds by elementary row operations, trying to zero out columns in tern. This depends on a choice of ordering for your vectors, which is already apparent in the explicit matrix representation. Buchberger's algorithm for a linear system of equations (on a set of linear polynomials) will achieve an effect similar to reducing to row echelon form. Buchberger's algorithm has the possibilty of adding new generators(rows) to the set. Gaussian elimination could be defined to do this also. In guassian elimination, we are not scared to multiply a row destructively because we can always undo such a thing by division. Not so for rings. You are safest if you merely append mutiples and sums of known generators to your generator set rather than destructively do something. It is safe to destructively perform reduction with respect to another known generator.













The terminology of algebra is extremely off putting and arcane. It upsets me, because there are so many good things there.







In linear algebra, you can talk about individual vectors, but also vector subspaces. Concretely vectors are going to be lists of coefficients which are interpeted a multpliers of some understood vectors. Subspaces can be represented as a list of such vectors, with it undertsood that you are speaking of the span of that set. This is remarkable that a vector subspace is an infinite thing from a set perspective, but you can describe it succinctly by closing over vector operations of sum and scalar multiplication. Alternatively you can describe a subspace as the set of vectors that dot to zero on a give concrete finite set of vectors.







Ideals are sets. They are concretely presented as a finite set of polynomials that generate the ideal. (Other ways?)







Algebraic geometry has internal ways of talking about differential feeling ideas.







The spectrum of a ring is the set of all prime ideals. This means it is a set of sets, quite a possibly large object. 







Maximal ideals are points. Prime Ideals are sets of points.







Krull dimension is maximum length of strict inclusion chain of prime ideals. By localizing, we can get the dimension at a position. 













The spectrum of a matrix is the set of its eigenvalues. These are the zeros of its characteristic polynomial det(A-lam). You can form an ideal generated by the characteristic polynomial. Then you can quotient the entire space by it to get a quotient ring? Uhh. I'm not sure this is what we want.







Polynomials can be thought of as functions from K^n -> K where n is the number of variables, or as a formal data structure. A map of polynomials is described contravariantly because of this.







[http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.39.488&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.39.488&rep=rep1&type=pdf) open dynamical systems. J Willems







[https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf](https://homes.esat.kuleuven.be/~sistawww/smc/jwillems/Articles/JournalArticles/2007.1.pdf) Shiiiiiit dude, get a load of this. [https://golem.ph.utexas.edu/category/2018/06/the_behavioral_approach_to_sys.html](https://golem.ph.utexas.edu/category/2018/06/the_behavioral_approach_to_sys.html) fong's thesis [https://arxiv.org/pdf/1609.05382.pdf](https://arxiv.org/pdf/1609.05382.pdf)







[https://wwwhome.ewi.utwente.nl/~poldermanjw/onderwijs/DISC/mathmod/book.pdf](https://wwwhome.ewi.utwente.nl/~poldermanjw/onderwijs/DISC/mathmod/book.pdf)







Behaviors - sets of functions. That feels in line. How do we describe sets of functions? a differential equation is one. Linear ODE describes a linear subspace. It is spanned by the Apsi + Bphi form of solution. No intrinsic breaking of system up into control and state







[https://www.sciencedirect.com/science/article/pii/S0196885899906577](https://www.sciencedirect.com/science/article/pii/S0196885899906577) The nullstullensatz for PDEs.







Hermite and Smith form. Forms of matrices for PID. Principal ideal domains. Single variable polynomials over field and integers are pid. They have a notion of prime decompoisiotn. unimodular matrices - matrices that are still invertible even though we're in a ring







[https://desr.readthedocs.io/en/latest/index.html](https://desr.readthedocs.io/en/latest/index.html) seems to be going back into olver and hubert town. ODE symmettries [https://tanbur.github.io/desr/dissertation/differential_algebra_and_applications.pdf](https://tanbur.github.io/desr/dissertation/differential_algebra_and_applications.pdf) a dissertation. Very interesting references.







Unimodular problems. That has come up in integer programming. If a problem is specified with a unimodular matrix, then it is solvable in poly time and LP gives the immediate correct solution I believe is the theorem. So another application of modules is integer programming, because Z is a ring, not a field.  Is this a way to see graver basis as grobner?







[https://euclid.ucc.ie/hanzon/20041106.pdf](https://euclid.ucc.ie/hanzon/20041106.pdf) constructive algerba and systems theory



