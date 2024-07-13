Multigrid perspective (ie linear) scaling, coarse graining, fine
graining. Recatngular Matrices

Black body? Assume no quantum mechanics is known. Can we get results
about blackbody radiation without divergences? Some kind of free
parameter= hbar?

Error analysis for series as scaling exponent law. Rumford integration
and richardson

Applications in stat mech and particle theory

Migdal Kadsnoff and even-odd reduction of matrix - fast poisson solvers.
Fast fourerir useful? AIC

Gaussian integration variable by variable = gaussian elimination schur
complement left behind.

Iterative LU?

Kadanoff block renomormzalization elemination corresponds cyclic order
reduction. correspondance to Momentum shell integration makes sense via
FFT recursion. FFT cornu spiral diagrams

The transfer matrix approach as a reduction full K matrix as a Initial
value problem. Band limited LU form allows back substitution steps to be
done in a convenient block format. Compare with renormalization approach

Tikhnoff type regularization terms have exactly the same form as
counterterms au\^2 and bu'\^2. QFT is ill-posed(sensistive or
nonunique)? QFT regularization = engineering regularization? Not like
anybody was hiding it if so. Can use dimnesional regularization on
matrices? Kronecker product idea, like a fractional kronecker power?
Zeta regularization, others. C utoffs? Matching mass parameters to the
experimental data at energy scales? The discrepancy principle.

How does renormalizability of theory correspond to discrete case? no
phi\^5 terms?

Feynman diagrams and matrices? Loops diagrams?

Lattice QFT. Chebyshev points.

Halton Sequence Is the same as my renormalize LU sequence. Not sure if
connected.

what does a coupling constant mean? how do we determine it?

Hamilton jacobi as semiring matrix. particle creation as nonsquare
matrix? symmettry properties, time reversal etc. particle networks

Sufficient Statistic. I have a suspicion this is important. Allows you
to gloss over shit perfectly. Perfect Decimation? Also the idea of
conjugate priors-form invariance

irrelevant operators - blocking operation. In 1-d everything goes to
tridiagonal under sufficent blocking. The invariance of special forms
under blocking is quite interesting

The partition function satisfies a dilation equation on shit. Whats that
called? The renormalziation eq?

Machine Learning approach. Consider theory unknown. Perhaps described by
prior random matrix gaussian, or parameters described by prior gaussian.
Given the theory, we can predict probability of results using quantum
mechanics. Use bayes rule to reverse and max likeihood to find
parameters. Alternatively fit theory to certain results (like a
particular cross section or mass measurement), use cross-validation on
other results. Cutoff can be implemented by allowing different size
matrices into the mix. the prior of the size of matrix maybe use poisson
dist with $V\Lambda^{2}$as poisson parameter

Possiblity: Dimension is the connection between a physical thing and the
macro human sized reference quantity we compare it to. Fracta geometry
is the failure of dimension to have integer exponenets scaling swith
chnages in the measurement process. Renormalization is the failure of
homogeneity itself. Check the derivation of homogeneity in dimensional
analysis (or the PI theorem). Some aspect of the assumptions must be
failing.

Is it possible for curvature to be a function of coarseness? I don't see
why not. Modeled by fractal extrinsic geometry of surfaces. If similar
triangles are required for dimension definiton, then the screwing of
similarity by noneuclidean business would cause scaling behavior of
measured quantities. Measuring angles and tlengths on a corrugated tin
roof. Easily imagine a system can get more ripply at small scales. Shit
happens all the time. But our typical diff geo conception is small
things get less curvy

a doint is a distirubtion of points (possible with given means and
varinces and such). You sample a doint. You can fit a line to doints or
paramer estimate the dine between two doints. You can fit any euclidean
geometric construct model to doints. Joint doint if not independant.
What is the dine specified by two doints?

$kx$ and $k'x-\frac{1}{3!}(k'x)^{3}$. If we use one to fit a sine curve,
we could then transfer to an equiolvanet k'. Over an interval, the
taylor series is not the best fit to the sine curve leads to two
different k estimates. Cutoff in the series. Not exactly momentum cutoff
but similar. The beta function transfers calues of k to different series
accuracy

Arnoldi gives effective hamiltonian?

Dimensional Analysis
====================

There is a symmettry between changing your ruler and changing the system
itself. Changing your ruler size is suppoesed to be meaningless as
regards to your system (perhaps not, see fractal dimension). Or changing
relative values of comparable quantities (what does it mean for a
quantity to be comparable? How sure must we be of the correspondaance,
and why is it monomial?). This is the natural scaling symmettry of the
world. Both lead to equivalent effects in the same manner that changing
to a new interial frame and just looker at an object with a different
velocity are under a symmettry. It is this symmettry that vayslty
reduces the legitimate possibilities of variable combination, in the
same manner that rotational symmettry requires to notion of scalars and
vectors, or the special relativity requires index matching.

Invariant quantities under this symmettry are known as dimensionless
quantities, which hold a similar conceptual place to scalars in relation
to rotational symmettries, or differences in regards to translational
symmettries

A deep question that I have no answer to is what happens when you try to
remove all dimensions. This seems like perhaps a bad move. Gauge fields
have proven to be quite useful. To go dimensionless is to gauge fix in a
sense. If that is all, maybe no harm done. But I'm not convinced
dimensionless is not more sinister than that.

Even abstract geometric volume is intrinsically unitful. We could define
$1m^{3}$to be the volume of a sphere with radius 1 instead of a cube
with side 1. Everything would work out. So dimensful objects have not
only unit lengths, they have unit shapes. We'd adjust in the usual way
from all our ordinary formulas by factors of $4\pi$. What is truly
important is comparison and the mechanism by which compariosn is
achieved.The ancient geometers used the mechamisn of straightedges and
compasses to be able to compare any lines. They may have been closer to
the truth of the matter than we. In a dimensionless universe, does one
even have metrics? We should only possess proportions and then only when
there is an plausble method of verifying such similarity. Can one
contruct a line with the length of the circumference of a unit circle
using only a compass and striaghtedge? Perhaps by a limitting process,
but otherwise no. $\pi$ is irrational and only quadratic numbers may be
produced.

Straightedge COnstructions, triangular similarity is the cnanonical
model of defining units.

How does a fish measure mass? Static definitions : use a scale. Has
buoyancy issues. Dynamical definitions has drag force. A fish cannot
leave water. W can't leave th EM field. Static mass and Dynamic mass
would require unficiation. The lower velocity dynamic mass would
correspond to our conception. Fast mass and weight mass would have oher
depdnencies.

Units of measruement are a construct of man. Just sayin'

The Ising Model
===============

The Ising model is in some ways a close cousin to the Laplace equation

$$\frac{d^{2}}{dx^{2}}u=0$$

In Variational form this comes from minimizing the square of the
derivative. In other words the function is trying to be as uncurvy as
possible given the contraints of boundary conditions. Neighboring values
of u want to have the same value ($du=0$ as much as possible), to go
with the crowd. If we force the ends to be at weird spots,

$$H=\frac{1}{2}\int(\frac{d}{dx}u)^{2}dx$$

We could discretize this integral and derivative to a sum and a
difference

$$\Delta=\left[\begin{array}{cccccc}
-1 & 1 & 0 & 0 & 0 & 0\\
0 & -1 & 1 & 0 & 0 & 0\\
0 & 0 & -1 & 1 & 0 & 0\\
0 & 0 & 0 & -1 & 1 & 0\\
0 & 0 & 0 & 0 & -1 & 1
\end{array}\right]$$

$$u=\left[\begin{array}{c}
u_{1}\\
u_{2}\\
u_{3}\\
u_{4}\\
u_{5}\\
u_{6}
\end{array}\right]$$

$$H=\frac{1}{2}u^{T}\Delta^{T}\Delta u$$

Now, u can still take on continuum values. This might be kind of a pain
partition function wise as we'll have to do a bunch of integrals
(Actually, the integrals would be much easier to do in closed form than
these new sums, but whatever). To simplify conceptually, we'll only
allow u to take on two different values at each index, let's say 1 and
-1. To count the energy, we just count to the number of changes u goes
through. For example

$$u=\left[\begin{array}{c}
1\\
-1\\
1\\
1\\
1\\
-1
\end{array}\right]$$

Has two $1\rightarrow-1$ transitions and one $-1\rightarrow1$ transition
so it basically has an energy of $3\times$Some Constant.

If we had left

We'll be integrating over each component of u a lot so let's define a
notation for it.

$$\int du_{1}\int du_{2}\int du_{3}\int du_{4}\ldots=\int d^{N}u=\int[Du]$$

Then the partition function will look like this

$$Z=\int[Du]e^{-\beta\frac{1}{2}u^{T}\Delta^{T}\Delta u}$$

Completing the squares is Gaussian Elimination
----------------------------------------------

We can perform linear changes of variables quite easily, since linear
algebra is one of the few things we understand.

In any polynomial we can remove one power that isn't the hightest one by
a linear chnage of variables

$$x\rightarrow my+r$$

$$p(x)=a_{N}x^{N}+a_{N-1}x^{N-1}+\ldots+a_{0}$$

$$p(my+b)=a_{N}(my+r)^{N}+a_{N-1}(my+r)^{N-1}+\ldots+a_{0}=b_{N}y^{N}+\ldots b_{0}$$

Now we want $b_{k}=0$, so we collect $y^{k}$terms

$$b_{k}=\sum_{i=k}^{N}(\begin{array}{c}
i\\
k
\end{array})a_{i}m^{k}r^{i-k}$$

This isn't working out right.

What I meant is that you can remove the N-1 term using a linear change
of variables

$$b_{N-1}=a_{N}m^{N-1}r+a_{N-1}m^{N-1}$$

I'm not making my point.

Let me start over

We want to complete the squares on

$$ax^{2}+bx+c$$

i.e take it to the form

$$(qx+r)^{2}+d$$

Well, we expand it back out and collecty powers of x.

$$r^{2}+d=c$$

$$2rqx=bx$$

$$q^{2}x^{2}=ax^{2}$$

We solve for r, q, and d

$$q=\sqrt{a}$$

$$r=\frac{b}{2\sqrt{a}}$$

$$d=c-ar^{2}=c-(\frac{b}{2})^{2}$$

Alright. Straightforward, but complicated.

Now suppose we had a quadratic function in many variables. Sadly it
seems that our notion of completing the squares breaks down. Yet, we
could pick some of the variables, and then perform a completing the
squares operation on him. In that case b will be a linear function of
the other variables and c will be a quadratic function of the other
variables. This will then lead to r also being a linear function of the
other variables and d remaining a quadratic.

But then we can repeat this process on d. We can complete the squares on
a new variable in d and so on until we have a hierarchy of completed
squares.

A quadratic function of many variable can be convenitenly written in
vector notation.

$$x^{T}Ax+b^{T}x+c$$

By analogy with the single variable case to complete the squares on it
we'd like it to be in the form

$$(Lx+r)^{T}(Lx+r)+d$$

Equating the sides we have

$$L^{T}L=A$$

$$2L^{T}r=b$$

$$r^{T}r+d=c$$

The first equation is solved by taking the matrix square root of A in
some sense (Which is not unique btw). Here's the key though, this is
equivalent to gaussian elimination or LU factization or Cholesky
Factorization, to get some buzzwords in there.

This completing the square is just absolutely perfect as far as a
multivariable gaussian integral is concerned. PERFECT I TELL YOU.

The change of variables is

$$y=Lx+r$$

Then the Jacobian (the factor to account for the ratio of $d^{N}x$ to
$d^{N}y$) is just

$$d^{N}y=d^{N}x|J|=d^{N}xDet(L)$$

$$Det(L^{T}L)=Det(L)^{2}=Det(A)$$

Incidentally, this route is much much much better than sum of all entry
combos with -1 thrown in formula if you want to actually numerically
calculate a determinant of A for some godforsaken reason. Gaussian
elimination to produce L is pretty fast, and then the Det of a
triangular matrix is just the product of its diagonal. If you need the
Det of a really really big matrix though, this might not cut it. I am
not aware of any sparse matrix based techniques (The big guns) for Dets
but they got to be out there, right?

This gaussian elimination process is exactly the process that is
demonstrated in introduction to path integrals techniques for the free
classcial particle. The books show you iterating the square completing
process, and then integrating out each variables as it comes along, and
hope you can decipher the pattern. I think think about it at the matrix
level is siginifacntly more poweful as we'll see.

Partitioned Matrices
--------------------

It is highly useful to think of a matrix as being partitioned into
submatrices. Let's look at the sinplest partition first, into two
subspaces

$$M=\left[\begin{array}{cc}
A & B\\
C & D
\end{array}\right]$$

where A is $r\times r$, B is $r\times q$, C is $q\times r$ and D is
$q\times q$. Ruh Roh! Rectangular Matrices!

The great and remarkable thing about this idea is that most matrix stuff
works like it should. A good sanity check on most things is to make sure
the dimensions of the blocks jive together correctly. Matrix
multiplication is still rows times columns at the block level (Careful
with ordering though!). Matrix addition is still sum of components at
the block level.

Transpose is quite similar to its scalar counterpart

$$M^{T}=\left[\begin{array}{cc}
A^{T} & C^{T}\\
B^{T} & D^{T}
\end{array}\right]$$

$$tr(M)=tr(A)+tr(D)$$

How about the inverse though? Or the Determinant? Hmmm\... Now we're
getting somewhere interesting.

How about LU decomposition? Let's review the scalar case

$$M=\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]$$

You multiply a matrix on the right side to add columns to one another
and on the left side to add rows. See, the first column of this right
side matrix says take the first col of M and the Second col of M to
produce to first new col. The second col of the right side matrix says
to just keep the second col of M as is

$$\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]\left[\begin{array}{cc}
1 & 0\\
2 & 1
\end{array}\right]=\left[\begin{array}{cc}
a+2b & b\\
c+2d & d
\end{array}\right]$$

$$\left[\begin{array}{cc}
1 & 0\\
2 & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]=\left[\begin{array}{cc}
a & b\\
c+2a & d+2b
\end{array}\right]$$

Hence all those row operations you're used to in gaussian elimination
will be left side multiplcations by row summing matrices

$$\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]M=\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]=\left[\begin{array}{cc}
a & b\\
0 & d-cb/a
\end{array}\right]$$

So we got it into triangular form. Not super pretty though. Let's take
that matrix off of M

$$\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]^{-1}=\left[\begin{array}{cc}
1 & 0\\
+c/a & 1
\end{array}\right]$$

This is true because the first row was untouched, so we just need to sum
that row onto row 2 in order to undo our previous subtraction from row
2. Or just matrix multiply them and you'll see its true.

Hence

$$M=\left[\begin{array}{cc}
1 & 0\\
c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
0 & d-cb/a
\end{array}\right]$$

Let's get it into a Nicer LDU form

$$M=\left[\begin{array}{cc}
1 & 0\\
c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & 0\\
0 & d-cb/a
\end{array}\right]\left[\begin{array}{cc}
1 & b/a\\
0 & 1
\end{array}\right]$$

Nice. Okay, we can follow our logic every step of the way through for
the block case, except now we need to make sure dimensions of matrices
match when we multiply them. If we're careful, we'll end up with this
form

$$M=\left[\begin{array}{cc}
I & 0\\
CA^{-1} & I
\end{array}\right]\left[\begin{array}{cc}
A & 0\\
0 & D-CA^{-1}B
\end{array}\right]\left[\begin{array}{cc}
I & A^{-1}B\\
0 & I
\end{array}\right]$$

This lower entry is very very important. Its called the Schur Complement

$$D-CA^{-1}B=M/A$$

Interpetation of Schur Complement (I need to think about this more): It
really IS aptly named. It is a complement in a true set like sense.
We've divided the space into two. The true and the false. The left and
the right. The black and the white. We've developed a dichotomy. If A
has dimension r, M has n, then M/A has n-r.

Hence

$$Det(M)=Det(A)Det(D-CA^{-1}B)=Det(A)Det(M/A)$$

Thinking about that slash as a division operation that seems mighty
plausible.

The beautiful thing about this block procedure is that you can remove
signifcant amounts of your variables by elimination all at once.

Thevenin Equivalence
--------------------

Thevenin equivlance is solving out an entire circuit section that is
lightly connected. Rank One update?

COnsider the following Hypothetical experiment. We have probes attached
to external nodes of a circuit. Noisy due to johnson-nyquist? We want to
determine internal structure of circuit. We can build circuit model
(possibly nonlinear), but complexity is limitted by noise. We may expand
and contract model at will by circuit equivalence more or less. Can we
probe more are higher frequencies, higher amplitudes? Get a larger data
set.

Bjorken and Drell mentions a circuit analogy to feynman diagrams. How
far can this be taken? A feynman diagram is like a bunch of circuits in
parallel kind of. Each one is harder to excite, more high pass.

Loops of momemntum like mesh analysis. If the ampltidue associated with
a diagrams can be written as some matrixy operatro Trace, det on the
adhacency matrix, that would be great. Could freely use elimination.

Matrix Boundary Conditions
--------------------------

Boundary conditions are the most subtle and best part of differential
equations, I think discretizing them gives significant clarity to the
whole process.

The finite element idea

You can take a differential equation to a weak form by mulltiplying by
an arbitrary function v and integrating

$$\int v\frac{d^{2}}{dx^{2}}udx=0$$

Now we can integrate by parts

$$\int\frac{d}{dx}v\frac{d}{dx}udx=0$$

and this should still be true for all v.

However, we're thinking of functions as huge vectors. Instead of letting
v or u be anything in the huge vector space, let's pick a finite set of
basis functions. A snesible set, it turns out are overlapping triangle
functions. They're nice because their derivative is constant and since
they're zero almost everywhere, they lead to sparse matrices, although
lots of choices are possible. We could for example use the first 20
fourier modes as out finite basis.

$$u(x)=\sum_{i}u_{i}\Phi_{i}(x)$$

$$v(x)=\sum_{i}v_{i}\Phi_{i}(x)$$

We plug this in to our weak form. Since v could be anything, everything
multplying a $v_{i}$has to be zero. This is a set of linear equations on
the $u_{i}$

$$\sum_{j}u_{j}\int\Phi'_{i}(x)\Phi'_{j}(x)dx=0$$

We could construct a matrix

$$M_{ij}=\int\Phi'_{i}(x)\Phi'_{j}(x)dx$$

Then this condition reduces to the matrix equation

$$Mu=0$$

This is an alternative way

This is almost identical to the variational idea used as an
approximating method, although the variational idea often doesn't
consder the set of possible u to be linearly parametized, so its got
some flexbility in that respect

$$H=\frac{1}{2}\int(\frac{d}{dx}u(x,\alpha))^{2}dx$$

Now we do the integral and minize with respect to $\alpha$. This is a
parametized subspace of the space of all possible functions, but
arbitrary minimzation can be a sticky problem in and of itself.

We know what the finite difference version of the second derivativ looks
like

$$\left[\begin{array}{cccccc}
-1 & 2 & -1 & 0 & 0 & 0\\
0 & -1 & 2 & -1 & 0 & 0\\
0 & 0 & -1 & 2 & -1 & 0\\
0 & 0 & 0 & -1 & 2 & -1
\end{array}\right]$$

This is rectangular. After all, what were we supposed to do with the
edges? To make it square, and hence solvable, we need to add two new
independant rows. These correspond to the two boundary cnditions we may
specify in the continuous problem. Adding the row

$$\left[\begin{array}{cccccc}
1 & 0 & 0 & 0 & 0 & 0\end{array}\right]$$

would be a specifcation of the left most value of the function
(Dirichlet conditions)

$$\left[\begin{array}{cccccc}
0 & 0 & 0 & 0 & 0 & 1\end{array}\right]$$

Would do the same for the right side

$$\left[\begin{array}{cccccc}
-1 & 1 & 0 & 0 & 0 & 0\end{array}\right]$$

Would specify the deirvative at the boundary (Neumann)

If we specify everything at the left, it is an inital value problem. One
condition on each side and its a boundary value problem

Now the Schur ideas come into play. We may want to remove the block of
boundary conditions to a new system which is only in the interior. The
trouble is that the current form of the equations is not symmettric,
which is a great boon. After eliminating the boundary points as
variables, we will have a symmettric form if we have symmettric boundary
conidtions specified.

Integration by parts corresponds to taking a transpose.

Irrelevant and Relevant Operators and Blocking
==============================================

In 1-d any banded diagonal operator will end up as tridiagonal is we
keep blocking. If it started as upper or lower triagnular, it will
maintain this property as well.

$$K=\frac{1}{\Delta x^{2}}\left[\begin{array}{cccccccc}
2 & -1 & 0 & 0 & 0 & 0 & 0 & 0\\
-1 & 2 & -1 & 0 & 0 & 0 & 0 & 0\\
0 & -1 & 2 & -1 & 0 & 0 & 0 & 0\\
0 & 0 & -1 & 2 & -1 & 0 & 0 & 0\\
0 & 0 & 0 & -1 & 2 & -1 & 0 & 0\\
0 & 0 & 0 & 0 & -1 & 2 & -1 & 0\\
0 & 0 & 0 & 0 & 0 & -1 & 2 & -1\\
0 & 0 & 0 & 0 & 0 & 0 & 2 & -1
\end{array}\right]$$

Let's consider a single blocking

$$K=\left[\begin{array}{cccc}
B_{1} & 0 & 0 & 0\\
L & M & R & 0\\
0 & L & M & R\\
0 & 0 & 0 & B_{2}
\end{array}\right]$$

$$M=\left[\begin{array}{cc}
2 & -1\\
-1 & 2
\end{array}\right]$$

$$L=R^{T}=\left[\begin{array}{cc}
0 & -1\\
0 & 0
\end{array}\right]$$

$$B_{L}=B_{R}=M$$

I labeled them $B_{1}$ and $B_{2}$ because for different boundary
conditions these matrices might not end up equal to M.

If K is symmettric then L and R have to be trnaposes of one another.

We could block again

$$M_{2}=\left[\begin{array}{cc}
M_{1} & R_{1}\\
L_{1} & M_{1}
\end{array}\right]$$

$$L_{2}=R_{2}^{T}=\left[\begin{array}{cc}
0 & L_{1}\\
0 & 0
\end{array}\right]$$

$$M_{n+1}=\left[\begin{array}{cc}
M_{n} & R_{n}\\
L_{n} & M_{n}
\end{array}\right]$$

$$L_{n+1}=R_{n+1}^{T}=\left[\begin{array}{cc}
0 & L_{n}\\
0 & 0
\end{array}\right]$$

$$$$

Haar Wavelet decimation? Integrating out wavelet level is the same as
integrating out that detail level. What does K do under Wavelet
transform?

Regularization, statistics and learning
=======================================

You want your model to only be as complex as your data allows. The
Cutoff regularization achieves that by shannon sampling theorem. As we
get more details, we expand the allowable bandwidth, increasing the
complexity of the fitting model. Since the data has only so much detail
at each experimental energy scale (only achieves wavelength probing?
What does that mean?),

Other types of regulization are probably similar, they all give
parameter that reduce complexity of model. Dimensional for example. 3
dimensional data is easier to obtain that 4 dimensional. Significantly
so.

Wavelets might also give a good extendable model scheme.

Relation to Reylieghs criterion. Not a hard and fast rule. Interference
experiments can do better, as well as near field calculations (Does this
also mean heisenberg can be beaten?). Also, Even if two lumps overlap,
with sufficient sampling time or lack of noise, I think they can be
deconvolved

And the idea of probing with wavelengths. Scattering experiments

Regularizing classical blackbody
--------------------------------

wavecutoff, should occur as quantumness kicks in. In compliance with my
general program, we need to show that one could not extrapolate
classical theory to high wavelengths according to experimental procedure
avaiable and remain honest. Perhaps tempurature was ill defined for
small wavelengths? We must verify that by sampling each wavelength.

1, some sort of rayleigh's criterion argument. basically a standin for
heisenberg

2\. set cutoff to match stefan blotzmann law. Why would one do this?
This is a hack job without motivation

Would work decent

Qunatum mechanics itself or quantum inspired mathemtics might be
considered a cutoff scheme using hbar

Casimir Effect
--------------

Domain decomposition - use for blocking procedure, corresponds to cutoff
change?

Finite energy comes from difference between free boundary conditions and
constrained

$E=\hbar(\sum\omega-V\int\omega d^{3}k)=\sum\frac{\hbar cn}{L}-\frac{\hbar}{L}\int dn$

Claim is that this is an instance related to renormalization

### Effective Mass in Ideal Fluids

The fluid does not go out of its way to move more than it has to meet
the boundary conditions, so it minimizes the kinetic energy

$$T=\frac{1}{2}\rho\int v^{2}dV=\frac{1}{2}\rho\int(\nabla\phi)^{2}dV$$

If we use the identity

$$\nabla\cdot(\phi\nabla\phi)=\nabla\phi\cdot\nabla\phi+\phi\nabla^{2}\phi$$

$$\nabla^{2}\phi=0$$

And the divergence theorem we get

$$T=\frac{1}{2}\rho\int\phi\nabla\phi\cdot\hat{n}dA$$

This surface integral includes all the surfaces, so it includes the
surface of the object and a surface at infinity.

One interpetation of $\phi$is as an impulsive pressure. If you applied
the pressure $\rho\phi\frac{1}{dt}$ for a split second $dt$, You could
produce the velcity field?

The boundary conditions for a moving object at velocity $u$ is

$$\nabla\phi\cdot n=u\cdot n$$

At the surface of the object.

If the object is spinning $u=u_{0}+\Omega\times r$

So if you wrench a paddle, and there is now kinetic energy in the water,
it had to come from you..

For a sphere, a dipole potential will do you good (Why? Well, it works.
You can find it by seperation of variables into spherical harmonic (or
legendre polynomials since axially symmettric) if you like.)

$$\phi=\frac{ua^{3}\cdot cos(\theta)}{2r^{2}}$$

$$T=\frac{1}{2}\rho\int\phi\nabla\phi\cdot\hat{n}dA=\frac{1}{2}\rho\int\frac{ua^{3}\cdot\cos(\theta)}{2a^{2}}u\cdot\cos(\theta)a^{2}d(\cos(\theta))2\pi=\frac{1}{2}\rho u^{2}2\pi a^{3}\frac{2}{3}\frac{1}{2}=\frac{1}{2}\rho u^{2}\frac{1}{2}V$$

So basically, your mass of the ball becomes

$$m=m_{0}+\frac{1}{2}\rho V$$

This also works for momentum

$$P=\rho\int\nabla\phi dV=\rho\int\phi\hat{n}dA$$

The z component is the only one to survive by symmettry

$$\rho\int\frac{ua^{3}\cdot cos(\theta)}{2a^{2}}\cos(\theta)\hat{z}d(\cos(\theta))2\pi a^{2}=\frac{2}{3}\rho2\pi a^{3}u\frac{1}{2}=\frac{1}{2}\rho Vu$$

What about an ellipsoid? Or a box?
