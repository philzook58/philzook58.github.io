Subspaces and The Determinant
=============================

inclusion exclusion of subspaces = determinant?

Contraction and Inner Product
=============================

Subspaces are represented by matrices filled with a spanning set of
vectors. The subspace and magnitude of the subspace are modified in a
similar manner to the determinant, and it fact you can provide
coordinates for the subspace by using the minors of this matrix.

Inner product of two equal sized subspaces is the determinant of a
matrix made of their dot products. For a space onto itself, this is
called the grammian, and it represents $\det A^{T}A$, so it contains the
squared product of the singular values of our subspace matrix. It
represents the volume occupied by our subspace

The Contraction is an orthogonalization process. Calculate $|A|$.
Project A down into B. Then use gram schmidt to remove A from B.
Multiply what remains by $|A|$.

Pack A and B into the same matrix. Perform QR on this matrix. Unpack. If
you ende up with enough

$$\left[\begin{array}{cc}
A & B\end{array}\right]=\left[\begin{array}{cc}
Q_{A} & Q_{B}\end{array}\right]\left[\begin{array}{cc}
R_{A} & 0\\
0 & R_{B}
\end{array}\right]$$

Clairty might comes by continually keeping the Matrix A in QR factored
form. The above diagonal elements are irrelevant and may be deleted. So
It may be stored as $QD$, where D is diagonal. For that matter, it may
stored as $aQ$ where a is the magnitude of the subspace and equal to all
the products of the diaognals of R.

Sums from grassmann algebra do not correspond to matrix summation.

Hodge Dual comes from using full QR. It is the nullspace of $A^{T}$, and
has a mgnitude. Is it associated with dual projector $I-P_{A}$?

A grassman vairable may be represetned by the porjection operator onto
that subspace, with a scalar outside. No not quite.

$$AA^{T}=|A|^{2}P_{A}$$

$$A=V^{T}\Sigma U$$

$$P_{A}=V^{T}V$$

$$A\lrcorner B=ab(I-P_{A})P_{B}$$

Join

$$A\cup B=A+B-A\cap B=P_{A}+P_{B}-P_{A}P_{B}$$

Does the order of projection not matter?

Or column reduce combined matrix and clip

$$\left[\begin{array}{cc}
A & B\end{array}\right]$$

Note Faugeras just uses wedge product as join, so requires A and B to be
a priori disjoint or else returns 0. Dorst and Mann do not require this.
Note the further reading sections comment on this

Meet

$$P_{A}P_{B}$$

Exterior Calculus
=================

Every vertex of your sturcture gets its own entry in a column vector

$$e_{1}=\left[\begin{array}{c}
1\\
0\\
0\\
0\\
0
\end{array}\right]$$

You can have linear combinations of the vertices. What does that mean?
Well, if you restrict it to integers, it might be a way of counting how
many of that vertex your geometric object has. You can also use this
vector as barycentric coordinates with a conversion matrix with columns
filled with the position of the vertices.

The exterior product of these vectors represent the lines connecting
them.

Is this correct?

$$e_{1}\wedge e_{2}=e_{1}\otimes e_{2}-e_{2}\otimes e_{1}=\left[\begin{array}{ccc}
0 & -1 & 0\\
1 & 0 & 0\\
0 & 0 & 0
\end{array}\right]$$

The inner product of wedges is ingerited from the inner product of
vectors

$$(a\wedge b)\cdot(c\wedge d)=\det\left[\begin{array}{cc}
a\cdot c & a\cdot d\\
b\cdot c & b\cdot d
\end{array}\right]$$

Similarly for forms. We can wedge forms together and then use it on
wedged vectors

We could also just make a column vector with an entry for each possible
combo. Then we'd need to build special matrices that create wedge
products and inner products. They'd all be fairly simple.

$$W_{(lm)ij}-\sum(\delta_{il}\delta_{mj}-\delta)e_{(lm)}\otimes e_{i}\otimes e_{j}$$

Exterior Algebra
================

Exterior algebra is entirely based upon the idea of the determinant. It
is a way at looking at th abstract manipulation of vector subspaces
(i.e. all linear combinations of some given set of vectors). The
anticommuting structure comes from determinants. Determinants determine
singularity, i.e. if a set of vectors are linearly independant or not,
so they're the perfect test

First off, the following definition

$$e_{1}\wedge e_{2}=e_{1}\otimes e_{2}-e_{2}\otimes e_{1}=\left[\begin{array}{ccc}
0 & -1 & 0\\
1 & 0 & 0\\
0 & 0 & 0
\end{array}\right]$$

I think this is bad. It is a numerical nightmare to antisymmettrically
kronecker product $n!$ terms. That is brute forcing the Leibniz
Expansions, which is terrible. One should probably just store the
vectors going into the wedge seperately, maybe orthogonalizing or gauss
eliminating as you go along (or you could just wait until the end). In
addition

$$(a\wedge b)\cdot(c\wedge d)=\det\left[\begin{array}{cc}
a\cdot c & a\cdot d\\
b\cdot c & b\cdot d
\end{array}\right]$$

To get this to work with the Kronecker product definition\... well,
maybe it would work. With a factor of $\frac{1}{\sqrt{n!}}$. Not sure.
My fear is that you might need to antisymmettrize covectors and keep
vectors unsymmetrized, which would be a pain in the dick.

Interesting connection, fermion QFT operator algebra and geometric
calclus on function vectors correspond to one another.

Projective Geometry and Homogenous Coordinates
==============================================

Camera Model

Usefulness in approaching translation

equivalence classes of rays

Pappus desargues

Crossratio

Duality

camera estimation

epipolar geometry

plucker coordinates

Desargues theorem - The reason is is useful is it is the foundation of
the barycentric coordinates. The two triangles are possible referene
triangles to build your coordinates from. The length of lines connecting
to the point are the coordinates of that point, and the length or angles
or something connecting to the line are the coordinates of the dual
line. Desargues tells us that regardless of refernce triangle, we
describe the same point and lines in our homogenous coordinates. The
theorem is doable in the euclidean plane since you just need to solve
some angles and shit to show that line is straight. Doing it from
projectgive axioms is more puzzling, and easier in a sense maybe.

Pappus - SOmething similar except for 1-d projective geometry and 2-d
homogenous coordinates.

projectivity

collineation - a point to point transfromation that turns lines into
lines

correlation - a point to line transfromation. Very curious. The
originator of the contact transfromation, a generaliztion of duality.

Dimensionl analysis uses homogenous coordinates of the physically
measured world. If our reference meter stick gets called 20 units then
all other values scale accordingly, represnting the same physical
configuration. Calling things negative would do similar things excpet
involve parity in reagrds to some reference parity object. Same physical
configuration though. Fixing reference stick is like picking absolute
conic kind of thing. There are classes of indvudally homogenous dudes.
When we start allowing pertinent conversion constants to take on finite
values, like c or hbar, we reduce the power. Is this like adding
metrical properties or removing them? time and space are incompatible
until you add c. Buckingham pi shows that physcial equations must be
algebraic curves in projective esque sense. What I don't see is the
equivalent of the wraparound for points at infinity. Well, maybe if you
consider a reference direction that shrinks to zero, the left becoes
right. Must compare to macroscopic human sized reference objects to make
sense of things.

Projective geometry is a kind of linearization of contact
transformations, but not at a local level like diff geo that has local
euclidean structure. We have no notion of distance, so we can't say
anything is infinitesimal (cross ratios maybe?). It is a global
linearization? Study of Abberrations is higher order. Maybe you select
three points and it is a linearization with respect to those three
points.

Conformal Geometry
==================

shutter model

riemann sphere and spin

I've seen similar ideas all over the place, but they are not crisp yet.
We add a point at infty and points are considered degenrate spheres. We
start from a higher dimensional cone from which we can work in any
geometry we please, hyperbolic, elliptic. They are the same.
