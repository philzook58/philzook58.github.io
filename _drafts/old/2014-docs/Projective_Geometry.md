Projective Geometry
===================

We have an intuitive idea of what consitutes space. Space is something
you can move around in. Its a place where you can put things. Geometry
is the study of space.

The ordinary geometry that we think of from High School, with triangles
and angles and distance and all that, is called Euclidean geometry. You
can think of it as the geometry of muscle, of feeling, of location.
Perhaps one might consider it to be physical geometry as well, as the
way things really are. I believe this is a debatable point.

Projective Geometry is the geometry of the eye. If you think about it,
the size of things is irrelevant to how large they appear and the angles
that things actually meet at does not determine the angle they meet at
according to your eye. You can demonstrate this with even your triangle
on a paice of paper. Sure, viewed top down it looks about correct, but
when you view the page almost edge on, the object is drastically
distorted. There

Some of the trouble understanding projective geometry is that you know
too much. When you see a lamp, you know how big the lamp is. When you
see a desk you know its edges meet at right angles. This is partially
what makes drawing accurate pictures of scenes so difficult. You put
down on the page what you know is there rsather than what you truly see
it there.

That the geometry you see is not the geometry you feel is also the
origin of a number of optical illusions.

Projective geometry is just as a legitimate as Euclidean geometry,
perhaps more so, as it turns out there is a neat hierarchy of Geometry.
If you approach geometry axiomatically, Euclidean Geometry is merely
Projective Geometry strengthened with a few extra axioms or by
specifying a few special lines and conics.

Pinhole Camera
--------------

The simplest picture to understand porjective geometry is that of the
pinhole camera. Imagine holding a card in front of your face with a tiny
hole in it. You can move your head side to side. The only thing you'll
see are things that are on the line connecting your eye to the hole,
everything else will be obscured. If it is really bright out, you can
place a screen behind the hole. and a scalded image with be porjected
into the screen, the image of the sun eppearing at the place on the
screen that is hit by the line connecting the sun to the pinhole. Now,
it is natrual to use (x,y,z) coordinates to describe the scene outside.
Let's place the camera at $(0,0,0)$. and place our screen on the line
$z=-1$. Then by looking at similar triangles made by the light ray
between hole and screen and the object and hole, we can see that an
object at $(x,y,z)$ will have an image on the screen at
$(-\frac{x}{z},-\frac{y}{z},-1)$

Fractions
---------

We all know what fractions are. They specify how much of a pie is left.
There are sticky parts of the theory of fractions that typically arise
from their ability to go inifnitely small and fine. In order to wrestle
with these beasts, one has to be very careful. When one approaches
fractions axiomatically, they are defined as equivalence classes of
pairs of integers. An equivalence relation is a grouping that satisfies
most of our intuitive ideas of equivlance

1.  If $a=b$, then $b=a$

2.  $a=a$

3.  If $a=b$ and $b=c$, then $a=c$

So for example, $(2,4)\in"\frac{1}{2}"$, and $(3,6)\in"\frac{1}{2}"$.
The pairing $(a,b)$ is defined to be in the same equivlalence class as
$(c,d)$ if $ad=bc$ (We would naturally reaarange this condiont to
$\frac{a}{b}=\frac{c}{d}$, but then we're using fractions in our
defintion of fractions, which is naughty. We want to found our fractions
in the bedrock of only the integers, which we may freely multiply, but
often not divide). So that means that if we multiply both terms by the
same factor, $(\lambda a,\lambda b)$, we do not change equivalance
class, because $\lambda$ "divides out".

One way of looking a projective geometry is to define it in terms of its
coordinates, which are known as homogenous coordinates. It is like using
fractions of real numbers instead of integers. We define a point on the
real projective line $RP^{1}$as the pair $(a,b)$ where $a,b\in R^{1}$.
Two pairs are equivalent if they differ by an overall factor $\lambda$.
Oftentimes we might think of the point $(a,b)$ as a point on the real
line $\frac{a}{b}$, but this correspondence cannot often be trusted, as
the correspondnce is. It is somewhat equivlaent to the porlbem in
Euclidean geometry of thinking about the point $(0,0,1)$ as the point on
the z-axis, when really, the point in the point, and the cooridnates
have an hidden dependance on how you define your axes. In Euclidean
geometry, we think rotationally and translationally invariant properties
of our setup as being truly important, and explicit coordinate
expressions might contain unimportant or deceptive details.

We can instead use the language of linear algebra to describe the same
thing. In linear algebra, n-tuples of numbers are called vectors. In
that case, a point in $RP^{1}$is given by a one dimensional subspace in
$R^{2}$, in other words a ray. A line in $RP^{n}$is given by a 2-d
subspace of $R^{n+1},$ a plane by a 3-d subspace, etc. The direction of
the vector matters, but its overall magnitude is irrelevant.

### Continued Fractions

For funzies, let's use our projective geometry ideas in an interesting
application, the study of some infinite contidued fractions.

The Babylon Method of Square Roots

$$x_{n+1}=\frac{1}{2}(x_{n}+\frac{b}{x_{n}})$$

We take our current best guess $x_{n}$ and calulcate $\frac{b}{x_{n}}$.
If our guess is really good, $\frac{b}{x_{n}}$ will be really close to
$x_{n}$, since ideally $x_{n}^{2}=b$. If $x_{n}$if too high, then
$\frac{b}{x_{n}}<\sqrt{b}$, because we divide by too big a number, if
our guess is too low then $\frac{b}{x_{n}}>\sqrt{b}$. So regardless of
where our guess lies, above or below the right answer, it feels like the
average of $\frac{b}{x_{n}}$ and $x_{n}$will be a better guess than
$x_{n}$was, since it will combine a too high and a too low number.\\

Augmented Vectors
-----------------

A third persepctive on homogenous coordinates is the idea of an
augmented vector. Let us agree to take any ordinary point vector and
just pack in an extra 1, for fun.

$$\left[\begin{array}{c}
x\\
y\\
z
\end{array}\right]\Rightarrow\left[\begin{array}{c}
x\\
y\\
z\\
1
\end{array}\right]$$

Any of our old familar operations, such as a rotation, or a relfection
about the origin, or skew transfromation, can similarly be extended

$$A\Rightarrow\left[\begin{array}{cc}
A & \begin{array}{c}
0\\
0\\
0
\end{array}\\
\begin{array}{ccc}
0 & 0 & 0\end{array} & 1
\end{array}\right]$$

Basically the 1 just comes along for a ride.

The benefit of this is now we can include translations as matrix
operations.

$$T=\left[\begin{array}{cccc}
1 & 0 & 0 & t_{x}\\
0 & 1 & 0 & t_{y}\\
0 & 0 & 1 & t_{z}\\
0 & 0 & 0 & 1
\end{array}\right]$$

$$T\underbar{x}=\left[\begin{array}{c}
x+t_{x}\\
y+t_{y}\\
z+t_{z}\\
1
\end{array}\right]$$

If we need to chain together a long sequence of rotations and
translation for exmaple, this seems like an elegant way to go about it.

We could extend our notion of the augmented vector slightly to the
homogneous vector. Instead of always having a 1 in the last row, we
allow it to be anything, but it really represents the same point

$$\left[\begin{array}{c}
x\\
y\\
z\\
w
\end{array}\right]=\left[\begin{array}{c}
\frac{x}{w}\\
\frac{y}{w}\\
\frac{z}{w}\\
1
\end{array}\right]=\left[\begin{array}{c}
x'\\
y'\\
z'\\
1
\end{array}\right]$$

Now our matrices are the same as before, exxcept the overall factor no
longer matters.

What about that last row of the matrix? It seems rather wasteful.

Duality
-------

Duality in linear algebra is the idea that linear scalar valued
functions on vector spaces are also vector vector spaces. In matrix
terminology, this means that a matrix with a signle row is a vector in
its own vector space (you can't add row vectors to columns vectors in
any sensible way, but you can add row vectors to row vectors).

Duality refers to various ways of identifying particular row vectors
with particular column vectors. The simplest duality is just hitting the
column vector with a transpose, an operation so trivial it barely feels
like one at all. The strange and wondrous thing is that while row
vectors look tirvially dsimilar on the page to columnv vectors, they
often have entirely different intepreations and this may buy you two
theorems for the price of one. In homogenous cooridnates, row vectors
represent hyperplanes, while column vectors represent points. Using the
transpose operator, we define a unique 1-1 correspondence between
hyperplanes and points.

### Hodge Duality

### Pole-Polar Duality

Estimating a Cow
----------------

Cross Ratio

Matrix Coordinates
------------------

Instead of packing our coordinates into vectors, we can pack them into
matrices. Matrices are not really that much different from vectors. You
can add them, multiply them, etc. In fact there is a conventional
correpsondence between matrices and vectors that can come quite in
handy, know as the vec operator. This operation is extremely common in
the Engineering and Statistics community, but less so in Physics.
Physicists also deal with rectangular matrices or non-hermitian much
less. What it does is it unfolds the matrix column by column into a
vector, which is most easily seen by inspecting the following example

$$\text{vec}\left[\begin{array}{ccc}
a & d & g\\
b & e & h\\
c & f & i
\end{array}\right]=\left[\begin{array}{c}
a\\
b\\
c\\
d\\
e\\
f\\
g\\
h\\
i
\end{array}\right]$$

The convention for the Kronecker product is given by the block matrix

$$C\otimes B=\left[\begin{array}{cc}
c_{11}B & c_{12}B\\
c_{21}B & c_{22}B
\end{array}\right]$$

Matrix multiplication on a matrix corresponds to matrix multplication on
its vectorized form.

$$\text{vec }BAC^{T}=C\otimes B\text{vec}A$$

Packing our coordinates into a matrix actually is more resitrtive than
packing the same elemetns in a vector, since the operators we use are
only those that are Kronecker factorizable.

$$x\sigma_{x}+y\sigma_{y}+z\sigma_{z}=\vec{\sigma}\cdot\vec{x}=\left[\begin{array}{cc}
z & x-iy\\
x+iy & -z
\end{array}\right]$$

$$\text{vec}\vec{\sigma}\cdot\vec{x}=\left[\begin{array}{c}
z\\
x+iy\\
x-iy\\
-z
\end{array}\right]$$

We can see that this is just a linear rearrangent of our oridnary
conception of a vector. We could think of this as a vector in a bizarro
basis.

$$\left[\begin{array}{c}
z\\
x+iy\\
x-iy\\
-z
\end{array}\right]=\left[\begin{array}{ccc}
0 & 0 & 1\\
1 & i & 0\\
1 & -i & 0\\
0 & 0 & -1
\end{array}\right]\left[\begin{array}{c}
x\\
y\\
z
\end{array}\right]$$

The matrix acting on this vector for rotation about the z axis would be
clearly be

$$\left[\begin{array}{cccc}
1 & 0 & 0 & 0\\
0 & e^{i\phi} & 0 & 0\\
0 & 0 & e^{-i\phi} & 0\\
0 & 0 & 0 & 1
\end{array}\right]$$

But this curiously factorizes as

$$\left[\begin{array}{cc}
e^{\frac{i\phi}{2}} & 0\\
0 & e^{\frac{-i\phi}{2}}
\end{array}\right]\otimes\left[\begin{array}{cc}
e^{\frac{-i\phi}{2}} & 0\\
0 & e^{\frac{i\phi}{2}}
\end{array}\right]$$

$$

By our vec correspondence, we can use this as a sandwhich of matrices on
our coordinate matrix.

Spinor Coordinates
------------------

### Stereographic Projection

$$\left[\begin{array}{c}
\cos(\frac{\theta}{2})e^{i\frac{\phi}{2}}\\
\sin(\frac{\theta}{2})e^{-i\frac{\phi}{2}}
\end{array}\right]$$

$\theta=0^{\circ}$

$$\left[\begin{array}{c}
1\\
0
\end{array}\right]$$

$\theta=180^{\circ}$

$$\left[\begin{array}{c}
0\\
1
\end{array}\right]$$

$\theta=90^{\circ}$, $\phi=0^{\circ}$

$$\frac{1}{\sqrt{2}}\left[\begin{array}{c}
1\\
1
\end{array}\right]$$

$\theta=90^{\circ}$, $\phi=90^{\circ}$ SOmethings off

$$\frac{1+i}{2}\left[\begin{array}{c}
1\\
-i
\end{array}\right]$$

$\theta=90^{\circ}$, $\phi=180^{\circ}$

$$\frac{1}{\sqrt{2}}\left[\begin{array}{c}
1\\
-1
\end{array}\right]$$

$\theta=90^{\circ}$, $\phi=270^{\circ}$

$$\frac{1+i}{2}\left[\begin{array}{c}
1\\
i
\end{array}\right]$$

### Points

Points in projective space are given by 1-d subspaces. This means any
multiple of the same vector gives the same point. For example

$$\left[\begin{array}{c}
1\\
3
\end{array}\right]$$

$$\left[\begin{array}{c}
2\\
6
\end{array}\right]$$

give the same point.

In the pinhole camera model this refers to the fact that a point of
light on the 2-d screen corrspeonds to a ray of possible points in 3-d
space

### Lines

There are two main ways to specify objects in space, implicit and
explicit (parametization). In the explicit version, which people are
typically more comfortable with, the coordinates of a point in the
n-dimensional object are given as a function of n parameters. You build
upward to higher dimensional objects by adding more parameters. For
example

$$x=\cos(t)$$

$$y=\sin(t)$$

gives the 1-d arc of a circle in 1 parameter, t. The system

$$x=u^{3}v^{2}$$

$$y=u^{7}$$

$$z=u+3v^{2}$$

Gives some cockamamie 2-d surface parametized by two parameters u,v. The
explicit method is often preferable if you want to easily produce points
rather than check if a point is in the set you're looking at.

The implicit method instead uses a system of constraints to specify an
object. It whittles down the space until you're left with what you want.
In an overall N dimensional space, k constraints gives you an object of
dimension N-k. Implicit methods make it very easy to check if a guess
point is within or near the set you're looking at. It is often
convectional to write the constraints As equations set to zero. The
system

$$\phi_{1}(x,y,z)=x^{2}+y^{2}+z^{2}-1=0$$

$$\phi_{2}(x,y,z)=z-\frac{1}{2}=0$$

Specifies the points where the plane $z=\frac{1}{2}$ cuts the unit
sphere in 3-d. This is a little 1-d loop,
since$3-2\text{ Constraints}=1$

One can specify a line in $R^{2}$ implicitly by the equation

$$\phi(x,y)=ax+by+c=0$$

Any point $(x,y)$ which satisifies this equation lies on the line.

One can also specify it explicitly by

$$x=x_{0}+mt$$

$$y=y_{0}+nt$$

or in vector form

$$\vec{x}=\vec{x}_{0}+\vec{m}t$$

$\vec{m}$is a vecotr which points in the same direction as the line, and
$\vec{x}_{0}$is a point lying on the line.

$$\vec{m}=(\vec{x}_{1}-\vec{x}_{0})$$

Going back to our standard connection between $RP^{2}$ and $R^{2}$

$$\left[\begin{array}{c}
\frac{x}{w}\\
\frac{y}{w}
\end{array}\right]\Longleftrightarrow\left[\begin{array}{c}
x\\
y\\
w
\end{array}\right]$$

We find that the implicit version reads

$$\phi(x,y,w)=ax+by+cw=0$$

Defining a new row vector $$l^{T}=\left[\begin{array}{ccc}
a & b & c\end{array}\right]$$

We can reqrite this condition as

$$l^{T}x=0$$

A point lies on the line if its inner product with the homogenous row
vector associated with the line is 0.

The explicit version also gets translated.

$$\left[\begin{array}{c}
x\\
y\\
w
\end{array}\right]=\mu\left[\begin{array}{c}
x_{0}\\
y_{0}\\
w_{0}
\end{array}\right]+\lambda\left[\begin{array}{c}
x_{1}\\
y_{1}\\
w_{1}
\end{array}\right]$$

Describing Subspaces
--------------------

One definition of an n-dimensional subspace is the set of all possible
linear combinations (also called the span) of a set of n linearly
independant basis vectors, so one possible way to specify a subspace is
to give a set of basis vectors. The thing is that this is an arbitrary
specificaiton of the subspace. We can choose a great deal of basis
vectors that span the same subspace.

### Determinants

See: Linear Algebra by Gil Strang, Advanced Math II: Geometry by Klein

Determinants test the independancy of a full set of N vectors. Pop the
vectors into the columns of a matrix, take the Determinant, and if it
gives 0, they are not independant.

They may also be conisdered as a test for the solvability of a system of
linear equations. Pop the coefficients into a matrix, place it inside a
determinant, and if it gives nonzero, the system has a unique solution.

There are 3 fundamental rules of Determinants

1.  The determinant of the identity matrix is 1. The columns of the
    indentiy matrix are clearly independant, so no problem there.

2.  The determinant is linear in each individual row or column at a
    time. It is NOT linear in all of the rows at once
    $$|\left[\begin{array}{c}
    -\alpha a-\\
    -b-\\
    -c-
    \end{array}\right]|=\alpha|\left[\begin{array}{c}
    -a-\\
    -b-\\
    -c-
    \end{array}\right]|$$ $$\left[\begin{array}{c}
    -u+v-\\
    -b-\\
    -c-
    \end{array}\right]|=|\left[\begin{array}{c}
    -u-\\
    -b-\\
    -c-
    \end{array}\right]|+|\left[\begin{array}{c}
    -v-\\
    -b-\\
    -c-
    \end{array}\right]|$$ $$|\left[\begin{array}{c}
    -a+a'-\\
    -b+b'-\\
    -c+c'-
    \end{array}\right]|\ne|\left[\begin{array}{c}
    -a-\\
    -b-\\
    -c-
    \end{array}\right]|+|\left[\begin{array}{c}
    -a'-\\
    -b'-\\
    -c'-
    \end{array}\right]|$$ This also makes sense as regards to its job as
    a test of linear independancy.

3.  Row swapping flips the sign of the determinant. This is the most
    unexpected of the rules. Certainly it is not inconsistent with our
    hope of using the determinant as a depdnancy test, but it is not
    clear that it is necessary

From these three rules, you can determine all the properties of the
determinant

Why are determinants volumes?

A parallelogram can be specified by giving the set of vectors of its
sides.

You can slide the sides of a parrellogram without changing its volume.
The operation of sliding is adding a multiple of one side to another
side. The Geometric version of QR decomposition AKA the Gram-Schmidt
process is sliding the sides under you have right-anglicized the
paraellogram. The volume of a rectangular box is the product of its
sides by definition.

### Minors

What about lower dimensional parralegrams embedded in higher dimesional
spaces? How do we find the area of a parallogram in 3-d space? We have
only two side vectors, each of which has 3 components, so we cannot pack
that into a square matrix, we can only pack it into a skinny $n/N$
matrix.

$$A=\left[\begin{array}{cc}
| & |\\
a & b\\
| & |
\end{array}\right]$$

One suspects that a determinant like operation must be necessary.

The solution is

$$\det A^{T}A$$

The Grammian Matrix is the matrix of all the possible inner products

$$\left[\begin{array}{cc}
a^{T}a & a^{T}b\\
b^{T}a & b^{T}b
\end{array}\right]$$

This matrix is a natural matrix to look at during the Gram-Schmidt
process.

If the parallelogram is degenrate, then its sides are not linearly
independant.

The minors of a matrix are subdeterminants. You find a little square
subsets of a larger matrix and take the determinant.

Cauchy-Binet

Barycentric Coordinates
-----------------------

One of the original motivations for homogenous coordinates was the idea
of a barycenter. This is the center of gravity of a figure. We pick some
reference triangle. To match it up to our Cartesian ideas, a good
reference triangle is one with vertices at

$$\left[\begin{array}{c}
1\\
0
\end{array}\right],\left[\begin{array}{c}
0\\
1
\end{array}\right],\left[\begin{array}{c}
0\\
0
\end{array}\right]$$

If we pretend we place a bunch of weight on each of thes vertices, we
can find the location on the plane where we could balance the plane on
our finger. The total amount of weight is irrelevant. What does matter
is the relative amount of weight.

$$\left[\begin{array}{c}
x\\
y
\end{array}\right]=\frac{1}{m_{1}+m_{2}+m_{3}}(m_{1}\left[\begin{array}{c}
1\\
0
\end{array}\right]+m_{2}\left[\begin{array}{c}
0\\
1
\end{array}\right]+m_{3}\left[\begin{array}{c}
0\\
0
\end{array}\right])$$

We will allow the weights to go negative, because otherwise our balance
point would never get outside the triangle and we want to describe the
whole plane. This actually is physically possible, for example if we
tied balloons to the vertices instead of hanging weights on them.

We could also consider these to be spring coordinates. If we imagine a
bunch of springs with dialable spring constants connected to the
vertices of the triangle., The position of equilbirum will also be at
the barycenter

We can make a vector out of these weights, and pack the corresponding
vertices into a matrix

$$\left[\begin{array}{c}
x\\
y
\end{array}\right]=\frac{1}{m_{1}+m_{2}+m_{3}}\left[\begin{array}{ccc}
1 & 0 & 0\\
0 & 1 & 0
\end{array}\right]\left[\begin{array}{c}
m_{1}\\
m_{2}\\
m_{3}
\end{array}\right]$$

$$\left[\begin{array}{c}
x'\\
y'\\
m_{1}+m_{2}+m_{3}
\end{array}\right]=\left[\begin{array}{ccc}
1 & 0 & 0\\
0 & 1 & 0\\
1 & 1 & 1
\end{array}\right]\left[\begin{array}{c}
m_{1}\\
m_{2}\\
m_{3}
\end{array}\right]$$

This makes it clear why subspaces are lines

### Dual Barycenter Coordinates

Instead of weighting the vertices, instead we could weight the edges of
the triangle.

### Mandelstahm Variables

Continued Fractions
-------------------

Using $RP^{1}$ you have an extension of what operations can be
represented as linear or matrix-like. As before multiplication is a
matrix

$$a\times\Longleftrightarrow\left[\begin{array}{cc}
a & 0\\
0 & 1
\end{array}\right]$$

But now addition is also a matrix

$$a+\Longleftrightarrow\left[\begin{array}{cc}
1 & a\\
0 & 1
\end{array}\right]$$

And most interestingly inversion is also now a matrix.

$$\frac{1}{-}\Longleftrightarrow\left[\begin{array}{cc}
0 & 1\\
1 & 0
\end{array}\right]$$

So now any operation that can be split up into a sequence of these basic
operations can be written as a matrix. This gives an interesting
approach to conitnued fractions for example

$$\frac{1}{2+\frac{1}{2+\frac{1}{2+\ldots}}}$$

What does this ultimately become? The answer is that it converges to the
eigenvector of the corresponding matrix

$$2+\Longleftrightarrow\left[\begin{array}{cc}
1 & 2\\
0 & 1
\end{array}\right]$$

$$\frac{1}{2+}\Longleftrightarrow\left[\begin{array}{cc}
0 & 1\\
1 & 0
\end{array}\right]\left[\begin{array}{cc}
1 & 2\\
0 & 1
\end{array}\right]=\left[\begin{array}{cc}
0 & 1\\
1 & 2
\end{array}\right]$$

$$\frac{1}{2+\frac{1}{2+\frac{1}{2+\ldots}}}=\left[\begin{array}{cc}
0 & 1\\
1 & 2
\end{array}\right]\left[\begin{array}{cc}
0 & 1\\
1 & 2
\end{array}\right]\left[\begin{array}{cc}
0 & 1\\
1 & 2
\end{array}\right]\ldots=\left[\begin{array}{cc}
0 & 1\\
1 & 2
\end{array}\right]^{N}$$

The eigenvectors and eigenvalues of this matrix are
$$\lambda_{1}=1+\sqrt{2},\left[\begin{array}{c}
\sqrt{2}-1\\
1
\end{array}\right]$$

$$\lambda_{2}=1-\sqrt{2},\left[\begin{array}{c}
-\sqrt{2}-1\\
1
\end{array}\right]$$

Method of Images Spherical Inversion

### The Line at Infinity

One of the most beautiful and important differences between ordinary
real space and projective space is the existance of a hyperplane at
inifnity. In 2-d this is a line at inifnity, in 3-d this is a plane at
inifity. Let's look at the typical correspondence between the real line
$R^{1}$ and the porjective real line $RP^{1}$

$$x'=\frac{x}{w}\Longleftrightarrow\left[\begin{array}{c}
x\\
w
\end{array}\right]$$

Now if we want $x'\rightarrow\infty$ we can very easily achieve this
without difficulty by letting $w\rightarrow0^{+}$. But the limitting
projective point

$$\left[\begin{array}{c}
a\\
0
\end{array}\right]$$

Does not appear intrisinsically nasty at all. It basically seems not all
that different from any other point. We can think of this projective
point as corresponding to $x'=\infty$ in some sense, although the
typcial correspondence requires us to use an ill defined divide by zero.
But what if we wanted $x'\rightarrow-\infty$? Then we would let
$w\rightarrow0^{-}$. Interestingly again the pont

$$\left[\begin{array}{c}
a\\
0
\end{array}\right]$$

shows up. So it seems that somehow, we have added a point at inifty, but
we've added the same point and negative ininty. This is an idea that
finds uses in many places. It feels like the graph of $\frac{1}{x}$. It
shoots up to inifnty on one side of zero and then comes up from negative
inifnty on the other side. If we want to enforce this as a coniitnuos
function without breaks, we have to say that the two inifities are
actually one. The real projectively line is topologically equvlaent to a
circle. This is an important fact since it means we can produce a nice
continuous mapping between the circle and the porjective line.

In 2-d, we have a whole line of points at inifnity.

$$\left[\begin{array}{c}
x\\
y\\
0
\end{array}\right]$$

Each point in a sense represents an unoriented direction since
projective points do not care about overall constants

$$\left[\begin{array}{c}
x\\
y\\
0
\end{array}\right]=\left[\begin{array}{c}
-x\\
-y\\
0
\end{array}\right]$$

### Conics

### Homographies

Euclidean transfromations preserve distances and angles. They consist of
rotations and translations. In some contexts they also include scaling
transforomations which just blow up or shrink everything by the same
factor.

When we take a photograph from different angles though, the distances
and angles are most defnitely not preserved. Closeup things appear
larger, and angles viewed may appear sharper.

The transofrmation that will take different persepctives into each other
are called homographies.

Homographies are the most general transfromations that maintains
collinearity of points. If three points lie on a line before the
homography, they will still lie on some other line after the homography.
Thus homographies not only can be seen as 1-1 point trnasfomrtaiotn, but
also could be called 1-1 line tranafromations, which is fitting with the
idea of projective duality.

Homographies may be very simply described in practice as linear
transformations (matrices) that act on the porjective vectors that
represent points. This actually includes all homographies.

$$x'=Hx$$

Homographies are completely determined oncey ou know their action on ?
points.

Inversions

Dualistic transfromations

Dualistic transfomrations add in a trnspose to the mix.

### Conics

Conics are described by matrices. Algebriacllay a conic in euclidean
space is given by the points that satisfy a qudratic equation

$$x^{T}Ax+2b^{T}x+c=0$$

But if we use augmented vectors, we can write this whole thing as a big
matrix equaltion

$$\left[\begin{array}{cc}
x^{T} & 1\end{array}\right]\left[\begin{array}{cc}
A & b\\
b^{T} & c
\end{array}\right]\left[\begin{array}{c}
x\\
1
\end{array}\right]=0$$

But we know that augmented vectors are just a short conecptual skip and
jump away from projective geometry. So in porjective geometry the points
on a conic satisfy

$$p^{T}Cp=0$$

Because the points at infnity are the same as other points from the
projective persective, types of conics that seem radically different can
be transfromaed into each other, for example hyperbola and circles.

Note that our defintion of the conic is homogenous. If we multiply the
point vector by an arbitrary consatnt, the above equation will remain
true. It is vital that any constrcution in porjective vectors remains
true under scaling the vector by a scalar for consistancy. If a
constucting doesn't do this, you're not doing projective geometry,
you're either wrong, or using some hybrid beast, in which case you must
remain more vigilant than relying on formalism.

### Envelopes

Curves can be described into two dual ways. They can be a collection of
points, which is very familiar. Very importantly they can also be
descirbed as the enevlope of a family of lines. A family of lines is a
set of lines with an ordering. In order to construct the envelope, what
you do is connect the dots. Draw the first line in the family, then draw
the second. Their intersection point is the start of your enevlope
curve. Draw the third line and connect the intersection of the 1st and
2nd to the interestion of the 2nd and 3rd. Keep going, connecting
interesction point 23 to 34 tto 45 to 56, etc. The resulting curve is
called the enevlope of that family of lines.

Mathemtically you find the intersection points using the cross product

$$p_{12}=l_{1}\times l_{2}$$

Then you connect all these points in order to get the envelope curve.

You can take the enevlope not only of a family of lines, but a family of
arbitray curves. The process is the same. Find the interesction of
neighboring curves in the family and connect the dots. The algebra of
this enveloping might be more difficult, but the drawing process is very
similar.

A conic has been described as a set of points, but we can also describe
it and the envelope of all its tangent lines. Given two points on the
conic, the secant line connecting them is

$$l^{T}=(p_{a}\times p_{b})^{T}$$

### Pole Polar

Given the ball of ice cream that is a conic and a point, you can find
the cone that has its tip at the point and that the ice cream sits
comforatbly on. At the point of cotact between the ice cream and the
cone, the cone is tangent to the surface of the ice cream. The
interesection of the ice cream conic and the cone will lie in a plane.
This plane is called the polar plane of the tiup of the cone, which is
called the pole. In this way, the conic creates a 1-1 correspondnec
between points and planes. Algebriacally, how this is done is
surprisingly simple. The polar is found by applying the conic matrix to
the point and then taking the transpose.

$$l^{T}=(Cp)^{T}$$

If the point lies on the ocnic itself then

$$p^{T}Cp=0$$

But then the polar to this point ought to also touch the conic and touch
the point itself. This is consistant with our feintion

$$$$

The ordinary dual where we just take the tranpose could be considered
the pole polar relationship using the conic described by the identity
matrix.

Straihgt-Line constructions

### The Case For Projective Geometry

The ideas of porjective geometry, and expecially homgenous coordinates
reduce a number problems in geometry to linear algebra, which we know
like that back of papa's hand.

1.  Changes of Camera Perspective become Matrix tranafromations

2.  Finding where geometric objects intersect is a linear system of
    equations

3.  The point at Inifnity

4.  Optical Systems like lenses act in ways that are most intrinsically

Porjective Geometry can be embedded in euclidean geometry (like the
camera model) and euclidean geometry can be embedded in projective
geometry (by desginating special lines and conics as special from all
the rest), so the two are equivalent in what they can describe, but the
language differences between the two can make different ideas obvious if
you use the right one or totally incomprehensible if you use the wrong
one.

### Algerbaicization of Geometry
