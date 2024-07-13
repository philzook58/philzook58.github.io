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

The SVD of $P_{A}P_{B}$ (Which is not commutative, PS) is related to the
CS decomposition, which tries to give an ordered set of angle between
subspaces. The CS is described in terms of orthogonal materices Q, but
$P=Q^{T}Q$. Combining the projectors is like taking all the dot products
between the orthonormal sets of the subspaces. Since the SVD
eigendecomposed the square of the matrix it ends up like
$P_{B}P_{A}P_{B}$. I think you'll get the $\cos^{2}$of the principal
angles between the subspaces as the singular values.

$$||P_{A}-P_{B}||=\sigma_{max}(P_{A}+P_{B}-P_{A}P_{B}-P_{B}P_{A})$$

Orthogonal projector means $P=P^{T}$. It takes the vector right down to
the subspace as quickly as possible, meaning the difference of $|x-Px|$
is minimized. This is a metric based concept. Other projectors might not
do this instead taking it on a slanty path

Porjections square to give themselves. Clifford objects square to one.
Interesting.

Householder Transformations and Versors?

Differential Geometry
=====================

First fundamental form is metric matrix. Can be found from an embedding
by squaring the jacobian matrix of the parametization
$\frac{\partial(x,y,z)}{\partial(u,v)}$ so that we have a 2x2 matrix
dealing on with the parametric space coordinates

Then the hessian gives the second derivatives. If you remove the span of
the jacobian from the hessian (perform the complement of the projection
onto the tangent space. This projection operator comes about from the
pseudo inverse of the jacobian construction.)

Second fundamental form gives normal component of acceleration when
dotted with the derivatives

The frenet frame. The idea is that $\kappa$ and $\tau$ are sufficient to
describe a curve in eulcidean space. Related the orthognal
transformation group. In matrix form the kappa and tau are written in
the antisymmetric form reminscent of a generator of rotations. But how
about in porjective geometry? What functions are enough to determine a
cruve in projective space up to a homography? What's the analog of
curvature?

Contact Geometry
================

A generalization of duality transformations. Duality takes points to
lines. Contact takes points to curves.

The generating function creates a N-1 surface in transformed space
corresponding to every point in original space. To a curve, there
corredponds a devleopable surface in the trans space? No. Seems like
it'll be a surface of same Dimensional in space 2.

To every point in space 1 wavefront corresponds a spherical propagating
wavesurface in space 2 due to Huygens.

What about the full clifford algebra vector space? Hodge duality flips
shit around, what about a more general setup? A linear tranformation on
clifford space. We can associate any geometric object with any other and
then locally it will look like a linear clifford transformation? Or pack
a class of curve parameters into a vector

lines to lines is very restrictive

A smooth transformation from the set of cruves to the set of curves. The
smoothness requires the contact condition. The point is considered a
degenerate cruve a la sphere geometry. There is a dual transformation of
surfaces to surfaces implied. This is the ray wavefront duality.

reducing contact trandfromations: Porjective gometry is natrual offshoot
of idea of going from 3d world to 2d plane. Contact geometry in 100d
reducing to contact geometry in 3d is also a kind of contact
transfromation if spacial elemtns remain in contact. Maybe In waves, to
get wavelike features from geometrical wavefronts in that we see the
porjection of a huge dimensional space (one for each daughter wave being
produced all the time )onto a much smaller one. Linear wave dynamics are
the linearized rpojective coordinates of the behavior.

Contact trnafromation os a transfromation of the pair of a line and a
point. They are transformed into a new point and line. For exmaple
Huygens wavefront constuction. A point on the dge of the wave and the
tengent line to the wave are transfromed to a point on the porgpagetd
wave and tangent on the propagated wave.

Contact transfromation are defined by generating functions. $\Omega$. If
omega is considered only to quadratic order, it is a projective
transformation. Not quite right. The generating function for projective
has no squares only non selfmultiplying quadratics. The Lie sphere
transfromations might be what it is to qudratic order. Then points map
to conics. Quadratic transformations include SHO and free particle.
Linear order generating fuctions are degenerate.

In optics, Why are imaging transformations approximately porjective? Why
is the rotatioanl symmettry important?

The Lie sphere transformations in which points and lines are unifed as
circles of degerenate radii are contact transformations. a point on a
circle and tangent to that circle better damn well transform to new
point on circle and tangent line to cricle. What is tangent line to
point circle? It is the "line at infinity"? there is a single point at
inifnity.

Projective Geometry
===================

Straightedge constructions only. No compass. Angles are defined via the
arc length of a unit circle between them, so they are out. Distance is
defined via circles as well. Put two segments together and compare
circles.

Perhaps this was more obvious to the greeks, who would be more
contentios about what acceptable tools could be used for geometry

The order of 3 points on a line is not defined wuite the same. It is not
clear that one point lies within two other points. However 4 points do
have an invariant property. Paired up, They can be interwoven or
seperate clumps. This is exhibitted in the sign of the cross-ratio
(Klein)

Like real number based fractions. From the porjective geometry
perspective, one can do geometry on the fractions. The fractions are the
porjective integers in a sense. Linear subspaces of a discrete 2d plane.
Fracitons are sort of eculidean, a lattice is kind of affine (homogenous
3 integers), and then prijective takes you somewhere else. interesting
possibilites. Harmonically related crystal momentum etc.

Camera model

Line plus plane at infty

subspaces of $R^{N+1}$minus origin

sphere with antipodes identified

Optics - Instead of projecting off of a line through a point back onto a
line, we project onto the focal center curve. The evolute of the curve?
How does the index of refraction play into this? Object plane is
projected through focus.

Barycentric matrix switches from 1/z representation to 1/a+b+c rep.

$$\begin{array}{ccc}
1 & 0 & 0\\
0 & 1 & 0\\
1 & 1 & 1
\end{array}$$

Geoemtric optics: the object point is a pencil of lines, the principal
plane and optical axis are a range of points. Interestingly, when you
approach the focus from one side, image goes off to infity, then comes
back from other side of infinity inverted! This is that double cover
business rearing its head (half angle spinor shit).

what kind of differential equations can be constructed in projective
space? How can I take the limit if things have no length?

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

Laplace operator porbanly necessary for scattering equation in
porjective coordinates. Suggested starting point is mean value theorem.
Instead of integrating on sphere, take a sum of polar points or
integrals on lines or something projective. In wave equation, there is
the identity that the sum on a charecteristic recatngle has to do
certain thngs. Suggestion: Barycentric Sums. In Needham Visual Complex
he mentions this as a starting point. For regular polygons in complex
plane it works.

spherical laplacian in CP2 coordinates?

Cone geometry. Able to construct only cones. Interesection of cones is
also cone? (maybe a hyperbola?). steep cone inside wide cone gives
circles, ellipses?

Scale space is related to projective space or at least homogenous
coordinates.

How do you define a probability distribution on the projective plane?
Can't? Can only define joint distribution for 4 points? cross ratio. For
exmaple, point in 3d projected unto random or uncertain camera plane.
Seems fine, but using implicitly euclidean concepts (in the 3d space) I
think. Then use bayes rule to reverse engineer the point in question.

The rutherford scattering result may be encoded in a stereographic
projection constrcution. The plane is the incoming beaming location, and
the sphere is the outgoing direction. Then porjective mapping between
the two, with energy and charge moving the plane in and out. Is there a
dynamical reason this is true? What aobut the hard sphere?

Mandelstahm variables are clearly some kind of barycentric coordiate
idea. Also the might be diagonal points of quadrangle produced by the
four particles? Crossing symmetty as a porjective symmettry? This might
be a really interesting (and lucrative) line of questioning.

Barycentric coordinates using distrubition functions.
$x=\frac{\int\rho xdx}{\int\rho}$. Taking triangle to qudariletral to
extreme. Highly Degenrate desciption of points.

Can parametize curves in projective space using a homogenous
parametization, so that if scale paramerter vector, we scale output
vector.

Experimental Geometry
=====================

One wonders. The idea of particle detectors is to map large scale
detectors to small scale phenomenon. Should renormalization be a
geometry split at the level of non-euclidean? MOdify the idea of similar
triangles. Does similarity fail when the triangles are vastly different
in scale like angle sums might fail for vast distances? Actually,
hyperbolic similar triangles (which typically aren't a thing) might be
an interesting model of renormalization. Weaken or modify an axiom.
Renormalization "Group" and Erlangen program. Fractal Geometry? Is there
a fractal geometry text from a euclid-esque percetive? Not that I see.

Diffferential geometry finds models in embeedded smooth surfaces. What
is the intrinsic geometry of fractal embeded surfaces? homogenous
coordinates? 3 points with 10 coorndates kind of thing. In a ratio that
becomes fractal dimension. 2 points on a line with 3 coordinates. Can't
use length. Length is inifnite everywhere. Embedded we can use .
Curvature is clearly not the issue at hand. Can projective geometry shed
any light? I think before we impose metric, fractal objects are still
projective. Two points can easily be inifty apart but not lie on the
plane at inifnity. That's new. No. That's not it. We can't use regular
euclidean distance. Then all points are infinity apart. We have a
scaling notion of distance. Its like a geometry that can be constructed
with: finite straight edge: Minimum length straight edge (points that
are too close can't be connected by a line because of ham hands).
Immovable compass (i don't think so I think this is equivlanet to
eculidean geometry): . The min max straightedges or straightedge range
is an interesting restriction that is veyr physical. We can't use points
that are too close in actual geometric drawing, nor too far. These are
physical realities of the constructions. and presumably do hamper the
possible constructions. The ocmbinatorics of a piece of paper filled
with dots is the number of possible constructions. Statistical analysis
of geometric drawing. There are intrinsic errors due to pencil width.
Geometry as an experimental science. You try things, and then pick out
what you want as axioms. Error propgation in geometry. Numerical
stability of geometry as calculation method. One could geometrically
compute the decimal expansion of sqrt 2 presuably. Line through two very
close tgether points is unstable. line through very far apart points .
Discrete geometry the plane as a finite grid. fractalness and
renormalization and such comes with changing grid size. The prbing
wavelength gives rough estimate. We can transfer constructions.

Reject: A unique line connects two points. Only true within experimental
accuracy.

Definitions : A point is a dot produced by your pencil on the paper

A line is the mark your pencil makes along your straightedge. It is
composed of many points.

You may produce a circle with any two points as a radius

A shcmoint is a set of points. Should a line be capable of being a
schmoint or should we add to definition to disallow? A schmoint should
be fundamentally pointesque. ROtational invariance might be a good
restirction.

A schmine between two schmoints is the set of all lines connecting the
all points in the schmoints.

We masy also choose to define a schmne as the set of all points in the
lines connecting the points. Then a schmine is in fact a schmoint unless
we require a schmoiint to be finite or some other restiction.

A schmoint lies on a schmine if (two possible defs) the schmoint possess
a point lying on a line for every line in the schmine or the schmoint
contains only points lying on the schmine lines. First the schmoint
severs the schmine. Also possible is schmoint to have one and only one
point for every line in schmine. A schmine may touch a schmoint if all
lines have points on them but there may be points with no lines. The
discitintion is whether the connection mapping between the schmoint and
schmine is onto, injective, bijection. a point line pair is in the
relation if the point lies on the line. If bijective, onto or injective
are different possiblities. Touches means relation is nonempty, schmoint
lies on schmine is every point has line, schmoint cuts schmine if every
line has point and schmine and schmine meet if 1-1.

Triangles as schmoints. Connect them with all possible lines. Then
points are triangles. In terms of discrte exterior algebra its like
vector we thought were points are actually living in the 3-blade of an
undelrying space.

Schmoints may contain other schmoints. We may intersect, union,
complement schmoints

But consider if the points making up the schmoints are not points, but
in fact schmoints themselves. Triagnlular schmoints then become
sierpinski gasket esque things. We get a beatiful recursive structure.

Other possiblity: shcmoint is all sets within a certain radius. Nice
because then schmoints are rotationally symmettric.

Line is convex hull of two scmhoints. Or line is affine completion of

Analytic and algberaic teeth needed. homogenous coordinates where 4th
coordinate is radius of schmoint. L

The big question is how we amplify fine things into coarser things.

The key interesting thing is that as schmoints get close together, their
schmines become extremely broad. This is an intrinsic problem with any
geoemtric diagram using finite crayons.

A contact schmoint/schmine pair for thick contact transfromations

May want to conisder a combination schomplex which is a set of points
and lines.

schmangle depends on how far away the arc of the circle is? Inner and
out angle?

The geometry of light with finite wavelength might be somewhat described
by this system. Then schmoint size is apoximately a wavelength.
Helmholtz equation with fixed k. The reality is fuzzier than what I'm
describing, so maybe I should go more for statisitcla geometry where
points are radnom variables. Or where the straigthedge is a stochastic
straightedge. But what are the elegant random varibales to use? Gaussian
doesn't seem to work great. Dual of gaussian point is guassian pencil?
This would actually be pretty good for points on a line:
$x_{1}+\lambda(x_{1}-x_{2})$. The variance gets big far away from them.
Or could use wdge product and get a gmma/chisquared distribution. Line
is drift random walk brownian motion? Line connecting points is
ocnditional on those points. Construct line by closely sepearted
gaussian points. Points get correlated by constructions. COuld attempt
to piggy back on quantum mechanics, but this feels like cheating

Geometry by sampling/inference. We can determine properties: curvature
metric etc by experiment. We can consider that perhaps either the data
is noisy or we can consider the possiblity that our conceptual model is
not rich enough to deal with anything that comes our way (For example
fractal shit). We could apply a euclidean model to a fractal object, if
we only sample points from it. As we sample more points, our model can
be richer. What distribution is the right one to sample from?
Symmettries might pare it down, or we could work with inequalities that
work for any distirbution A la VC theory. We could try to polynomial or
foureir fit the curve either with sampled points or sampled definite
integrals of charecteristic size. What does the regularization do?

Or could parametize curve with fourier series expanded functions or
wavelet. Can put a cutoff scale in there. low pass, or maybe band pass
to isolate at each scale. Use this to define cyrvature at a scale.
(curvature will be dominated by higherst term in series we allow). Feet
on the carpet or ant on the carpet. Totally differenty geodesics,
totally deifferent experience.

In this case, the non point wise convergence of fourier series is a
boon. I can make fractally things that converge in L2 but not pointwise,
and then start "illegally" bringing derivatives under integral signs for
evaluating metrics and curvature.

Curvature/diff geo of a thermal string. Every mode has energy means
every mode is curvy. But at coarse level still basically smooth.
Brownian motion curvature. All cutoff depdnant. Renormalization of
curvature? Yes. Definetly necessary if curvautre is to have any meaning
whatsoever. What does similarity mean? distance, angle? all become
cutoff dependant. and renormalizable.

The fuzziness in fractal dimension and fractal definitiosn corresponds
to fuzziness in other things.

Sensible to describe particle coordinates in terms of light coordinates.
Crispify Hesienberg microscope?

Conformal quantization- big quantizes if small quantizes

Spinors
=======

Projective geometry adds a lot of clarity to where the theory of spin
comes from. Can I use this clarity to get clbesch gordon coefficients?

Multipole diagrams are projective-esque. Barycentric calculus. The exact
charge and position are immaterial. Ratios are.

Conjectures: The homogeniety of dimensional anaylsis is quite similar to
projectivity. Does this perhaps suggest the important things are not
dimensionless quantities, but ratios of dimnensionless quantities? In
some manner, physics has to "project" any observation onto our reference
meter sticks. changing units of measurement is sort of an affine thing
so ratios are good, but cross-ratios might be more fundamental. what
about the scaling at critical points? Could this be interpetated
projectively? This is very very rough.

IS quantum mechanics some kind of porjective like linearization of
contact transformations (classical mechanics)? It is very roughly like
this. The generating function of porjective trasnformation is a
quadratic I think. The connection between QM and CM is much stronger in
this case. Only ratios matter. Is measurment perhaps the reduction
(projection interestinlgy) down onto a particular image plane, taking
those ratios with Z? What is hbar then? Can I geometrically construct
the wavefunction similarly to how I can for spinors?

Conformal Geometry
==================

shutter model

riemann sphere and spin

I've seen similar ideas all over the place, but they are not crisp yet.
We add a point at infty and points are considered degenrate spheres. We
start from a higher dimensional cone from which we can work in any
geometry we please, hyperbolic, elliptic. They are the same.

Stereogrpahic projection is a mapping from $RP^{n}$ to $S^{n}$ . It is a
coordinate system for studying sphere surfaces using porjective
coordinates.

But there is an lternative mapping $RP^{n}$ to $RCo^{n-1}$(real
conformal space)(which means there are n+2 homogenous coordinates for
each point in $RCo^{n}$) Which is ultimately a way of studying the plane
using 3 diensional projective space. We specify an inifnity point and a
origina point to specify the stereographic projection. Points outside
our stereographic conic can be dualized to slice it. That is why points
are on the same level as circles and lines. Linear or spehreical cuts of
spheres give you sphery things. In the reverse direction, this is a
projective homog noeus parametization of the sphere in the higher
diemnsions.

There is no reason stereogrpahic projection had to use two poles and a
diameter perpedicular between them. The diameter could have been another
conic maybe, since lines are inifite radius conics. Or that it had to
use a circle instead of an ellipse

But closure of studying $RCo^{n+1}$to $RCo^{n}$might really solidfy
shit, in the same way that porjective geometry is $R^{3}$ to $RP^{2}$,
but it gets more elegant if you describe the higher 3 space projectively
as well $RP^{3}$ to $RP^{2}$.

In this closed stereography, we could take our null conic to a line
using a conofrmal transformation. Then we can interpret the geometry
using our huygens wavelet construction. The dual lines of the points
become the circular wavelet that just kisses our studying plane.

Points inside the sphere the polar lines slice up the sphere, so they
represent dual circles or lines.

Higher dimensional spaces can be used to study lower ones, just not in a
metrical fashion.

Rutherford scattering might be equivlanet to viewing orbits of other
planets from planet earth. porjection onto celestial spehre.

$o(x^{2}+y^{2})+e_{1}x+e_{2}y+\infty$=0. Dual coordinates of sphere
equation.

Dual cone cooradinates Can place cone anywhere, test if points are on
cone

Use as model of how relativsitc images look somehow.

$o(t^{2}-y^{2})+e_{1}t+e_{2}y+\infty$=0

subspaces of coordinates represent all points that match linear combos
of the variables. Reprsents collision? 2-2 collision is matrix?

Collisions are linear fractional even in nonrelativsitc due to center of
mass tranasfromation? Barycentric coordinates indeed.

$$\begin{array}{ccccc}
1 & v_{x} & v_{y} & v_{z} & v^{2}\end{array}$$

If doesn't match cones condition, becomes hyperbola. in pE space, could
be used to specify particles mass hyperbola. Road to projective
mandelstahm.

Lorentz Boost will be subset of possible transfomrations. Time Inversion
takes upper cone to lower cone?

Use in descipriton of method of images for sphere. Confromal Field
theory.

o is base point on sphere, $\infty$ is projection point, and e1 e2 are
points at infinity (directions). That's how you can visualize the 2d
case in terms of a 3d sphere.

HOw can we use canonical generating function? Seems very close to
contact transfromations. N+2 coordinates. Contact has 2N (x,p)?
