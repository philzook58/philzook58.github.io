Projective Tranasformations, homogenous representations - fractions
using reals instead of integers, also a good way to think about
perspective. Riemann Sphere. Continued fraction usings matrices

Nonlinear porjections - local projective coordinates? Envelopes of
families of projective coordinates (Applications to image stitching).

DImensional analsysi and projective trransformations

Theormsynamics and porjective transformations (Scaling)

Projection and Special relativity.

Projection and scattering - interesting new perspective. Scattering is
more or less map from plane to sphere.

Cross ratio?

Homogenous derivative? $(\nabla,1)?$

Geometric Duality - perspective, Legendre, M-C. Hodge dual, dual
optimization. 1-forms, exterior algebra

Pinhole First

Imaging, diffraction limitting,pinhole size (Better criteria for
resolution. Something more vc dimensional. We would discern 3 or 4
points for any perfect finite sized pinhole system, but above that the
other points may be completely masked. vc dimension of optical model is
like 3 or 4. Sample inside circle of possible projection. Assume object
point has some distribution of rays, Then that would lead to a
distribution on image plane) Integration over focus point?

Thin lens. Isn't there some more elegant way to think about this? using
porjective coordinates maybe? Thick lens matrix equations? Depth of
field, aperture size

$$ff'=zz'$$

Newton's Equations

$$\frac{y'}{y}=\frac{f}{z}=\frac{z'}{f'}$$

$$\left[\begin{array}{c}
y'\\
z'\\
w'
\end{array}\right]=\left[\begin{array}{ccc}
f & 0 & 0\\
0 & 0 & ff'\\
0 & 1 & 0
\end{array}\right]\left[\begin{array}{c}
y\\
z\\
w
\end{array}\right]$$

Conjugate points

Abberrations

Hamiltonian optics

Wave Theory?

Holography beats diffraction limitting.

Rock skimming on pond like critical angle. Effective mass of rock in
pond is greater since dresses itself with water, Stokes law. Energy
conserved, momentum isn't, Could use with least action to determine
critical angle for skimming of round rock. Also would predict a Snell's
law equivlanet if the rock does enter the water.

The eikonal is like the road that energy travels on. You find it, then
use it as a directional/material derivative for the conservation law of
energy.

The Wigner Function probes in front and behind a point to find
autocorrelations. It's the natural 3d extension of the autocorrelation
function. It disassocoates into plane waves. Similar to Hough Transform.
BUT from this context it seems that the ofurier transform isn't what we
want. We want sepeartion into rays, which means eikonals. kx is
$\tau(k,x)$ at that point. But in an inhomgenous medium (or curved
space) maybe what we want into the exponential is $\tau(k,x)$, the mixed
charecterstic of that point

$$\int\phi(x+.5x')\phi(x-.5x')e^{i\omega\tau(k,x)}$$

The wigner function might also be connected to the idea that to measure
momentum, one sensible approach is to take two position measurements.

Also, we could look to the past (for exmaple if we wanted to find
particles in a density function) Again, this is a hough transform on a
spactime picture.

Ambiguity function is the flipside to Wigner. This is all in FOurier
optics.

Kirckoff angle factor and pilot spinor?

How do you catpult from using n in optics to working with geodesics in
GR? Fermat's princiople and all that. I suspect n is similar to the
determinant of the metric.

Th Lie brackets and such of GR ought to correspond to poisson brackets
in optics?

Hough transform. overlay line lump with expoential. Then effectively its
a ray decomosition of the field. Combo Hough fourier. Or Instead of
lines use actual geometric rays. Unclear how wide to make line lump.
Could also use kirkhoof factor localized around point to seperate into
more point-like directed objects making spherical waves. Transform into
spinor form Use cross correlation matrix in extended least squares

Reslving power of diffraction gratings - information transfer via
freqeuncy modulation

Numerical aperture of fiber optics

Lens aperture as a low pass filter (fourier optics see hecht abbe
imaging)

What is light?
==============

Light as a bundle of rays. Light moves in straight lines. Note that rays
may intersect. The road function does not allow this. Standard ray
diagrams will also not show this.

Light as cone bundles. This perspective is useful as it draws focus to
neighborhoods of rays, not just one ray, which is vital for imaging.
Also draws attention to etendue as a qunitity of interest

Light as all possible cameras. The location of camera gives perspective.
Location on image plane gives angle information

Light as wavefronts. Going through relfecting or refracting surfaces
imposes properties of the surface upon the wavefront of light. This is
evident in the power formulation of lenses. The lens adjusts the local
curvature (and orientation) of the wavefront. Are there a set of
additive quantities that fully charecterize adjustments to the
wavefront? Time propagation is just a linear increase of curvature.
Equivalent of power in Higher order optics?

Extrapolating Light
-------------------

What light means is found by extrpolating it backwards from a point in
image space. Typically we assume straight line propagation, even though
this may not be physically true. Hence we get fish at the wrong depth.
The Center of curvature of nearby rays is the extrpolated location. It
is the location where nearby rays intersect when extrapolated backwards.
The Caustic is the envelope of the wavefront. It is the surface of all
extrpolated images. Where your image is on the caustic depends on your
location of sampling rays.

The Optical Axis
----------------

A wave surface can be represented as a graph

$$z=f(x,y)$$

We call z the optical axis.

In the surface

$$ds^{2}=dz^{2}+dy^{2}+dx^{2}=(1+(\partial_{y}z))^{2}dy^{2}+(1+(\partial_{x}z))^{2}dx^{2}$$

$$\partial_{x}z=-\cot\theta$$

Where $\theta$ is the angle between the surface normal and the x axis

$$\hat{n}\cdot\hat{x}=\cos\theta$$

The optical momentum is defined as

$$p=n\cos\theta=\hat{}$$

$$\cos\theta=\frac{\cot\theta}{\sqrt{1+\cot^{2}\theta}}=\frac{-\partial_{x}z}{\sqrt{1+(\partial_{x}z)^{2}}}\approx-\partial_{x}z$$

The optical axis acts like the time coordinate of a particle. Paraxial
corresponds to nonrelativistic motion. Index of refraction is like mass,
optical momentum along optical axis is like Energy

Ray coordinates act like marticle coordinates. $m\sim H$

$$m=\sqrt{n^{2}-p^{2}-q^{2}}$$

$$\frac{\partial x}{\partial z}=\frac{\partial m}{\partial p}=\frac{-p}{\sqrt{n^{2}-p^{2}-q^{2}}}\approx-\frac{p}{n}$$

$$a=(dx,0,dx\partial_{x}z)$$

$$b=(0,dy,dy\partial_{y}z)$$

$$\hat{n}\propto a\times b=dxdy(-\partial_{x}z,-\partial_{y}z,1)$$

$$\hat{n}=\frac{1}{\sqrt{(\partial_{x}z)^{2}+(\partial_{y}z)^{2}+1}}(-\partial_{x}z,-\partial_{y}z,1)$$

$$p=\frac{-\partial_{x}z}{\sqrt{(\partial_{x}z)^{2}+(\partial_{y}z)^{2}+1}}$$

$$q=\frac{-\partial_{y}z}{\sqrt{(\partial_{x}z)^{2}+(\partial_{y}z)^{2}+1}}$$

$$z=ax+by+z_{0}$$

$$z-ax-by=D\hat{n}\cdot r=z_{0}$$

$$\hat{n}=(-a,-b,1)$$

The graph method is decidedly ungeometrical. The z-axis has nothing
fundamnetally special about it

Prisms
------

Prisms turn beams of light. Angular deviation $\delta=(n-1)A$. Sum of
two interior angles is the exterior angle. This theorem is obvious if
you think about it, but you need it in your back pocket. Its
surprisingly uuniversal

Cardinal Points
---------------

Every wavefront has two focal lines (central axes of curvature). So too
do lenses. They possess primary focal lines and secondary focal lines,
which are related to the curvature of the surface weighted by index of
refraction.

Principal planes? Principal Surfaces? Isometric?

Nodal Points, Nodal axes? Conformal? b

Spherical Surfaces
------------------

Set r = infty to get the apparent depth formula for paraxial planar
surface.

Magnification
-------------

Linear Magnification is for screens. Angular Magnification is for sight.
Sometimes Linear magnficiation turns to crap

Fourier Optics
--------------

parallel rays give a phase factor on the object plane. Leads to shifted
delta function in focus plane (Like it should!)

Coherence and Fourier optics? How spatially or temporally coherent does
the light source have to be for the transfrom to show in the focal plane

Smooth variation between real space and fourier space between focal
point and image plane

Etendue
-------

If a light source is placed very far away, the light rays become more
directional. An infinitely far away source gives off parallel rays. At
the same time, the Intensity of the light gets spread over a larger
surface $\sim4\pi r^{2}$. It is a curious fact that you can take a combo
of these things in such a way that the spread of intensity is
compensated exactly by the focusing of directionality. This is known as
etendue.

Another way of speaking about it is in terms of a pinhole camera placed
at locations. If you place the pinhole camera way out, The spot created
by an extended source will decrease, but at the same time, the intesity
will decrease as well.

The same phenomenon happens in particle mechanics. Suppose we had a box
filled with hot particles, then we open the walls. The particles will
spread out, but the fast ones will spread out faster. Eventually, the
particles of different velocity seperate themselves out, the fast ones
being far away and the slow nearby. This concentration in velocity is
compensated exactly by the dispersion in position.

These both are rather noninteracting case. What becomes truly remarkable
is the conservation of these quantites in the face of interactions as
well.

Etendue is reated to the denisty of wave states, entropy

Diffraction occurs because etendue comes in chunks of a size proprtional
to wavelength

Etendue is a measure of bundles of rays

$$n^{2}\frac{dA_{1}dA_{2}\cos\theta_{1}\cos\theta_{2}}{r^{2}}$$

View Factor as Number of communication channels between sources.

$$n^{2}dA\cos(\theta_{1})d\Omega$$

Etendue can also be consdiered the measure of wavefront direction and
area. Because of the inherent chunkiness, curvature has uncertainty,
hence origin point has uncertainty.

Etendue is the phase volume of slowness (optical momentum) and position.

Optical axis is like time in mechanics.

Fiber optics/Waveguides as bound state?

Apertures and obstruction of etendue

Spatial Coherence of source = etendue of source - far away have small
angular diameter, so they are coherent.

Diffraction and Etendue - comes in chunks. Squeeze the area and you have
to unsqueeze directionality

Velocity Potential (Slowness Potential) or Road Function
--------------------------------------------------------

An approximation taken in fluid dynamics. Optics is all about the
slowness rather than the velocity. The two are related.
$\vec{p}=\frac{n^{2}}{c^{2}}\vec{v}$

Lagrange Invariant
------------------

The Road Function tells you that when you place a lump of energy in the
field, where it will flow. A lump of energy flows with a velocity given
by the gradient of the Road Function. Quite trivially, if you take a
closed line integral of the velocity from a given Road Function, you
will get zero.

$$\oint p\cdot dr=\oint\nabla S\cdot dr=0$$

Velocity or Slowness vector? Optical Momentum

$\nabla L=p$

p is indeed slowness $\frac{dt}{dx}$, $\nabla t$.

n is slowness index.

In the energy tranpsort we require two factors of n to convert to
velocity $v=\frac{1}{n^{2}}\nabla t$.

The state eikonal is slowness potential

$$\nabla L=p$$

With slowness parametized as function of time $p(t)$, $x(t)$.

$$p=\frac{1}{\frac{dx}{dt}}$$

$$n\frac{dp}{dt}=\nabla n$$

$$p=n\frac{dx}{ds}=n^{2}\frac{dx}{dt}$$

$$p^{2}=n^{2}(\frac{dx}{ds})^{2}=n^{2}$$

We could also parametize as function of arc length

$$\frac{d}{ds}=n\frac{d}{dt}$$

$$\nabla$$

$$p^{2}=n^{2}$$

From this you can get Snell's Law. But what else can you get?

Hamilton's Optics
=================

The Point Charactersitic
------------------------

We want to specify the wavefront resulting from a flash of light at
poisition $P_{0}$ at $t=0.$ We can write this wavesurface as a level
surface of a function called the point charectestic

$$V(P_{0};P)-ct=0$$

So we set $P_{0}=(x_{0},y_{0},z_{0})$, and then any set of cooridnates
$P=(x,y,z)$ which satisfy the above equation is in our wavefront at time
t.

The obvious one is the spherical wavefront for a homogenos medium

$$V=|P-P_{0}|$$

The wavefront is located at all points that are eqaual distance from the
flash point, ie a spherical wavefront centered at $P_{0}$with a radius
ct.

Okay, so how can we figure out what V is in more general media? The
spherical wavefronts get warped from mirrors or varying indexes of
refraction.

Well, we know the wavefront starts at the flash point, hence

$$V(P_{0};P_{0})=0$$

The direction normal to the wavefront flashed from $P_{0}$ and evaluated
at point P is

$$\hat{n}=\frac{\nabla V}{|\nabla V|}$$

We can turn the definition around though. Instead of using it to
implictly define a wavefront, we could ask Fremat style, how long does
the ray which connects $P_{0}$and $P$ take to traverse this distance?
The answer is again the function V, since

$$V(P_{0};P)=ct$$

Huygens Principle
-----------------

Every point on the wavefront can be considered as a new flash source.
The resulting new wavefront is the envelope of the wavefront of all
these flashes.

What is an envelope? First off, you need a family of curves or surfaces.
A family is a parametized set. The family in this instance is the set of
all wavefronts parametized by their flash points.

$$V(P_{0},P)$$

You can take two members of the family and find where they interect. In
particular, you can take the surface that corresponds to parameter
$P_{0}$ and the very similar surface specified by $P_{0}+dP_{0}$. The
envelope of a family is the set of all of these intersection points from
nearby parameters. If you drew all the surfaces of the family on a page,
you'd blacken it in sort of a noodle around the points $P_{0}$. The
envelope will be the edge surface of this blackened noodle.

The intersection occurs when

$$V(P_{0},P)=V(P_{0}+dP_{0},P)=ct$$

rearranging

$$dP_{0}\cdot\nabla_{0}V=0$$

$P_{0}$ can't vary any direction though. It can only vary inside the
original surface

$$S(P_{0})=0$$

$$dP_{0}\cdot\nabla_{0}S(P_{0})=0$$

Hence the derivatives of V and S have to be parrallel to each other. We
can treat this with the method of lagrange multipliers

$$\lambda\nabla_{0}S+\nabla_{0}V=0$$

$$\lambda=-\frac{|\nabla_{0}V|}{|\nabla_{0}S|}=-\frac{n}{|\nabla_{0}S|}$$

or in other words

You can use these three equations to determine P in terms of $P_{0}$

Then you plug these back into your original expression of the surface

$$S(P)+V(P)=ct$$

Mixed Charecterstic
-------------------

A plane is described implictly by a linear function of the coordinates

$$S(P_{0})=ax_{0}+by_{0}+cz_{0}+d=0$$

$$\hat{n}\cdot(P_{0}-\vec{o})=0$$

Where o is a point in the plane (which we'll call the origin) and
$\hat{n}$is a vector normal to the surface.

A plane wave is just going to propagate very simple, translating itself
normal to its surface at a speed c. However using the point
charecterstic to do this seems unneccesarily messy.

So we define a new type of function that given the orinetation of a
plane surface passing through the origin, will give its later shape.

$$S(P_{0};\vec{n})=\vec{n}\cdot P_{0}=0$$

$$|\vec{n}|=n$$ We call this new function W, the mixed charecterstic.

$$W(\vec{n};P)-ct=0$$

So the simplest is again homogenous media propagation.

$$W=\vec{n}\cdot(P-\vec{o})$$

Note that

$$\nabla W=\vec{n}$$

$$\nabla_{n}W=$$

All this says is that the porjected distance to the surface is going to
be equal to the time (as opposed to the point charecterstic which said
that the distance to the center of the sphere was the time.)

We can use this charecterstic to find the general propagation of any
surface by decomposing a surface into its planar components via a
legendre transform.

Geometrical Legendre Transform
------------------------------

The algebraic defintion of the Legendre transform is

$$H(p)=\min_{x}xp-G(x)$$

Geometrically speaking, we are taking enevlopes of planes.

A surface is defined by

$$S(P_{0})=0$$

The normal vectors to the surface are given by

$$\nabla_{0}S=\vec{n}$$

Therefore the family of tangent planes to the surface (Parametized by
the point on the original surface $P_{0})$ are given by the level sets

$$G(P;P_{0})=\nabla S(P_{0})\cdot(P-P_{0})=0$$

The so called cooridnates of a plane are the values of its normal
vector.

$$G(P;\vec{n})=\vec{n}\cdot(P-P_{0}(n))=0$$

Taking the envelope over the family parameter $P_{0}$ will give you back
the original surface. (The It will sort of look like connecting the dots
on a polyderon to get back a sphere).

Angle Charecterstic
-------------------

The angle characterstic we have to interpet a little differently. Now we
have a starting plane wave ad we want to know what is the direction that
the final surface crosses the origin on the other side.

Or we let the wave come out on the other side and progpage until it is
essentially a plane. Then we back propagate that plane to the origin.

The angle charecterstic is a scattering kind of thing.

We legendre transform our initial surface, we find out where this plane
ends up thanks to the angle charecterstic, then we inverse legendre
transform to reconstruct our propagated surface. A very analgous
procedure qualitatively to the fourier transform.

General Charecterstic
---------------------

We could have any type of surface and give its later shape.
