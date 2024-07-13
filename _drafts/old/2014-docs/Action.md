A profitable second subject for thought after producing a question is
what form could the answer take. I believe most peoples first objective
is to achieve the answer to a mechanics problem in the form

$$q_{f}(\{q_{i}\})$$

The natural experiment in your head is that of an initial value problem.
"If I chuck this ball at Pete's head from over here and with the much
force, where will it end up?"

One wants to find functions that you may place whatever physical values
you twiddle your dials to (in the fifth grade you called them
independant variables and always put them on the horizontal axis of your
plots) and have the functions spit out whatever numbers your meters will
read (dependant variables, your vertical axis). However, this
distinction, while often an intuitive categroization, is arbitrary.
These theoretical answers can be inverted, or you could twiddle your
dials until you read something on your meter and then read the number on
the dial (Or you could have turned your graph 90 degrees and freaked Ms.
Zerbopple the fuck out). What does seem to have intirnsic meaning is the
number of degrees of freedom your theory posesses.It seems natural to
want to state your theory in a mathemtical form that doesn't have such
arbitrary distinction implicit in it. The form that does this well is
the implicit form, a sequence of relations between all quantities of
interest (set to zero because it looks real pretty).

$$\phi_{j}(\{x_{i}\})=0$$

The Group Property of the Action (or transformation functions)

To combine 2 transformation, you add their correspinding tranasformation
functions ad then remvoe the intermdeiate variable using the constraint
equation that the derivative with respect to the intermediate variable
is zero,

$$F_{1}(A,B)+F_{2}(B,C)=F_{3}(A,B,C)$$

$$\frac{\partial F_{3}(A,B,C)}{\partial B}=0\Rightarrow F_{3}(A,C)$$

or keeping the stationaryzation with respect to B implicit

$$F_{1}(A,B)+F_{2}(B,C)=F_{3}(A,C)$$

Nice and clean.

In the context of the Action function, this amounts to splitting a
movement into two sections, and then combing the two segemtns by setting
the final momenta of the first equal to the inital momenta of the
second.

$$\frac{\partial S_{1}}{\partial x_{f1}}=p_{f1}$$

$$\frac{\partial S_{2}}{\partial x_{i2}}=-p_{i2}$$

Another property is the inverse operations

$$F(A\rightarrow B)=-F(B\rightarrow A)$$

Also the identity operation

$$F(A,A)=0$$

Some examples.

F(x,x')

Active and Passive points of view

Action as solution of explosion wavefront.

$$\frac{\partial S(x_{0,}x_{f},t)}{\partial r_{0}}=p_{r}(\theta,\phi)$$

$$\frac{\partial S(x_{0,}x_{f},t)}{\partial\theta}=p_{\theta}(\theta,\phi)$$

$$\frac{\partial S(x_{0,}x_{f},t)}{\partial\phi}=p_{\phi}(\theta,\phi)$$

$$r_{0}=0$$

These three contraints give sufficient contraints that the explosions
surface may be parametized by t.

Of cource an explosion does not have uniform directional momentums. It
would have a distribution.

But after all cannot, regular motion be considered a directed explosion?
Huyghen's Principle. Wouldn't a sequence of directed explosions Look
identical to regular motion? Similar to green's principle, a bunch of
impulses add.

Quantization
============

The previous law for the combination of transfromation is changed

$$F_{1}(A,B)+F_{2}(B,C)=F_{3}(A,B,C)$$

$$\frac{\partial F_{3}(A,B,C)}{\partial B}=0$$

We define a new function for notational convenience

$$K(A,B)=e^{\frac{i}{\hbar}F(A,B)}$$

The new law of transfomrations is changed to (Normalization factors?)

$$K_{3}(A,C)=\int K_{1}(A,B)K_{2}(B,C)dB=\int e^{\frac{i}{\hbar}[F_{1}(A,B)+F_{2}(B,C)]}dB=e^{\frac{i}{\hbar}F_{3}(A,C)}$$

The inverse property is mainainted So that

$$K(A,B)=e^{\frac{i}{\hbar}F(A,B)}=K(B,A)*=e^{-\frac{i}{\hbar}F(B,A)}$$

Note that these new F functions will not be equal to the old F functions
except under very special circumstances, However the new integral method
of removing the interioir variable is related to the previous
stationization method very simply through the method of stationary
phase.

For infinitsimal transformations, The K function will become nearly a
delta function. The more delta function like a function is (peaked), the
better the steepest descent or stationary phase approximation works.
Hence the correspondence of classical poisson brackets and quantum
commutators

Variational
===========

As long as you keep The endpoints fixed, you can go through as many
intermediate variables as you want. In fact, you could imagine lettting
your number of variables going towards a continuum. Then the ombination
property of the action function becomes Hamilton's principle.

One of the mopst interesting things baous the variational principle is
its computational teeth. If you imagine arbitrarily parametizing how you
expect something to move, you may use the viartiaonal principle to
achieve a decen approximation to the actual motion. In this way, you can
find effective descirptions of deeper theories either for conecptual or
calculational purposes.

Varitional pricniple allows nature to keep her skirts down.

Equations of Motion = J

One could also view J as a variational parameter for the variational
solution x\[J\], which sets the path equal to that of the unperturbed
problem with a J forcing term. Dtermining J exactly is impossible
however, so this varitional prpblem is then treated perturbationally.

The second functional derivative of S w.r.t J is a generalization of the
Green's Function. Wr.t. x a generalization of eq of motion (L operator).

Scattering and The Classical S-Matrix
=====================================

The Soft Sphere

Optics
======

If you have never seen the Action based formalisms in the optical
context, you probably have no idea what the fuck is going on. Fermat's
principle is the optical equivlaent of the action principle. Hamilton
develpoed in essence all the fancy techniques that find their typical
application in the context of mechanics for the field of optics. At the
time (\~1830-ish), people were just transitioning from the corpuscular
theory of light a la Newton (in vogue because Newton said so and few had
sufficiently weighty physics balls to dispute him) over to the wave
theory of light thanks the the work of Fresnel and Young (Who both died
in freak gay bathhouse accidents at around this period).

Fermat's Principle.
-------------------

If you pre decide that a light beam travels from point A to point B, it
will travel the path between them that possesses the least time. Since
the velocity of light is a function of posittion in materials, this
equates the the smallest optical path

$$\int_{A}^{B}dt=\int_{A}^{B}nds$$

I stress that the fixing of the endpoints is VITAL to the principle. As
such, I believe the statement is very unnatural feeling as it is not a
statement of cause and effect such that we're used to. When F equals ma,
that makes sense. Forces cause accelerations. I believe the first
instinct for most would be to go for something similar. Given the
starting point of a ray and its intial direction, where does it go?
Fermat's Principle is instead a principle of deduction. Given a man's
birth certificate and obituary, how did he lead his life?

The key manipulations of path length expressions are

You may slightly move any pooint on the interior of a true stationary
path andf have the path length remain the same to first order. This is
Fermat's principle restated. $$[APA']=[AQA']+O([PQ]^{2})$$

The second mainipulation is that an endpoint of a line is displaced
perpendicular to the line, the length of the line is unchanged.
Essentially, this corresponds to first order of keeping the other
endpoint as the center of a circle and the other points being on its
circumference.

$$[AB]=[A'B]+O([AA']^{2})\text{ given }AA'\perp AB$$

Point Charecterisitc
--------------------

Mixed Charecterestic
--------------------

Angle Charecteristic
--------------------

Foci
----

Imaging
-------

A Mathy Aside: Implicit Surfaces and Inversion
==============================================

Implicit surfaces have completely gone out of vogue. Parametized
surfaces are stressed much more in calculus classes, perhaps because
they are more intuitive. Examples of parametized surfaces include polar
cooridlates of the sphere, arc length coordinates of curves, etc. If you
need to describe a 3d surface, you need 3 parameters. Excellent. If you
want a picture of the surface, pick some parameter values out of a sack,
evalyate and connect the dots.

Explicit parametization builds the surface up. You add a new variable
for every dimension your surface has.

Implicit Surfaces cut down. You start with a space of size d and then
you add constraints, lowering d by one each time. For example, start in
3d space. Now add one constraint of the form

$$\phi(x,y,z)=0$$

such as

$$x^{2}+y^{2}+z^{2}-1=0$$

Now you have a d-1 dimensional surface, in this case a 2d unit sphere.
Now add another constraint, like

$$z=0$$

This is now a d-2 dimensional surface, in this case a 1d unit circle in
the xy plane.

There are complciations. Your ocnstraints could be incompatible, or they
could be repetitive, or they could just kiss each other, but typically
that's how it works. One dimensional lowering per contraint.

Hodge Dual - Differential Version of the equivelance between parametized
and constrained geometric objects

Power Series Inversion
----------------------

Inverting functions is hard. In general there is no algebraic procdedure
that is going to guarantee you'll be able to ioslate the variable you
want on one side of the equality. For example, proven fact that there is
no general formula for the inversion of polynomials of degree greater
than 5 (The Abel-Ruffini Theorem. And no, I have no idea how it works.
I'm quoting math gurus.) Given this, it is hard to imagine how we can go
around inverting functions so flippantly. I believe it is very important
to know that in principle it is possible to invert "any" function
approximately inside a region, in a similar sense that it is possible to
approximate "any" function in a taylor series in a region.

Lagrange Multipliers
--------------------

Suppose you had cleverly achieved writing f as a function of the
contraint and the d-1 other variables. Then you could write its
differential as

$$\delta f=\delta f)_{\phi}+\frac{\partial f}{\partial\phi})_{others}d\phi$$

Now optimization under contstraint is all about setting

$$\delta f)_{\phi}=0$$

or we take the total change in f and take off the part due to changing
$\phi$, which we weren't supposed to do.

$$\delta f-\frac{\partial f}{\partial\phi})_{others}d\phi=0$$

With $\frac{\partial f}{\partial\phi})_{others}$ being some number
evaluted at the extremum point which we will call $\lambda$. However,
how the hell can we know what the value of $\lambda$ is if we can't even
find the extremum point? Leave it unevaluted. We can expand $\delta f$
and$d\phi$in the our original variables since that is the form we have
their expression in.

$$\delta f=\sum_{i}\frac{\partial f}{\partial x_{i}})_{x_{i\ne j}}dx_{i}$$

$$d\phi=\sum_{i}\frac{\partial\phi}{\partial x_{i}})_{x_{i\ne j}}dx_{i}$$

We then have

$$\sum_{i}\frac{\partial f}{\partial x_{i}})_{x_{i\ne j}}-\lambda\frac{\partial\phi}{\partial x_{i}})_{x_{i\ne j}}dx_{i}=0$$

This equation must be satisified regardless of which direction we make
dx so very term in the sum must vanish. This is known as Lagrange's
Method of the undetermined multiplier. Perhaps a better name would be
Lagrange's Method of the unknown constraint derivative. If we have more
contraints, we can instead produce analogous expressions to the above
with additional lagrange multipliers.

Note that the Lagrange multiplier shows the dependance upon small
changes to the contraint.

$$\phi=0\Rightarrow\phi=\epsilon$$

$$f_{min}\Rightarrow f_{min}+\lambda\epsilon$$

In a sense, the lagrange multiplier measures how much the function
"hates" the contraint. In mechanics, where f may be the potential energy
in statics or lagrangian in dynamics, you may recall the the lagrange
multiplier often ends up being the force of contraints, such as normal
forces or tensions in rods or something. This is why. If the contraint
is secretly slightly "spongy" the lagrange multiplier is also a measure
of how much the contraint is violated.

Lagrange Mulitplier Series

If you want any guarantees about convergence, you'll have to talk to my
lawyer

We can rewrite the condition as

$$d(f-\lambda\phi)=0$$

Contact Transformations - Kind of a Big Deal
============================================

What is a canonical transformation? Let me count the ways

A transformation mixing up coordinates and tangent planes in such a way
as to maintain contact between any two surfaces (Wut?)

Preserves phase space volume

Preserves Poisson Brackets

Preserves Hamiltonian Form of EqMo

Generated by a function F

Legendre Transformations
------------------------

One can apply the eikonal approximation to a higher order partial
differential equations in order to convert it to an approximate (often
nonlinear) first order PDE. However, one can also use the Fourier
transfrom trick to solve these PDES by considering the function to be a
linear combination of planes waves. What is the equivalent method on the
eikonal? The answer is the well known, but rarely understood Legendre
transformation, a transformation with signinifcantly more depth than it
is given credit for

Surfaces can be though of in two equivalent ways. They can be thought of
as the union of all of the points in the surface. I believe this is the
deafult understanding these days. They can also be though of as the
envelope of all the tangent planes.

The Dual Transform turns points into lines and lines in to points. If
you take a collection of points creating a surface is real space, you
can get an envelope of their corresponding lines in dual space. This is
the legendre transformed surface.

The Legendre Transform is a geoemtric object. Its algebraic form is
sucky.

### Envelopes

What the hell is an envelope. Old school mathemticians loved this
concept because it is fundamentally geometric. A continuous (is
continuity necessary? can't I use some discrete time step?) family of
surfaces may have a point or line or surface of interestion between
negiboring surfaces. This point will also be a point of tengency to the
first order I think. Proof? If you trace this point through the entire
family, you get a new curve or surface. This is known as the envelope of
the

### First Order PDE

The fundamenetal trick of first order partial differential equationsin N
variables is the consider the equation actually describing a surface in
a N+1 variable space. In other words, look at the graph of f(x). Now
twist your brain so that the graph is not a representation of a
function, but instead is a plane curve, i.e. a totally geometrical
object. This is a very subtle and slight conceptual step to the left. In
this way we can use all our geomtrical intituition and theory on the
essentially algebraic theory of partial differential equations and vice
versa.

The simplest case: The first order ODE as describing a plane curve

The implicit description of the graph in the x-y plane given by the
function f(x) is

$$\Phi(x,y)=y-f(x)=0$$

The Legendre trick to solve first order PDEs is useful when the equation
is sophisticated in derivatives, but very simple in coordinates, just
like the Fourier transfrom trick (The Airy function example)

For a good hard read on the subject see Courant and Hilbert

Envelopes are the locations of constructive interference for a family of
wavefronts, where they have the same phase.

The derivative ocndition on the action could be considered an
eneveloping equation, with the interior variables paramatizing the
family of exterior surfaces

Nevelopes occur in parametized minimization problems

http://www.sjsu.edu/faculty/watkins/envelopetheo.htm

Wavefront Ray Duality (I like that word. Duality)
-------------------------------------------------

Generators and Noether's Theorem
--------------------------------

Crystal Momentum and the finite F translation?

Maupertuis Action, Hamilton's Action, Poincare Invariants
=========================================================

Poincare Invariants
-------------------

TL;DR Poncare invariants are The natural extension of Liouville's
Theorem when one considers that uncoupled systems each have their own
phase space conservation, which must a type of subspace volume
conservation in the combined phase space.

Liouville's Theorem gurantees the preservation of volume of phase space.
If you track a little blob that gets carried with the flow, it will
neither compress nor expand. However, phase space is very easily
dimensionally extendable. We can take two independant systems, say a
rocket ship on pluto and a simple harmonic oscillator in Oslo, and
consider them to be a single system. They will evolve completely
independantly of one another. Since the dynamics is still Hamiltonian,
the volume of the entire combined phase space will be preserved. But,
since we could have considered them seperately, the volume of the
indvidual phase spaces will be conserved. These volumes in the
independant phase spaces are now high dimensional "areas" (areas in the
sense they have less dimension than the volume yet more than a point) in
the combined phase space.

However, what if we played such games with a system that couldn't be
seperated into such obviously independant parts? Systems that actually
are coupled to each other, yet we try to compute phase space volumes as
if they were independant? Here the concept of the Poincare invariants
comes in.

We can inspect the coupling of the volumes of systems via their Jacobian
matrix.

If we define some 2n dimensional surface in phase space, and calculate
its area, this area is invariant if the surface is carried along with
the flow.

Calling it an area may be a bit deceptive, as there is no notion of
distance in phase space and some aspects of area one is familiar with do
not apply. Perhaps it would be better to call it very explicitly the
symmetric sum of the projected subvolume invariant.

$$J_{n}=\sum\dotsint\prod dxdp$$

If the surface is parametized by the 2n variables $(u,v,w,z,\ldots)$,
would could write this as an integral of the sum of all the Jacobians
$D_{ij\ldots}$

$$x_{i}=x_{i}(u,v,w,z,\ldots)$$

$$p_{i}=p_{i}(u,v,w,z,\ldots)$$

$$D_{ij\ldots}=\frac{\partial(x_{i},p_{i},x_{j,}p_{j},\ldots)}{\partial(u,v,w,z,\ldots)}$$

$$J_{n}=\dotsint\sum_{ij\ldots}D_{ij\ldots}dudvdwdz\ldots$$

The two most common examples of this are 2 dimensional surface
invariance and the full volume invariance we've already encountered in
the Liouville theorem.

The 2 dimensional invariant $J_{2}$is can equivalently be thought of as
the line integral $$\int pdq$$

via an application of Stokes theorem.

If a system in a probabilistic distribution of states comes into contact
with another system in a determined pointlike state, the total volume of
the distribution is zero, similar to a sheet of paper in which the
thickness is the pointlike state's dimension and the paper surface
directions are the distrubuted state directions. As the piece of paper
evolves in time, it will warp and bend, since the systems are coupled.

Why am I even talking about this? Projected dynamics

Action-Angle, Adiabatics, and Old Quantum
=========================================
