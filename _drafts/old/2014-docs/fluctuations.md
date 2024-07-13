Nonequilibirum Statistical Mechanics is a subject still ooking for the
right questions. And by right questions, I mean questions that can be
answered in any meaningful way.

Read Landau and Lifshitz

Find that Gibbs Einstein Paper

Kinetic chapter in kardar

Tie is with renormalization? Critical Points (Super fluctationy)?

Gaussian Fluctations

All of the above are really beside the point

Gallvotti Cohen

Jaxrynski

Crookes

Evans and Searles

Look in Dynamical Chapter, see what can be found

Carnot Engines

Time ordering(Can I do more permutations of a process than just time
flipping?), reversibilty

Lingevin Equation

All the above seems too standard for Dima, I guess? Needs something
esoteric and spicy.

The first fluctation theorem was kirchoff's law

Nyquist Formula

Einstein Smolukowski

Dima doesn't want the history of the subject. 2 Pages of that shit

The fluctuation comes in many flavors, all of which are very similar to
each other in their statement. Different Authors have derived them from
surpissingly varied peresectives with sometimes surprisingly subtle
distinctions for the definitions of the terms in the theorem. All seem
to flow from the same fundamental consideration of reversibility that
Carnot used to found the subject of thermodynamics which were eventually
refined by Clausius into the concept of entropy. The modern fundamental
conception of entropy typically stems from the probablistic work of
Boltzmann and often interpreted with the information theoretical bent.
Evans and Searles come at it from the position of stochatic differential
equations. Gallvotti and Cohen derive it in the context of markov
chains, Jazrynski derives it using the physically familiar concept of
deterministic Hamiltonian reservoirs. Wow. This is so wrong

The 0th law of thermodynamics, that equilbirium and therefore
tempurature exists universally between all systems is highly surprising
from the microscopic perspective. Why should this be the case at all?
Why should we be so "lucky" as to have thermodynamic work in the first
place? When taken as given, this axiom can be used to derive powerful
corrollaries. In essence, this is the essence of the classic fluctuation
results. Kirchoff essentially started the subject with his law of
blackbody radiation, that in equibilrium, a surfaces emissiivty must
equal its absorvitiy. Einstein used the facts to connect diffusion
coefficients to mobility? Nyquist derived the Johnson Noise equation by
considerations of equilbirum with blackbody radiation.

What is Entropy?
================

Short answer: no one is quite sure, but whatever it is, its important.

In the subdomain of equilbirium, there is a great more clarity. It would
be closer to the heart of equilibirum thermodynamics to call it
entropistatics. The original thermodynamic definition of entropy is
given by

$$\int\frac{dQ}{T}\le\Delta S$$

With equality holding for reversible porcesses,defining entropy as a
function of the state of the system (let's say the pressure and
tempurature) up to an additive constant

However, this inequality has to be wrong.

The trouble lies in the fact that thermodynamic variables are a crass
description which describes the predictable and important parts of a
large number of possible microscopic realizations of the process. The
modern consensus is that the time evolution of these microscopic degrees
of freedom ought to be Newtonian, consisting of a collection of
conservative forces describing the changes of positions and velocities
of the particles. These ordinary dynamics have a vital symmettry of time
reversal. We see no reas on that an instantaneous flip of all the
velocities by some genie should change the measured tempurature and
pressure of the system. Yet, if that is the case, this flipped system
will violate the entropy inequality just as assuredly and the original
complied with it, and then we have broekn the second law of
thermodynamics by construction.

Time Reversal
-------------

Section worthy? It is kind of interesting

$$S(x_{i,}x_{f},-t)=S(x_{f},x_{i},t)=-S(x_{i,}x_{f},t)$$

The powerful physical beuaty that underlies the fluctuations theorems is
that of a time conjugate path. If the path x goes from A at time 0 to B
at time T, then the conjugate path x\* follows the reverse trajectory,
going from B at time 0 to A at time T. In other words, if we film the
path, we play the film in reverse to see the time conjugate path.
Transcribing words into equations

$$x*(t)=x(T-t)$$

$$x*(0)=x(T-0)=x(T)=B$$

$$x*(T)=x(T-T)=x(0)=A$$

If we assume time reversal symmettry, the time conjuagate path is an
allowable motion.

$$\delta S=\int_{A}^{B}L(x+\delta x)dt=0$$

$$\delta S=\int_{B}^{A}L(x*+\delta x*)dt=0$$

This is the case if L is an even function of the velocities

The momenta flip their sign

$$\frac{\partial L}{\partial\dot{x}}=p=-\frac{\partial L}{\partial\dot{x}*}=-p*$$

A common and practically important impediment to time reversal symmetry
that deserves a short mention is the presence of a magnetic field. The
magnetic field couples in the lagrangian with a term linear in the
velocity

$$L=e\vec{\dot{x}}\cdot\vec{A}$$

Unless we flip the sign of the magnetic field, the conjugate path is no
longer an acceptable motion. We can see this simply by looking at the
lorentz force law and the right hand rule

$$F=ev\times B=-ev*\times B$$

Probabilistic Entropy
---------------------

First off, how do we assign a value of S to an exact microstate?

In theoretical practice, the entropy is often defined by

$$-\frac{\partial F}{\partial T})_{V,N}=S$$

In a general probablistic setting, entropy is a number that nicely
characterizes the concentrated-ness of a probability distribution.

$$S=-\sum p_{i}\ln p_{i}$$

Two simple clarifying examples

First, the certainty distribution where every probability is zero except
one

$$p_{i}=\delta_{i0}$$

$$S=-\sum\delta_{i0}\ln\delta_{i0}=-1\ln1=0$$

A completely uniform spread over N possibilities

$$p_{i}=\frac{1}{N}$$

$$S=-\sum_{i=1}^{N}\frac{1}{N}\ln\frac{1}{N}=\ln N$$

If instead we had defined entropy using $\log_{2}$, this would
correspond to the number of bits neccessary to select one of the
possibilities out of all of them ($2^{N}$ objects can be selected by N
bits) .

Entropy is superior measure of concentration to the often used measure
of variance $\sigma$ in which calculates a width of the distribution in
that if the probiabilty is in many seperate lumps, the entropy will add
for the lumps, whereas the variance will depend mostly more on the
relative seperation of the lumps.

Jacobians
---------

The fundamental object of interest for the deterministic evolution of
entropy is the Jacobian matrix. The porbability distribution is carried
along by the flow of the system.

We can imagine two very close points in phase space and a vector between
them. They will get carried along by the time evolution of the system.
This time evolution might shrink the vector, expand it, or turn it, and
one might expect that assuming the points are sufficiently close to one
another, there will be a linear map, a matrix, that describes the
mapping from the orginal seperation vector to the later one. This matrix
is called the Jacobian matrix.

Suppose we had the time evolved point $(q,p)$ as an explicit function of
its initial position $(q_{0},p_{0})$, for example for a falling bowling
ball

$$q(q_{0},p_{0},t)=q_{0}+\frac{p_{0}}{m}t+\frac{1}{2}at^{2}$$

$$p(q_{0},p_{0},t)=p_{0}+at$$

Then

$$dq_{t}=\frac{\partial q}{\partial q_{0}}dq_{0}+\frac{\partial q}{\partial p_{0}}dp_{0}=dq_{0}+\frac{t}{m}dp_{0}$$

$$dp_{t}=\frac{\partial p}{\partial q_{0}}dq_{0}+\frac{\partial p}{\partial p_{0}}dp_{0}=dp_{0}$$

Then the Jacobian matrix is simply

$$J(t)=\left[\begin{array}{cc}
\frac{\partial q}{\partial q_{0}} & \frac{\partial q}{\partial p_{0}}\\
\frac{\partial p}{\partial q_{0}} & \frac{\partial p}{\partial p_{0}}
\end{array}\right]$$

$$\left[\begin{array}{c}
dq_{t}\\
dp_{t}
\end{array}\right]=J(t)\left[\begin{array}{c}
dq_{0}\\
dp_{0}
\end{array}\right]$$

We can also find an explicit differential equation for $J(t)$

$$\left[\begin{array}{c}
dq_{t+dt}\\
dp_{t+dt}
\end{array}\right]=J(t+dt)\left[\begin{array}{c}
dq_{0}\\
dp_{0}
\end{array}\right]$$

$$\frac{dJ}{dt}\left[\begin{array}{c}
dq_{0}\\
dp_{0}
\end{array}\right]=\frac{1}{dt}\left[\begin{array}{c}
dq_{t+dt}-dq_{t})\\
dp_{t+dt}-dp_{t})
\end{array}\right]=\frac{1}{dt}\left[\begin{array}{c}
d(\dot{q}_{t}dt)\\
d(\dot{p}_{t}dt)
\end{array}\right]=\left[\begin{array}{c}
\frac{\partial\dot{q}}{\partial q_{t}}dq_{t}+\frac{\partial\dot{q}}{\partial p_{t}}dp_{t}\\
\frac{\partial\dot{p}}{\partial q_{t}}dq_{t}+\frac{\partial\dot{p}}{\partial p_{t}}dp_{t}
\end{array}\right]=\left[\begin{array}{cc}
\frac{\partial\dot{q}}{\partial q_{t}} & \frac{\partial\dot{q}}{\partial p_{t}}\\
\frac{\partial\dot{p}}{\partial q_{t}} & \frac{\partial\dot{p}}{\partial p_{t}}
\end{array}\right]\left[\begin{array}{c}
dq_{t}\\
dp_{t}
\end{array}\right]=\left[\begin{array}{cc}
\frac{\partial\dot{q}}{\partial q_{t}} & \frac{\partial\dot{q}}{\partial p_{t}}\\
\frac{\partial\dot{p}}{\partial q_{t}} & \frac{\partial\dot{p}}{\partial p_{t}}
\end{array}\right]J(t)\left[\begin{array}{c}
dq_{0}\\
dp_{0}
\end{array}\right]$$

Let's define the derivatives of the velocities matrix

$$B(x,p,t)=\left[\begin{array}{cc}
\frac{\partial\dot{q}}{\partial q} & \frac{\partial\dot{q}}{\partial p}\\
\frac{\partial\dot{p}}{\partial q} & \frac{\partial\dot{p}}{\partial p}
\end{array}\right]$$

$$\frac{dJ}{dt}=B(x(t),p(t),t)J(t,x_{0},p_{0})$$

It's a mess, but

$$J(t+dt)=(1+dt\left[\begin{array}{cc}
\frac{\partial\dot{q}}{\partial q_{t}} & \frac{\partial\dot{q}}{\partial p_{t}}\\
\frac{\partial\dot{p}}{\partial q_{t}} & \frac{\partial\dot{p}}{\partial p_{t}}
\end{array}\right])J(t)$$

Iterating the above equation and using the intial condition

$$J(0)=I$$

We get.

$$J(t)=(1+dtB(t-dt))\cdots(1+dtB(2dt))(1+dtB(dt))(1+dtB(0))$$

or for short

$$J(t)=T\{e^{\int_{0}^{t}Bdt}\}$$

T is the time ordering operation placing earlier factors of B to the
right, which is required since the B factors do not necessarily commute.

From the Jacobian matrix we can get the volume expansion factor. Given a
little box or parrellopiped with vectors $\vec{a}_{i}$ for edges, the
volume is given by packing a matrix A with these vectors and then taking
the determinant. This is the geometric definition of the determinant and
all the clever little algebraic properties derive from this fact.

$$dV_{0}=\det A_{0}=\det\left[\begin{array}{ccc}
| & |\\
\vec{a}_{1} & \vec{a}_{2} & \cdots\\
| & |
\end{array}\right]$$

Each of these vectors is mapped to its evolved vector by $J(t)$, so

$$dV_{t}=\det A_{t}=\det(J(t)A_{0})=\det J(t)\det A_{0}=\det J(t)dV_{0}$$

Because of this property of the Jacobian, it is the most vital dynamical
object needed for the study of deterministic entropy dynamics or
statics. This is opposed to the typical approach to entropy, such as the
Boltzmann equation. The Boltzmann equation does not describe the
evolution of a gas on its entire phase space. It describes the
probablistic evolution of the 1-particle distribution function. It is
quite natural that a system in an uncertain state, evolving in an
uncertain way will grow even more uncertain. In comparison, a
determinstic system will just carry its distribution along with the
flow. The entropy does not care about the seperation of lumps of
probability or their location so just being carried around will not
change its value. What does change its value is an interesting Jacobian
that will squeeze certain sections of the distribution and expand
others. For conceptual purposes, one could roughly equate this volume
dilation factor to the local entropy production

Liouville's Theorem
-------------------

The incompressibility of phase space. A vital component of statistical
mechanics. Why is Liouville's theorem? A simple reason? What does it
take to break it? The equivalent to some degree of the unitarity
postulate in QM. Etendue?

A fundamental object of interest for nonequilbirum statistical mechanics
is the law of entropy increase. Liouville's theorem is a major
impediment to a fundamental microscopic explanation of this phenomenon,
and yet without Liouville's theorem, the concept of equilbirum entropy
would be questionable.

Liouville's Theorem is the statement that in Hamiltonian phase space the
volume dilation factor is a constant factor 1 for all time. This theorem
is of vital importance to equilbirium statistical mechanics, as it helps
guarantee that any distribution that is a function of H only will be
stationary, allowing for the simple definition of the equilbirum
statistical ensembles in phase simple. Hamiltonian dynamics generates
the phase space velcoties from the Hamiltonian

$$\dot{q}=\frac{\partial H}{\partial p}$$

$$\dot{p}=-\frac{\partial H}{\partial q}$$

This is the true of all continuous canconical transformations which can
be charecterized similarly by a generator G in place of H. Now we look
at the Jacobian evolution equation

$$J(t+dt)=(1+dt\left[\begin{array}{cc}
\frac{\partial\dot{q}}{\partial q_{t}} & \frac{\partial\dot{q}}{\partial p_{t}}\\
\frac{\partial\dot{p}}{\partial q_{t}} & \frac{\partial\dot{p}}{\partial p_{t}}
\end{array}\right])J(t)=(1+dt\left[\begin{array}{cc}
\frac{\partial^{2}H}{\partial p\partial q} & \frac{\partial^{2}H}{\partial p^{2}}\\
-\frac{\partial^{2}H}{\partial q^{2}} & -\frac{\partial^{2}H}{\partial p\partial q}
\end{array}\right])J(t)$$

Now we take the determinant

$$\det J(t+dt)=\det\left[\begin{array}{cc}
1+dt\frac{\partial^{2}H}{\partial p\partial q} & dt\frac{\partial^{2}H}{\partial p^{2}}\\
-dt\frac{\partial^{2}H}{\partial q^{2}} & 1-dt\frac{\partial^{2}H}{\partial p\partial q}
\end{array}\right]\det J(t)$$

$$\det\left[\begin{array}{cc}
1+dt\frac{\partial^{2}H}{\partial p\partial q} & dt\frac{\partial^{2}H}{\partial p^{2}}\\
-dt\frac{\partial^{2}H}{\partial q^{2}} & 1-dt\frac{\partial^{2}H}{\partial p\partial q}
\end{array}\right]=(1+dt\frac{\partial^{2}H}{\partial p\partial q})(1-dt\frac{\partial^{2}H}{\partial p\partial q})-(dt\frac{\partial^{2}H}{\partial p^{2}})(-dt\frac{\partial^{2}H}{\partial q^{2}})=1+dt(\frac{\partial^{2}H}{\partial p\partial q}-\frac{\partial^{2}H}{\partial p\partial q})+O(dt^{2})=1+O(dt^{2})$$

If we take the definition of entropy as

$$S=\int\prod_{i=1}^{N}dx_{i}dp_{i}\rho\ln\rho$$

and we look at its time evolution

$$\frac{\partial S}{\partial t}=\int\prod_{i=1}^{N}dx_{i}dp_{i}\partial_{t}\rho[\ln\rho+1]=0$$

Liouville's theorem tells us that the flow of the exact probability
distribution changes its shape, but not its concentration. The entropy
is a measure of that concentration, so it cannot change.

Therefore we have to adopt more ad hoc definitions of entropy, the
criteria for a definition being that it seems reasonable (i.e matches
some property of macroscopic entropy). All good entropy definitions
should lead to the same equivalent macroscopic entropy behavior.

The simplest form of incompressbility is

$$\nabla\cdot v=0$$

In words, this says that the divergence of velocity is zero. That
expression is almost a definition of incompressible.

It adds a bit more clarity to put it in it's integral form

$$\int\nabla\cdot vdV=\oint v\cdot dS=0$$

Any closed surface has as much stuff going in as coming out.

A thoery of nonequilbirum statistical mecahnics must have the increase
of entropy, which requires explicity non-Liouvillian dynamics.

Lyapunov
--------

Magnetic Fields
---------------

Onsager Relations
-----------------

Boltzmann's Approach and the H-Theorem
--------------------------------------

$$S=\int\rho\ln\rho d\Gamma$$

$$\frac{\partial S}{\partial t}=\int d\Gamma\partial_{t}\rho[\ln\rho+1]$$

$$\int d\Gamma\rho=1$$

$$\int d\Gamma\partial_{t}\rho=\partial_{t}1=0$$

The material or streaming derivative gives the rate of change of an
expression as we follow it along a flow. It is defined as

$$\frac{DA}{Dt}=\partial_{t}A+\dot{\Gamma}\cdot\nabla_{\Gamma}A$$

Because we must have

$$\int d\Gamma\partial_{t}\rho=\int d\Gamma[\frac{D\rho}{Dt}-\dot{\Gamma}\cdot\nabla_{\Gamma}\rho]=0$$

We can integrate by parts to get

$$\frac{D\rho}{Dt}=-\rho\nabla_{\Gamma}\cdot\dot{\Gamma}$$

This is the case for local behavior of $\rho$, i.e. if we assume the
integrand vanishes everywhere. These are the equations of motion in a
completely deterministic system

In Boltzmann's approach, which includes porbablistic collisions, we
instead can only guarantee the total integral vanishes.

$$\frac{\partial S}{\partial t}=\int d\Gamma\partial_{t}\rho\ln\rho=$$

I'm not sure where I'm going with this

Projection of Phase Space
-------------------------

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

Jazrynski/Hamiltonian Evolution 
===============================

This is the program. We will take a large reservoir system in a
canonical ensemble and put it into dynamical contact with a system of
interest in a particular state. We will use the macroscopic definition
of entropy

$$dS=\frac{dQ}{T}|_{rev}$$

We will then compare the relative probabilities of a evolution compared
to its time reversed evolution

$$\frac{P(A\rightarrow B)}{P(B\rightarrow A)}$$

I hesitate to call the above program the physical approach. Just because
your theory does not relate back to what is considered fundamental, does
not make it not physical. However, physicists love Hamiltonian dynamics,
so let's call this the physicsy approach.

Actually, I'm not sure I should call the the Jazrynski approach, maybe
the Hamiltonian approach is better.

Although it is practical impossibility to verify, the scientific
community at large believes that the phenonmenon of statistical
mechanics are consequences of the detailed microscopic motion of the
many many degrees of freedom of a macroscopic system.

Jazrynski's approach to the fluctation theorem is to track the
presumably hamiltonian and conservative microscopic motion of the system
and its environent (or reservoirs).

The reservoirs may be taken to have distrbitution of the canonical
ensemble.

He associates entropy with the exchange of energy to the reservoirs

$$\Delta S=\frac{\Delta Q}{T}$$

The system does external work by the external parameter $\lambda(t)$,
which could be for example the position of a piston during compression.

The system is brought into thermal contact with the reservoirs in some
manner, the interaction hamiltonian being turned on and off with the
function $c(t)$

The Hamiltonian giving the evolution of the system and the reservoirs is

$$H=H(z,\lambda(t))+\sum_{n}H_{n}(y_{n})+\sum_{n}c_{n}(t)h_{n}^{int}(z,y_{n})$$

Jazrynski's Equality
--------------------

A common form for the statement of the irreversiblity for constant
tempurature reservoir processes in thermodynamics is

$$Q\le T_{R}\Delta S$$

Where T is the tempurature of the reservoir and $\Delta S$ is the change
of the systems entropy

$$W=\Delta E-Q\le\Delta E-T\Delta S$$

Defining the Helmholtz free energy as

$$F=E-TS$$

We get the inequality

$$W\le\Delta F)_{T_{R}}$$

with equality holding for perfectly reversible processes.

Jarzynski found the equivlent statistical statement of this law

$$<e^{-\frac{W}{k_{B}T}}>=e^{-\frac{\Delta F}{k_{B}T}}$$

This fluctation theorem is independant of the manner in which the work
was carried out

We may derive it by

We define

The Hamiltonian has an explicit time dependace due to an external
paramter

$$H(\Gamma,t)$$

$\Gamma$is short for then entire set of coordiantes and momenta

Why am I using such obtuse notation?

We define the work done on the system by

$$W(\Gamma_{0})=H(\Gamma_{t}(\Gamma_{0}),t)-H(\Gamma_{0},0)$$

$$\frac{d}{dt}\Gamma_{t}(\Gamma_{0})=\{\Gamma_{t},H\}$$

$$<e^{-\beta W}>=\frac{1}{Z}\int d\Gamma_{0}e^{\beta H(\Gamma_{0},0)}e^{-\beta[H(\Gamma_{t}(\Gamma_{0}),t)-H(\Gamma_{0},0)]}=\frac{1}{Z}\int d\Gamma_{0}e^{-H(\Gamma_{t}(\Gamma_{0}),t)}$$

Even in a time dependant system, Liouville's theorem still holds so the
Jacobian

$$\frac{\partial\Gamma_{t}}{\partial\Gamma_{0}}=1$$

$$<e^{-\beta W}>=\frac{1}{Z_{0}}\int d\Gamma_{t}e^{-\beta H(\Gamma_{t},t)}=\frac{Z_{f}}{Z_{0}}$$

$$Z=e^{\beta F}$$

Giving us our final result

$$<e^{-\frac{W}{k_{B}T}}>=e^{-\frac{\Delta F}{k_{B}T}}$$

It almost feels like we cheated somehow, doesn't it?

Probablistic Approach? I don't think this is appropriate Thermostatted approach
===============================================================================

Master, Lingevin, Path Integral

Thermostats
-----------

A difficulty of understanding the dynamics of thermodynamic quanitites
is the fact that the dynamics depend on the surroundings. The physical
thermostat or thermal reservoir is a big hot rock that we put in contact
with our system, giving or removing energy in a manner such that certain
averages and tempuratures are maintained. In equilbirium statistical
mechanics this is difficulty is avoided because whatever the mechanism
that an average tempurature is maintained, the important fact is that
the tempurture is maintained at all. If this was not the case,
thermodynamics would not be a general theory, as every means of
maintaining tempurature would require a new analysis. In
Non-equuilbirum, we lose this universality to some degree.

The thermostat is a technical device for maintaining constant
tempurature for completely determinsitic systems which was invented for
the purposes of molecular simulations. It explicitly breaks the
incompressible Liouvillian behavior of the system and allows a steady
state to be simply achieved in a forced system during simulation.

Isokinetic

Nose-Hoover

Gauss Principle of Least Constraint
-----------------------------------

The form of the Thermostat follows from a constraint. The constraints
that a thermostat uses are extremely nasty ones, like keeping kinetic
energy a constant. Lagrangian mechanics handles pulley and gear
constraints admirably, but try to imagine a system of pulleys and gears
that could enforce such a constraint. So we can't use Lagrangian
mechanics. Instead, certain researchers turned to ad hoc methods, which
ended up being equivalent to Gauss' Principle of Least Constraint.
Exactly because of its excessive power and versatility, Gauss' Principle
is perhaps a little silly. A really good fundamental system of mechanics
should not allow the construction of equations of motion for unphysical
and contrived constraints. I think the best that can be said about the
resulting equations is that they are minimally unreasonable in some
sense. The mathematical thermostat should not be considered to get any
of its validity from attaching itself to the illustrious name of Gauss,
but instead because it is convenient and seems to work.

When the external forcing bumps the system locally, the constraint sucks
the equivalent amount of energy from the entire system.

Gauss' Principle of Least Constraint is an alternative system to derive
the equations of motion of a system, which is not always equivalent to
the Lagrangian and Hamiltonian Formalism (Reference? Is this even
true?). The principle is to compute the lost force

$$Z=\sum m_{i}(\ddot{x}_{i}-\frac{F_{i}}{m_{i}})^{2}$$

and now consider all possible variations of the quantities $\ddot{x}$
consistent with the constraint. At the very least, this is reasonable on
account that in the abscence of contraints $Z=0$ is a possiblity and we
get the usual $F=ma$.

One could see this as being very convenient computationally

$$$$

Note to self: Gauss placed some emphasis on the similarity between this
principle and his method of least squares, which can be dignified as the
best method to remove a gaussian distributed error term from measured
data. Perhaps Gauss principle of Least Constrait could be dignified on
similar grounds based on an error in the acceeration, or a gaussian
random force whose net effect is to enforce the constraint.

References: Sommerfeld's Mechanics, Foundations Of Physics Lindsay and
Margenau, Lanczos.

The Nose-Hoover

Another way of controlling the Kinetic energy would be to change the
rate of time flow. Imagine watching a bunch of energy conservastive
billiard balls in a movie, getting kicked around by cues. Every time a
cue hits a ball, it'll increase or decrease its energy. However if a
little man behind a curtain controls the payback speed, he could slow
down the film every time the cue would increase the kinetic energy is or
speed it up if it is decreased. The Potential energy of the system would
be unchanged since it is only position dependant and thus independant of
playback speed.

Evans and Searles
-----------------

In a nutshell, watch the evolution of probabilty in explicity non-phase
space conserving systems. Check the time reversed version. Compare.

Do they use lingevin type random forcing combined with constraints?

Gallvaotti and Cohen
--------------------

Experimental Confirmation - DNA micromanipulation
-------------------------------------------------

http://www.nyu.edu/classes/tuckerman/stat.mechII/lectures/lecture\_9/node4.html

THis is what PRL looks likes

J. M. Smith, R. Brown, and C. Green, Phys. Rev. B 26, 1 (1982);

Nucl. Phys. A195, 1 (1982). J. M. Smith, Phys. Rev. D (to be published);

R. Brown, Phys. Rev. B 26, 706(E) (1982).

J. M. Smith, Molecular Dynamics (Academic, New York, 1980), Vol. 20, p.
20.

R. Brown, in Charge Density Waves in Solids, edited by C. Green, Modern
Problems in Condensed Matter Sciences Vol. 25 (North-Holland, Amsterdam,
1989). C. Green, University of Wisconsin, Madison, Report No.
MAD/PH/650, 1991. J. M. Smith et al., in Proceedings of the Topical
Meeting on CP Violation, Calcutta, June 1990 (unpublished).

1 A. Sommerfeld, Mechanics (Levant Books, Kolkata, 2003).

M. Kardar, Statistical Physics of Particles (Cambridge University Press,
Cambridge, 2011).
