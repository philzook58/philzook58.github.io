Introduction
============

Nonequilibirum Statistical Mechanics is a subject still looking for the
right questions. And by right questions, I mean questions that can be
answered. One strange question that has recently found to be answerable
is known as the Fluctuation Theorem. There are a number of roughly
identical relation that can be achieved from multiple approaches of
attack.

I would classify the fluctuation relations as coming from three
different main approaches. The first approach is the Hamiltonian
approach[@key-8]. In this approach, one uses Hamiltonian dynamics to
describe the microscopic motion of the system. This involes explicit
inclusion of the reservoir of the system that is initially in a standard
thermodynamic ensemble. Any quantum mechanical descriptions of the
fluctuation theorems are invariably going to fall into this category, as
any non-Hamiltonian approaches will not be easily quantizable. This
approach seems very reasonable and intuitive, and is altogether the most
popular.

The original approach, that of Evans and Searles[@key-7], came from the
perspective of molecular simulations, for which modeling the reservoir
itself would be infeasible. A thermostatting mechanism is placed into
the equations of motion to replace the need to track a large number of
reservoir degrees of freedom. Hence it does not use pure Hamiltonian
dynamics and the resulting equations of motion are not phase space
preserving. It is this resulting phase space dilation that is of
interest.

A final approach is that of Gallavotti and Cohen, which comes from a
background of chaos theory[@key-11; @key-10]. They propose that
non-equilibrium statistical mechanics is best described by the concepts
and framework of chaos theory and propose what they call The Chaotic
Hypothesis, which is an analog of the Ergodic Hypothesis. From this they
derive of form of the fluctuation theorem. Their approach is easily to
most complicated in terms of mathematical framework, and thus much more
inaccessible to the average physicist, and will not be discussed further
in this paper.

It is interesting that these fluctuation theorems all seem to throwback
to the same fundamental considerations of reversibility that Carnot used
to found the subject of thermodynamics. This concept was refined by
Clausius into that of entropy, but since that time the emphasis of
statistical mechanics and the study of entropy has largely shifted over
to equilibrium scenarios and the probabilistic interpretation of
entropy. The fluctuation theorem is perhaps the current pinnacle of
combining these aspects of entropy.

Preliminaries
=============

Macroscopic Entropy
-------------------

What is entropy?

Short answer: no one is quite sure, but whatever it is, it's important.

The original thermodynamic definition of entropy is given by

$$\int\frac{dQ}{T}\le\Delta S$$

With equality holding for reversible processes,defining entropy as a
function of the state of the system (let's say the pressure and
temperature) up to an additive constant

However, this inequality has to be wrong.

The trouble lies in the fact that thermodynamic variables are a crass
description which describes the predictable and important qualitative
aspects of a large number of possible microscopic realizations of the
system. The modern consensus is that the time evolution of these
microscopic degrees of freedom ought to be Newtonian, consisting of a
collection of conservative forces describing the changes of positions
and velocities of the particles. These ordinary dynamics have a vital
symmetry of time reversal. We see no reason that an instantaneous flip
of all the velocities by some genie should change the measured
temperature and pressure of the system. Yet, if that is the case, this
flipped system will violate the entropy inequality just as assuredly and
the original complied with it, and then we have broken the second law of
thermodynamics by construction.

Time Reversal
-------------

The powerful physical concept that underlies the fluctuations theorems
is that of time reversal symmettry. From any path, one can form the time
conjugate path. If the path x goes from A at time 0 to B at time T, then
the conjugate path x\* follows the reverse trajectory, going from B at
time 0 to A at time T. In other words, if we film the path, we play the
film in reverse to see the time conjugate path. Transcribing words into
equations

$$x*(t)=x(T-t)$$

$$x*(0)=x(T-0)=x(T)=B$$

$$x*(T)=x(T-T)=x(0)=A$$

If we assume time reversal symmetry, the time conjugate path is an
allowable motion.

We can approach this from the action principle. If the original path is
an allowable motion, it will obey

$$\delta S=\int_{A}^{B}L(x+\delta x,\dot{x}+\delta\dot{x})-L(x,\dot{x})dt=0$$

Then if the conjugate path is also acceptable

$$\delta S=\int_{B}^{A}L(x*+\delta x*,\dot{x}*+\delta\dot{x}*)-L(x*,\dot{x}*)dt=0$$

This is the case if L is an even function of the velocities

Under this symmettry, the momenta flip their sign

$$\frac{\partial L}{\partial\dot{x}}=p=-\frac{\partial L}{\partial\dot{x}*}=-p*$$

A common and practically important caviat to time reversal symmetry that
deserves a short mention is the presence of a magnetic field. The
magnetic field couples in the Lagrangian with a term linear in the
velocity

$$L=e\vec{\dot{x}}\cdot\vec{A}$$

Unless we flip the sign of the magnetic field, the conjugate path is no
longer an acceptable motion. We can see this simply by looking at the
Lorentz force law and the right hand rule

$$F=ev\times B=-ev*\times B$$

However, had we included everything in our dynamics, including the
current producing the magnetic fields, time reversal would still hold.
The currents would flip in direction and produce the opposite valued
magnetic fields, just as we needed.

Probabilistic Entropy
---------------------

In a general probabilistic setting, entropy is a number that nicely
characterizes the unconcentrated-ness or mysteriousness of a probability
distribution.

$$S=-\sum p_{i}\ln p_{i}$$

Entropy is superior measure of concentration to the often used measure
of variance $\sigma$ in which calculates a width of the distribution. If
the probability is in many separate lumps, the entropy will add for the
lumps, whereas the variance will depend mostly more on the relative
separation of the lumps.

Two simple clarifying examples may help to give a feel for this
definition.

First, the certainty distribution where every probability is zero except
one

$$p_{i}=\delta_{i0}$$

$$S=-\sum\delta_{i0}\ln\delta_{i0}=-1\ln1=0$$

Since we know with exact certainty exactly what the outcome of the
distribution is, its

A completely uniform spread over N possibilities

$$p_{i}=\frac{1}{N}$$

$$S=-\sum_{i=1}^{N}\frac{1}{N}\ln\frac{1}{N}=\ln N$$

To demonstrate the practical application of entropy note that if instead
we had defined entropy using $\log_{2}$, this would correspond to the
number of bits necessary to select one of the possibilities out of all
of them ($2^{N}$ objects can be selected by N bits). If we pulled balls
from a hat in San Francisco and needed to communicate which ball we
pulled to New York, Entropy corresponds to the expected number of bits
needed to communicate the message. If we had only one kind of ball in
the hat, we'd need to send no message at all (0 bits). If we had N
different balls, we'd need to send $\log_{2}N$ bits to say which one we
picked. In a more intermediate case with a less uniform distribution, we
could pick a code where we could send a small number of bits for the
likely result and a larger number of bits if we pull the unlikely
result. Still, the entropy is bound on the average bits in the maximally
efficient message system.

In mechanics, we're going to what to put these probability distribution
on a continuous space, like phase space, and this introduces some slight
conceptual problems. The natural definition following

$$S=-\int\rho\ln\rho d\Gamma$$

Given the interpretation of entropy as number of bits needed to select
an object, how many bits are needed to select a point out of an infinite
continuum of points? Ultimately this definition is safe because phase
space is discrete thanks to quantum mechanics. Phase space is roughly
composed of cells of size $\hbar$, so we do not fall into this problem.

Jacobians
---------

The fundamental object of interest for the deterministic evolution of
entropy is the Jacobian matrix. We can imagine two very close points in
phase space and a vector between them. They will get carried along by
the time evolution of the system. This time evolution might shrink the
vector, expand it, or turn it, and one might expect that assuming the
points are sufficiently close to one another, there will be a linear
map, a matrix, that describes the mapping from the original separation
vector to the later one. This matrix is called the Jacobian
matrix[@key-12].

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
\end{array}\right]$$

$$=\left[\begin{array}{c}
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

Iterating the above equation and using the initial condition

$$J(0)=I$$

We get.

$$J(t)=(1+dtB(t-dt))\cdots(1+dtB(2dt))(1+dtB(dt))(1+dtB(0))$$

or for short

$$J(t)=T\{e^{\int_{0}^{t}Bdt}\}$$

T is the time ordering operation placing earlier factors of B to the
right, which is required since the B factors do not necessarily commute.

From the Jacobian matrix we can get the volume expansion factor. Given a
little box or parallelepiped with vectors $\vec{a}_{i}$ for edges, the
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

Because of this property of the Jacobian, it is the most vital object
needed for the study of deterministic entropy dynamics. This is opposed
to the typical approach to entropy, such as the Boltzmann equation. The
Boltzmann equation does not describe the evolution of a gas on its
entire phase space. It describes the probabilistic evolution of the
1-particle distribution function. It is quite natural that a system in
an uncertain state, evolving in an uncertain way will grow even more
uncertain. In comparison, a deterministic system will just carry its
distribution along with the flow. The entropy does not care about the
separation of lumps of probability or their location so just being
carried around will not change its value. What does change its value is
an interesting Jacobian that will squeeze certain sections of the
distribution and expand others. For conceptual purposes, one could
roughly equate this volume dilation factor to the local entropy
production

Liouville's Theorem
-------------------

Liouville's Theorem is the statement that in Hamiltonian phase space the
volume dilation factor is a constant factor 1 for all
time[@key-3; @key-5]. This theorem is of vital importance to equilibrium
statistical mechanics, as it helps guarantee that any distribution that
is a function of H only will be stationary, and lends credence to the
concept of a priori equal probiibility for phase space volumes, allowing
for the simple definition of the equilibrium statistical ensembles.
Hamiltonian dynamics generates the phase space velocities from the
Hamiltonian

$$\dot{q}=\frac{\partial H}{\partial p}$$

$$\dot{p}=-\frac{\partial H}{\partial q}$$

This is also true of all continuous canonical transformations which can
be characterized similarly by a generator G in place of H. Now we look
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
\end{array}\right]=(1+dt\frac{\partial^{2}H}{\partial p\partial q})(1-dt\frac{\partial^{2}H}{\partial p\partial q})-(dt\frac{\partial^{2}H}{\partial p^{2}})(-dt\frac{\partial^{2}H}{\partial q^{2}})$$

$$=1+dt(\frac{\partial^{2}H}{\partial p\partial q}-\frac{\partial^{2}H}{\partial p\partial q})+O(dt^{2})=1+O(dt^{2})$$

We see that to first order in time step, the volume dilation remains
constant, The fundamental step in this derivation being the equality of
the mixed partial derivative of H.

If we take the definition of entropy as

$$S=\int\prod_{i=1}^{N}dx_{i}dp_{i}\rho\ln\rho$$

and we look at its time evolution

$$\frac{\partial S}{\partial t}=\int\prod_{i=1}^{N}dx_{i}dp_{i}\partial_{t}\rho[\ln\rho+1]=0$$

But since

$$\int d\Gamma\rho=1$$

$$\int d\Gamma\partial_{t}\rho=\partial_{t}1=0$$

The material or streaming derivative gives the rate of change of an
expression as we follow it along a flow. It is defined as

$$\frac{DA}{Dt}=\partial_{t}A+\dot{\Gamma}\cdot\nabla_{\Gamma}A$$

Because we must have

$$\int d\Gamma\partial_{t}\rho=\int d\Gamma[\frac{D\rho}{Dt}-\dot{\Gamma}\cdot\nabla_{\Gamma}\rho]=0$$

We can integrate by parts to get

$$\frac{D\rho}{Dt}=-\rho\nabla_{\Gamma}\cdot\dot{\Gamma}$$

But because of Hamiltonian dynamics

$$\nabla_{\Gamma}\cdot\dot{\Gamma}=\sum_{i}\frac{\partial^{2}H}{\partial x_{i}\partial p_{i}}-\frac{\partial^{2}H}{\partial x_{i}\partial p_{i}}=0$$

This is another restatement of Liouville's theorem

Hence

$$\frac{\partial S}{\partial t}=\int\prod_{i=1}^{N}dx_{i}dp_{i}\partial_{t}\rho\ln\rho=\int\prod_{i=1}^{N}dx_{i}dp_{i}(\frac{D\rho}{Dt}-\dot{\Gamma}\cdot\nabla_{\Gamma}\rho)\ln\rho$$

$$=\int\prod_{i=1}^{N}dx_{i}dp_{i}(-\dot{\Gamma}\cdot\nabla_{\Gamma}\rho)\ln\rho=\int\prod_{i=1}^{N}dx_{i}dp_{i}\rho\nabla_{\Gamma}\cdot(\dot{\Gamma}\ln\rho)=\int\prod_{i=1}^{N}dx_{i}dp_{i}\dot{\Gamma}\cdot\nabla_{\Gamma}\rho$$

$$=-\int\prod_{i=1}^{N}dx_{i}dp_{i}\rho\nabla_{\Gamma}\cdot\dot{\Gamma}=0$$

Liouville's theorem tells us that the flow of the exact probability
distribution changes its shape, but not its concentration. The
probablistic entropy is a measure of that concentration, so it cannot
change.

Hamiltonian Fluctuation Relations
=================================

A Version of the Fluctuation Relation
-------------------------------------

This is the program. We will take a large reservoir system which we will
call Y in a canonical ensemble and put it into dynamical contact with a
system of interest in a particular state A. We will use the macroscopic
definition of entropy

$$\Delta S=\frac{\Delta Q}{T_{res}}=\frac{\Delta H(Y)}{T}$$

We will then compare the relative probabilities of a evolution compared
to its time reversed evolution. We find that the relative probabilities
$$\frac{P(A\rightarrow B,\Delta S)}{P(B*\rightarrow A*,-\Delta S)}=e^{\frac{\Delta S}{k_{B}}}$$

To prove this is simple, using time reversal symmettry. The numerator is
composed of a sum of factors

$$Numerator=\sum\frac{1}{Z}e^{-\beta H(Y_{0})}d\Gamma_{0}$$

This sum will be restricted to only those values of $Y_{0}$ that evolve
according to the requirements of taking the system of interest from A to
B and resulting in a reservoir entropy change $\Delta S$. There will be
exactly one corresponding time reversed term in denominator sum to each
term in the numerator sum, thanks to the one-to-one nature of the time
reversal mapping.

$$Denominator=\sum\frac{1}{Z}e^{-\beta H(Y_{0}*)}d\Gamma_{0}*$$

Where $$Y_{0}*=(x_{0}*,p_{0}*)=(x_{f},-p_{f})=Y_{f}$$

and thanks to Liouville's theorem

$$d\Gamma*=d\Gamma_{f}=d\Gamma_{0}$$

$$H(Y_{0}*)=H(Y_{f})=H(Y_{0})+T\Delta S=H(Y_{f}*)+T\Delta S$$

We can pull out the common factor of $k_{B}\Delta S$ in the denominator
sum and cancel the sums to achieve our result

$$\frac{P(A\rightarrow B,\Delta S)}{P(B*\rightarrow A*,-\Delta S)}=\frac{\sum\frac{1}{Z}e^{-\beta H(Y_{0})}d\Gamma_{0}}{\sum\frac{1}{Z}e^{-\beta H(Y_{0}*)}d\Gamma_{0}*}$$

$$=\frac{\sum\frac{1}{Z}e^{-\beta H(Y_{0})}d\Gamma_{0}}{e^{-\frac{\Delta S}{k_{B}}}\sum\frac{1}{Z}e^{-\beta H(Y_{f}*)}d\Gamma_{0}*}=\frac{\sum\frac{1}{Z}e^{-\beta H(Y_{0})}d\Gamma_{0}}{e^{-\frac{\Delta S}{k_{B}}}\sum\frac{1}{Z}e^{-\beta H(Y_{0})}d\Gamma_{0}}=e^{\frac{\Delta S}{k_{B}}}$$

Jarzynski's Equality
--------------------

A common form for the statement of the irreversibility for constant
temperature reservoir processes in thermodynamics is

$$Q\le T_{R}\Delta S$$

Where T is the temperature of the reservoir and $\Delta S$ is the change
of the systems entropy. There is a simple inequality that can be found
for the work possible in a constant temperature environment.

$$W=\Delta E-Q\le\Delta E-T\Delta S$$

Defining the Helmholtz free energy as

$$F=E-TS$$

We get the inequality

$$W\le\Delta F)_{T_{R}}$$

with equality holding for perfectly reversible processes.

Jarzynski found the equivalent statistical statement of this law

$$<e^{-\frac{W}{k_{B}T}}>=e^{-\frac{\Delta F}{k_{B}T}}$$

This fluctuation theorem is independent of the manner in which the work
was carried out.

W may derive it by creating a Hamiltonian that has an explicit time
dependance due to an external parameter[@key-9]

$$H(\Gamma,t)$$

We define the work done on the system by

$$W(\Gamma_{0})=H(\Gamma_{f},t)-H(\Gamma_{0},0)$$

Now we can evaluate the left hand side of the theorem

$$<e^{-\beta W}>=\frac{1}{Z}\int d\Gamma_{0}e^{\beta H(\Gamma_{0},0)}e^{-\beta[H(\Gamma_{f}(\Gamma_{0}),t)-H(\Gamma_{0},0)]}=\frac{1}{Z}\int d\Gamma_{0}e^{-H(\Gamma_{t}(\Gamma_{0}),t)}$$

In a Hamiltonian System, Liouville's theorem still holds so the Jacobian

$$\frac{\partial\Gamma_{f}}{\partial\Gamma_{0}}=\det J=1$$

$$<e^{-\beta W}>=\frac{1}{Z_{0}}\int d\Gamma_{t}e^{-\beta H(\Gamma_{t},t)}=\frac{Z_{f}}{Z_{0}}$$

$$Z=e^{\beta F}$$

Giving us our final result

$$<e^{-\frac{W}{k_{B}T}}>=e^{-\frac{\Delta F}{k_{B}T}}$$

That was so easy, it feels like we're cheating.

Thermostatted Approach of Evans and Searles
===========================================

Thermostats
-----------

A difficulty of understanding the dynamics of thermodynamic quantities
is the fact that the dynamics depend on the surroundings. The physical
thermostat or thermal reservoir is a big hot rock that we put in contact
with our system, giving or removing energy in a manner such that certain
averages and temperatures are maintained. In equilibrium statistical
mechanics this is difficulty is avoided because whatever the mechanism
that an average temperature is maintained, the important fact is that
the temperature is maintained at all. If this was not the case,
thermodynamics would not be a general theory, as every means of
maintaining temperature would require a new analysis. In
Non-equilibrium, we lose this universality to some degree.

The thermostat is a technical device for maintaining constant
temperature for completely deterministic systems which was invented for
the purposes of molecular simulations[@key-6; @key-4]. It explicitly
breaks the incompressible Liouvillian behavior of the system and allows
a steady state to be simply achieved in a forced system during
simulation.

There are a number of ways of achieving this. One of the original
methods used is the Anderson Thermostat. This is a stochastic thermostat
which occasionally randomly selects a particle and changes its momentum
to one taken out of the Maxwell-Boltzmann distribution. This thermostat
is not reversible or deterministic however and difficult to analyze.

A deterministic way of controlling the Kinetic energy would be to change
the rate of time flow. Imagine watching a bunch of energy conservative
billiard balls in a movie, getting kicked around by cues. Every time a
cue hits a ball, it'll increase or decrease its energy. However if a
little man behind a curtain controls the payback speed, he could slow
down the film every time the cue would increase the kinetic energy is or
speed it up if it is decreased. The Potential energy of the system would
be unchanged since it is only position dependent and thus independent of
playback speed. The playback speed is an extra dynamical variable used
to keep the kinetic energy roughly constant. This is method is known
Nose-Hoover thermostat.

A large class of thermostats can be constructed by Gauss Principle of
Least Constraint.

Gauss' Principle of Least Constraint
------------------------------------

Gauss' Principle of Least Constraint allows the easy construction of a
thermostat in order to deterministically satisfy a general
constraint[@key-2; @key-4]. The constraints that a thermostat uses are
extremely nasty ones, like keeping kinetic energy a constant. Lagrangian
mechanics handles pulley and gear type (relations between coordinates)
constraints admirably, but try to imagine a system of pulleys and gears
that could enforce the isokinetic constraint. So we can't use Lagrangian
mechanics. Instead, people turned to ad hoc methods, which ended up
being equivalent to Gauss' Principle of Least Constraint. Exactly
because of its excessive power and versatility, Gauss' Principle is
perhaps a little silly. A really good fundamental system of mechanics
should not allow the construction of equations of motion for unphysical
and contrived constraints. I think the best that can be said about the
resulting equations is that they are minimally unreasonable in a sense.
This mathematical thermostat should not be considered to get any of its
validity from attaching itself to the illustrious name of Gauss, but
instead because it is convenient and seems to work.

Note that it would be tempting to call the energy constraints
dissipative, but this would be misleading since they may also pump
energy to the system. The effect of the extra force derived from the
method is that when the external work-like force bumps the system
locally, the constraint sucks from or injects to the system the
equivalent amount of energy.

The principle is to compute the lost force

$$Z=\sum m_{i}(\ddot{x}_{i}-\frac{F_{i}}{m_{i}})^{2}$$

Then we minimize with respect to $\ddot{x}$ in a manner consistent with
the constraint, keeping the current positions and velocities fixed. This
is reasonable on account that in the absence of constraints, $Z=0$ is a
possibility and we get the usual $F=ma$.

For example, we can introduce the isokinetic constraint

$$\phi(x_{i},\dot{x_{i}})=\sum_{i}\frac{1}{2}m_{i}\dot{x}_{i}^{2}-K=0$$

Differentiating this equation once with respect to time gives the
constraint in terms of the acceleration

$$\sum_{i}m_{i}\dot{x}_{i}\ddot{x}_{i}=0$$

We now minimize Z with the method of Lagrange multipliers

$$Z=\frac{1}{2}\sum_{i}m_{i}(\ddot{x}_{i}-\frac{F_{i}}{m_{i}})^{2}+\lambda\sum_{i}m_{i}\dot{x}_{i}\ddot{x}_{i}$$

$$\frac{\partial Z}{\partial\ddot{x_{i}}}=0=m_{i}\ddot{x}_{i}-F_{i}+\lambda m_{i}\dot{x}_{i}$$

We may solve for $\lambda$by going back to the constraint equation

$$\sum_{i}m_{i}\dot{x}_{i}\ddot{x}_{i}=\sum_{i}m_{i}\dot{x}_{i}(\frac{F_{i}}{m_{i}}-\lambda\dot{x}_{i})=0$$

$$\lambda=\frac{\sum_{i}F_{i}\dot{x}_{i}}{\sum_{i}m_{i}\dot{x}_{i}^{2}}$$

Now we have a system that will deterministically maintain its kinetic
energy, at the cost of some complication and a little realism. If one
considers that the net effect of the reservoir is to maintain a
temperature and if both our artificial method and the actual situation
do this subtly, one may hope that results calculated in different ways
will coincide..

Evans and Searles Transient Fluctuation Theorem
-----------------------------------------------

We could follow a packet of probability from an initial time to a final
time. Let's say that the bit had an initial probability density $f_{0}$
at position $\Gamma_{1}$ which evolves to a final probability density
$f_{f}$ value at $\Gamma_{2}$. The total probability in the little
packet is unchanged by the evolution

$$f_{0}d\Gamma_{0}=f_{f}d\Gamma_{f}$$

But as we have seen, these Non-Liouvillian dynamics have a phase space
volume expansion factor

$$d\Gamma_{f}=d\Gamma_{0}\det J$$

Hence the densities at corresponding positions are related by

$$f_{0}=f_{f}\det J$$

The entropy produced due to this hunk of probability as a function of
$\Gamma_{0}$is given by

$$\Delta dS=f_{f}\ln f_{f}d\Gamma_{f}-f_{0}\ln f_{0}d\Gamma_{0}=f_{0}d\Gamma_{0}\ln\frac{f_{f}}{f_{0}}=-f_{0}d\Gamma_{0}\ln\det J$$

One issue with just looking at the expectation of $-\ln\det J$ like
this, is that even for a steady state distribution, this function is not
locally zero, even though the integral of the change in entropy must be.
A useful quantity of interest is instead the dissipation function,
defined as

$$\bar{\Omega}_{t}t=\ln\frac{f_{0}(\Gamma_{1})}{f_{0}(\Gamma_{2})}-\ln\det J$$

Where again $\Gamma_{2}$ is the endpoint of the path that starts at
$\Gamma_{1}$ and $f_{0}$ is the initial distribution. For a steady state
distribution

$$f_{0}=f_{f}$$

So

$$\Omega=\bar{\Omega}_{t}t=\ln\frac{f_{0}(\Gamma_{1})}{f_{f}(\Gamma_{2})}-\ln\det J=\ln\det J-\ln\det J=0$$

The Evans and Searles Transient Fluctuation Theorem is about the
probabilities of getting values of this function $\bar{\Omega}_{t}t$

$$\ln\frac{Prob(\bar{\Omega}_{t}=A)}{Prob(\bar{\Omega}_{t}=-A)}=\ln\frac{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f(\Gamma)d\Gamma}{\sum_{\bar{\Omega}_{t}(\Gamma)=-A}f(\Gamma)d\Gamma}$$

Now we use the idea of time reversal symmetry. $\Gamma*$is the time
reversed starting point. It is equal to $\Gamma_{2}$ except the signs
have been flipped on the momentum so that the phase point will move
backwards. $d\Gamma*=d\Gamma_{2}$

$$d\Gamma*=d\Gamma\det J$$

If $\Gamma$ produces dissipation A, then $\Gamma*$ will produce
dissipation -A

$$=\ln\frac{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma)d\Gamma}{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma*)d\Gamma*}$$

Replacing the volume element and multiplying by a factor of
$1=\frac{f_{0}(\Gamma)}{f_{0}(\Gamma)}$

$$=\ln\frac{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma)d\Gamma}{\sum_{\bar{\Omega}_{t}(\Gamma)=A}\frac{f_{0}(\Gamma*)}{f_{0}(\Gamma)}f_{0}(\Gamma)\det Jd\Gamma}$$

Now the bottom looks like the expectation value of
$e^{-\bar{\Omega}_{t}t}$.

$$=\ln\frac{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma)d\Gamma}{\sum_{\bar{\Omega}_{t}(\Gamma)=A}e^{-\bar{\Omega}_{t}t}f_{0}(\Gamma)d\Gamma}$$

Since we are only summing over those values where
$e^{-\bar{\Omega}_{t}t}=e^{-At}$, we can bring it outside the sum and
logarithm

$$=At\ln\frac{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma)d\Gamma}{\sum_{\bar{\Omega}_{t}(\Gamma)=A}f_{0}(\Gamma)d\Gamma}=At$$

Conclusion
==========

Results in Nonequilbirum Statistical Mechanics have largely remained
elusive. There have been a few high points in the theory of
nonequilbirum: The Onsager reciprocal relations, The Einstein relation,
the Nyquist fluctuation-dissipation theorem, and the Green-Kubo
relations. All have required the assumption of being near thermodynamic
equilibrium in some sense, however the principles of thermodynamics
state that the entropy always increases regardless of how near
equilibrium one is and it would be nice to have some semblance of a
theory predicting how and why this occurs in a quantifiable way. This
new crop of results under the heading of fluctuation theorems claim
validity in these far out of equilibrium regions and add perhaps a touch
of clarity to how irreversible behavior can result in bulk from
reversible dynamics. Boltzmann was never able to quite quash the famous
objections of Loschmidt entirely satisfactorily as the how macroscopic
irreversible entropy production could result from microscopic reversible
dynamics. These new theorems focus on the concept that the second law is
only statistically valid, and produce a surprisingly simple estimate of
the relative probability that an amount of entropy is produced during a
process.

10 A. Sommerfeld, Mechanics (Levant Books, Kolkata, 2003).

M. Kardar, Statistical Physics of Particles (Cambridge University Press,
Cambridge, 2011).

D.J. Evans, G.P. Morriss, Statistical Mechanics of Nonequilibrium
Liquids (ANU E Press, 2007).

H. Goldstein, Classical Mechanics (Addison-Wesley Press Inc, 1951)

Y. Zhao, A Brief Introduction to Thermostats,
http://www.math.ucsd.edu/\~y1zhao/ResearchNotes/ResearchNote007Thermostat.pdf

D.J. Evans, Debra Searles, The Fluctuation Theorem (Advances in Physics,
2002, Vol. 51, No. 7, 1529).

C. Jarzynski, "Hamiltonian derivation of a detailed fluctuation
theorem", cond-mat/9908286

M Tuckerman, Jarzynski's equality and nonequilibrium methods,
http://www.nyu.edu/classes/tuckerman/stat.mechII/lectures/lecture\_9/node4.html

G. Gallavotti, Statistical Mechanics: Short Treatise, (Springer 1998).

G. Gallavotti, E.G.D. Cohen, Dynamical Ensembles in Nonequilbrium
Mechanics, (Physical Review Letters, 1995, Vol. 74 No. 14).

P. Cvitanovic', R. Artuso, R. Mainieri, G. Tanner and G. Vattay, Chaos:
Classical and Quantum, ChaosBook.org (Niels Bohr Institute, Copenhagen
2009).

D Cohen, Y Imry, Straightforward quantum-mechanical derivation of the
Crooks fluctuation theorem and the Jarzynski equality, (Phys. Rev. E 86,
011111 (2012))
