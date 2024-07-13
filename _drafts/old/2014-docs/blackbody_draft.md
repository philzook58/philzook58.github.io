The World is Wiggly
===================

It comes as a great shock when you first hear it, but the entire world
around is wriggling. Even a the deepest ice of the Antartic, or a hunk
of rock isolated in the farthest reaches of space, is wiggling. This is
unavoidable. To exist is to wiggle.

Now, I'm not talking about quantum mechanics. It's obvious to anyone
with any common sense that is just a bunch of made up stories and I will
refuse to acknowledge its existance for the rest of this document. I'm
talking the real McCoy.

Thermodynamics, baby.

Now, these wiggles are so slight compared to the magnitudes of ordinary
existence, meaning things larger than fleas.The bulk movement of big
stuff in the short term are unaffected. And yet, they're there. So let's
look at them.

Johnson Noise: Audiophile's Nightmare, Thermodynamicist's Dreamboat
===================================================================

$$V=IR$$

This relation is known as Ohm's Law. IT IS COMPLICATED.

Despite being discovered early, and the extreme simplicity of its form,
its microscopic origins are deep.

In elementary electrical circuit theory, you are taught how to deal with
idealized circuit elements. Voltage sources, current sources, resistors,
capacitors, and inductors. You go into the electronics lab, build up
these circuits, and gosh darn it if they don't work basically perfectly,
and you feel pretty smug. Well, if you really really believe that, you
got the wool pulled over your eyes, bucko. Those things are designed to
work how the simple theory says they should and your teachers only asked
you to inspect their operations in the regimes and resolutions of time,
space, and voltage that they knew they would work just like they said.

The Transmission Line
---------------------

The transmission line is the next step of complication above the
idealized circuit element. It also is the perfect realizable one
dimensional wave system. You can model the transmission line as a
sequence of very very many, very very small capacitors and inductors.
After years of indoctrination in circuit diagrams, this is the view an
electrical engineer would be most comfortable with. You can also view it
from the top down. A physicist might prefer imagining the entirety of
Maxwell's equations, and then throwing out two of the three spatial
dimensions as an approximation. Whatever floats your boat.

Look at a tiny bit of wire with length $dx$. Between the two lengths of
wire there is a bit of capacitance $dC$. Any two disconnected hunks of
metals that are put real close together have a non-negligible
capacitance between them. Although the wire in regular inductors are all
spiraled up to increase their inductance to more useful levels, current
flowing through a lone piece of wire will produce a magnetic field, and
thus store energy in this magnetic field. So the tiny bit of wire has an
inductance $dL$. We could also consider the resistance of the wire. I
choose to ignore this for our purposes, but it would lead to dissipation
along the line in addition to wave propagation. Also, It is often a
neglible in application.

The connecting equations are then

$$V(x+dx)-V(x)=dL\,\frac{dI(x)}{dt}\Rightarrow\frac{\partial}{\partial x}V=\frac{dL}{dx}\frac{\partial}{\partial t}I$$

$$I(x+dx)-I(x)=dC\,\frac{dV(x)}{dt}\Rightarrow\frac{\partial}{\partial x}I=\frac{dC}{dx}\frac{\partial}{\partial t}V$$

We can combine these to get

$$(\frac{1}{c^{2}}\frac{\partial^{2}}{\partial t^{2}}-\frac{\partial^{2}}{\partial x^{2}})V(t,x)=0$$

So long story short, you get a wave equation with a wave speed of
$$c=\frac{1}{\sqrt{\frac{dL}{dx}\frac{dC}{dx}}}$$

We can specify boundary conditions by placing idealized circuit elements
at the ends. They will correspond to various conditions connecting the
time derivatives and the values of V at the endpoints. The most
interesting boundary conditions are the open circuit, which corresponds
to homogenous Neumann boundary conditions in the voltage and Dirichlet
in the current

$$I(L)=0\Rightarrow\frac{\partial}{\partial x}V(L)=\frac{dL}{dx}\frac{\partial}{\partial t}I(L)=0$$

And the short circuit, which is the flipside.

$$V(L)=0\Rightarrow\frac{\partial}{\partial x}I(L)=\frac{dC}{dx}\frac{\partial}{\partial t}V(L)=0$$

Finally the no reflection or matched load boundary condition

$$R=\sqrt{\frac{\frac{dL}{dx}}{\frac{dC}{dx}}}$$

When this condition is satisfied, the end load looks just like another
piece of transmission line to the incoming wave, so the entirety of the
energy in the line is absorbed by the load.

The energy in the transmission line is

$$H=\int\frac{1}{2}\frac{dC}{dx}V^{2}+\frac{1}{2}\frac{dL}{dx}I^{2}dx$$

If we put a short circuit at each end of a transmission line with length
d, we can expand the solution to the voltage as a Fourier sine series

$$V(x,t)=\sqrt{\frac{2}{d}}\sum_{n=1}^{\infty}a_{n}(t)\sin(\frac{n\pi x}{d})$$

We go back to the relations connecting voltage and current to find

$$\frac{\partial}{\partial x}I=\frac{dC}{dx}\frac{\partial}{\partial t}V$$

$$\frac{\partial}{\partial x}I(x,t)=\frac{dC}{dx}\sqrt{\frac{2}{d}}\sum_{n=1}^{\infty}\dot{a_{n}}(t)\sin(\frac{n\pi x}{d})$$

Integrating this expression gives

$$I(x,t)=-\frac{dC}{dx}\sqrt{\frac{2}{d}}\sum_{n=1}^{\infty}\frac{d}{n\pi}\dot{a_{n}}(t)\cos(\frac{n\pi x}{d})+B$$

B is a constant current that will not be interesting for our purposes,
so we set it to zero.

The expression for energy reduces considerably using the orthogonality
of the Sines and Cosine functions

$$H=\frac{1}{2}\frac{dC}{dx}\sum_{n=1}^{\infty}(|a_{n}|^{2}+\frac{|\dot{a}_{n}|^{2}}{\omega_{n}^{2}})$$

$$\frac{dL}{dx}(\frac{dC}{dx})^{2}(\frac{d}{n\pi})^{2}=\frac{dC}{dx}(\frac{d}{cn\pi})^{2}=\frac{dC}{dx}\frac{1}{\omega_{n}}$$

$$\omega_{n}=ck_{n}=c\frac{n\pi}{d}=\frac{n\pi}{d\sqrt{\frac{dL}{dx}\frac{dC}{dx}}}$$

Although ugly, we see that this is a sequence of uncoupled harmonic
oscillators oscillating at frequency$\omega_{n}$, which according to the
equipartition theorem should each possess on average $k_{B}T$ of thermal
energy.

$$H=\sum_{n=1}^{\infty}k_{B}T=\int\frac{c\pi k_{B}Td\omega}{L}$$

A short note: The infinity in the upper bound of that sum is ridiculous
and I should really never have included it. The transmission line
approximation only works down to wavelengths that are slightly larger
than the cross-sectional dimensions of the line, which may happen when
the sum reaches $n=1000$ or some large number. Further down, the model
becomes invalid.

Resistors and Johnson Noise
---------------------------

Consider the following ridiculous arrangement

We place the end of our circuit in a constant magnetic field. We attach
a conducting sliding bar to a spring at thermal equilibrium to complete
a circuit to a resistor. Now, nothing happens.

Then we look closer. We find the spring is wiggling. Huh. In fact, we
find that a particular location and velocity occur with a Boltzmann
probability

$$P(x,v)=\frac{m\omega}{2\pi kT}e^{-\frac{mv^{2}}{2k_{b}T}-\frac{m\omega^{2}x^{2}}{2k_{b}T}}$$

What's more, we set this thing up so that when the bar moves, there is
an EMF around the circuit

$$EMF=\frac{d\Phi}{dt}=Blv$$

Oh, but the average EMF given by the bar is zero. That's boring.

Wait! The power delivered to the resistor is

$$P=\frac{V^{2}}{R}=\frac{(Blv)^{2}}{R}$$

Holy smokes! The average value of that is

$$<\frac{(Blv)^{2}}{R}>=\frac{(Blk_{b}T)^{2}}{m^{2}R}$$

Now if we put the resistor in a bath of a higher temperature, we
spontaneously are taking heat from a lower temperature reservoir to a
higher one. That can't be good.

The solution to this paradox is that the electrons in the resistor are
wiggling and will spontaneously polarize the resistor very slightly,
which will balance out the power put into the resistor by pushing power
back into the bar.

Imagine another scenario with two resistor back to back. Suppose
resistor 2 spontaneously generates a voltage $V_{2}$. Using the voltage
divider law, the power delivered to resistor 1 is

$$P_{1}=(\frac{V_{2}}{R_{1}+R_{2}})^{2}R_{1}$$

Vice versa,

$$P_{2}=(\frac{V_{1}}{R_{1}+R_{2}})^{2}R_{2}$$

However, these two power deliveries should balance if the resistors are
at the same temperature or we have a spontaneous generation of a
temperature difference.

$$(\frac{V_{2}}{R_{1}+R_{2}})^{2}R_{1}=(\frac{V_{1}}{R_{1}+R_{2}})^{2}R_{2}\Rightarrow\frac{V_{2}^{2}}{R_{2}}=\frac{V_{1}^{2}}{R_{1}}=f(T)$$

Since the resistors are arbitrarily sized, $f(T)$ must be universal.
What's more, we can place a lossless frequency dependent filter between
the two resistors to see that they must match in each individual
frequency range.

We can connect the resistors to a matched transmission line to determine
$f(T,\nu)$

$$E(d\nu)=\frac{2d}{c}k_{B}Td\nu$$

The time it takes for a wave train to travel the entire transmission
line is

$$T=\frac{d}{c}$$

So the average power from one resistor must be

$$P(d\nu)=k_{B}Td\nu$$

As before, the resistor generates a time averaged power which it will
push through the line

$$P=(\frac{VR}{2R})^{2}\frac{1}{R}=\frac{V^{2}}{4R}$$

Here V has become a root mean square voltage, which I use to comply with
convention.

To match the two powers gives

$$V^{2}=4Rk_{B}Td\nu$$

This is the Nyquist formula for thermal noise.

The Standard Derivation
=======================

Although my explanation may not do it justice, the thermal noise in
transmission lines is essentially blackbody radiation, a subject of
study that has been a goldmine for physics. Blackbody radiation is the
red glow off a hot poker. We understand electromagnetism pretty well
these days, so one would expect we should be able to derive any
phenomenon it presents to us from first principles.

In statistical mechanics, we have a black box. We say "I know how big
this box is. I know how much pressure this box is pushing out with. I
can tell when energy goes into this box. I know the rough mechanics that
the objects in the box are obeying, but really, I do not care about the
details, I just want the big picture." In other words, we are agnostic
about the detailed state of the internals of the box. We then ask, how
many states could the box be in and still satisfy everything known about
it (i.e. the temperature, internal energy, pressure, etc.)? We count up
the states, take the log, slap on a constant and call this number the
entropy. It turns out that this is a very important number.

What is a state? A definition is that is a hunk of canonical phase
space, which consists of generalized coordinates and momenta. Phase
space seems to mean something. Liouville's theorem guarantees that phase
space is incompressible, suggesting that such a definition isn't as
arbitrary as others might be. In order to use this definition, your
system must be phrased in the language of Hamiltonian dynamics.

To start off, we need the Lagrangian for the field. The Lagrangian
fomulation of mechanics is a thing of beauty. It has clean lines and
elegant expressions, and throughout history has been found to be
philosophically satisfying. However we've got work to do, so we must
send it to the butcher shop to be hacked into the hunks of gristly
pieces that is the Hamiltonian formulation.

$$$$

The Lagrangian formulation only works because of an interplay of
coordinates and their velocities. With just the E and B fields , there
are no derivatives and no trade off. The field for which the action is
stationary is quite simple

$$E=0$$

$$B=0$$

The vector potential is a necessity for an action formulation

What we see when we look at the world with a discerning eye is a bunch
of charges wiggling about. We notice that the wiggles have a definite
relation to one another. Through the tireless experimentation of our
forebears, we deduce the existence of the electric and magnetic field.
These are objects we can feel in our gut. The electric field is a yank,
the magnetic field is a twist. We can with practice easily imagine the
consequences of there existance. We have a tendency to start with the
gut and end with the head. Newton's laws of yanking gave way to
formalisms twice as algebraically and conecptually powerful, and three
times as abstract. SO too comes the four-potential, an object more
abstract than the bare Electric and Magnetic fields, and yet perhaps
more poweful. The biggest trouble with the extra layers of abstraction
is the ambiguity of their definition. A force is an obvious thing. It is
what it is. The measure it with a scale and that's the end of the
discussion. A potential is more subtle. Only its derivative is truly
important, intorucing an ambiguity of an overall constant. Still, it is
a very evocative idea, the valleys and cliffs of its graph connecting in
our brains with the forces felt at the edges of real valleys and cliffs.
The four-potential is not so lucky. it is ambiguously defined up to
something we call a gauge transforamtion, an transformation of sufficent
complexity and variety to make 2 equivalent 4-potentials appear
initially unrelated.

In statics, the electric potential and the vector potential are directly
related to the energy in the field.

The gauge invariance of the 4-potential enforces charge conservation.

The extra degree of freedom is a lagrange multiplier of sorts - The
lagrange multiplier that enforces charge conservation. So the gauge
field is a measure of how pissed off your theory is by the contraint of
charge conservation.

I believe it is everyone's first inclination that the method of lagrange
multipliers is cockamamie. Why introduce another variable when we
already have too many? Gosh darn it if it doesn't work like a charm.

If you pulled a completely random solution for 2 vector fields out of a
hat, they would not in general satisfy Maxwell's equations, and thus
they could not be possible states of the inside of your box.

We introduce the vector potential to automatically satisfy 2 of
maxwell's equations by definition. This is analogous to Restricting the
movement of a particle to the surface of a sphere by introducing polar
coordinates, considering two of Maxwell's equations (specifically
$\nabla\cdot B=0$ and $\nabla\times E=-\frac{\partial B}{\partial t}$)
to be kinematical equations and not dynamical ones. The distinction
between the kinematics and dynamics of fields is much blurrier than that
of simple particle mechanics, akin the line blurring that occurs between
that of space and time. However this process is not complete. There
still remains a degree of arbitrariness, the gauge.

The Dirac Bracket. The poisson bracket is capable of generating
constants of motion. They are not guaranteed to exhuast the complete
list, but given one, you may poisson bracket it with other constants of
motion to possibly generate further constants of motion. So it goes with
the dirac bracket and contraints. Since you enforce a contraint to be a
constant of moition (The contraint is identically enforced for all
times), it is somewhat intuitive that the bracket of contraints with
other contraintds egnerate further contraints (perhaps less obious ones)
necessary for the consitancy of your equations of motion.

There is a deep similiarty between constants of motion and constraints.
Noether's? What would that be? That something something symmettry
implies contraints? the lagrange multiplier variable has a symmettry
that its time derivative appears no where. very unusual. Is that the
charecteristic of a contraint?

Lorentz boost the crap out of a vector field. Does it gain gauge
invariance? I feel it must. The proca field is not necessarily
relativistic and is not gauge invariant.

Planck's derivation

Consider the following system, corresponding to a one dimensional string
bound to zero at its endpoints

$$(\frac{1}{c^{2}}\frac{\partial^{2}}{\partial t^{2}}-\frac{\partial^{2}}{\partial x^{2}})g(t,x)=\hat{L}g=0$$

$$g(t,0)=0$$

$$g(t,L)=0$$

We can Fourier transform the time derivative into a constant leaving

$$(\frac{-\omega^{2}}{c^{2}}-\frac{\partial^{2}}{\partial x^{2}})g(\omega,x)=0$$

Furthermore, we may expand the solution into a fourier series in x,
which may be familiar from the infinite square well in Qunatum Mechanics
and other places

$$g_{n}(\omega,x)=\sqrt{\frac{2}{L}}\sin(\frac{n\pi x}{L})$$

$$n=1,2,3\ldots$$

$$k_{n}=\frac{n\pi}{L}$$

$$g(t,x)=\sum_{n=1}^{\infty}a_{n}(t)\sqrt{\frac{2}{L}}\sin(\frac{n\pi x}{L})$$

$$(\frac{\omega^{2}}{c^{2}}-k_{n}^{2})g_{n}(\omega,x)=0$$

$$\sum_{n=1}^{\infty}(\frac{1}{c^{2}}\ddot{a}_{n}(t)+k_{n}^{2}a(t))\sqrt{\frac{2}{L}}\sin(k_{n}x)=0$$

This is satisfied if

$$\frac{1}{c^{2}}\ddot{a}_{n}(t)+k_{n}^{2}a(t)=0$$

The solution of which is oscillating exponentials

$$a_{n}(t)=a_{n}(0)e^{\pm i\omega_{n}^{2}t}$$

$$\omega_{n}=ck_{n}$$

$$Re(a_{n})=\int_{0}^{L}\sqrt{\frac{2}{L}}\sin(k_{n}x)g(0,x)dx$$

$$Im(a_{n})=\int_{0}^{L}\sqrt{\frac{2}{L}}\sin(k_{n}x)\dot{g}(0,x)dx$$

or in other words

$$a_{n}=\int_{0}^{L}\sqrt{\frac{2}{L}}\sin(k_{n}x)(g(0,x)+i\omega_{n}\dot{g}(0,x))dx$$

Because our fields are all real, this restricts our use of the negative
and positive freqeuncy solutions such that the constants out front have
to be complex conjugates of one another. To alleviate this notational
burden, we will use only the negative frequency.

The energy of this string is a combination of kinetic and potential
energy terms

$$H=\int_{0}^{L}\frac{1}{2}(\frac{1}{c^{2}}\dot{g}^{2}+g^{2})dx$$

If we place our decomposition of the fields into this definition and use
the orthogonality of the sine function

$$\int_{0}^{L}\frac{2}{L}\sin(k_{n}x)\sin(k_{m}x)dx=\delta_{nm}$$

We get the result

$$H=\sum_{n=1}^{\infty}\omega_{n}|a_{n}|^{2}$$

The pressure on the edges of the box

All of this derivation is very easily taken tohigher dimensional spaces
and fields. For vector fields, we promote the coeffcients $a_{n}$to
vectors $\vec{a_{n}}$. For higher dimension spaces, we replace the one
dimensional fourier series

$$g(t,x)=\sum_{n=1}^{\infty}a_{n}(t)\sqrt{\frac{2}{L}}\sin(\frac{n\pi x}{L})\Rightarrow g(t,x,y,z)=\sum_{l=1}^{\infty}\sum_{m=1}^{\infty}\sum_{n=1}^{\infty}a_{lmn}(t)\sqrt{\frac{8}{L_{x}L_{y}L_{z}}}\sin(\frac{l\pi x}{L_{x}})\sin(\frac{m\pi y}{L_{y}})\sin(\frac{n\pi z}{L_{z}})$$

$$k_{n}=\frac{n\pi}{L}\Rightarrow\vec{k}_{lmn}=(\frac{l\pi}{L_{x}},\frac{m\pi}{L_{y}},\frac{n\pi}{L_{z}})$$

The whole point behind this entire discussion was the vector potential

$$\vec{A}=\sum_{l=1}^{\infty}\sum_{m=1}^{\infty}\sum_{n=1}^{\infty}\vec{a}_{lmn}(t)\sqrt{\frac{8}{L_{x}L_{y}L_{z}}}\sin(\frac{l\pi x}{L_{x}})\sin(\frac{m\pi y}{L_{y}})\sin(\frac{n\pi z}{L_{z}})$$

This is not the end however. This expression is a little too general, as
the gauge has not be fixed. The simplest procedure is to pick the
coulomb gauge

$$\nabla\cdot\vec{A}=0$$

which corresponds to

$$\vec{k}_{lmn}\cdot\vec{a}_{lmn}=0$$

meaning that the fourier component must lie in the plane perpendicular
to the wave vector of that mode. This is the origin of two polarizations
for each wave, as $\vec{E}$is parallel to $\vec{a_{lmn}}$in each mode.
This is often written as

$$\vec{A}=\sum_{l=1}^{\infty}\sum_{m=1}^{\infty}\sum_{n=1}^{\infty}\vec{\epsilon}_{\lambda lmn}a_{\lambda lmn}\sqrt{\frac{8}{L_{x}L_{y}L_{z}}}\sin(\frac{l\pi x}{L_{x}})\sin(\frac{m\pi y}{L_{y}})\sin(\frac{n\pi z}{L_{z}})$$

Where $\vec{\epsilon}_{\lambda}$are 2 unit vector chosen orthogonal to
$\vec{k}_{lmn}$

$$\vec{E}=-\nabla\Phi-\frac{1}{c}\frac{\partial}{\partial t}\vec{A}$$

$$\vec{B}=\nabla\times\vec{A}$$

Gauss' Law states that

$$\nabla\cdot\vec{E}=0=-\nabla^{2}\Phi-\frac{1}{c}\frac{\partial}{\partial t}\nabla\cdot\vec{A}=-\nabla^{2}\Phi$$

Which implies that we can set $$\Phi=0$$

Making the fields simply

$$\vec{E}=-\frac{1}{c}\frac{\partial}{\partial t}\vec{A}$$

$$\vec{B}=\nabla\times\vec{A}$$

Wien's Displacement Law: Those Old Guys Were Pretty Smart
=========================================================

Wien's law is a jewel among derivations. In essence, it combines the
facts of doppler shift, the equation of state of a photon gas, and the
elementary principles of statisitcal mechanics to deduce a truth more
powerful than one would expect any of those elemtns to contain.

The Photon Gas
--------------

In the early days, it was not at all clear that light must possess a
pressure, although it was fairly obvious that it possessed some form of
heat. After all, the sun warms you on a summery day. Bartolli's argument
says that if something has energy and a tempurature and volume, it must
have a pressure or else a violation of the second law of thermodynamics
is possible

$$E=ucdtdA\cos(\theta)\frac{d\Omega}{4\pi}$$

We'll allow the reasonable relation relating the energy and momentum
density of light

$$c|P|=E$$

$$Fdt=2P\cdot\hat{n}=\frac{2E}{c}\cos(\theta)$$

$$\frac{F}{dA}=p=2u\cos^{2}(\theta)\frac{d\Omega}{4\pi}$$

$$\int2u\cos^{2}(\theta)\frac{\sin(\theta)d\theta d\phi}{4\pi}=\frac{u}{3}$$

Once you have obtained the expression

$$p=\frac{1}{3}u$$

you are golden. The Stefan-Boltzmann Law and other thermodynamic
properties fall out of the thermodynamic machine like freshly made
sausage.

$$dU=d(uV)=TdS-pdV$$

$$dS=\frac{\partial S}{\partial T}|_{T}dT+\frac{\partial S}{\partial V}|_{V}dV$$

$$Vdu+udV=T\frac{\partial S}{\partial T}|_{T}dT+T\frac{\partial S}{\partial V}|_{V}dV-pdV$$

Meanwhile, we also know that $u$ is a universal function of $T$ ,
independant of $V$

$$du=\frac{du}{dT}dT$$

We can arbitrarily set either $dV$ or $dT$ to 0 to get

$$udV=T\frac{\partial S}{\partial V}|_{V}dV-pdV\Rightarrow\frac{\partial S}{\partial V}|_{V}=\frac{4}{3}\frac{u}{T}$$

utilizing or pressure relation and

$$V\frac{du}{dT}dT=T\frac{\partial S}{\partial T}|_{T}dT\Rightarrow\frac{V}{T}\frac{du}{dT}=\frac{\partial S}{\partial T}|_{T}$$

Now we can use the most bizzarrely powerful trick in thermodynamics: The
identity of the double derivative.

$$\frac{\partial^{2}}{\partial x\partial y}=\frac{\partial^{2}}{\partial y\partial x}$$

This identity, whic apears abvious to everyone who isn't a mathemtician
has the physical interpetation that all the quantities we are dealing
with in thermodynamics are functions of state and not path dependant
quantities.

Slapping one a deriative on each side of the fomer equation we get

$$\frac{\partial}{\partial V}\frac{V}{T}\frac{du}{dT}=\frac{\partial^{2}S}{\partial T\partial V}=\frac{\partial}{\partial T}\frac{4}{3}\frac{u}{T}$$

$$\frac{1}{T}\frac{du}{dT}=-\frac{4}{3}\frac{u}{T^{2}}+\frac{4}{3T}\frac{du}{dT}$$

$$\frac{du}{u}=\frac{4dT}{T}$$

$$u=\alpha T^{4}$$

Green's Function Doppler Shift
------------------------------

$$(\frac{1}{c^{2}}\frac{\partial^{2}}{\partial t^{2}}-\frac{\partial^{2}}{\partial x^{2}})G_{0}(t-t',x-x)=\delta(x-x')\delta(t-t')$$

We can Fourier Transform this into the form

$$(\frac{-\omega^{2}}{c^{2}}+k^{2})\tilde{G}_{0}(k,\omega)=1$$

The solution of this equation isn't so hard

$$\tilde{G}_{0}(k,\omega)=\frac{1}{\frac{-\omega^{2}}{c^{2}}+k^{2}}$$

Now we can Fourier transform back

$$G(t-t',x-x')=\frac{1}{(2\pi)^{2}}\intop_{-\infty}^{\infty}\intop_{-\infty}^{\infty}\frac{e^{ik(x-x')-i\omega(t-t')}d\omega dk}{k^{2}-\frac{\omega^{2}}{c^{2}}}$$

First we do the $\omega$ integral. I'm not going to bother will all that
$i\epsilon$ jazz. I'll just tell you to put both your poles in the lower
half of the$\omega$plane.

$$t-t'>0\Rightarrow e^{-i\omega(t-t')}\text{decays in the lower half plane}$$

$$\Theta(t-t')$$

If we resitrcted oursleves to only positive x values, forcing string to
be zero at the edge of the wall, we can solve the Green's function
uysing the method of images. We can pretend that behind the wall, there
is a magic genie forcing the string in the exact opposite way we are
forcing the string, at just the right location to cancel the effcets of
our wiggling at the wall. The full Green's function is then

$$G(x,x',t-t')=G_{0}(x-x',t-t')-G_{0}(x+x',t-t')$$

Using similar consideration, we can derive the Green's function for a
moving wall. We need to place an image source so that it is conteracted
at the wall. The picture basically solves the problem.

We see the location of the wavefront produced by the image charge is at

$$x=x_{2}+c(t-t')$$

The wavefront produced by the real source is at.

$$x=x_{1}-c(t-t')$$

and finally the walls location is given by

$$x=x_{0}+v(t-t')$$

First we solve for the collision time by setting the wall location to
the real source wavefront

$$x_{1}-c(t-t')=x_{0}+v(t-t')\Rightarrow t-t'=\frac{x_{1}-x_{0}}{v+c}$$

If this derivation seems unduly complicated, you're right! I orginally
intended to go other places with it, but they got cut.

The Displacement Law
--------------------

We will compress the photon gas very slowly, so we can expand the
doppler shift to

$$\frac{1+\frac{v}{c}}{1-\frac{v}{c}}\approx1+\frac{2v}{c}$$

In addition, we now are going to work in three dimensions. The doppler
shift will only effect the component of the wavelength parallel to the
velocity of the wall, so we get the expression

$$1+\frac{2v}{c}\cos(\theta)$$

We define $u_{\nu}d\nu$ to be the amount of radiation energy in the band
of energy frequency between $\nu$ and $\nu+d\nu$ per unit volume. The
total amount of energy in the bandiwdith $d\nu$ hitting the wall in a
time $dt$ heading into the solid angle $d\Omega$ is

$$E=u_{\nu}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu$$

That expression is a surprisingly hearty load, so let's break it down a
little. $cA\cos(\theta)dt$ is an expression with the units of volume.
Since the radiation moves at a speed c, this is the size of the brick of
radiation that will hit the wall in the time. The $\cos(\theta)$ comes
about due to the orientation of the beam compared to the oreintation of
the wall. If one extrudes some cheese through a window at a velocity v,
you will get a huge hunk of cheese if the velocity points directly
through the window , whereas you will only get a slight slice of cheese
if the velocity is almost parallel to the window. Proper cheese grating
technique is the latter, while proper cheese eating technique is the
former. The $\frac{d\Omega}{4\pi}$is a factor that takes into account
that the energy is moving about equally in all directions.

This hunk of energy does work on the moving wall. Light has the
convenient relation

$$E=Pc$$

The power delivered to the wall is approximately given by

$$F\cdot v=\frac{\Delta P}{dt}\cdot v=\frac{2E\cos(\theta)v}{cdt}=-\frac{dE}{dt}$$

Which means that

$$du=-\frac{2v}{c}\cos(\theta)u$$

At the same time, any energy density in frequency band $d\nu$is shifted
into $d\nu'=d\nu(1+\frac{2v}{c}\cos(\theta))$

$$\nu'=\nu(1+\frac{2v}{c}\cos(\theta))$$

$$u_{\nu'}\approx u_{\nu}+\frac{\partial u{}_{\nu}}{\partial\nu}\nu\frac{2v}{c}\cos(\theta)$$

Putting it all together, the energy coming off the wall is

$$E'=E=u'_{\nu}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu'=u_{\nu}(1-\frac{2v}{c}\cos(\theta))cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu(1+\frac{2v}{c}\cos(\theta))$$

$$E'-E=du_{\nu}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu+u{}_{\nu'}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu'$$

$$-\frac{2v}{c}\cos(\theta)u_{\nu}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu+u{}_{\nu}cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu\frac{2v}{c}\cos(\theta)+\frac{\partial u{}_{\nu}}{\partial\nu}\nu\frac{2v}{c}\cos(\theta)cA\cos(\theta)\frac{d\Omega}{4\pi}dtd\nu$$

$$=\frac{\partial u{}_{\nu}}{\partial\nu}\nu\frac{2v}{c}cA\cos^{2}(\theta)\frac{d\Omega}{4\pi}dtd\nu=\frac{\partial u{}_{\nu}}{\partial\nu}\nu\cos^{2}(\theta)\frac{d\Omega}{2\pi}dVd\nu$$

Where we have used $$dV=vAdt$$

To represent the change in volume

We can integrate this over a hemisphere

$$\int\cos^{2}(\theta)\frac{d\Omega}{2\pi}=\frac{1}{3}$$

The total energy of freqeuncy $\nu$ in the box is

$$u_{\nu}Vd\nu$$

so we have

$$d(u_{\nu}V)=\frac{1}{3}\nu\frac{\partial u{}_{\nu}}{\partial\nu}dV$$
