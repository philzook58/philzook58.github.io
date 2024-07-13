Impedance

Circuit Matrices

Amplfication
============

The op-amp 
----------

The op-amp is the perfect idealized amplfier

Digital Mode- Comparator - no feedback

Analog mode - feedback

The feedback network could be seen as the following equation

$$V_{n+1}=AV_{i}-fAV_{n}$$

We iterate and this becomes an infite series. What we really want is the
self consistant point

$$V_{o}=\frac{AV_{i}}{1+fA}$$

If A is quite large, it doesn't matter much

A is a soft constraint parameter, a la tychonoff regularization. The
hard constraint it corresponds to is the virtual short between op amp
inputs

Why do constraints give such power? Impedance transformation,
Amplification?

The principle of the virtual short
----------------------------------

In a proper negative feedback configuration, the plus and minus inputs
will be at the same voltage with no current running between them.

BJT
---

The BJT has a virtual short between the base and the emitter in the
active mode

The emitter follower is the same as an op-amp with zero resitance
feedback path

Digital mode - saturation and cutoff

Analog Mode - Active

FET
---

Power
=====

The unifying principle of circuits is power. The action principle for
which the circuit equations can be derived is the principle of least
power

$$P=V^{T}\nabla^{T}\frac{1}{Z}\nabla V$$

A resistor network arranges the voltages to disspate minimum power.

Noise
=====

6-10 {#section .unnumbered}
====

To join an antenna to an electrical circuit, you have to include the
circuit as a driving term. You need to solve the antenna for all kinds
of boundary conditions, because you need to be able to construct the off
diagonal matrices. The antenna and the driving circuit are not spearate
systems. They effect each other. So you'll need

Its easier to say residuals get smaller than to say the solutions
converge, because residuals are easy to claculate. That's what this
energy norm thing is about

### Diodes

Before understanding transistors, we should understand a simpler device,
the diode.

A perfect rectifier could be placed between the two wires of a
transmission line. The transmission line possess thermal energy in each
of its fundamental freqeuncies.

$$E(\omega)=\frac{\hbar\omega}{1-e^{\frac{\hbar\omega}{k_{B}T}}}$$

$$\omega=\frac{n\pi c}{L}$$

However, a diode could connect two lines to each other or

A diode connected to a capacitor. Capaictors do have johnson noise. The
diode noise must match such that the capaictor does not charge.

A perfect rectifier would build up all the charge on one. We could then
disconnect the diode and connect a load to extract work.

A way out is if the perfect rectifier has a lot of thermal noise, a la
the ratchet and pawl.

How many energy and spatial states qwould I need to get the qulaitative
features of the diode right in a quantum matrix model. Wrong approach
proably. Diodes are intrinsically stochastic botlamanny objects. What is
a ballistic diode? It would break time invariance.

The beat equation

$$\cos\theta\cos\phi=\frac{1}{2}(\cos(\theta-\phi)-\cos(\theta+\phi))$$

Is of vital importance.

$$I=I_{S}(e^{-\frac{V}{V_{T}}}-1)$$

Expanding to second order

$$I=I_{S}(-\frac{V}{V_{T}}+\frac{1}{2}(\frac{V}{V_{T}})^{2})$$

When we square the signal voltage, we create the two beats, one at
$(\omega_{c}+\omega_{s})-(\omega_{c}-\omega_{s})$ and one at
$(\omega_{c}+\omega_{s})+(\omega_{c}-\omega_{s})$ . The quartic term is
the first one that gives you the freqeuncies you need I guess.

Wait\... Is this the DFT? or rather DCT? The ampltiude mudlation process
is like forward transform (Signal times different exponential, Sum up in
same field), rectification is like backwards transform.

The phase detector. If you have them lined up right, the chopping will
act as a perfect rectifier. If you have them lined up wrong, chopping
will just make an f-ed up chopped sine wave. Low pass the result and
you've got

In the freqeuncy domain, this becomes a convolution equation. A cosine
is two delta functions, on at $\omega$ and one at $-\omega$. Convolution
with a delta function shifts.

### Cause and Effect

Cause and Effect in circuits. Difficult. However time inequlaities are
easier. There is often a useful idea of effective cause and effect. if
cause is way up chain from effect, or if two cuases from same effect.

cross-correlation - Energy in past minus power in future. Possibly
weighted by time from synchronized. The voltage in a rightward moving
wave. The left vltage will cause the right voltage.

This seems insufficient. Dleyaed effect from same source would regiater
as cause effect.

Fourth order expression using past A, past B, future A, future B

Should gaussians be capable of exhibitting cause and effect?

Better yet, how to determine cause effect directed graph, chain, tree.

Or relatedly, cross-infromation Given past of one, how much information
about future of other. Statistical hypthesis is time ordering of events.

Cause and effect, given past of one, how much infromation of the other -
the self infromation of the other's past on its future

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B})$$

Prediction gain

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B, Past A})$$

Back to my condition number conjecture

$$H(\text{Future B}|\text{Past A})-H(\text{Past A}|\text{Future B})$$

Since cause effect can only go one way, a number that is highly negative
or positive for likely cause effect relationship (like correlation in
this way).

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B, Past A})-(H(\text{Future A}|\text{Past B})-H(\text{Future A}|\text{Past B, Past A}))$$

Correlation does not imply causation, because this is a higher order
effect. Fourth order maybe? The question is if correlation does not
imply causation, what does?

Cause and Effect are not in the domain of logic. They are intuitive
ideas, inductive ideas.

Stiffness of cause from effect.

TIme domain. The start up properties of a circuit are often irrelevant
to most of its operation, and much startup is almost instanteanous.

Transmission Line has wavetrains. Transmission line feedback into
op-amp. Model as delay element dt in feedback loop. Cannot count on dt
as a paramter though, can only count to be small.

$$V_{n+1}=GV_{i}+FV_{n}$$

Big gain of op-amp means that G and F are huge

Geometric Series

$$V_{\infty}=\frac{GV_{i}}{1-F}$$

Convergence if $|F|<1$. Does that matter? Evidently not. Which means our
model is not so good. The wild oscillations caused by non convergence
get damped by a averaging or low pass properties f the circuit.

Negative feedback is somewhat reminscent of rejection sampling methods.
We make huge gain with weird proeprties but then accept only a small
amount of it, in order to approach whatever ideal gain we wanted.

Does voltage cause current? NOt in all cases, but It seems more likely
in many. Maybe a linear combination of voltage and current is real
input, which is approximately just one are the other in certain cases.

Transistor, Vbe causes Ic and causes Ib.

### Linear Circuits

The structure of a acircuit can be necoded into an adjacency matrix.

A circuit diagram is a topological diagram. Warping the edges is
irrelevant, What matters is what connects to what.

Each node can have a voltage associated with it. We want to know the
voltage drop across each edge

$$\left[\begin{array}{c}
v_{12}\\
v_{13}\\
v_{23}\\
\ldots
\end{array}\right]=\left[\begin{array}{cccc}
-1 & 1 & 0 & \ldots\\
-1 & 0 & 1 & \ldots\\
0 & -1 & 1 & \ldots\\
\ldots & \ldots & \ldots & \ldots
\end{array}\right]\left[\begin{array}{c}
v_{1}\\
v_{2}\\
v_{3}\\
\ldots
\end{array}\right]$$

$$\Delta v=Dv$$

The voltage vector is a way of encoding a voltage function, which has
different values from place to place. The indices of the vector encode
this location. To find the actual physical location of each node, we
could encode it in a matrix

$$\left[\begin{array}{ccc}
x_{1} & y_{1} & z_{1}\\
x_{2} & y_{2} & z_{2}\\
x_{3} & y_{3} & z_{3}\\
\ldots & \ldots & \ldots
\end{array}\right]$$

When we take the difference between connected nodes, it is the
equivlaent of taking a finite difference gradient operation. This
operation is called taking the exterior derivative. The way we organize
the indices is rather arbirtray. In fact, the only way we define which
nodes are connected to each other is by writing down this matrix.
Interesting porpterties of the domain are also connected to the matrix
poroperties of thius matrix. For example, the Kernel of D is . The
Nullspace is the . Cycles and Boundaries

The voltage differences in edges are related to the currents in them by
empirical physical laws, like Ohm's law. The impedance matrix Z is
typically diagonal

$$i=Z\Delta v$$

These voltages are connected by physical laws to current flowing in the
edges

Chains and Cochains

Circuit eigenvectors

$$v_{t+dt}=(A+dtB)v$$

Circuit Stability-Numerical stability

Op-Amps are sensible amplfiiers

Transistors are not simple amplifiers in that the input and output are
not so simply related

Edge, Point, Face Functions
---------------------------

A distinction should be made between edge point and face functions. Any
fluxy integral equation can be dicretized using exterior calculus. We
can discretize the possible domains of integration (all allowed volumes,
lines, face, points). The boundary operator is a matrix that gives the
oriented boundary of dimension d-1 for the object in question.

The coboundary operator is defined such that

$$\int_{\Gamma}d\alpha=\int_{\partial\Gamma}\alpha$$

This is a screwy looking notation but the integral sign with domain
represents a column vector with multiplicities of each part of the
domain as entries

$$\int_{\Gamma}=v$$

The summation of domains

$$\int_{\Gamma_{1}}+\int_{\Gamma_{2}}=\int_{\Gamma_{1}\cup\Gamma_{2}}$$

Follows immediately for vector summation

The $\alpha$ represents a row vector

$$\alpha=u^{T}$$

Hence the statement that

$$\int_{\Gamma}d\alpha=\int_{\partial\Gamma}\alpha$$

Just says the standard

$$u^{T}\partial v=(du)^{T}v$$

$$d=\partial^{T}$$

So the d matrix is the transpose of the boundary matrix.

There are two types of current, the mesh currents M and the branch
currents i. The Mesh current is a face function. The branch current is
an edge function. They are related as

$$di=M$$

$$i=\partial M$$

SOmething hodge dualy and funky is happening here. d takes low dim
objects to high dim objects. But the second one screws with my
interpreation of the primary space. Maybe functions on the dual mesh and
prime mesh?

This is analgous to the relation of the bound current (or magentization)
M and the current

$$\nabla\times M=i$$

The Edge voltage E and the point voltage V. E is the analog of the
electirc field (modula some distance factors) whereas V is the analog of
the potential.

$$E=dV$$

$$\left[\begin{array}{cc}
Z & d\\
d^{T} & 0
\end{array}\right]\left[\begin{array}{c}
i\\
V
\end{array}\right]$$

$$\left[\begin{array}{cc}
Y & d\\
d^{T} & 0
\end{array}\right]\left[\begin{array}{c}
E\\
M
\end{array}\right]$$

Voltage controlled current source come in as

$$\left[\begin{array}{cc}
Z & d\\
d^{T} & \alpha
\end{array}\right]\left[\begin{array}{c}
i\\
V
\end{array}\right]$$

Impedance
---------

Impedance is (possibly) the Dirichlet to Neumann map.

Maximum power transfer at imdepance matching.

Z(s) includes time depednance Laplace style. One

Transmission line antenna. Electric field between lines is
$\frac{V}{a}$. Current is current. Magnetic field is Biot Savart.

Single line antenna. model as series of inductors and capacitors all in
series? Charge has to bunch up.

Loop antenna. model as series of capacitors amnd inductors. or just big
inductor?
