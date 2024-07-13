The subject is vast and far-reaching, requiring a mastery of the
fundamental aspects of solid state physics. I think I rather
underestimated it on first glance as the mathematics is at the same time
very simple and familiar, dealing with wavefunctions and tightbinding
matrices rather than much Quantum Field magic, and yet very
sophisticated, leading down murky alleys of the theory of topology and
geometry that I am not yet capable of treading. In this paper I
apologetically attempt to at least touch key threads, without including
many of the manipulations necessary to back most of it up, for lack of
understanding, time, and space. Such a lack of equations, god forgive
me, befits a chemist more than a physicist (I jest).

Topology
--------

In classical mechanics the path of a particle must be continuous. The
path parametrized as a function of time must never move instantaneously
fast (in relativity this would mean that the path must never move
outside of a light cone). Quantum mechanics softens this condition by
allowing the particle to be in a superposition of two places at once,
yet quantum mechanics still does not allow the particle to move
instantaneously fast or send objects outside of light cones. The study
of the classes of equivalent trajectories is that of homotopy.

The conservation law

$$\partial_{t}\rho+\nabla\cdot j=0$$

or better yet the integral form

$$\partial_{t}P=-\oint j\cdot dS$$

can be seen as the corollaries of the continuity of paths translated
into the language of densities.

Differential operators reflect the topology of their domain. That is the
lesson of Homology, which categorizes the topologically robust
properties of differential operators (and their abstractions and
generalizations). These properties remain even when approximating
differential operators with their finite difference equivalents, such as
the adjacency matrix in graph theory. When we define how to take curls,
dels, and divergences on a correctly discretized domain, we find that we
cannot honestly create a square matrix. What we miss are boundary
conditions, the holes of space, which we can describe via the properties
of the subspaces of these fniite difference matrices.

I propose without proof that these two facts are the origin of some of
the topological character of physical phenomenon.

Current is King
---------------

The current function is the best stand in for velocity that there is in
quantum mechanics.

$$j\approx\rho v$$

There is something physically disturbing about defining $j(x)$, and it
never seems to sit well with the spirit and formalism of quantum
mechanics.

Momentum and velocity in the presence of a vector potential are not
quite the same thing, but we all can't help thinking that they
essentially are, especially since the vector potential is too loosely
constrained to be anything but physically cryptic.

$$v=p-\frac{q}{c}A$$

Therefore, defining the current as a function of position has the flavor
of defining both a position and a momentum to a particle

If we integrate the current function, we may then integrate by parts and
see that this integral is indeed the expectation of an operator.

$$j(x)=\frac{1}{2m}(-i\psi^{\dagger}\nabla\psi+i\psi\nabla\psi^{\dagger}-\frac{2q}{c}A\psi\psi^{\dagger})$$

$$\int jdx=<\psi|v|\psi>$$

Instead of extending our integration to infinity, we may integrate the
current function over only a unit cell of our crystal. These are the
games that we start playing in the time independent Bloch bulk crystal
theory. The continuity equation then constrains the manner that one bulk
behavior can transition into another, creating robust topological
properties of the bulk. While the time independent formalism is very
convenient (indispensably so) and has its own consistent intuition, it
obscures the gut physics that time dependent formulations have.

Half-Solved Motion
------------------

The trick of separating fast and slow motion is a universal one. The
dynamics of the slow motion can be written in terms of the average of
the fast motion.

The fundamental motion in a strong magnetic field is that of cyclotron
motion, where a centripetal force is applied by the magnetic force law
and charged particles run around in little circles.

$$\frac{mv^{2}}{R}=\frac{qv}{c}B$$

From this we immediately get the frequency of the orbit

$$\omega=\frac{qB}{mc}$$

And we get the radius of the orbit

$$R=\frac{pc}{qB}$$

Now, what if we had additional forces at play? Electrics fields, or
springs, or rubber hoses and roller skates? What then?

If we anticipate the cyclotron orbit as essentially dominating motion we
may write the complete motion as

$$x(t)=x_{d}(t)+x_{c}(t)$$

Where the cyclotron motion is swift circular motion and the other is
slow motion.

### The Hall Effect

The classical picture of conduction is a sloshing about of some electron
fluid inside a material. The vital parameter in this Drude model is the
relaxation time $\tau$. On average the momentum of a conduction electron
decays in roughly this time.

$$\frac{d}{dt}p=-\frac{p}{\tau}$$

In the steady state in the presence of an electromagnetic field, it
achieves a terminal drift velocity.

$$\frac{mv_{d}}{\tau}=q(E+\frac{v_{d}}{c}\times B)$$

We can solve for the drift velocity and plug it into the definition of
current to achieve the hall conductivity $\sigma_{xy}(B)$

$$j_{x}=nqv_{d}=\sigma_{xx}E_{x}+\sigma_{xy}E_{y}$$

### Landau levels

We can perform this same slow-fast decomposition in the quantum domain.
Roughly speaking

$$e^{\frac{i}{\hbar}classical}=quantum$$

Hence the classical addition of slow and fast behavior becomes
multplication of wavefunctions describing the slow and fast behavior
$\psi=\psi_{slow}\psi_{fast}$. We could call this the carrier envelope
decomposition.

The Landau gauge

$$A=(0,Bx,0)$$

allows us to transmogrify the k vector dependance of the band to be an
effective x dependance of the band

$$H=\frac{1}{2m}(p-\frac{q}{c}A)^{2}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{(p_{y}-\frac{q}{c}Bx)^{2}}{2m}$$

$$\psi=u(x)e^{ik_{y}y}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{(k_{y}-\frac{q}{c}Bx)^{2}}{2m}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{q^{2}B^{2}(\frac{c}{qB}p_{y}-x)^{2}}{2mc^{2}}$$

$$\omega_{c}=\frac{qB}{mc}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{1}{2}m\omega_{c}^{2}(x-\frac{c}{qB}p_{y})^{2}$$

This is the equation for a simple harmonic oscillator with an
equilbirium position at $\frac{c}{qB}p_{y}$, hence the energies are
quantized into

$$E_{n}=\hbar\omega_{c}(n+\frac{1}{2})$$

### Crystals

Whatever half truths it has to tell about the electron electron
interactions, the main lesson of Bloch theory is that crystal symmetry
(discrete translational symmettry) implies band structure and experiment
shows that band structure is some kind of physical reality.

According tight binding models, we hang a band at each rung of the
energy levels of an individual unit cell, since the connections between
cells allow for both more relaxed lower energy states and more stressed
high energy states than the isolated unit cells.

The old story of envelopes and carriers is at work, although in a
twisted form. The carrier waves in this case are the orbital functions,
and the envelopes are either a wave packet lump or a quasi-momentum
$e^{ikx}.$ By supposing we build a wave packet centered around a
quasi-momentum k and in an energy band n, we can say that the wave
packet will travel with a group velocity
$\frac{\partial E_{n}}{\partial k}$. The group velocity formula is not
completely correct, in that it misses contributions of the other bands
that unavoidably get mixed into the movement of the wave packet.

### Berry's Phase

In the Bloch theory of crystals, the nature of current is sometimes
obscure. The total current from a filled band is 0, yet there is current
flowing and polarizations occurring even in fully band filled
insulators. A vital key in undertsanding this is Berry's phase. Phase
factors are typically seen as irrelevant, since the quantum state is
defined as a vector modulo a phase factor. However, during a cyclic
adiabatic process an unavoidable total phase factor appears on the state
which is strangely not irrelevant, and many of the physical properties
of the crystal can be put in terms of it.

Berry's connection can be thought of as a kind of analogous to the
vector potential in magnetism, in that it's real content lies in its
behavior under loop integrals.

$$A=i<n(R)|\nabla_{R}|n(R)>$$

Integrating it around a closed loop in parameter space gives the Flux
through the loop. This integral can be rewritten using Stokes theorem
into an area integral over the Berry curvature

$$\Omega=\nabla\times A$$

In the example of a changing magnetic field coupled to a spinor, the
total integrated Berry's curvature is related to the total solid angle
that the magnetic field has traversed. This Berry's curvature is related
to the contribution of each quasi-momentum to the bulk current.

The total Berry curvature over the entire domain of the parameter comes
in discrete numbers, called Chern numbers. This is analogous to the
Gauss Bonnet Theorem where the integral of the curvature is related the
the Euler number of the domain, a topological quantity, not a metrical
one.

Berry's phase seems to be most helpful explaining phenomenon where the
bulk of the crystal is unchanged during a process, however something has
occurred nevertheless. An example is the explanation of polarization.
The quantization leads curiously to the fact that polarization must
occur in integers chunks of charge $e$, something that is physical
obvious, but a tad odd as to the manner it pops up mathematically.

More sophisticated applications of Berry's phase occur in the quantum
Hall effect . In the bulk, there is a swirling and transport of current
due to Lorentz force. This current is uniform on average however, not
leading to any net current through the bulk. Outside the material, there
must be no swirling and somewhere in between there is a a transition
somewhere. In other words, the Hall effect causes a uniform
Magnetization current $M$ to appear, however, actual current only
results from $\nabla\times M$, or $\Delta M\times\hat{n}$ across a
transition boundary.

### Integer Hall Effect

Von Klitzing discovered that the Hall conductivity in exactly quantized
in integers of $\frac{e^{2}}{h}$. The most remarkable part of this is
that the impurity and type of the sample does not matter. The property
is so universal that it is now being used as the standard to define
other units.

The picture is that the conductance is due to states at the edges. The
impurities and edges modulate the Landau levels thorugh the crystal. The
chemical potential may be in between Landau levels in the bulk but since
the sample is bounded, eventually the effective potential has to start
increasing to some large value at the edges of the sample. The chemical
potential will unavoidably cross at least one of these edges. leading to
conducting behavior in these edge states.

Two Hamiltonians are topologically equivalent if they can be
continuously deformed into one another without having a degeneracy. This
is similar to the idea of two pieces of string being topologically
equivalent if you can wiggle them continuously to each other. In the
presence of a pole, the strings can get hung up on them. We are using
degeneracies in our spectrum like poles.

The edge states live inside the band gap. The edge states are
topologically unavoidable if we transition between two topologically
nonequivalent systems. One way to argue this is we can imagine very
slowly spatially interpolating our Hamiltonian between the two bulks
instead of having a sharp transition. In slowly varying systems, we can
use the Bloch dispersion relations and crystal momentum to understand
the dynamics as we make the spatial variation slower and slower it makes
more and more sense to talk about a local band structure. A wave packet
constructed of Bloch waves will slowly move from one region into the
other with the group velocity, a behavior we could simulate by using an
adiabatic time dependant Hamiltonian changing its parameters at the same
rate as the packet traverses.

Spin Orbit Coupling
-------------------

One way to see that the spin and motion of a particle are energetically
coupled in an electric field is to note that in the electrons rest frame
the stationary ions become currents, generating magnetic fields. The
electron is a little spinning ball of charge with a magnetic dipole
moment, hence it couples to this field. We can write this in terms of
the Lorentz boosted electric field as

$$H\propto s\cdot(v\times E)$$

We can approach the problem in alternative way in the ionic rest frame.

Consider the following paradox: You sit in a tank watching the tread
move. The length of of the tank is L. The top tread appears to move at
velocity v behind you, the bottom at a velocity v towards your front. A
person on the ground sees the tank length contracted, the top tread even
more length contracted, and the bottom tread length expanded all
according to the length contraction formula

$$L=L_{0}\sqrt{1-\frac{v^{2}}{c^{2}}}$$

Where $L_{0}$is the rest frame length of an object. How is the tank not
torn to shreds in the ground reference frame?

Part of the trouble lies in our conception that the tank tread cannot be
stretched, or that amount of stretch is reference frame independent.
Perfectly rigid objects cannot exist in relativistic contexts, since you
could then send a signal faster than light by merely poking someone with
your rigid stick. Another trouble is our intuition on simultaneity.
Suppose we painted half the tread red and half blue. In the tank frame,
we can have all the top tread be red and all the bottom be blue. In the
ground frame, it is possible for the top tread to be all red plus have a
little blue, something that could never simultaneously happen in the
tank frame.

The classical electron is quite similar to the tank, in that it is a
spinning ball or belt of charge and mass, and weird things will happen
to this belt in relativistic contexts.

A simple way to see this mathematically is to build a ridiculous model.
One can build a square rigid pipe electron with a four current $j^{\mu}$
running through it. Like the tank body, the pipe structure does indeed
suffer the Lorentz contraction, but opposite directional four currents
feel different effects and the electric fluid will thicken
asymmetrically on one side, causing a dipole moment. This dipole moment
can be related to the spin and the velocity of the electron

$$H\propto E\cdot(v\times S)$$

which can be rearranged into the same form as the previous spin orbit
coupling.

Degeneracy and Symmetry 
-----------------------

The fundamental equation of symmetry is

$$[S,H]=0$$

Where S is some unitary operator, or generator of a continuous symmetry
(for example p for translational symmetry, J for rotational, or maybe
some element of a finite point group). The reason this often implies
degeneracy is that unless S and H have completely the same eigenvectors,
or S is fiddling about and rotating within a degenerate subspace of H.
If that is the case, then H and S can both we simultaneously block
diagonalized. and the eigenvalues of the symmettry operation can be used
as labels for the slippery degeneracies in H.

### Time Reversal and Kramer's Pairs

Time reversal reverses all velocity. This also implies that it reverse
all spins since we can conceive of spin as arising from a little loop of
electric current.

Time reversal also changes the sign of magnetic fields. We can apply
time reversal to our system or the the universe. If we apply it to the
universe, the currents producing magnetic fields get flipped and hence
the sign of the magnetic fields gets flipped. If we just apply it to our
system, then systems in external magentic fields are not time reversal
symmetric.

Spin orbit coupling is a time reversal invariant term, because it
contains a factor of p and a factor of spin, both of which get a minus
sign under time reversal. The operation of time reversal can be
described somwhat loosely as the following interchange.

$$T\left[\begin{array}{c}
\psi_{\uparrow}\\
\psi_{\downarrow}\\
\psi_{\uparrow}^{\dagger}\\
\psi_{\downarrow}^{\dagger}
\end{array}\right]=\left[\begin{array}{cccc}
0 & 0 & 0 & 1\\
0 & 0 & -1 & 0\\
0 & 1 & 0 & 0\\
-1 & 0 & 0 & 0
\end{array}\right]\left[\begin{array}{c}
\psi_{\uparrow}\\
\psi_{\downarrow}\\
\psi_{\uparrow}^{\dagger}\\
\psi_{\downarrow}^{\dagger}
\end{array}\right]=\left[\begin{array}{c}
\psi_{\downarrow}^{\dagger}\\
-\psi_{\uparrow}^{\dagger}\\
\psi_{\downarrow}\\
-\psi_{\uparrow}
\end{array}\right]$$

We see that $T^{2}=-1$, introducing an overall phase factor to our
wavevector. The quantum state is the vector modulo phase factor, so this
-1 does not affect the state, however it has consequences nevertheless.

$$\left[\begin{array}{cccc}
0 & 0 & 0 & 1\\
0 & 0 & -1 & 0\\
0 & 1 & 0 & 0\\
-1 & 0 & 0 & 0
\end{array}\right]\left[\begin{array}{cccc}
0 & 0 & 0 & 1\\
0 & 0 & -1 & 0\\
0 & 1 & 0 & 0\\
-1 & 0 & 0 & 0
\end{array}\right]=-I$$

Kramer's theorem states that in a time reversal symmetric system with
half-integer spin, there exists an energy degeneracy. There are special
symmetry points in the Brillouin zone where Kramer's theorem creates
drastic consequences (the origin and where the toroidal nature of the
Brillouin zone makes k equivlaent to -k). It is this pinning action of
this degeneracy that topological insulators exploit to retain their
chiral edge states in the face of impurities.

Conclusion
----------

This is a subject matter that is equally simple and deep, practical and
abstract. Since my current goal is to cook these Topological Insulators
and the like, and equally to understand the theory as the best of them,
I've got a lot of work to do.
