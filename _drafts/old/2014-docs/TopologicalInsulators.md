Topology
--------

In classical mechanics it it obvious that the path of a particle must be
continuous. More so, the path parametized as a function of time must
never move instaneaouly fast (in relativity this would mean that the
path must never move outside of a light cone). Quantum mechanics softens
this condition by allowing the particle to be in a superposition of two
places at once, yet quantum mechanics still does not allow the particle
to move instantaeously fast or send objects outside of lightcones. The
study of the classes of equivalent trajectories is that of homotopy.

The conservation law

$$\partial_{t}\rho+\nabla\cdot j=0$$

or better yet the integral form

$$\partial_{t}P=-\oint j\cdot dS$$

can be seen as the corrolaries of the continuity of paths.

Differential operators reflect the topology of their domain. That is the
lesson of Homology, which categorizes the topologically robust
properties of differential operators (and their abstractions and
generalizations). These properties remain even when approximating
differential operators with their finite difference equivalents, such as
the adjacency matrix in graph theory. When we define how to take curls,
dels, and divergences on a correctly discretized domain, we find that we
cannot honestly create a square matrix. What we miss are boundary
conditions.

I propose without proof that these two facts are the origin of some of
the topological character of physical phenomenon.

Current is King
---------------

The current function is the best stand in for velocity that there is in
quantum mechanics.

$$j\approx\rho v$$

There is something physically disturbing about defining $j(x)$, and it
never seeems to sit well with spirit and formalism. The velocity in the
presence of a magnetic field is

$$v=p-\frac{q}{c}A$$

Momentum and velocity are not quite the same thing, but we all can't
help thinking that they essentially are, especially since the vector
potential is so intuitively cryptic.

Defining the current as a function of position has the flavor of
defining both a position and a momentum to a particle

$$j(x)=\frac{1}{2m}(-i\psi^{\dagger}\nabla\psi+i\psi\nabla\psi^{\dagger}-\frac{2q}{c}A\psi\psi^{\dagger})$$

However, if we integrate the current function, we may then integrate by
parts and see that this integral is indeed the expectation of an
operator.

$$\int jdx=<\psi|v|\psi>$$

Instead of extending our integration to infinity, we may integrate the
current function over only a unit cell of our crystal.

Current flow within a unit cell is irrelevant for many macroscopic
purposes, so in a sense we have circumented the uncertainty pricniple in
a manner to get cus what we want.

Half Solved Motion
==================

Motion in Magnetic Fields
-------------------------

The general motionn of all systems is complicated but if we assume the
magnetic field is strong or weak, we can understand the motion
perturbatively, staing from simple problems

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
slow motion. We anticipate that the drift motion ought ot essentially
Then Newton's law becomes

$$m(\ddot{x}_{d}+\ddot{x}_{c})\approx F(x_{d})+x_{c}\cdot\nabla F+\frac{q}{c}(\dot{x}_{d}+\dot{x}_{c})\times B$$

$$m\ddot{x}_{d}\approx F(x_{d})+x_{c}\cdot\nabla F+\frac{q}{c}\dot{x}_{d}\times B$$

The drift velocity may be come at from another direction, using
relativity. We may lorentz transform the pure cyclotron motion into
another frame in which it drifts. In this frace the pure magnetic field
will have transformed into a bit of electric field perpendicular to it.

$$E'_{\parallel}=E_{\parallel}$$

$$B'_{\parallel}=B_{\parallel}$$

$$E'_{\perp}=\gamma(E_{\perp}+v\times B)$$

$$B'_{\perp}=\gamma(B_{\perp}+\frac{1}{c^{2}}v\times E)$$

We can convert pure cyclotron motion into a drifitng motion in another
reference frame

Charged particles drift along potential curves

### The Hall Effect

The classical picture of conduction is a sloshing about of some electron
fluid inside a material. The vital parameter in this Drude model is the
relaxation time$\tau$. On average the momentum of a conduction electron
decays in roughly this time.

$$\frac{d}{dt}p=-\frac{p}{\tau}$$

In the steady state in the presence of an electromgnetic field, it
achieves a terminal drift velcotiy.

$$\frac{mv_{d}}{\tau}=q(E+\frac{v_{d}}{c}\times B)$$

We can solve for the drift velcity and plug it into the definition of
current

$$j_{x}=nqv_{d}=\sigma_{xx}E_{x}+\sigma_{xy}E_{y}$$

Motion in Crystals
------------------

The trick of seperating fast and slow motion is a universal one. If
instead of the cylotron motion dominating, we had considered a very
rapid but periodic ordinary potential on the motion plus a slower
spatially varying potential, we might expect that we can achieve a
perturbative graps of the motion by considering the periodic part in
isolation and then adding the slower motion as a drift.

Quantum Half Solving
--------------------

### Landau Bands and Quantum Hall Effect

How does the band structure play with magnetic strcuture?

Depends on the strength. If the magnetic field is really strong, we
should start from the Landau level picture in a magnetic brillouin zone.
If the field is weak, we should start from the Bloch pciture in a
crystal birllouin zone. Extended zone scheme for one and redcued zone
scheme for the other.

Extendend zone scheme for magnetic field with redcued zone scheme for
crystal. Varying B changes width of Magnetic zone

Van de Haas

SdH

The Landau gauge allows us to transmogrify the k vector depednance iof
the band to be an effective x dependance of the band

$$H=\frac{1}{2m}(p-\frac{q}{c}A)^{2}$$

$$A=(0,Bx,0)$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{(p_{y}-\frac{q}{c}Bx)^{2}}{2m}$$

$$\psi=u(x)e^{ik_{y}y}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{(k_{y}-\frac{q}{c}Bx)^{2}}{2m}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{q^{2}B^{2}(\frac{c}{qB}p_{y}-x)^{2}}{2mc^{2}}$$

$$\omega_{c}=\frac{qB}{mc}$$

$$H=\frac{p_{x}^{2}}{2m}+\frac{1}{2}m\omega_{c}^{2}(x-\frac{c}{qB}p_{y})^{2}$$

This is th equation for a simple harmonic oscillator, hence the energies
are quantized into

$$E_{n}=\hbar\omega_{c}(n+\frac{1}{2})$$

Band Structure
--------------

Whatever half truths it has to tell about the electron electron
interactions, the main lesson of Bloch theory is that crystal symmettry
implies band structure and experiment shows that band structure is some
kind of physcial reality.

The old story of envelopes and carriers is at work, although in a
twisted form. By supposing we build a wae packet centered around a
quasi-momentum k and in an energy band n, we can say that the wave
packet will travel with a group velcoity
$\frac{\partial E_{n}}{\partial k}$

The classical enevlope and carrier motion is additive. The quantum
mechanical version is multiplicative.

$$e^{\frac{i}{\hbar}classical}=quantum$$

Growing from the oribtals, a range of allowed energy is grown around the
original orbital energy by the periodicity of the lattice.

assume $\psi=e(x,t)c(x)$

$$\psi=e_{j}\otimes c(x')$$

$$-\frac{a}{2}<x'\le\frac{a}{2}$$

$$x=x'+ja$$

The matrix constructed for such a basis will be in a block diagonal
form. If we are considering a tight binding model, the carrier space is
N dimensional, where N is the number of sites per unit cell

The denisty matrix formed from this decomposootion is similar to that of
the denisty matrix of two indepdnant particles. We can perform a partial
trace

But now we can add some extra conditions

While the time independant formalism is very convenient (indispensably
so) and has its own consistant intuition, it obscures the gut physics
that time depdnant formulations have.

The integral of the current over a unit cell gives zero.

Quantum Hall Effect
-------------------

Von Klitzing disvoered that the hall conductivty in exatly quantized in
integers of $\frac{e^{2}}{h}$

If the variation of impurities is less than the band gap, it matters
very little. As we raise the chemical potential, The level fills in
little pools until we half fill the band. Since the sample in bounded,
everntually the effective potential has to sdtart increasing to some
large value at the edges of the sample. The chemical potential will
unavoidably cross at least one of these edges.

Two hamiltonians are topologically equivlaent if they can be
continuously deformed into one another without having a degernacy. This
is similar to the idea of two pieces of string being topologically
equivlaent if you can wiggle them continously ito each other. In the
prwsnsce of a pole, the strings can get hung up on them. We are using
degenracies like poles.

The edge states live inside the band gap. The edge states are
topologically unavoidable if we transition between two topologically
inequivlaent systems. One way to argue this is we can imagine very
slowly spatially interpolating our hamiltonian between the two bulks
instead of having a sharp transition. In slowly varying systems, we can
use the Bloch dispersion relations and crystal momentum to understand
the dynamics as we make the spatial variation slower and slower it makes
more and more sense to talk about a local band structure. A wavepacket
contrcuted of Bloch waves will slowly move from one region into the
other with the velocity

### The Laughlin Argument

Suppose we insert flux into a cylinder. Around the cylinder, the
wavefunction is a plane, wave with quanitzed wavenumbers

$$e^{-ik_{y}y}$$

$$\psi(0)=e^{i\frac{q}{c}\int A\cdot dx}\psi(L)=e^{i\frac{q}{c}\phi}\psi(L)$$

$$1=e^{ik_{y}L+i\frac{q}{c}\phi}$$

$$2\pi n=k_{y}L+\frac{q}{c}\phi$$

Putting that flux inside the tube geernates an electric field

$$EL=\frac{1}{c}\partial_{t}\phi$$

Degeneracy and Symmettry 
------------------------

The fundamental equation of symmettry is

$$[S,H]=0$$

Where S is some unitary operator, or generator of a continuous symmetry
(for example p for translational symmetry, J for rotational, or maybe
some element of a finite point group). The reason this often implies
degegeneracy is that unless S and H have completely the same
eigenvectors, in which case in that basis the equation reduces to

$$\mu\lambda-\lambda\mu=0$$

Or S is fiddling about and rotating within a degenerate subspace of H.
If that is the case, then H and S can both we simultaneously block
diagonalized.

### Time Reversal and Kramer's Pairs

Time reversal reverses all velocity. This also implies that it reverse
all spins since we can conceive of spin as arising from a little loop of
electric current.

Time reversal also changes the sign of magnetic fields. We can apply
time reversal to our system or the the universe. If we apply it to the
universe, the currents producing magnetic filds get flipped and hence
the sign of the magnetic fields gets flipped. If we just apply it to our
system, then

Hamiltonians that are magnetic field free do obey time reversal

Spin orbit coupling is a time reversal invariant term, because it
contains a factor of p and a factor of spin, both of which get a minus
sign under time reversal.

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

$$\left[\begin{array}{cccc}
H\\
\\
 &  & H\\
 &  &  & H
\end{array}\right]$$

$$I\otimes H+\sigma\otimes I$$

There are special symmettry points in the Brillouin zone where Kramer's
theorem creates drastic consequences.
