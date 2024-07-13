Topology is the study of global geometry.

Gauges seem weird. They locally are irrelvant. Globally however, they
have unavoidlable physical properties. This is analogous to a string
wrapped around a pole. The string can be wiggled, but the global
catching on the pole is the interesting part. This all seems quite
counterinutuive to us.

Band structure crosses each other (valence crosses conduction).
Different fermi surface for different spins?

Integer quantum hall effect

Spin orbit

= topological insulator

### Current

Current is more associated with the velocity than the momentum.

The classical current density is

$$j=\int dp\rho(x,p)v$$

Sadly we're not going to be able to count on the simple connection
between momentum and veloctiy. We shall use

$$v=p-\frac{q}{c}A$$

The quantum analog of the porbability distrbiution function is the
denisty matrix $\hat{\rho}$.

Consider a free particle. If we slowly apply a weak electric field, we
can build up some current. We can do this by adding in a potential term
or by using the vector potential. If we use ah omogenous field, the
vector potential approach is particularly appealing, because there will
be no necessary spatial depdnenace invthe hamiltonian, hence we can
count on momentum conservation (which follows from spatial symmettry),
if not energy conservation (which follows from time symmettry). One way
to mathematically do this is in a gauge with.

$$j=\frac{1}{2m}(\psi^{\dagger}p\psi-\psi p\psi^{\dagger}-\frac{2q}{c}A\psi\psi^{\dagger})$$

### Polarization

One way to measure polarization is to integrate the current that runs
through a point over time.

Integrate current over a unit cell over time.

The net current out of a unit cell is

$$\oint j\cdot dS=$$

The rate of change of the polarization vector may be written as an
average of the current over a unit cell.

$$\dot{P}=\frac{1}{V}\int jdV$$

The average current over the unit cell may be written in the crystal
momentum space via parceval's equality.

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

Berry Phase
-----------

Adiabtic Ket chain

$$i\phi=\ln<1|...|3><3|2><2|1>=\sum\ln<n+1|n>$$

$$|n>\rightarrow e^{i\delta}|n>$$

$$|n><n|\rightarrow e^{i\delta}|n><n|e^{-i\delta}=|n><n|$$

This seems strange to use in terms of 3d pointy vectors, since these
don't have phase really. Your options are limitted to +-1.

Taking this to the continuous parameter case

$$|\lambda+d\lambda>=|\lambda>+d\lambda\frac{d}{d\lambda}|\lambda>$$

From time independanet pertruabtion theory

$$<\lambda|\frac{d}{d\lambda}|\lambda>=\frac{dH}{d\lambda}$$

$$\int<\lambda|\frac{d}{d\lambda}|\lambda>d\lambda$$

Th continuous definiton of berry phase is

$$\gamma_{n}=i\oint<n(R)|\nabla_{R}|n(R)>\cdot dR$$

$$A(R)=<n(R)|\nabla_{R}|n(R)>$$

The berry phase can also be written as a surface integral using Stokes
thoerem

$$\Omega=\nabla\times A$$

$$\gamma=\int_{S}\Omega\cdot dS$$

$$i\partial_{t}\psi=H(t)\psi$$

Rearranging into finite difference form for a small timestep $dt$

$$\psi_{t+dt}=(1+iH(t)dt)\psi_{t}$$

And putting it all together

$$\psi_{t}=(1+iH(t)dt)...(1+iH(2dt)dt)(1+iH(dt)dt)(1+iH(0)dt)\psi_{0}$$

We have a representation of the propagator

$$(1+iH(t)dt)...(1+iH(2dt)dt)(1+iH(dt)dt)(1+iH(0)dt)=T[e^{i\int Hdt}]$$

We can insert a complete set of instantaneous energy eigenvstaets at
each step

$$I=\sum_{n}|n(t)><n(t)|$$

$$\psi_{t}=(1+iH(t)dt)...(1+iH(2dt)dt)(\sum_{n}|n(dt)><n(dt)|)(1+iH(dt)dt)(\sum_{n}|n(0)><n(0))|(1+iH(0)dt)\psi_{0}$$

$$\psi_{t}=(1+iE_{n}(t)dt)...(1+iE_{n}(2dt)dt)(\sum_{n}|n(dt)><n(dt)|(1+iE_{n}(dt)dt))(\sum_{n}|n(0)><n(0)|(1+iE_{n}(0)dt)\psi_{0}$$

The two hamiltonians at nearby timestep vary by a small perturbation

$$H(t+dt)=H(t)+dt\partial_{t}H$$

Hence using standard time indepdnant perturbation thoery to first order
in dt

$$<m(t+dt)|n(t)>=\delta_{mn}+\frac{<m|dt\partial_{t}H|n>}{E_{m}-E_{n}}$$

Now we have all the pieces, we need to collect the terms in our
expression

Suppose $\psi_{0}=|n(0)>$

$$$$

Josephson Junction
------------------

Magnetic Fields
---------------

Moition in magenitc fields

The fundamental motion in a magnetic field is that of cyclotron motion,
where a centripetal force is applied by the magnetic force law and
charged particles run aorund in little circles.

$$\frac{mv^{2}}{R}=qvB$$

From this we immediately get the frequency of the orbit

$$\omega=\frac{qB}{m}$$

And we get the radius of the orbit

$$R=\frac{p}{qB}$$

All complicated problems are insolvable, but we may hope to attack them
starting from a simple problem. What if we had additional forces at
play? Electrics fields or springs?

If we anticipate the cyclotron orbit essentially dominating motion we
may write the complete motion as

$$x(t)=x_{d}(t)+x_{c}(t)$$

Where the cycltron motion is swift circular motion and the drift motion
is slow motion. The proper parameter is $\omega R=$

$$\ddot{x}_{d}+\ddot{x}_{c}=F(x)+q(\dot{x}_{d}+\dot{x}_{c})\times B$$

The drift velocity may be come at from another direction, using
relativity. We may lorentz transform the pure cyclotron motion into
another frame in which it drifts. In this frace the pure magnetic field
will have transformed into a bit of electric field perpendicular to it.

We have the curious fact that the flux through the orbit is an adibatic
invariant.

Classical adiabatic invariants

$$m\omega R^{2}$$

$$RqB=p_{\perp}$$

$$i=\frac{q}{T}=\frac{\omega q}{2\pi}$$

$$\frac{\pi R^{2}q}{T}=\mu=iA=\frac{R^{2}q\omega}{2}$$

$$RqB=p_{\perp}$$

$$\frac{p_{\perp}^{2}}{B}=\mu$$

Charged particles drift along potential curves

Ahamorov Bohm
-------------

put particle on a ring. Put field in center. periodic boundary
conditions will wiggle energy levels up and down. Landau Levels. The
scattering equivalent ias ahamorov bohm.

### Topology

A question for EM fields is whether they are defined on points, edges,
faces of the 3d structure. It all sort of looks the same when you go to
continuum.

This may be taking half measures. It may not make sense to define a full
vector if directions have been chunked up.

Perhaps a 4d view would be instrcructive. $E\wedge B$. Hodge dual to
secondary potentials (magnetic scalar and electric vector).

The wave function itself is a gauge field, since certain aspects of
phase kind of don't matter

Homology and cohomology use the structure of the derivative to find
topological facts about structures. Kind of like graph theory.

We can find boundaries of domains quite easily. Then we can put
wavefunctions on them. These are surface states

The derivative in a gauge field according to hatsugai is something like
this

$$\left[\begin{array}{ccccc}
-1 & e^{i\phi}\\
 & -1 & e^{i\phi}\\
\\
\\
\\
\end{array}\right]$$

My suggestion was to enforce magnetic boundary conditions where the
endpoint is equal to a finite phase times the starting point. This is
probably more akin to using a magnetic scalar potential and making a cut
somewhere. COnsider an adiabatic perturbation of this boundary phase,
slowly ramping it up. What happens?

I do not understand surface states so good, but I would think that they
are essentially a d-1 variational reduction of the original problem.
Could attempt a glarkin approach, with spike rings at the edges. If we
want to do in continuum, perhaps solve a taylor series (first order?
second?) in the inward parater from the edge? Can't be exactly on the
boundary of course, just a little in.

$$\psi\approx a(x,y)+b(x,y)z+c(x,y)z^{2}$$

on inner hole

$$\psi\approx a(\theta)+b(\theta)(r-r_{0})+c(\theta)r^{2}+d(\theta)\frac{1}{r}$$

A gauge invariant quantity is the flux per face. We can define flux in
faces quite naturally. flux = $\phi=\int B\cdot dS=\int A\cdot dl$. This
suggests A should be defined on edges?

On a grid, there are tons of holes in our domain. However, whether these
are really holes depends on whether we include the faces.

How do you describe paths in vector space? Parameter. The pertubration
method is to select an egienvaector of a hamiltonian and then follow it
as you change the hamiltonian. Another possiblity is in a continuum of
eigevenctors for example to crstayl momentum. These are still
eigenvectors but now instead of the parameter being a change of the
operator, we travel through the spectrum. A third possibility would be
to give a sequence of the discrete eigenvalues of an operator. Trouble
with this is that they will probably all be orthogonal (perhaps unless
there is degeneracy)? could slowly turn perhaps, each trasition being
taken continuously.

Polarization = integral of current through ssytem under adiabatic
perturbation. Nice.

What about a generator? Could sweep a magnet through a coil of wire.

change of flux/time = voltage = R \* current. How much total charge?
well, for normal resitance, we must have an integer number of electrons.
so Q = Ne

Something funny is going on in that the time it takes to do something
doesn't matter. A surprising coincidence. This means our language is
bad. It should be neither surpising nor a coincidence.

$\Delta\phi=R\Delta Q$ is another way of writing the combined lenz's and
ohm's law.

$j=\sigma E$

Then in hall effect

$d\phi/dt$

Another one. In the correct gauge $\dot{A}=E$ (This is from that
interpreation of vector potential paper I have somehwere)

$$e\int Edt=\Delta p$$

Hence $\Delta A=\Delta p$. Another result independant of the time it
takes. THis might be the formal momentum and not the intuitive momentum
though. There is also the magnetic field playing in there somewhere.

Another one. Adibatic bringing together of disparate metals. The Cntact
potential is defined from currents that flow.

Adiabatic equations kind of mean finding two things that are equal to
total time derivatives under a slow limit.

Consider a edge bouncing state. What is the flux enclosed (circle or big
bouncing circle)? Is it adibatically conserved?

Is virial an adibatic therem? (Berry phase?). Hmmm, actually
$\int T-Vdt=S=t(\bar{T}-\bar{V})=\frac{1}{\nu}(\bar{T}-\bar{V})$. Virial
theorem might be related to action.

Relation to old quantum perspective (ehrenfest?) That quanitzed things
must be adiabtic (maybe vice versa).

The old story of fast and slow movement comes into play again. Drift
veloicty and hall effect? The movement of the gyrocenter (enevelope) on
the cyclotron movement (carrier). The edge states are quite different.

Does adibaitc phase connect to envelope behavior?

Anywhere adiabatic changes are happening (I'm looking at you
thermodynamics), Berry phase is worth a look.

Band Structure
--------------

The main lesson of Bloch theory is that crystal symmettry implies band
structure and experiment shows that band structure is some kind of
physcial reality. However to take the fully interacting picture into
some kind of effective noninteracting picture takes a lot of work and
questionable apporximations. By just stating that the band gap of such
and such material is 1eV you are often doing as well as a sophisticated
numerical package.

carriers and envelopes. The classical enevlope and carrier motion is
additive. The quantum mechanical version is multiplicative.
$e^{\frac{i}{\hbar}classical}=quantum$

assume $\psi=e(x,t)c(x)$

But now we can add some extra conditions

where $|\frac{de}{dx}|<<|\frac{e}{a}|$

and $c(x+a)=c(x)$

Fourier form

average current

While the time independant formalism is very convenient (indispensably
so) and has its own consistant intuition, it obscures the gut physics
that time depdnant formulations have.

Now we can sepearate schroedinger's equation

$$ic\partial_{t}e=\nabla^{2}c+V(x)$$

Tight binding - rung of an energy ladder with scine at each

Free particle, sepeartion

The carrier and envlope picture falls to pieces at reflection edges,
similarly to the WKB method.

The existance of band structure is a result of periodic symmettry.

A plot of the

Different limits - letting the legnth of the chain become infinite fills
in the allowed k. The corresponds to the limit of the DFT to the fourier
series.Letting the number of states inside each unit cell go to inifnity
builds all the bands.

Inhomogenous crystals, what does band strcture mean? We build a clear
perception that far away from a junction, somehow band strcutre makes
sense. With slowly varying overtop potnetials, we have an adibatic
change in the time depndant picutre as the particle traverse from one
region to another. For sharp inhomgenities, it makes snese to transfer
to a scattering picture.

$\rho(x,x',E)=\int e^{-iky+iky'}dy\rho(y+na,y'+n'a,E)=\rho(n,n',k,k',E)$

The diagonal elements of this function are essentially the band
strcture. A little too concrete to be useful. Proably does not capture
the full essence of band theory.

Once we have removed the crystal momentum, we have a mapping from
cyrtsal momentum to a hamiltonian

Consider the adiabatic transition from one region to another We can
write a 2d brillouin zone (kx, ky) paramiztezed by z. As we move z, we
smoothly interpolate between one topology to another one (adibatically).
For a slowly moving wave packet, we can simulate this via putting a time
dpeendant transition between the two crystal types. The z rate and the t
rate are related via the group velicty of the wavepacket, but since both
are slow, it does not matter much thanks to the adiabatic thoerem.

### Landau Bands and Quantum Hall Effect

How does the band structure play with magnetic strcuture?

Depends on the strength. If the magnetic field is really strong, we
should start from the landau level picture in a magnetic brillouin zone.
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

Quantum Hall Effect
-------------------

Von Klitzing disvoered that the hall conductivty in exatly quantized in
integers of $\frac{e^{2}}{h}$

The Drude model has a quanityt the relaxation time$\tau$. On average the
momentum of a conduction electron decays in roughly this time.

$$\frac{d}{dt}p=-\frac{p}{\tau}$$

In the steady state in the presence of an electgromgnetic field

$$\frac{mv_{d}}{\tau}=q(E+\frac{v}{c}\times B)$$

$$j=nqv_{d}=\frac{nq^{2}\tau}{m}(E+\frac{v}{c}\times B)$$

$$$$

$$$$

### Surface states

Appears to be connected to resonant scattering. Clearly no true energy
eigenstate is loclaized at surface. That would be patently ridiculous.

Or maybe not

The phenomenon of band strcture does appear to be a physical truth. It
can be eperimentally measured. Its original conception as a single body
problem can be patched up, but it is untilmately a fiction. The band
strcture will obivously not occur if you create a periodic potential of
the nuclear coulomb attraction, as this neglects electron electron
interaction (and the movement of the nucelei)

There is no reason to imagine the effective potential at the surface is
the same as the effective potential in the interior.

One could imagine surface wave packets

However the complex valued energy eigenstaes - resonant states, beg to
differ.

I think resonance comes about due to domain decomposition techniques.

Simplest procedure would be to just work in a projected surface
subspace.

Surface band structure only makes sense with a brilluoin zone of the
same dimensionality as you surface. In other words, you cannot plot
surface bands on the bulk band structure

ARPES

Spin Orbit Coupling
-------------------

In the electron rest frame, all E fields get transformed a little bit
into B fields by the transformation laws

$$E'_{\parallel}=E_{\parallel}$$

$$B'_{\parallel}=B_{\parallel}$$

$$E'_{\perp}=\gamma(E_{\perp}+v\times B)$$

$$B'_{\perp}=\gamma(B_{\perp}+\frac{1}{c^{2}}v\times E)$$

Relativistic tank tread problem

Consider the following paradox: You sit in a tank watching the tread
move. The legnth of of the tank is L. The top tread appears to move at
velocity v behind you, the bottom at a velocity v towards your front. A
person on the ground sees the tank length contracted, the top tread even
more length contracted, and the bottom tread length expanded according
to the length contraction formula

$$L=L_{0}\sqrt{1-\frac{v^{2}}{c^{2}}}$$

Where $L_{0}$is the rest frame length of an object. How is the tank not
torn to shreds in the ground reference frame?

The trouble lies in our conception that the tank tread cannot be
stretched, or that amount of stretch is reference frame independnat.
Perfectly rigid objects cannot exist in relativstic contexts, since you
could then send a signal faster than light by merely poking someone with
your rigid stick. Another trouble is our intuition on simultaneity.
Suppose we painted half the tread red and half blue. In the tank frame,
we can have all the top tread be red and all the bottom be blue. In the
ground frame, it is possible for the top tread to be all red plus have a
little blue, something that could never simultaenously happen in the
tank frame.

The classical electron is quite similar to the tank, in that it is a
spinning ball or belt of charge and mass, and weird things will happen
to this belt in relativstic contexts.

A simple way to see this mathematically is to build a ridiculous model.

Let us say that our electron is a square toroidal tube with an electric
fluid flowing through it. The fluid has a charge density $\rho$ such
that

$$e=4\rho_{e}a^{2}L$$

and a mass density $\rho_{m}$ such that

$$m_{e}=4\rho_{m}a^{2}L$$

To achieve an intrinsic angular momentum of $\approx\hbar$ it must have

$$\hbar=j_{m}a^{2}L^{2}$$

The density and current can be collected into a covariant 4-vector
$j^{\mu}$

The tube itself is stationary, so we can apply the standard length
contraction formula to it.

Let us say that in the tank rest frame, the tread has a square cross
section $a^{2}$ Length L.

Classical electron model

relativstic transformation of dipoles (current loop)

relativsitc dipoles appear to be fairly controversial.

Derivation from Dirac Eq

Take average dipole moment as time goes to inifty

$$M_{\mu\nu}=\lim_{\tau\rightarrow\infty}\frac{1}{\tau}\int x_{\mu}j_{\nu}d^{4}x$$

This definition is clearly covariant (well except for possible trouble
with definition of tau. Center of mass movement?).

$$j_{\nu}=eu_{\nu}$$

This definition is reasonable for a "stationary" system.

$$M=\sum_{particles}e\frac{1}{\tau}\int d\tau x_{\mu}u_{\nu}$$

$$\tau=\int\frac{\rho^{\nu}u_{\nu}}{u_{\mu}u^{\mu}}d^{4}x$$

Consider a rectangular loop of travelling charge. This is our model of a
perfect dipole. What does it do under lorentz transformation?

Topology and the Derivative
---------------------------

Derivatives require you know what \[art of the domain is near or
connected to which other parts. you then compare the values at these
points. In this way the derivative reflects agreat many topological
properties.

Imagine a pile of nodes. We may encode which ones are connected to which
by putting it in a matrix. This is called the adjcecncy matrix. The
adjnecy matrix encodes what kinds of paths are possibly trversed.

A similar thing can be done on the set of all edges. We can say which
edges touch one another on the same face. And so on.

With these sets of matrices, we have established how everything is
connected to everything else in our domain.

Going more geometrical, when we discretize space into a buch of
traingular chunks, do functions of x,y,z become functions of points,
lines, or faces? Do we desi cretize vector functions as vector functions
of points or as functions on lines?

Chains are sets of the domain of various dimensionality

Co-Chains are real valued linear functions. We can use the integrsal
notations $\int_{C}$ represent a chain. The chain is a weighting of
domains. $\alpha\int dS+\beta\int dV$ . $d\omega$ represents a cochain.
It is the function that is on the path.

Barycentric coordinates. The coordinates represent weighted sums of
things. Hence subspaces become the n-D regions between points.

Mesh currents are functions of faces. of the circuit.

Duality can be used to map n objects to D-n. Duality maps chains to
co-chain? No. Duality maps chain to another chain s.t $a\wedge b=V$ the
unit volume form. In the full any simplex space, the Volume form
procuing thing can be written as a matrix. The duality opearotr is also
a ginat matrix.

Cycles are loops. They are the column space of the derivative operator.

Boundaries are the kernel. When we differenitate all 1 on a simpple
domain, of course we get 0.

The laplacian

Gauge fields have contraints built into them via topology.

Nullspaces \<=\> Gaussian elimination \<=\> Schur complement

Clearly we could include points that are essentially irrelevant. How do
we elminate them.

Visualizing 1d+spin
-------------------

78/;Two lines, one for up one for down. This is geometrically incorrect
I believe, although it does represent well the matrcies involved.

What is more correct is visualizing a sphere connected to every point on
the line.

Nearby points azre connected to nearby points spatially, but also
different spins at the same point are connected to one another.

I do not know what a dicrete version of spin would look like.

Fermi Systems in the language of simplices
------------------------------------------

We discretize our domain. represent homogenously. Grassman proudtcs
represent subspaces in domain. Subspaces of f on the domain. Then
functions on subspaces can be added together. A function of subspaces is
paramtized by a set of values, one for each grassman product.

The annihilation operator is then the exterior derivative

the creation ooerator is the co exeteior derivative.

Charecterstic classes
---------------------

The curvature has to satisfy certain consistnacy conditions. If you go
around one loop then another, the toal angular dedfect has to be the sum
of the two.

The curvature is derived from a potential The Metric (or perhaps the
second fundamental form?),just like an magnetic field is derived from a
potential. The extrinsic embedding of the object is irrelvant (hence
gauge freedom), yet extrnsic embedding is clearly the simplest way to
ddiscuss curvature.

The determinant of the curvature matrix is the gaussian cyrvature

the charetceristic clases get their name from the charecteristic
polynomial. You can define a matrix for every point on your manifold
(for example the curvature matrix) and then

The unitary matrix that takesy ou from one place to the next. Like time
evolution, or effectvily parameter evoltuoin if you have an adiabatic
parameter evolving.

$$\lim_{t\rightarrow\infty,\lambda(t)=C}U(t(\lambda)\dot{\lambda})=Te^{i\int_{\infty}^{t}dtH(\lambda(t))}=U(\lambda)$$

$$U^{\dagger}(\lambda)U(\lambda+d\lambda)=I+id\lambda Q$$

For homology we can place matrix fields on the grid. This means we need
to do blockwise gaussian elimination

$(1+tA)\otimes(1+tA)\otimes...$ Is a generating function that gives the
Noninteracting boson hamiltonian as the coefficient of t.

$\frac{1}{\lambda^{N}}(\lambda+A)\otimes(\lambda+A)\otimes...$ can be
instantly inverted from single particle green's function

$\sum\frac{z^{k}}{k!}(1+tA)\otimes^{k}$

$(1+tA)\otimes(1-tA)\otimes...$ gives the fermi hamiltonian

$(1+tA-A/t)\otimes(1-tA)\otimes...$

$(1+tA-wA)\otimes(1-tA)\otimes...$

These sorts of things occurs in the charecteristic equation. If I can
formulate bosonic expectations in terms of characterstic eq of
1-particle

$(1+(z_{1}+z_{2}+z_{3})A+(z_{1}z_{2}+z_{1}z_{3}+..)U)^{-1}$as a
multiparticle resultaqnt. Symmettric or antisymmetric polynomials. A and
U can't be summed

$(1+(z_{1}A\otimes I\otimes+z_{2}...)+(z_{1}z_{2}U\otimes I+...)^{-1}$

$(z^{2}I\otimes I+U)\otimes^{N/2}$no not quite. This is pariwise by
twos. I need all possible pairs.

Insetad of a pole grabber, the resultant as a generating functions?
Generates powers of A geometric serives

Charatcerstic equation generatures symmetric polynomials.. traces of
antisymmetric exterior products?

Generating function kronocker porduct can do cool things. I can get
things that aren't kronecker porducts from kronecker porducts by
collecting approirate powers.

$((I+tA)\otimes(I+tA))(I\otimes I+zU)\otimes^{N/2}$

$\oint dX\frac{1}{A-X}$

durecitonal derivative. Define rgular old vector on a face of simplex.
The the covariant dierative is associated with each edge on the face.
The last index is not a vector index, but is instead given by each each.
Maybe i mean Christoffel Symbol. Or transfer matrix. The matrix that
transfers you from one face to the next is an edge function. Or we could
define a normal vector for each face.

loops on dual mesh = face on dual mesh

cristoffel on uncruved space = imagine a cockammaie mesh where we have
different bases defined in different simpices.
