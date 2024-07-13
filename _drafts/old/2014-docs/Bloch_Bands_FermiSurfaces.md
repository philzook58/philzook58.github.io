$$x\in[0,a]$$

$$n\in\{0,1,2,3\ldots,\frac{L}{a}-1\}$$

$$X\in(0,L)$$

$$X=na+x$$

Crystal Momentum is more clear as crystal action.

In 1-d x-p phase space, the Action variable J for a periodic system is
defined as the area enclosed by the path of the object at a given
energy. Hence you can define J(E). This also implies that J does not
change with time. You can find a canonically conjugate angle variable to
J. It more or less smoothly parametizes how far along you are in the
period. The action and angle vairable sort of correspond qualtiiatively
to the idea of polar coordiantes $(r,\theta)$ in phase space.

As far as I know, general systems are not guranteed to spearbly into
action angle variables. The Poincare Invariants sort of are a starting
place, but not as powerful.

If you imagine phase space moving, it kind of looks like an
incompressible (thanks to Liouville's theorem) vortex flowing around in
a loop. The constant energy or action contours are streamlines that the
fluid never crosses. The action is the volume of fluid enclosed out at a
certain energy distance from the center unmoving part of the vortex
(which corresponds to the ground or equilibirium possition).

Probably the most important property of the action angle variables is
that the derivative with respect to time of the angle is constant, and
in fact is the frequency of system at that energy

$$\dot{\theta}=\frac{\partial H}{\partial J}=\nu(E)$$

Another veyr important property is that the action is an adiabatic
invariant. If you slowly change the string on a pendulum (or slowly
change any parameter of the system), you add or take away energy to the
pendlulum. Curiously, if you do it slow enough, the action is preserved
though.

It is these two properties that found the action angle variables as
central players in old quantum mechanics. First of it was known that if
something was quantized, it had to be an adiabatic invariant. Secondly
freqeuncies were of vital interest since the Bohr model of the atom
radiating required strange quantum conditions onthe frequnecies of the
system. The original quntization conditions were that the action comes
in chunks of $\hbar$. This is shown to be approximately correct thorugh
the modern theory via the WKB approximatuion.

The perturbation methods of classical action angle variables are
reidicuslousy similar to the methods for time independnat qauntum
mechanics and predate them significantly (In fact they were probably
inspired by them). The essential trick is that the peridic system can be
expanded in a fourier series in the angle variable. Heisenberg wrote
some paper that had a good exposition of it in Van Der Waerden

The action angle vairblaes do not work for just periodic systems (like a
SHO or a particle in a box or on a loop), they also work for repeititive
systems (Like a cosine/rollercoaster potential, or a crystal lattice
potential).

So let's say we solve our repetitive system. The particle crosses one
cell of size a in a time $\frac{1}{\nu}$ and we have H(J) or J(E) or
whatever we want. Now we introduce a new perturbing potential V for
example an external DC electric field.

$$\dot{J}=\frac{\partial V}{\partial\theta}$$

Dual Domains - interval - countable, real - real, finite-finite

Shannon-Sampling Theorem - you can use domains to simultate other
domains given certain consition on the function

Block Fourier

$$A\Psi=\sum_{n}A_{m-n}\psi_{n}(x)$$

$$A=\begin{array}{ccccc}
A_{0} & A_{-1} & A_{-2}\\
A_{1} & A_{0} & A_{-1}\\
A_{2} & A_{3}\\
A & A\\
A & A
\end{array}$$

In a localized, pretty much all the A are zero except the tridiagonal
ones

At the block level, we can perform a discrete fourier transform
$w=e^{\frac{i2\pi}{N}}$

$$\begin{array}{ccccc}
wI & w^{2}I & I & I\\
w^{2}I & w^{4}I & w^{6}I & I\\
w^{3}I & w^{6}I & I & I\\
\\
\\
\end{array}$$

If we let N get real big, this becomes more and more like a Fourier
series instead of a DFT.

This block fourier wavevector is the crystal momentum.

Looking at all the sub cell details inside block matrices, The lattice
space looks like an ordinary translation invariant second derivative,
with matrices instead of 1, 2, 1. The off diagonal matrices are veyr
small coupling matrcies. The tight binding model Uses the eigenvector of
the cell blocks and then has a transition between them using these off
diagonal lattice space matrices.

If you fix the distance between sample points (lattice), You fix the
total size of the fourier space block you're describing. putting on more
and more lattice points fills in your fixed range of fourier space until
you have a conitnuum.

Wavepacket needs surrounding crystal momentum lump, since etails on
lattice scale require crystal vectors (which are small, which describe
low freqeuncy, ie large scale phenom).

Because lattice is finite a apart, finite differences make energy
spectrum of crystal momentum shifted cosine instead of k\^2. Means they
reach a max.

Band structure is more or less finite band of kinetic crystal energy
hung at discrete rungs of cell block energy.

Classical version: YOu can calculate a v average across then cell.

$$\bar{p}(E)=\frac{1}{a}\int pdx$$

This momentum will be slowly changing, since you have a slowly varying
potential.

$$\bar{F}_{ext}=\frac{1}{a}\int F_{ext}dx\approx F_{ext}$$

Because periodic, the average cell block force averages to nothing

$$\bar{F}_{int}=\frac{1}{a}\int F_{int}dx=\frac{1}{a}(V(a)-V(0))=0$$

We more or less get

$$\frac{d}{dt}\bar{p}=F_{ext}$$

And really, that is good enough to understand what's happening, even
though an uncoarsened version might be very complicated.

Well, we can use a de brogile relation to relate this average to

$$\bar{p}=\hbar k_{cry}$$

What about the average velocity?

Phonon interaction though perturbation (or freqeuncy modulation) of
evolution matrix.

Can we achieve interesting boundary effects if we do not use born
boundary conditions (which strike me as unphysical though conveneint. We
really use them because we anticipate time depednant crystal momentum
wavepakcets as being more accurate, which more closely approximate a
bunch of one way exponentials rather than the two way cosine sine.
Recall the similar fiction used for scattering theory (discussed by
shankar in some light detail).

Surface wavepackets.

Topological insulators: The crystal momentum operator is a laplacian
more or less. or adjacency matrix. Since we have boundaries, could
homology thoery come into play? Crystal momentum space is the whole
space modulo cell space and spin space. Its also usually the space we
actually give a shit about. Projective geometry esque (perhaps\... proj
has equivlanece classes, but not linear ones quite like this\... hmmm
but maybe. Since states are rays\... can't go through center\... hmmmm.)
when you say it like that. What is the exact procdure to find the
crystal momentum of exact state. Kronecker division (quivlaence
classing)/ porjection. Quantum mechanics is a porjective space. We also
want the porjected dynamics of crystal mommentum space. Lots of rad shit
happens when transitions gets blocked. Covering spaces.

Bands
-----

Oh Bands! Let me count the ways

From a single orbital tight binding model, we create one band as we let
the number of cells go to inifnity. The band gets filled in by the
discrete states. In the green's function pole behavior, we see poles
fill in the line between the upper ad lower band limitsd, eventually
creating a branch cut.

We can add two orbitals per cell to get two bands.

In 1-d, is it possible to have overalpping bands?

In phonons, we build first the acoustic band (even with a single
"orbital", by whhich I would mean a lsgiht rigid displacement of the
entire unit cell, we still have 1 transverse and 2 longitudinal possible
displacements.) When we allow ocscillation inside the unit cell, we get
the next 3 bands.

TIght binding in chemistry is called the Huckel approximation

Tight binding model and loose binding model are dual to one another.

oribtals \<=\> wannier

plane waves \<=\> bloch waves

Loose binding is block diagonal in k-space - Potential connects

tight binding is block diagonal in x-space - orbital overlap connects

\# of orbitals per unit cell = number of bands. more oribtals, less
tightbidning

\# of k-vectors per reciricol cell ,or number of unit cells per k? more
reciprcol lattice vectors, less loose bindy

Loose bidning is for when shielding has smopothed everything to nothing,
conductors

Tight binding is for when

I wonder if you can see where the two models overlap? Kramers Wannier
Style. At conduction edge, fermi energy? or vacuum level?

Feynman diagrams are for nearly free electrons, equivlaent for tight
binding?

$\det(H(k)-E)=S(E,k)=0$ is an implicit function defining the bands. We
start with a 4D space, (E,k). S(k,E) cutsa it down by one. It is a
polynomial that weaves in and out positive and negative between regions.
The standard band diagram can be considered the depdnant variables, with
the bands being the 0 locations of the function. If the function is zero
at a minima or maxima, then we have a closed band gap. If we fix k, we
get a matrix whose eigenvalues give the energy spectrum at that k and
everything looks like the standard finite system matrix quantum
mechanics. If we fix E, say at the fermi energy, we get a surface of
constant energy. $E=\mu$is another constraint equation, so we now have a
2d surface. A curious question might be to ask what perturbation does to
this surface, or to the maxima and minima points $\nabla S=0$ where
interesting degeneracies occur. This all seems very geometrical

Calculations
============

Variational
-----------

The entire thoery of linear differential equations can be based on
variational approaches if you wish it to be so.

Bloch's Theorem is used a a guide to make sure that the guess functions
have the correct symmettry in regards to crystal translations.
Variational guesses that lead to linear equations are of the form

$$|\psi>=\sum a_{n}|\phi_{n}>$$

We sandwich these around H to get our projected Hamiltonian. If we
choose well, The spectrum of this finite matrix will reflect the true
spectrum. It can actually be difficult to choose guess bases really
poorly without malelovent intent. For example, what is the spectrum for
a random subspace?

We use a lagrange multplier to maintain normalization

$$Q[\{a_{n}\}]=\min<\psi|H|\psi>-\lambda<\psi|\psi>$$

$$\partial_{a_{n}}Q=(\tilde{H}-\lambda\tilde{S})a=0$$

Which is a generalized eigenvale equation

$$\tilde{H}_{nm}=<\phi_{n}|H|\phi_{m}>$$

$$S_{nm}=<\phi_{n}|\phi_{m}>$$

### The Cell

The continuity equation across each cell becomes the boundary condsition

$$\psi(r)=e^{ika}\psi(r+a)$$

Somehow, when we partially solve the large block cystal matrix, we end
up with an effective k depdnant hamiltonian due to boundary condition
terms.

### Nearly free electrons - 

Use plane waves $e^{ikx}$.

$S=I$ since plane waves are already orthonormal

Energy borrowing. Periodic ptentials only mix plane waves that differ by
a reciprocol vector. If we're injecting an electron of energy E into the
crystal, that quantity is fixed. Hence, the electron should only be able
to mix with plane waves of the same energy. What happens is that if the
kinetic energy of the mxed in plane wave does not match energy E, it
wouldn't mix. In weak potential limit, only waves on brilluoin zone
boundaries mix. However, if the extra geoemtrical freedom makes it miss
or hit potentials more often, the energy condition is relaxed.

### Tight Binding - 

Use atomic orbitals. A lot of the fun comes from S. S may be regarded as
creating a second derivative operator on a blocking level. We often
truncate it conceptually to just nearest neighbors, saying that next
nearest neightbors don't overlap. Also, we might say that different band
types don't mix. But they often do. sp3 hydribidization and whatnot

Estimate band width. Should essentially by size of S. S is crystal
lattice displaced overlap integral. This estimate would say that band
width is approximately bonding vs antibonding orbital splitting.

### Augmented Planes Waves

\- Use plane waves boundary matched to atomic orbitals at arbitrary
radius

### Orthogonlaized Planes Waves

\- Use plane waves orthogonlalized to atomic orbitals

$$\chi=e^{ikx}-\sum_{filledorbitals}|\phi><\phi|e^{ikx}>$$

### Green's Function Methods

### Pseudopotentials

Given the exact wave functions and energies, we can construct the
hamiltonian quite easily. The hamiltonian can be considered an encoding
of the spectrum and wavefunctions. But what could a effective 1-particle
hmailtonian even mean for a many body system? Perhaps an extension to
nonlinear eigenvalue problems.

What is a 1-particle green's function or hamiltonian? The translation of
the quantum field seocnd quanizted approach to a concrete numerical or
conceptual system is still fuzzy to me.

Perturbation
------------

$k\cdot p$. At points of high symmettry in the zone (due to the point
group), Lots of matrix elements fall out, making the matrices sparse.
Hence a reasonable plan of attack is to evaluate there, then perturb,
i.e. build a taylor series in k at the Brillouin Zone point that is
easy.

Differences between 1D 2D 3D band structure
-------------------------------------------

The human mind can really grasp 1D, strucutres, struggle with 2D and is
basically miserable when it comes to visualizing the 3D. Hence I'm going
to list the places where your ordnary 1-D thinking can fail you.

Surfaces
--------

The band thoery counts on infinite extent of the crystal.

Wehen we put it in a box, we would mix the opposite valued crystal
momentums into sines and cosines. However, this is an idealization.

The band thoery is a totally cockamamie thoery that makes the electrons
weakly interacting. The fermi theory is sctually for quasiparticles,
electrons dressed with a cloud of surrounding charge.

The extension of wavefunctions outside the box and the gibbs
oscillations. In a noninteracting fermi gas filled to the fermi sphere
in a box, we are trying to create a uniform denisty inside the box. This
is the fourier sine series decomposiiton of the constant function, which
has the well known gibbs oscillations. In this contest, these are called
(friedel?)
