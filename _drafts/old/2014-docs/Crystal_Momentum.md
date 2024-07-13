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
