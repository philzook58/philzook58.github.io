Dirac Fermions

Graphene. Why graphene? Well we don't really mean graphene. Hexagonal
lattices are strangely prevalent. They've got just a tad more complexity
than square lattices and have subtle guys occurring. Check out the
review by Castro Neto

Hexagonal lattices have two subunits associated with each point. Each
hexagon holds two lattice points. Or you can pick a parralelogram that
conatins two lattice poitns

The lattice vectors can be chosen to be $a=3,\sqrt{3}$ and $3,-\sqrt{3}$
among other choices. You can straightforwardly build a tight binding
hamiltonian. It's going to have two bands. This is two components of the
vector, the a and b sublattices

These two bands meet at two points in K-space. A low energy theory then
has a choice of which points, how far in k space from these points, and
which sublattices, leading to 4 component wavefunctions (2 sublattice
hoice times 2 dirac point choices.)with k dependance.

Around a set point, the dispersion is approximately linear. This is true
classically to. Small changes in momentum don't change the velcotiy
much. This is the origin of Born expansion and the like for example.
Fast particles aren't deflected much. So we can perturbatively solve
their motion by calculating the momentum transfer accumulated if the
travel unimpeded.

When we talk about a 2 component dirac equation, we're usually talking
about picking on a the k points. The two components are then sublattice
components. The two dirac points are going to need rapid potentials to
mix, potentials with wavelenths on the order of the recpriocl lattice
vector. Smooth potentials aren't going to do it. Sharp ones like edges
will.

$\sigma\cdot\partial\psi$ puts the derivatives on the off diagonal,
which is because in order for the thing to propagate it has to flip flop
between sublattices. The same sublattice does not have a connection term
to itself, only via the other sublattice.

There is sublattice pseudo spin locking with momentum. Since the
efective "magnetic" field for the pseudo spin dendns on k, it changes
depending on which direction you are from the dirac point.

Semiclassically, working with weak magnetic field, this would quantize
the cycltron orbits at different values. $2\pi Rk=2\pi n+\pi$. This may
be the origin of the funky magnetic field depednace of graphene

$\psi=\begin{array}{c}
e^{i\theta_{k}}\\
\pm e^{-i\theta_{k}}
\end{array}$

Looping once around the dirac poitn gets you a berry phase of pi.
$\psi\rightarrow-\psi$. Because the effective magentic field has looped
around the equator once. So if you weakly pushed on the electron always
perpndicular to its motion, until it did a full loop, you'd have an
extra negative sign on top of what you'd expect.

Time reversal symmettry is messed up. Naively you think of it as complex
conjugation. But that notion is basis dependant. Spatially it is true.
And trasnforming bases for antiuntiary operators is tricky.

Magentic field. The dirac equation takes the square root of the sho form
of the landau gauge.

This is expacially relevant when you've got a fermi surface. In a sense,
the guys have no choice but to go fast. fast being the fermi velcoty.

Okay, first off, we have $\partial_{t}-\partial_{x}$. This is the one
way wave equation.

In 1-D we've got guys going both ways. We can then have a vector

In2D we can sort of have a pilot vector that points which way the thing
is going. It's a pretty smart setup.

Weird point, can't just have 1 of these. They have to come in pairs.
What goes up must come down. Nielson thoerem or something.

Hall effect in graphene. The one subtle point I determined is that the
traditional lowest landau level wavefunction being in one component is
wrong. travelling through potentials will twist it. Any particular point
can be untwisted to be put back in that form, but globally it can't be
written like that.

The rasiing and lowering algebra

Form a wavepacket and let it travel through.

So the lowest landau level is a fella that can rotate in the spin space
of the dirac man.

Then Son's theory is one in which there is a magnetic interaction
between the boys.

The thing that makes perfect sense is that a dipole will trvael through
unimpeded.

RPA Pine and Bohm
-----------------

Wavefunction is a parition function facotr Jastrow form of shielded
potnetial. Do Hubbard transfromation only for long range part of coulomb
potential. Pauli Villars regulated to remove high momentum/short scale
cutoff. ($\frac{1}{k^{2}}-\frac{1}{k^{2}+\mu^{2}}$) Quantum
Electrostatics. Porjection operator maintains the porpoer gausses law
relation. Is it really a hubbard? Something
like$\int D[A]\delta(\nabla\cdot E-\rho)e^{-\int E^{2}}$.

The RPA can also be determined using an effective $\epsilon(\omega,k)$.

Self energy is integral of impulse response. For unregulated field, has
ultraviolet divergence.

It is interesting to contemplate the real space form of various
regulated theories. They often have the flavor of a shielded potential.

$\Sigma=\int(\nabla E)^{2}=\int\frac{d^{D}k}{k^{2}}$

Working in 2D and integrating against $dp^{2}$lets you get lots of
closed form results
