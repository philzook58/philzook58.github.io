Fourier - Counting States - dividing k space

Crystal momentum is big scale (larger than cell) motion. Corresponds to
small k vectors. Internal cell sctructure carried along like big-d E
vector

Momentum and crystal momentum. Basically: Related up to a lattice
vector. Unclear which rung pure sinusoid gets hung at. Aliasing.

Old Quantum Band Theory?

Tight Binding Model - Hang crystal momentum band at rungs

The Nearly Free Electron Model - Second order perturbation split. Hmmm.
That's not intuitive.

Madelung Constant - Conditionally convergent series

RPA - recollecting permittivity - mean field thoery - what is the sound
of an air molecule

Ewald Summation - Add gaussian subtract gaussian charge distribution to
sepearte sum into slowly varying (easy to sum ofurier) and short range
part (easy to sum real space) Related to hubbard stratonvich
transformation. also related to RPA. Long range DOF and short range.
There are a lot of seeds of things in here.

Electron Interaction
--------------------

Coulomb interaction is so strong that it is best treated as a constraint
rather than a force.

There are two key concepts

### Screening

Screening is achieved by determining the dielectric function.

Sum Rules
---------

### Oscillator Strength, Thomas Kuhn Reiche

### Friedel

The One-particle denisty of states needs to have Z electrons associated
with the impurity. Coulomb interaction is so strong that it enforces
charge neutrality as a constraint of the material.

$\int\rho_{0}-\rho_{Impurity}=Z_{0}-Z$

It is this principle that picks the correct fermi energy from the
denisty matrix in the first place

$\int\rho dVdE=N$

$\int^{E_{f}}\rho dE=n$ Is an implicit equation for the fermi energy.
Similar to how

$\int\rho f(\mu)dE=n$ is an implicit equation for the chemical potential
(The two cases coincide for fermi statistics at T=0).

$\rho$ is the 1 particle denisty matrix. How true are these statements
really?

You count states in spherical coordinates using the phase shift.

if we pin the wavefunction in a spherical box of radius R

$\sin(kR-\pi l/2+\eta_{l}(k))$=0

$kR-\pi l/2+\eta_{l}(k)=n\pi$

$0<k<k_{F}$

We see that higher l states have more k values that will work. Eahc k
value that works can be sandwich onto any m value for $Y_{l}^{m}$, and a
factor of 2 for spin, so the total number of states is

$2\sum_{l}(2l+1)\#_{l}(k)$
