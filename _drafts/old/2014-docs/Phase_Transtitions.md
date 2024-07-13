Weiss Model - Mean Field Theory
-------------------------------

The self consistatent field mothed or the mean field method is the
stiatical mechanical version of the hartree or hartree fock methods.
Interacting systems are complciated. They interact via za field that
they apply to each other. If we can determine the response of a
noninteracting system to an externally applied field (magnetic,
electric, etc.), it we can then see what kind of reponse it has
(polarization, spin alignment, etc). These responses then produce fields
of their own (the electric field from polarization) according to some
consitutive relation. We cna then match the external field necessary to
the field excitation that is produced. What we then have is a mean
field.

The level at which this is total bullshit is varying. On one hand, it
makes some kind of sense, and such appoximations can be dignified in
terms of variational caclations. On the other hand, it can miss
correlations of vital importance for the actual behavior.

The energy for a spin spin orientation is $\pm\mu B$

$$Z=e^{\alpha B}+e^{-\alpha B}=2\cosh(\alpha B)$$

$\alpha=\mu\beta=\frac{\mu}{k_{b}T}$

Then the mean magnetization (how uppy or downy in total the system is)
is ($m=\pm1)$

$$<m>=\frac{e^{\alpha B}-e^{-\alpha B}}{e^{\alpha B}+e^{-\alpha B}}=\tanh(\alpha B)$$

You may notice that $<m>=\frac{\partial}{\partial(B\alpha)}\ln Z$. It is
a useful trick to find good qusntities as derivatives of the partition
function.

Then the field produced from $B=\mu<m>$ so we need to solve

$$\mu B=\tanh(\alpha B)$$

The solution is often shown grpahically as where tanh function meets the
straight line.

TO take it up in sophisticaition, we could find the free energy of a
noninteracting system as a function of a spatially varying external
field. We can then find what kind of field the resulting spin
distribution would make and match the two up again. Now the equation

$$B(x)=\mu m(x)$$

Will be updated to a matrix equation, where mu is sort of a green's
function

$$<m(x)>=\frac{\delta}{\delta B(x)\alpha}\ln Z$$

Landau Theory
-------------

Landau theory is seeing what conseqeunces can be found from the mean
field concept. We can take a legendre transform of the free energy as a
function of the appllied field to get the free energy as a function of
the response. What is the actual response in an unapplied field then?
The answer is that the self consistent field will occur at the point of
the free energy that minimizes this energy. All other values will be
achieved only under the application of an external field.

In terms of the Weiss model, the free energy is

$$-\beta F=\ln Z=\ln2\cosh(\alpha B)$$

Now we can Legendre transform to F as a function of the order parameter
m.

$$G=mB-F$$

The free energy of this type that comes from the mean field response we
might call the landau free energy.

The derivative with respect to m will give you the full field, not just
the external field (E or B, not D or H. A material with built in
polarization will have an E field, but no D field)

Landau Theory also works for any free energy that is analytic at its
phase transition. The failure of this assumpiton about the free energy
shows that it cannot be analytic at these points. In some sense, the
mean value of the order parameter is insufficient information to
determine what is really going on. Really, its kind of a mriacle that
tht is usually what you need. We don't need the entire microscopic
state, but we need more than just the average amount of certain
quanities. Where do we break it off? At a critical point, where
fluctations get crazy, it is sensible that you need more data. Perhaps
moments of the order paramter is not a good approac11'h. In the scaling
approach, we assume that some ultimate details het washed out but some
don't and we try to track this.

spinodes

The gist of the Landau Theory. We can draw qualitative free energy
curves for different phases. IF we then assume that these curves are in
fact power series in the order parameter, we can make predictions.

Find an order parameter. You want a numerical variable that is
noticeably different for the two phases in question. For example density
in a liquid and solid. Magnetization in a spin lattice.

Symmettry

The free energy as a function of the order parameter. What does it mean?
The order parameter can be wirrten as the response to an extrenally
applied force. We legendre transform with respect to this force to get
another tpye of free energy that is the order free energy.

$$F=a+b\phi+c\phi^{2}+d\phi^{3}+e\phi^{4}$$

We could play these same games to get qunatum phase transitions. We
could in principal find the ground state of an uniteracting system to an
applied field, we can .Instead of interesting things happening as a
function of temprature, instead w could look for interesting things to
happen as a function of the interaction parameter g (perhaps the value
of some order parameter). The Hartree-Fock method may perhaps have a
crossover point. Instead of free energy, we'd use the hartree fock
ground energy.

In functional form, the legndre trasformation takes on a functional
character. Legendre rtansformations do interesting things to matrices.
They invert them. Hence if there are green's functions in our free
energy, then we get differentia operators in our new free energy. This
is the idea of the effective action (effective vertices) in QFT. The
legendre traasformation is a way to define the green's function for
nonlinear equations. The legendre trnadformation is the brother of the
fourier tranasform. The fourier transfrom is used to solve second order
linear equations, like the wave equation. Legendre is used to solve
first order nonlinear equations like the eikonal or hamilton jacobi
equation. The lgendre trasnoform results from steepest descent of linear
things.

Th gaussian integral works good for noninteracting systems (single
particle noninteracting). The addition of interactions between particles
can be attempted to be dealt with via a self constant field method.

The hamiltoinanian of a huge many particle system is linear. However, it
is in some sense a nonlinear operator. How can we introudce this? Like
so.

A is rectangular, it compresses the total fiekld into a denisty

$$L=J^{T}A\psi-\psi^{\dagger}H\otimes I+...\psi$$

$$L=J_{i}A_{ijk}\psi_{j}\psi_{k}^{\dagger}-\psi^{\dagger}H\otimes I+...\psi$$

$$L=(\phi A\psi)(\psi_{k}^{\dagger}A\phi)...-\psi^{\dagger}H\otimes I+...\psi$$

$$tr(\psi\psi^{\dagger}A\phi\phi^{\dagger}A\psi\psi^{\dagger}A\phi\phi^{\dagger}\psi\psi^{\dagger}A\phi\phi^{\dagger})$$

Or maybe just $(\phi_{n}A_{n}\psi)(\psi_{k}^{\dagger}A_{n}\phi_{n})$,
where the n is the number of particle green's function it is, 2, 4, ,6
,8 \...

Okay. That porbably has a closed form matrix solution. Or maybe a super
degernatre minima.

for many particle green's function

If

$$L=J^{T}A\psi\psi\psi-\psi^{\dagger}H\otimes I+...\psi$$

If A had been the indenity, then the lgendre transformation would just
invert the matrix completely. However, we screwed with it.

A very very large linear porblem may be equivlanet to a much smaller
nonlinear problem.

Critical Parameters
-------------------

Broken Symmettry and soft modes
-------------------------------

The peierls transition

The Jahn Teller Effect

A poymer chain is often modeled as an energy-less chain, whihc has a
tendncy to crunch up in the center because there are more squiggly
states than stright states, therefore it is energetically preffered.
Therefore it is not always energy that drives a spring like force, but
is insetad free energy, some compormise between entropy and energy. We
might assume the same in a crystal. The elastic constants of the lattice
come from assuming that the electrons are in some thermodynamic
ensemble. The elastic constants arise the same way that a box of gas
will reisst being compressed. The adiabtic compression law,
$pV^{\gamma}=Const$ is somewhat the equilvaent of a spring force for a
gas. If we assume adiabtic correction to the electron gas, we get a
similar thing. The elastic constants are compression of the electron gas
constants. Therefore they may be functions of tempurature, chemical
potential, etc. If we find the normal modes of such a stiffness matrix
parametized by tempurature, we may occasionally find at some T a mode
whose freqeuncy goes to 0. A harmonic osciialotr of freqeuncy 0 has a
period of inifty and goes to the free particle. The freqeuncy is
intuitively equivlanet to the spring constant, so a 0 freqeuncy mode has
no restoration force.

The peirls transition is one example of this. Whenever you split a
degeneracy, you get a higher energy and a lower energy. Therefore,
perturbations that split degeneracies may be energetically favored. In a
1-d tight binding, you have a single cosine energy band. If you increase
the lattice size by a factor of 2, you decrease the brillouin zone by a
1/2. The part of the energy band that was in the further parts becomes a
new band in the smaller brillouin zone and there is an energy splitting
if the lattice warsp, because the band is only half filled if you have 1
electron per lattice site, but it has 2 possible spins. The elastic
contants are gotten by seeing the energy change due to a distrortion in
thelattice, if we distort the lattice to double the lattice size, we
lower the electornic enerygy, therefore the distortion gets reinforced
up to a point. Energy favors the warped lattice. Entropy favors the
unwarped?

The Jahn Teller effect is similar

A continuous phase transition happens when the system does not respond
in kind to gentle perturbations/fluctuations. A first order happens when
it takes a big fluctuation to minimize the overall free energy. Too big
and you get a metastable state, which may never phase transition at all.

Quntum or Thermal fluctations will overwelm any mode with zero
freqeuncy. This is the infrared catastrophe.

Classically, each harmonic degrree of freddom gets $\frac{1}{2}k_{b}T$.
Hence the mean squared displacement from equilibrium

$$\frac{1}{2}m\omega^{2}x^{2}=\frac{1}{2}k_{b}T$$

$$\sigma_{x}=\sqrt{\frac{k_{b}T}{m\omega^{2}}}$$

This displacement diverges as the frequency goes to 0. Of course, as the
fluctations gets larger, the system becoems furhter and further from its
equilbiurm position and modelling the dyanamics as simple harmonic
motion becomes absurd.

The gaussian field
------------------

If the energy of the field is quadratic in the field (the sort of energy
you get linear differential euqations from during the minimization,
therefore vit is solvable). The gaussian integral of many variables is
just a wrapper for linear algebra.

We get moments (averages, standard deviations, etc.) by differentiating
partition functions with respect to a forcing term. This brings down a
factor from the exponent inside the integral sign, just like we wanted

This momentu generating function has the same form as the fourier or
laplace transform. This makes sense because taking the derviative in
fourier space is the same as multpliying by x in real space.

To perform a huge multivairiate gaussian integral, one way to see the
answer is to find the eigenbasis (The modes of oscillation of the
system, each one get $k_{b}T$ accoridng to the equippartiton theorem),
transform to those as the new variables, do the gassian there, where it
factorizes into a product of 1-d gaussians. Another approach is to
complete the squares in the exponent one vairable at a time. If you
squint, you can see that this is in fact gaussian elminination. In any
case, we get a factor of the determinant and we get the inverse of the
matrix

Renormalization
===============

The scaling hypothesis
----------------------

In ordinary material, it is quite obvious how certain quantities vary
with the size of the magterial. Let us say we have a box of size
$b^{3}$. Then the mass goes as $b^{3}$, the energy does, the number of
particles do. The pressure and tempurature are independant of b.

Consider resistance
