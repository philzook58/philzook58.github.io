Key Points:

All elementary excitations can be written as bosonic excitations

Jordan Wigner String

Linear Dispersion around fermi sphere.

Left Modes and Right Modes

Probably off base:

Childs Langmuir. The electric field step function from plane charge.

In more dimensions, holes and particles have the freedom to wander off
in different directions. In 1d they are two contrained, so they'll end
up going in the same direction with the same velocity, highly coupling
them. (Is that from opposite sides of fermi seurface or same side?)

A linear dispersion moves dispersion free wavelike. We could get this
perhaps in a plasma in a big cyclotron orbit. Positive charge one way
and negative the other

Also, two rigid rings would move this way.

e-phonon heat current (wonon? Wignon. Wigner crystal phonon). Wiedemann
franz law?

Often the best way to bosonize is to assume the ability to bosonize, try
the heisnberg eq of motion and back solve for the appropriate
hamiltonian

The kinetic energy term can be written in terms of current operator
because denisty of states = constant.

First order ODE when linearize dispersion. Leads into a whole different
set of techniques. Child langmuirs from method of cahrecterstic

Burger equation style hopf transfromation to

Classical phase space version. Consider density when the middle section
is mostly irrelevant. We can see ballistic conduction in the conditions
and see whats up.

The left right model (random walker versus walker with momentum and the
transition between.)

Density
-------

$\rho(x)=\sum\delta(x-x_{i})$

Hence

$\rho(q)=\sum e^{-iqx_{i}}$

$\rho(q)$ do not commute because we are using bizarre infnite ground
states.

Background density. $\rho=\rho+\rho_{0}$

kelin factor increase backgrouund by 1?

And indeed $\rho(q)=\rho(-q)^{\dagger}$

We can slap this on the side of a wavefunction

Bosonization in 1d

$\prod\text{sign}(x_{i}-x_{i+1})\psi_{F}=\psi_{B}$

Both will satisfy the same hamiltonian. The discontinuoity when two are
the asame position softens the sign function. While the second
derivative has a deltas function disconituiy in it. To make the
schrdoginer ewqaution okay, you may have to add a detla function to the
hamiltonian. If the fermionic wavefunction crosses zero such that the
first diervative is also zero, you're golden. Highly repulsive
potentials do this. A delta function potential will create a dsicontuity
in the first derivative proptoional to the value of the function there.

Fermions replling via delta function will never experience the delta
function.

Now do all boson wavefunctions have zeros at matching positions? Highly
repulsive ones might.

Jordan Wginer String style

$\prod\text{sign}(x_{i}-x_{i+1})=e^{i\pi\sum\theta(x_{i}-x_{i+1})}=e^{i\pi\sum\int^{x_{i+1}}dx\delta(x-x_{i})}=e^{i\pi\sum\int^{0}dx\delta(x-(x_{i}-x_{i+1}))}\approx e^{\int\rho}$

$\psi_{B}(x,x_{i}$)

We can bosonize ground state, bosonically add a particle, then
fermionize back.

$\psi(x_{i},x_{j}....,k_{F})$. excitaiton variables + kf location of
fermi surface

Polarization
------------

$j=\dot{P}$

$\rho=\nabla\cdot P$

Hence, trivially the continuity equation is obeyed

Polarization is not particularly distinct from eleastic displacement
(crystalline stuff, sound, phonons)

In the continuum, polarization is irrelevant. Only the changes matter.

In this sense it is a DENSITY POTENTIAL.

Similarly, the velocity potential $\nabla\phi=j$

Stream Function is conjugate to velcoity potential.

Normal ordering
---------------

$:ABC:=ABC-<0|ABC|0>$

The bosonic excitation operators are close to the normal ordered desnity
operator

Linear Dispersion 
-----------------

Linear dispersion = constant density of states

"Well-defined" Excitations E(q) not E(q,k)

Plasma excitations (Density Waves)
----------------------------------

$e^{\sum ikx_{i}}\psi_{0}$ is the canonical collective oscillation built
off of a ground state.

In operator talk, this is
$b_{q}^{\dagger}=\frac{i}{\sqrt{n_{q}}}\sum_{q}c_{k+q}^{\dagger}c_{q}$.
Different authors use different convections, the $n_{q}$factor is the
number q is from the q=0. This depends on box normalization.
$q=\frac{n\pi}{L}$

$[b_{q}^{\dagger},c_{r}^{\dagger}]=[\sum_{q}c_{k+q}^{\dagger}c_{q},c_{r}^{\dagger}]=\sum_{q}[c_{k+q}^{\dagger}c_{q},c_{r}^{\dagger}]=$

This can be considered a momentum raising operator

This can also be considered to be the fourier transform of the density
$|\psi(x)|^{2}$

$\rho(x)=\sum\delta(x-x_{i})$

$\rho(k)=\sum e^{ikx_{i}}$

$\rho(k)=c^{\dagger}*c=\sum c_{q-k}^{\dagger}c_{q}$

$\rho(0)=N$

Jordan Wigner String
--------------------

Phase counting

$c_{j}=e^{i\pi\sum_{j<i}n_{i}}b_{j}$

$z\otimes z\otimes z\otimes z\otimes z\otimes\sigma^{\dagger}\otimes I\otimes I\otimes I\otimes I\otimes I$

$f_{i}^{\dagger}=\prod_{j<i}z_{j}\sigma_{i}$

$\prod_{j<i}z_{j}=\prod_{j<i}(2n_{j}-1)=e^{i\pi\sum n_{j}}$

$zz=I$

$z=\left[\begin{array}{cc}
1 & 0\\
0 & -1
\end{array}\right]$

$n=\left[\begin{array}{cc}
1 & 0\\
0 & 0
\end{array}\right]$

$\sigma^{\dagger}=\left[\begin{array}{cc}
0 & 1\\
0 & 0
\end{array}\right]$

$\sigma^{\dagger}\sigma=n$

$\{\sigma^{\dagger},\sigma\}=1$

$\{z,\sigma^{\dagger}\}=z\sigma^{\dagger}+\sigma^{\dagger}z=\sigma^{\dagger}-\sigma^{\dagger}=0$

$f_{i}^{\dagger}f_{k}^{\dagger}$=$I\otimes I\otimes I\otimes\sigma^{\dagger}\otimes z\otimes\sigma^{\dagger}\otimes I\otimes I\otimes I\otimes I\otimes I$

$\{f_{i}^{\dagger},f_{k}^{\dagger}\}$=$I\otimes I\otimes I\otimes\{\sigma^{\dagger},z\}\otimes z\otimes\sigma^{\dagger}\otimes I\otimes I\otimes I\otimes I\otimes I=0$

$\{f_{i}^{\dagger},f_{i}\}$=$I\otimes I\otimes I\otimes\{\sigma^{\dagger},\sigma\}\otimes I\otimes I\otimes I\otimes I\otimes I=1$

This transformation can turn indepednant spin chains into fermionic
chains. The creation and annihilation of spin seem bosonic except that
you can't put more than one excitation in each box. (Different site
operators commute though)

Klein Operator
--------------

Transitions between total particle level. Commutes with particle hole
excitations.

Klein shifts entire excitation spectrum up by one. Written in terms of
b, state does not appreicably change. Basically thickens non-important
background conbstrant density.

A reshifting in linear dispersion means F does basically nothing

F is a uniform reduction of density.

F is the q=0 excitation operator\.... sort of. N is the q=0 (counting
operator)

Ibelieve the picture of deleting from a point is the same as squelching
and uniform lowering

Coherent States
---------------

Fermi Quasiparticle are boson coherent states.

$e^{\alpha\phi^{\dagger}(x)}$ makes a coherent state. What does this
mean? That the field value is a little ball around $\alpha$.

$e^{\lambda\phi}$ is the displacement operator for $\partial_{x}\phi$.
It puts a derivatvie at that point.

$\phi_{0}+\lambda x$ basically? Think of a fat sausage as a qft.

$e^{\alpha a^{\dagger}}$makes state located at$\alpha=x+ip$

$\psi\approx Fe^{i\Phi}$

Annihilation is the same as F lowering ground state then coherent
excitation of particle-holes. Non obvious at the moment.

$$

$[b,\psi]=e^{iqx}\psi$ Shows that $\psi$is a ladder type operator for b.
and that $\psi|0>$ is a coherent state since it is an eigenstate of b.

Vertex Operators
----------------

Seem to be hiighly related to coherent states

Ordered identities

Operator List
-------------

Delft:

$\eta$ spin/LR/mode index

c

$b=\sum cc$, bosonic commutation

$\phi=\sum b+b^{\dagger}$. This is the real field

$\partial_{x}\phi\approx\Pi_{\phi}.$ Approx Canonical commutation
between phi and derivative

$\phi=\sum\theta(x-x_{i})=\int\rho dx$

$\rho\approx\partial_{x}\phi=:\psi\psi:$

$\nabla\theta\approx j$=right minus left

Hence the density is approximately conjugate to the boson field. Hence
applying $e^{\lambda\phi}$ increases density (coherently) in a sense.

$I=\sum|\alpha><\alpha|=\sum|\alpha><0|c_{\alpha}=\sum c_{\alpha}^{\dagger}|0><\alpha|$

$\rho(x)=\frac{1}{V}\sum_{k,k'}e^{i(k-k')x}c_{k'}^{\dagger}c_{k}$

Analytic Signal
---------------

The anlytic signal of a delta function is
$A[\delta]=\frac{1}{t+i\epsilon}$

Likewise instead of convolving

the analytic signal of a heaviside step function is $\ln(t+i\epsilon)$

The phase of the anlaytic signa of the density function
$\sum\delta\rightarrow\sum\frac{1}{x-x_{i}+i\epsilon}$ is the CDF which
is what you need for the jordan wigner string.

The way you get a chiral green's function is to put $\theta(k+\omega)$
on the hting. THen you wil probably want to put $\theta(t)$ which is how
you get quantumy things. You nly want a single quadrant of the
$\omega-k$ domain

D'Alembert Decomposition
------------------------

The linear dispersion system. Green's function, yada yada, anderson
model, dirac equation. Immediate absorption of potentials into velcoity
