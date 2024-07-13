Duality and Chern Simons Theory
-------------------------------

One of the goals of the axiomatic geometry of Euclid is that the figures
become redundant. All the arguments can proceed by word and logic
without the necessity of a picture. Allowing this level of abstraction
in geometry and physics, one can find strange similarities between
unlike things.

Duality is when one can replace a set of words by another and still have
true statements. A classic physical example is particle-wave duality.
Under the appropriate circumstances (assuming some kind of wavepackets
and ignoring details), statements about waves apply to statements about
particles using the mapping Energy goes to frequency, momentum to
wavenumber.

$\begin{array}{cc}
E & \omega\\
p & k\\
v & v_{g}\\
\\
\end{array}$

Hodge duality. Every plane in 2d has a unique normal vector associated
with it.

In 2-d every faces and vertices are dual to one another in the same way.
Every face has 4 edges and every vertx has four edges. An edge is the
boundary between two faces dually becomes an edge connects two vertices.
An edge gets rotated 90 degrees.

Duality extends to potentials.

$\nabla\cdot D=0$

$\nabla\cdot B=0$

$\nabla\times E=-\partial_{t}B$

$\nabla\times H=\partial_{t}D$

One duality that is quite clear is the duality between electric and
magnetic fields in the source-free 3+1D Maxwell equations. Upon the
exchange $E\rightarrow-B$, $B\rightarrow E$, we get the same set of
equations back. Such transfromation can be mathemtically useful as it
allows the application of techniques from solving electrostatic problems
to magnetostatic problems for example. In such a situation, an electric
vector potential and magnetic scalar potential are equally as acceptable
as the standard $A_{\mu}$.

If we consider the definition of Maxwell's equations as
$\partial_{\nu}A_{\mu}-\partial_{\mu}A_{\nu}=0$, then this duality does
not persist in other dimensions. The number of components just do not
match. For example, in 2+1D, the magnetic field has a single component,
while the electric field has 2.

3D electromagnetic duality. Source free. In the presence of source, the
duality can be patched up by remaining outside of the regions that
comtain sources and creating slices. The Amperian double layer.

2D charge flux duality.

Consider the following two equations

$\partial_{t}\rho+\nabla\cdot j=0$

$\partial_{t}B+\nabla\times E=0$

In 2+1D, the numbers do match up and one could conjecture the duality
$\rho\rightarrow B$, $j\rightarrow\epsilon_{ij}E_{j}$.

### Planar Electric circuit duality

In a circuit,

We transform to a new circuit with one dual node per face, one dual face
per node and one dual edge per edge.

The dual node voltage

$$\begin{array}{cc}
V & M\\
\Delta V & I\\
C & L\\
Q & \Phi
\end{array}$$

In moving to the continuum, geoemtrical constrcutys have to be weighted
by their size

The node voltages become the potential.

Voltage drops across elements become the electric field.

Loop currents become the magnetization

Voltage drops across capacitors become Polarization.

Magnetization and Polarization
------------------------------

In the asembly of the macroscopic Maxwell equations, we subtract from
the polarization P from E

$D=\epsilon_{0}E+P$

We might visualize P as representing a clustering and alignment of
microscopic dipoles. This might not be the case however. In a homogenous
material we may still wish to talk about polarization, even though there
is not obvious microscopic dipole unit. What is P in this case? P is a
potential for density. The value of P at a point is irrelevant and
unobservable as the value of the electric potential, representing the
propagation of a choice of boundary conditions with the definition
$-\nabla\cdot P=\rho$. Only spatial or temporal changes in P are true
local and physical quantities.

Likewise the magnetization M

$B=\mu_{0}(H+M)$

$\nabla\times M+\partial_{t}P=j$

We can combine these two quantities to create the 3 vector
$a_{\mu}=(M,P_{y},-P_{x})$, which is the dual to the ordinary vector
potential $A_{\mu}$.

The integer Edge
----------------

The main feature that charecterizes the dynamics of the bosonic
description of the edge , is that the edge is one way motion.

When we introduce an interaction between edges, they settle back out
into effectively indepdnant edge modes with . The interaction intorduces
image charges.

Any charge which is moving counter to the ordinary flow will be
considered an image charge of an primary charge flowing in the ordinary
direction.

When the interaction goes between two edges that propgate in oppoiste
directions, the image charge will flow counter to the ordinary direction
in that mode. Only image charges may travel against the natural flow in
that edge. When an primary charge reaches the region where an
interaction is present, it dresses itslef with an image charge. To
preserve charge, a charge of opposite sign to the image charge is
immediately ejected into the free region on the other side.

Once the original charge arrives all the way at the right end, it exits
back into a free region. However, it's image charge has arrived at the
left side of the interaction region. It cannot progress into the free
region, where it would be propagating counter the the flow, and it
cannot disappear, so it bounces back, going in the ordinary edge
direction and dressing itself with it's own image charge.

A soultion in the free region is simply a function of the form

$f(x-vt)$

The solution in the interaction region can be written

$f(x-vt)+Zf(-x-vt)$

where Z is the ratio between primary charge and image charge.

$(1+ZP)f(x-vt)$

$$k\partial_{t}\partial_{x}\phi+\partial_{x}\partial_{x}\phi+\partial_{x}uP\partial_{x}\phi=0$$

$$((-kv+1-uZ)+(kvZ+Z+-u)P)f''(x-vt)$$

$$\left[\begin{array}{cc}
-kv+1 & -u\\
-u & kv+1
\end{array}\right]\left[\begin{array}{c}
1\\
Z
\end{array}\right]$$

Taking the determinant

$(1-k^{2}v^{2})-u^{2}=0$

$v=\sqrt{\frac{1-u^{2}}{k^{2}}}$

$Z=$

Let us conisder an incoming step function (which corresponds to a point
charge via $\partial_{x}\phi=\rho$).

First it is $\theta(x-vt)$.

When $t=-a$

Then once it hits the interior it becomes
$\theta(x-vt)+Z\theta(-x-vt)-Z\theta(x-vt-a)$.

When $t=a$ the primary pulse exits

$\theta(x-vt)+Z\theta(-x-vt)-Z\theta(x-vt-a)-Z\theta(x-vt-a)+Z$

$<\phi(x,t)\phi(x',t')>=-\ln\frac{2\pi i}{L}(\frac{-x+x'}{v}+t-t'-i\alpha)$

$<\phi(x,0)\phi(x',0)>=-\ln\frac{2\pi i}{L}(\frac{-x+x'}{v}-i\alpha)$

### The semi-infinite electron gas

Consider an electron gas that has all states $k<0$ filled and all states
$k>0$ empty.

$\rho(k,k')=(2\pi)^{2}\delta(k-k')\theta(-k)$

Fourier trnasforming back into real space
$\rho(x,x')=\int\frac{dkdk'}{(2\pi)^{2}}e^{ikx-ik'x'}\rho(k,k')=\int_{-\infty}^{0}e^{ik(x-x'-i\alpha)}dk=\frac{1}{i(x-x'-i\alpha)}$

How is this useful? Obviously, no semi-infinite electron gas should
exists in an realistic system. What is more reasonable is the fermi
sphere $\rho(k)=-\theta(k-k_{f})+\theta(k+k_{f})$. What we have is
essentially $\frac{1}{2}$ of the femri sphere. We have studied only one
edge. When we combine the two we get the
$\rho(x,x')=\frac{e^{ik_{f}(x-x')}-e^{-ik_{f}(x-x')}}{i(x-x')}$.

The off-diagonals

Notice that the energy did not come into play other than how it would
determine the filling of momentum levels.

K Matrix Formalism
------------------

Number polarization. We can talk about number denisty instead of charge
density. Then we simply hae to record charge per particle to convert
between the two.

The quantum hall effect is the locking of magnetic field to particle
density at particular rational filling factors.

$\frac{n}{B}=\nu$.

In the integer hall effect, we can conceive of a model which uses to
ubiquitous non-interacting electrons. We can construct an individual
potential $a_{\mu}$ to describe the macroscopic state for each Landau
Level. An electron missing from a filled Landau level would act as a
source term

If we take it into our heads to use polarization and magnetization, how
can we obtain these equations of motion

$\nabla\cdot P=\nu B=\nu\nabla\times A$

We can imagine fluids of different types of particle. Each type maybe
have it's own polarization field. The net charge then becomes
$\sum_{I}q_{I}\nabla\cdot P_{I}=\rho$

The field $\phi$ is the integrated height function $\int ydx$ or the
$\partial_{x}\phi=P\cdot\hat{n}$ edge potential.

The lagrangian is
$L=\frac{-1}{4\pi}K_{IJ}a_{I\nu}\partial_{\mu}a_{J\lambda}\epsilon^{\mu\nu\lambda}+\frac{e}{2\pi}q_{I}A_{\mu}\partial_{\nu}a_{I\lambda}\epsilon^{\mu\nu\lambda}$

The equations of motion are

$$\frac{-1}{2\pi}K_{IJ}\partial_{\mu}a_{J\lambda}\epsilon^{\mu\nu\lambda}+\frac{e}{2\pi}q_{I}\partial_{\nu}A_{\mu}\epsilon^{\mu\nu\lambda}=0$$

seperating into components.

$K_{IJ}\rho_{J}=eq_{I}B$

$\epsilon_{im}K_{IJ}j_{Jm}=eq_{I}E_{i}$

The first equation defines the filling factor.

The second equation describes the hall effect, an electric field
connected to a current perpendicular to it.

The total charge density is $\rho=eq_{I}\rho_{I}$. The filling factor is
$\nu=\frac{\rho}{B}=q_{I}K_{IJ}^{-1}q_{J}$

### Edge theory

The edge thoery is described by the lagrangian
$L=-\frac{1}{4\pi}(K_{IJ}\partial_{t}\phi_{I}\partial_{x}\phi_{J}+V_{IJ}\partial_{x}\phi_{I}\partial_{x}\phi_{J})$.
The matrcies involved are symmettric. The variation leads to the
equations of motion

$$K_{IJ}\partial_{tx}\phi_{J}+V_{IJ}\partial_{xx}\phi_{J}=0$$

Fourier transforming leads to

$$(K_{IJ}v_{\lambda}-U_{IJ})\phi_{J}=0$$

Where the eigenvelocities are $v_{\lambda}=\frac{\omega}{q}$

This takes the form of a generalized eigenvalue problem. One can find a
set of eigenvectors that are orthonormal with respect to $K$

$$\alpha_{I\lambda}K_{IJ}\alpha_{J\lambda^{'}}=\delta_{\lambda\lambda'}$$

and that have a completeness relation of the form

$$\sum_{\lambda}\alpha_{I\lambda}\alpha_{J\lambda}=K_{IJ}^{-1}$$

Once this basis is found, the problem can be easily related to the
solutions for the integer modes.

$$\phi_{I}=\sum_{\lambda}\alpha_{I\lambda}\phi_{\lambda}$$

where each $\phi_{\lambda}$is now an independant uncorrelated field with
velocity $v_{\lambda}$.

Using the completeness of $\alpha$

$$<\phi_{I}(x,t)\phi_{J}(0,0)>=\sum_{\lambda}\alpha_{I\lambda}\alpha_{J\lambda}<\phi_{\lambda}(x,t)\phi_{\lambda}(0,0)>$$

The unequal velocities prevent further simplfiication unless $t=t'$, for
which the differeing velocities of the eigenmodes drops out and using
the completeness of $\alpha_{I\lambda}$ reduces to

$<\phi_{I}(x,0)\phi_{J}(x',0)>=K_{IJ}^{-1}\ln(\frac{2\pi i}{L}(x-x'-i\alpha))$

Giving the equal time commutation relation
$[\phi_{I}(x,0),\phi_{J}(x',0)]=i\pi K_{IJ}^{-1}\text{sign}(x-x')$

### Quasiparticles

Quasiparticles are parametrizations of many-body hilbert space possess
an intiuitive advantage of being though of as particle-like. Usually
this means some kind of countability, localizability, and exchange
symmettry.

One very manifestation of this is the parametrized Laguhlin
wavefunctions.

In the bosonized description of the edge, quasiparticle creation and
annihilation operators take the form of $e^{il_{I}\phi_{i}}.$The charge
created by an operator $e^{il_{I}\phi_{I}}$is $eq_{I}K_{IJ}^{-1}l_{J}$
which we can see from

$$[Q,e^{il_{I}\phi_{I}}]=eq_{I}K_{IJ}^{-1}l_{J}e^{il_{M}\phi_{M}}$$

### Current

Tunnelling current is that rate that charge leaves one edge and enters
another $I=\dot{Q}=i[H,Q_{L}]$

$\frac{e}{2\pi}\partial_{x}\phi\leftarrow\rho$.

The chiral field $\phi$ counts the charge total charge
$Q=\int dx\rho=\frac{e}{2\pi}(\phi(\infty)-\phi(-\infty))$

The tunneling term in the Hamiltonian will inject particles from the
left moving to right moving
edges$H_{\Gamma}=\Gamma(\psi_{L}^{\dagger}\psi_{R}e^{i\omega_{0}t}+\psi_{R}^{\dagger}\psi_{L}e^{-i\omega_{0}t})$,
where $\omega_{0}=eV$ the biasing voltage. The bosonized form of this
term is

$H_{\Gamma}=\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}+e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t})$
Recheck this convention.

$I=i[\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}+e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t}),\frac{e}{2\pi}(\phi_{L}(\infty)-\phi_{L}(-\infty))]=i\frac{e}{2\pi}\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}-e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t})$

$U(t,-\infty)=1-i\int_{-\infty}^{t}dt'H_{\Gamma}(t')U(t',-\infty)$

$U(-\infty,t)=1-i\int_{t}^{-\infty}dt'H_{\Gamma}(t')U(t',-\infty)=1+i\int_{-\infty}^{t}dt'H_{\Gamma}(t')U(t',-\infty)$.

$\phi=\phi_{R}+\phi_{L}$

To first order in the tunneling Hamiltonian this works out to be

$<I>\approx<i\int_{-\infty}^{0}dt[H_{\Gamma}(t),I(0)]>=i<\int_{-\infty}^{0}dt[\Gamma(e^{i\phi(0,t)}e^{i\omega_{0}t}+e^{-i\phi(0,t)}e^{-i\omega_{0}t}),i\frac{e}{2\pi}\Gamma(e^{i\phi(0)}-e^{-i\phi(0)})]>$

$=-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{0}dt<e^{-i\omega_{0}t}[e^{-i\phi(0,t)},e^{i\phi(0)}]-e^{i\omega_{0}t}[e^{i\phi(0,t)},e^{-i\phi(0)}]>$

Using the time translation invariance of $\phi$ we obtain the identity
$<\phi(t)\phi(0)>=<\phi(0)\phi(-t)>$. We can collect terms to obtain
integrals that can be easily evaluated using contour integral methods.

$-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt<e^{-i\omega_{0}t}e^{-i\phi(0,t)}e^{i\phi(0)}-e^{i\omega_{0}t}e^{i\phi(0,t)}e^{-i\phi(0)}>$

If $[A,B]=C$, $[A,C]=0$, $[B,C]=0$ and A and B are linear in
annihilation and creation operators.

$<e^{A}e^{B}>=e^{<AB>+\frac{1}{2}<AA>+\frac{1}{2}<BB>}$

Using this identity we can reduce to

$-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})e^{<\phi(t)\phi(0)-\frac{1}{2}\phi(t)\phi(t)-\frac{1}{2}\phi(0)\phi(0)>}$

Thus once we have calculated the correlation function for the bosonic
field $\phi$, we can exponentiate and Fourier transform it to calculate
the tunneling I-V characteristic.

### The parameter g
