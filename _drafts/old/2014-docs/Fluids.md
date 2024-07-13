-7-13

### Reducing Rotations

$$U=z'z^{T}+x'x^{T}+y'y^{T}$$

In 2-d

$$U=x'x^{T}+y'y^{T}$$

a rtoation counterclockwise by $\theta$

$$x'=\left[\begin{array}{c}
\cos\theta\\
\sin\theta
\end{array}\right]$$

$$y'=\left[\begin{array}{c}
-\sin\theta\\
\cos\theta
\end{array}\right]$$

You can see where cosine and sine go by checking that $\theta=0$ makes
sense, and that x starts going up and y starts going left for the
correct signs.

$$U=\left[\begin{array}{c}
\cos\theta\\
\sin\theta
\end{array}\right]\left[\begin{array}{cc}
1 & 0\end{array}\right]+\left[\begin{array}{c}
-\sin\theta\\
\cos\theta
\end{array}\right]\left[\begin{array}{cc}
0 & 1\end{array}\right]$$ $$U_{2}=\left[\begin{array}{cc}
\cos\theta & -\sin\theta\\
\sin\theta & \cos\theta
\end{array}\right]$$

$$\frac{d}{d\theta}U_{2}=\left[\begin{array}{cc}
0 & -1\\
1 & 0
\end{array}\right]=g=-i\sigma_{2}$$

We can expand in a taylor series

$$U_{2}\approx I+\theta g$$

Does the Taylor Error theorem still hold? The Lgarange form probably
doesn't. COnsider the matrix as just a collection of functions. The same
$\xi$will not give the exact remiabneder for all of them. The mean value
theorem won't guarantee it.

By the fact we know that the angles of rotations add, we have the
identiy

$$U_{2}(\theta)U_{2}(\phi)=U_{2}(\theta+\phi)$$

We can also laboriously check this by excplicity using the matrices and
cosine and sine angle sum rules.

Similarly as a corrollary

$$U_{2}(\theta)^{n}=U_{2}(n\theta)$$

$$g^{2}=-I$$

The generators of rotation about the z axis

$$U_{z}=\left[\begin{array}{cc}
U_{2} & 0\\
0 & 1
\end{array}\right]$$

$$U_{x}=\left[\begin{array}{cc}
1 & 0\\
0 & U_{2}
\end{array}\right]$$

The eigenvectrs of a z axis roation are

$$\left[\begin{array}{c}
0\\
0\\
1
\end{array}\right],\left[\begin{array}{c}
1\\
i\\
0
\end{array}\right],\left[\begin{array}{c}
1\\
-i\\
0
\end{array}\right]$$

$$z,x+iy,x-iy$$

and correspnding set of eiegenvalues

$$1,e^{i\phi},e^{-i\phi}$$

The kronecker product is a space of $3\times3=9$ components. We can
sepearte this into the irreducible subspaces of dimension 1, 3, and 5,
corresponding to the dot product, the cross product, and the nameless
one, the traceless symmettric product. The dot product represents
projection or sameness or length. The cross porduct represents twist,
rotation, or area. The symmettric propduct represents.

To compute the decomposition, we ask for the schur decomposition of the
general rotation matrix $U\otimes U$. No\... I guess not

barycenter product?, slant product, strain product, bulging product,
permutation product,quadrupole product, box product, ellipticity product

$$dv=dr\nabla\cdot v+dr\times\nabla\times v+dr?\nabla*v=(dr\cdot\nabla)v$$

Diveregence represents expansion, and net outflow

Curl represents roation and swirliness

Bulge (Shear) represents bulge and skew and shear flow

$$u=a+Br+\ldots$$

$$B\sim u\otimes r$$

$$B=u_{x}\hat{x}+u_{y}^{T}\hat{y}+u_{z}^{T}\hat{z}$$

where u is the small displacement from original position, and r is the
original position. This can be decomposed into three objects

and expansion is given by

$$u=\alpha r$$

$$dr\cdot r=\alpha r^{2}$$

The volume change can be found by integrating over a little sphere. Only
the normal component of the dispacement to the sphere counts as
expansion.

$$dV=|r|\int u\cdot rd\Omega=r^{2}\int u\cdot Y_{1}d\Omega$$

Surface area change from expansion $d(4\pi r^{2})=$

$$dr=4\pi\alpha r$$

$$dr\cdot r=\alpha4\pi r^{2}$$

A solid roation is represented by

$$dr=\Omega\times r=U(d\theta)r$$

A box or sphere gets warped into a ellipsoid or parallelopiped. The
divergence accounts for total volumetric change, the curl accounts for
rigid turning, and finally the bulge accounts for warping of angles.

Reflections. If we allow 3 reflections to occur at not the same point,
what kind of operation do we have? How do I get skew from reflections? 2
relfections that meet at a point create a rotation about that point. Two
paralell reflections (meet at infinity projectively speaking) generate
translations (rotations about infinit points aka directions). Is an
airplane wing therefore a fan blade with the axis at inifnity?

Strain/skew is affine trnasformation, divergence is similairty, and
roation is orthogonal

What about homogrpahiuc strain? Something thaty locally seems like a
homography, cross ratio preserving. Poles could be dislocations?
Homogenous coordinates for strain? extra coorinate is atom size or
something. Or inversions orccurring in fluid flow (bubble collpase?).
Sounds possible.

Action and Fluids
-----------------

The idea of a velcity field is a restirctive one. The mleucules can flow
thourgh ones another (feinetly in a gas), so the mean velocity may not
be a great specifier of the fluid. The intensity distribution in optics
is the equilvanet of a velcity distirubtion in fluids. The eikonal in
optics is the vlecity potential in fluids. The fluid green's function
for the velicty potential.. is the equivlaent of hamilton's function? I
should definetly explore the fluid-optics analogy more. The lagrange
invariant is the Klevin circulation theorem, I believe. Etendue is?
Essentially, you could do imaging with a fluid. A big difference is the
self interaction of the fluid, but the action kind of has that built
into it too. Vlecity optential will obey neumann boundary conditions
(gradient point out is zero no fluid flows into boundary). The eikonal
carries energy. The vleocty carriers itself,mass, and energy. If
iirrotational and inviscid, you can kind of not include carryinbg itself
and just say that it carries just bernoulli energy as well. Why is the
action first order nonlinear while velocity potential is second order
linear? Could take eikonal of velocity potential, espically if
compxefied (sound waves?).

The Bernoulli Equation is the hamilton jacobi equation when you express
it in terms of potential.

$$\partial_{t}\phi+(\nabla\phi)^{2}+V=Const$$

The integration along streamlines is like integration along true paths.
The potential is the eikonal.

$$\int_{\text{true path}}p\cdot dx-Hdt=S(x,t;x',t')$$

The Hamilton function is sort of a Lagrange picture.

Malus' theorem is helhotlz vorticity theorem (that a field thats starts
from a potential remians a potential field).

Flow over airfoil as scattering. Connection to imaging? $G(p,p')$. Let's
just pretend that the vecloty field for fluids can come from
$e^{i\phi}$. The scattering term would correspond to the circulation
term. Then, the Born scattering formuyla for lift would involve the
foueir transfrom of the airfoil. Momentum in/momentum out.

$$p_{in}=\int\rho v(x\rightarrow-\infty)dy$$

$$p_{out}=\int\rho v(x\rightarrow\infty)dy$$

$$p_{out}-p_{in}=$$

Another aspect to the helmholtz system is control. The dual of
observaibility. How close to a given pattern can I build the field
(external and internal source control.)? Conventional wisdom is that I
cannot achieve significant sub wavelength focusing.

6-8-13
------

The lift theorem
----------------

The big idea is that the rate that momentum is leaving the fluid must
equal the force on the wing.

We're working in a time indepndentat system so the conservation law
reduces to just the boundary term

Is we perform the line integral

$$\int_{\text{big sphere}}\rho\vec{v}\cdot\hat{n}dA+\int_{wing}\rho\vec{v}\cdot\hat{n}dA=0$$

how the boundary condition ofn the wing says that nothing flows into it,
so this second integral is 0

$$\int_{\text{big sphere}}\rho\vec{v}\cdot\hat{n}dA=0$$

The rate that momentum comes into this thing is

$$\int_{\text{big sphere}}\rho\vec{v}\vec{v}\cdot\hat{n}dA+\int_{wing}\rho\vec{v}\vec{v}\cdot\hat{n}dA+\int\nabla pdA=0$$

The pressure diofferential on the big sphere disappears as
$R\rightarrow\infty$

Lift

$$L=-\int_{\text{big sphere}}\rho\vec{v}\vec{v}\cdot\hat{n}dA$$

If we work in a z-symmetric flow, using a giant cylinder as our surface
(hopefully the encaps are neglibile)

$$L=-Z\int_{\text{big sphere}}\rho\vec{v}(\vec{v}\cdot\vec{r})d\phi$$

BAC CAB identity

We can write the constant ,$v=v_{\infty}\hat{x}+v'$

$$L=-Z\int_{\text{big sphere}}\rho(\vec{v}_{\infty}+\vec{v}')((\vec{v}_{\infty}+\vec{v}')\cdot\vec{r})d\phi=-Z\vec{v}_{\infty}\int_{\text{big sphere}}\rho(\vec{v}'\cdot\vec{r})d\phi+\rho\vec{v}'\cos\phi d\phi+\rho\vec{v}'(\vec{v}'\cdot\vec{r})d\phi$$

Neeeeh. Maybe not a good approach.

Linear Fluid Dynamics
---------------------

For incompressible fluids, the continuity equation reduces to

$$\nabla\cdot v=0$$

With the irrotational condition

$$\nabla\times v=\omega=0$$

Because of this we can write the volecity as a potential

$$\nabla\phi=v$$

The value of the potential

$$\int v\cdot dl=\int\nabla\phi\cdot dl=\Delta\phi$$

This

Now a small trip up. The disappearace of the curl of v only means that
the integral circulation is zero

$$\oint v\cdot dl=\iint\nabla\times v\cdot d\vec{A}$$

The closest connection to the linear theory of fluids is the theory og
mangetic potential. Outside the region of a bar magnet,
$\nabla\times H=0$ so H can be represented by a scalar potential.

In addition

$$\nabla\cdot B=\nabla\cdot(\mu H)=-\nabla\cdot(\mu\nabla\psi)=0$$

The amphere magnetic double layer is the same idea as the vortex sheet.

Each vortex line is like a wire carrying current up out at you.

Thought: through relativty, E transforms into B and stationmary charges
become currents. Does perhaps fluid sources become vortex sources under
gallilean tranasfromation? Applications to starting vortex?

### Minimum Kinetic Energy

The fluid does not go out of its way to move more than it has to meet
the boundary conditions, so it minimizes the kinetic energy

$$T=\frac{1}{2}\rho\int v^{2}dV=\frac{1}{2}\rho\int(\nabla\phi)^{2}dV$$

If we use the identity

$$\nabla\cdot(\phi\nabla\phi)=\nabla\phi\cdot\nabla\phi+\phi\nabla^{2}\phi$$

$$\nabla^{2}\phi=0$$

And the divergence theorem we get

$$T=\frac{1}{2}\rho\int\phi\nabla\phi\cdot\hat{n}dA$$

This surface integral includes all the surfaces, so it includes the
surface of the object and a surface at infinity.

One interpetation of $\phi$is as an impulsive pressure. If you applied
the pressure $\rho\phi\frac{1}{dt}$ for a split second $dt$, You could
produce the velcity field?

The boundary conditions for a moving object at velocity $u$ is

$$\nabla\phi\cdot n=u\cdot n$$

At the surface of the object.

If the object is spinning $u=u_{0}+\Omega\times r$

So if you wrench a paddle, and there is now kinetic energy in the water,
it had to come from you..

For a sphere, a dipole potential will do you good (Why? Well, it works.
You can find it by seperation of variables into spherical harmonic (or
legendre polynomials since axially symmettric) if you like.)

$$\phi=\frac{ua^{3}\cdot cos(\theta)}{2r^{2}}$$

$$T=\frac{1}{2}\rho\int\phi\nabla\phi\cdot\hat{n}dA=\frac{1}{2}\rho\int\frac{ua^{3}\cdot\cos(\theta)}{2a^{2}}u\cdot\cos(\theta)a^{2}d(\cos(\theta))2\pi=\frac{1}{2}\rho u^{2}2\pi a^{3}\frac{2}{3}\frac{1}{2}=\frac{1}{2}\rho u^{2}\frac{1}{2}V$$

So basically, your mass of the ball becomes

$$m=m_{0}+\frac{1}{2}\rho V$$

This also works for momentum

$$P=\rho\int\nabla\phi dV=\rho\int\phi\hat{n}dA$$

The z component is the only one to survive by symmettry

$$\rho\int\frac{ua^{3}\cdot cos(\theta)}{2a^{2}}\cos(\theta)\hat{z}d(\cos(\theta))2\pi a^{2}=\frac{2}{3}\rho2\pi a^{3}u\frac{1}{2}=\frac{1}{2}\rho Vu$$

What about an ellipsoid? Or a box?

### Viscosity

$$f=\nu\nabla^{2}v$$

Water is about 100 times as viscous as air.

$$\nabla^{2}v=\nabla(\nabla\cdot v)-\nabla\times(\nabla\times v)$$

Air - $1.81\times10^{-5}Pa\cdot s$

Water - $8.90\times10^{-4}Pa\cdot s$

$$F\sim\nu A\frac{v}{d}$$

Asymptotics and Boundary Layers.
--------------------------------

All the solutions you read for fluid motion smell a little of bullshit,
because to make things solvable you have to make crazy sounding
assumptions, that an armchiar man would have difficulty guessing at.
They are ultimately validated by experiment. This is always true, but
you tend to have a great deal more conifdence the physicality of your
solution to maxwrll's equations than

6-11 {#section-1 .unnumbered}
====

Method of Dominant Balance

$$\epsilon x^{2}+x+1=0$$

$$x=\frac{-1\pm\sqrt{1-4\epsilon}}{2}$$

$$x_{-}=-1+\frac{1}{2}\frac{1}{2}(-4\epsilon)+\frac{1}{2}\frac{1}{2}\frac{-1}{2}(-4\epsilon)^{2}+\ldots$$

$$x_{0}=-1$$

$$\epsilon(x_{0}+\epsilon x_{1})^{2}+x_{0}+\epsilon x_{1}+1=0$$

$$\epsilon x_{0}^{2}+\epsilon x_{1}=0$$

$$x_{1}=-1$$

and so on

$$x_{+}=0+\frac{1}{2}\frac{1}{2}(-4\epsilon)+\frac{1}{2}\frac{1}{2}\frac{-1}{2}(-4\epsilon)^{2}+\ldots$$

Regardless of how small $\epsilon$ is eventually it dominates

### Singular Perturbation

$$\epsilon x^{2}+2x+1=0$$

$$x_{0}=-\frac{1}{2}$$

$$\epsilon(x_{0}+\epsilon x_{1})^{2}+x_{0}+\epsilon x_{1}+1=0$$

$$\epsilon x_{0}^{2}+\epsilon x_{1}=0$$

$$x_{1}=1$$

$$x_{2}=$$

### Duffing Oscillator

$$\frac{d^{2}}{dt^{2}}u+\omega^{2}u=\epsilon u^{3}$$

$$u_{0}=A\cos(\omega t+\phi_{0})$$

$$u_{0}=Ae^{-i\omega t}$$

$$L=\dot{u}^{2}-\frac{1}{2}\omega^{2}+4\epsilon u^{4}$$

### Beam Equation

$$\frac{d^{2}}{dt^{2}}u+\omega^{2}u=\epsilon\frac{d^{4}}{dt^{4}}u$$

Equation is seperated into dominant and submissive halves in a sum like
manner because asymptitcs. Pairing isn't neccessary. All binomial
combinations of terms might be dominant together. Including a submissive
in the dominant part doesn't hurt anything.

Effective Boundary Conditions

Boundary Layers

The WKB turning point as a boundary layer. $\hbar\nabla^{2}S$ dominates,
like viscosity does at boundary. $\mu\sim\hbar$, kind of. de broglie
wavelength $p=\frac{\hbar}{\lambda}$ is analogous to Reynolds Number
$\rho v=\frac{\mu}{a}$. Hrrrm. This is total crackpottery. But
interesting. This is totally wrong. $\nabla^{2}S=0$ is supposed to be
the velicty potential conditon.

Quantum-esque fluid dynamics. The burgers equation. Quantum mechanics
linearizes chaos, maybe it also linearizes turbulence. Hamilton Jacobi
equation is basically bernoulli equation.

How can you get quantum to have vorticity equivalent. Vorticity is like
vector potential, or B. Particle in mangetic field? Quantum schrod + EM
dynamics = fluid dyanmics?

$$\nabla\vec{A}e^{iS}$$

Does this suggest that perhaps a particle scttaering of a cylinder with
B field should become turbulent in a sense? turblunece = interference?

Born and WOlf did mention skew fields occurring in electron optics.
Could be referring to magentic field stuff.

I suppose that the State action (one set of variables) describes
noninteracting fluid dynamics (pressure free) aka dilute gas dynamics,
which is almost the opposite of incompressible fluid dynamics. Vorticity
would indeed be possible in the presence of a magnetic field for the
noninteracting gas. The Hamilton function corresponds to a lagrangian
persective of the fluid dynamics.

The ibncmpressibility suggests that many body fermi systems might be the
right linear analog, which would suck, because those are hard.

Perhaps noninteracting rigid body gas could be used to include
voriticty. The rotation of the bodies in the gas gives vorcitiy.

Applications of inviscid flow to superconductivity. The paradox of no
drag would seem non paradoxical if used in this context. Drag =
resistance. Electron gas in metal is incompressible fluid. Bernoulli law
in electron gas? nonconducting Wing shapes producing lift in electric
current? If wing needs magentic flux thorugh it, then sort of hall
effect/bohm aharomov. Crystal fluid flow? Any special theorems?

What is wkb in magnetic field?

$$e^{iS+\int A\cdot\nabla S}$$

Applications to scattering. Is the velcoty potential exactly what you
should put in the exponential? eikonal approximation. For constant
amplitude field solutions only. (COnstant amplitude corresponds to
incompressible)

$$e^{i\frac{m}{\hbar}\phi}$$

Scattering of electrons off a tilted plate ought to produce lift.

Vortex dynamics - two vortices rotate abut a center of vorticity. Cooper
pairs? I'm being real silly here.

Vortex = electron spin magnetic field. back to the idea of rigid bodies
carrying angular momentum. Vortex rings instead offilaments (tiny
current loop/dipole)

Neutral spin liquid is model of rotational inviscid flow?

Or in superfluids, I've heard that vortices in the fluid are important.

Wavefronts are volumes carried with flow.

### Conservation laws

The mass (or any substance) in a region is

$m=\int\rho dV$

or the charge in a region

$Q=\int\rho dV$

To decrease these things, we have to have it flow out of the boundary

The flow $j$ per unit area is

$\vec{j}=\rho\vec{v}$

So the rate of change of mass

$$\dot{m}=\int\partial_{t}\rho dV=\int\rho v\cdot\hat{n}dA$$

If we use Gauss' Law we can turn the right hand side into a volume
integral

$$\int\nabla\cdot(v\rho)dV=\int\rho v\cdot\hat{n}dA$$

Hence we have the differential form

$$\partial_{t}\rho-\nabla\cdot(\rho v)=0$$

This is called the contuity equation. Its a good one. Take note. We can
use some vector product rules (basically guess something that looks
product rule like and has the vectorially-ness match in the right spots
and you'll usually get it right.)

$$\partial_{t}\rho-\rho\nabla\cdot v+v\cdot\nabla\rho=0$$

Under the condition that the fluid is incompressible, all derivatives of
$\rho$vanish and we instead have

$$\nabla\cdot v=0$$

The material derivative is the changes that a particle that follows
along the flow sees. You can basically replace time derivtatives in
particle theory with this operator instead to get fluidy equations

$$D=\partial_{t}+v\cdot\nabla$$

The momentum in the fluid per unit volume is also $\rho v$

So $F=ma=m\frac{dv}{dt}=\frac{dp}{dt}$ becomes

$$D\rho v=f$$

We have to work on a per volume basis, so bscially all equations get
divided by a volume. The volumetric force $f$ is $\frac{F}{V}$

The pressure acts on all sides of a little cube, so only gradients of
pressure will create net forces. Also $p=\frac{F}{A}$ the grdient adds
an extra length in the dneominator, $\nabla p=\frac{F}{V}$. The force
pushes towards lower pressure, so put a negative sign on that sucker.

$$D\rho v=-\nabla p+f$$

Other forces that show up a lot are gravity $f=-\rho g\hat{z}$ and
noninertial centrifugal force $f=\rho\Omega\times v$ , or maybe a
charged fluid will have a electric field term $\rho_{q}E$

If we're working incompressible then we can bring that $\rho$ out

$$\rho Dv=-\nabla p+f$$

If we assume that the flluid is irrotational then $\nabla\times v=0$,
And by Helmhotlzs theroem there is a potential $v=\nabla\phi$, in the
same way electorstiac vectors can be derived from

From the incompressible condition, the potnetial obey's lapaces euqstion

$$\nabla\cdot v=\nabla^{2}\phi=0$$

SOurces on the other side of this represent regions of fluid injection
if you've got them. As an example of one of the worst idnetites in
vector calculus, we have

$$\nabla\frac{1}{2}v^{2}-(v\cdot\nabla)v=v\times(\nabla\times v)$$

It is the vector calculus version of the worst identity in regular
vector algebra, plus a use of the product rule

$$a\times(b\times c)=(b\cdot a)c-(c\cdot a)b$$

Anyhoo, we can use this in the momentum equation.

$$\rho\nabla\frac{1}{2}v^{2}=-\nabla p-\nabla\rho gz$$

$$\frac{1}{2}\rho v^{2}+p+\rho gz=\text{Const}$$

We get the Bernoulli equation after all of this.

This equation is kind of a version of Energy Conservation.

### The one way wave equation

$f(x-ct)$ Looks like a function that's sliding to the right at a
velocity c.

The 1-d version of the wave equation is

$\partial_{t}-c\partial_{x}=0$

We can make c a function of x for spatially varying wave equation

If we want to bump this up to higher dimensions, we can still have a one
way wave equation, except the function c becomes a vector function
$\vec{c}.$In this way, the way the function is moving is detemrined by
its location. The function $\vec{c}$ is like a railroad that the lumps
in the function follow.

### Vector Differential Operators

The divergence is defined as the limit of flow out of an inifitesmal box

The curl is defined as the limit of a little baby loop integral

The gradient is the limit of a little baby line integral

### Vector Potential Solutions

Vector potential soolutions are related to a bunch of electrostatic and
magnetostatic solutions.

We can use the solution of a line charge

We can use the solution for magnetic field around a striaght wire as a
vortex solution

$$v=\frac{\Gamma}{2\pi r}\hat{\phi}$$

Another good one is to use th legendre series expansion for axially
symmettric problems

$$\sum(a_{n}r^{n}+b_{n}r^{-n-1})P_{n}(\cos\theta)$$

### Viscosity

### Multipoles and 

Force is like charge, comporession and ension like dipole. Torque is
magneticy, bending moment if magentic quadroply.

### Harmonic Derivatives

$$\nabla_{l}^{m}u=\frac{1}{\epsilon^{l}}\int Y_{l}^{m}(\theta,\phi)u(r'+\epsilon r)d\Omega$$

This will split off the right terms in the Taylor series, a local
version of an orthognal function expansion. If we differentiate a vector
function

$$\nabla_{l'}^{m'}v_{l}^{m}$$
