### States Exist

The state of a thermodynamic system has N free variables. Once you fix
those N, all other quantities ought to be expressible as functions of
them. These states are often inherited from or related to ordinary
kinematics or dynamics.

In the common special case of the closed piston system, the state has 2
variables. The quantities of interest are Energy E, Temperature T,
Volume V, pressure p, Entropy S.

### A digression on Partial Differentiation

Partial derivatives are a tad more subtle than is emphasized in Calculus
courses. The ordinary rule of differntiting one variable while keeping
all other variables fixed is insufficent for thermodynamics, since we
will often need to keep fixed quantities which are not one of the
vairables themselves. For example, consider the function
$f(x,y)=x^{2}+y^{2}+x$

The ordinary partial derivative leaves assumed that y is kept fixed

$$\frac{\partial f}{\partial x}]_{y}=2x+1$$

Whereas you may also partial differentiate keeping the radius r fixed

$$\frac{\partial f}{\partial x}]_{r}=1$$

Notice that the fixed quantity changes the value of the partial
derivative

### Entropy Exists

The Second principle of thermodynamics is that entropy is a quantity
that systems have. You may choose to use entropy as a state variable, or
you may choose to express it in terms of your state variables.

### Entropy for an Equilibrium Isolated system is Maximal

Isolation is a constraint placed upon the system. A system in complete
isolation has constant total Volume, Energy, momentum, angular momentum,
etc.

This is often written as

$$\delta S]_{E,V,\ldots}=0$$

### The Grand Potential

The Grand potential is for when the system ius in complete contact with
a reservoir, which can supply energy, volume and also number.

$$\delta\Omega)_{p,T,\mu}=0$$

### Duality and the Legendre Transform

Optimization problems often posess a dual problem. Let us suppose that
you know the maximum value of the objective function under your
constraint (although perhaps you do not know what value of the
coordinates that achieve this). You could instead take the objective as
a constraint for a secondary dual problem. If loosening your original
constraint always allowed a higher maximum to be achieved (the condition
that will achieve this is related to convexity)

In the context of linear algebra and least squares, the contraint
specifies a subspace that you can work with. Given that subspace, we
attempt to minimize the square error. The dual problem is to assume that
you know the value of the squared error. You then find the maximal
vector that achieves this squared error.

Because of the Lagrange multiplier has the intepreation of a derivative
of the objective function with respect to a constraint, we can look at
the inverse of the multiplier.

$$\frac{1}{\frac{\delta f}{\delta\phi}}=\frac{\delta\phi}{\delta f}$$

Using the method of Lagrange multipliers, we construct the lagrangian to
takecare of the fixed E constraint

$$L_{1}=S-\lambda E$$

The maximal condition becomes

$$\delta S)_{V}-\lambda\delta E)_{V}=0$$

However we can rearrange this equation simply

$$-\frac{1}{\lambda}\delta S+\delta E=-\mu\delta S+\delta E=0$$

Which is the problem we would get from The lagrangian

$$L_{2}=E-\mu S$$

This is instread comes from the condition that for fixed entropy and
fixed Volume, the system will be in the state with minimum energy.

$$\delta E)_{S,V}=0$$

Now ths pricniple correspond to the principle of minimum energy from
mechanics. The ideal lack of coupling between the thermodynamic degrees
of freedom and the mechanical reduces this law to

### Examples

The isolated piston is two boxes of gas. The tweo sides of the piston
can exchange volume and energy with each other in such a way that the
total remains fixed.

$V_{1}+V_{2}=V$

$E_{1}+E_{2}=E$

The entropy is the sum of the indvidual entropies

$S_{1}+S_{2}=S$

$dV_{1}+dV_{2}=0$

$dE_{1}+dE_{2}=0$

$dS_{1}+dS_{2}=0$

$$\delta S(V_{1},V_{2},E_{1},E_{2})]_{E,V}=0$$

### Gibbs Principle or The Principle of Virtual Subdivision

Any system can be subdivided into a collection of smaller systems. We
can then use one of our equivlaent forms of equiblirum condition to
maximize out these degrees of freedom. Because of this, we achieve
certain inequalities that must always be achieved by thermodynamuic
potentials. Essentially certain hessians of potentials must be positive
definite matrices, which is a condition of convexity and stability.

Let's take a brick. The condition of mechanical equibirium may be taken
to be miniminum energy, or it could be the balancing of all forces. We
may subdivide the brick into smaller and smaller bricks. We produce new
variables, but still we have a balancing of forces

### Lagrange Multipliers

Lagrange Multipliers are a method by which to maximize with respect to
constraints.

Suppose you had cleverly achieved writing f as a function of the
contraint $\phi$ and the d-1 other variables. Then you could write its
differential as

$$\delta f=\delta f)_{\phi}+\frac{\partial f}{\partial\phi})_{x_{n}}d\phi$$

$$\delta f)_{\phi}=\sum_{n=1}^{d-1}\frac{\partial f}{\partial x_{n}}dx_{n}$$

Now optimization under contstraint is all about setting

$$\delta f=0$$

Because of the constraint, one can only move in the directions$d\phi=0$,
hence we have

$$\delta f)_{\phi}=0$$

Anotehr way of doing this is to allow us to wiggle in any direction and
take off the part due to changing $\phi$, which we weren't supposed to
do.

$$\delta f-\frac{\partial f}{\partial\phi})_{others}d\phi=0$$

With $\frac{\partial f}{\partial\phi})_{others}$ being some number
evaluted at the extremum point which we will call $\lambda$. However,
how the hell can we know what the value of $\lambda$ is if we can't even
find the extremum point? Leave it unevaluted. We can expand $\delta f$
and$d\phi$in the our original variables since that is the form we have
their expression in.

$$\delta f=\sum_{i}\frac{\partial f}{\partial x_{i}})_{x_{i\ne j}}dx_{i}$$

$$d\phi=\sum_{i}\frac{\partial\phi}{\partial x_{i}})_{x_{i\ne j}}dx_{i}$$

We then have

$$\sum_{i}\frac{\partial f}{\partial x_{i}})_{x_{i\ne j}}-\lambda\frac{\partial\phi}{\partial x_{i}})_{x_{i\ne j}}dx_{i}=0$$

This equation must be satisified regardless of which direction we make
dx so very term in the sum must vanish. This is known as Lagrange's
Method of the undetermined multiplier. Perhaps a better name would be
Lagrange's Method of the unknown constraint derivative. If we have more
contraints, we can instead produce analogous expressions to the above
with additional lagrange multipliers.

Note that the Lagrange multiplier shows the dependance upon small
changes to the contraint.

$$\phi=0\Rightarrow\phi=\epsilon$$

$$f_{min}\Rightarrow f_{min}+\lambda\epsilon$$

In a sense, the lagrange multiplier measures how much the function
"hates" the contraint. In mechanics, where f may be the potential energy
in statics or lagrangian in dynamics, you may recall the the lagrange
multiplier often ends up being the force of contraints, such as normal
forces or tensions in rods or something. This is why. If the contraint
is secretly slightly "spongy" the lagrange multiplier is also a measure
of how much the contraint is violated.

Lagrange Mulitplier Series

If you want any guarantees about convergence, you'll have to talk to my
lawyer

We can rewrite the condition as

$$d(f-\lambda\phi)=0$$

### Capacitor Processes and Constraints

The energy in a capacitor is a function of two vairables , (Q,V), (Q,d),
(Q,C)

The differential is most natrually expressed

$$dU=Fdx+VdQ$$

We may choose to connect it to a battery, keeping Voltage constant. Or
to a mass, keeping force constant, or isolate the thing, keeping charge
constant. We may consider different functions, the equivalents of the
enthalpy function (and to some degree the free energies, although we
have abasonded entropic consideration here, although we could and must
if we consider changes to the dielectric in between the plates)

We can attach two capacitors to one another

The equation of state of a capacitor is

$$CV=Q$$

$$C=\epsilon\frac{A}{d}$$

Discharging capacitors is an irreversible process. We could slosh energy
around in capacitors forever if we did it adiabatically.

### Enthalpy and Pressure Work

### The Free Energy F

From E, we can use a Legendre transfromation to change our constraint
from constant S to a constant T.

$$F(\lambda,V)=\min_{S}(E(V,S)-\lambda S)=\min_{S}F(\lambda,S,V)$$

Notice that we replaced the

$$\delta E)_{S,V}\rightarrow\delta F)_{\lambda,V}=0$$

Now just for kicks, we'll replace $\lambda$ with $T$. The first step we
took

$$F(\lambda,V)=\min_{S}(E-\lambda S)$$

This condition implies that

$$\frac{\partial E(V,S)}{\partial S})_{V,\ldots}-\lambda=0$$

But the defginition of T is in fact

$$T(S,V)=\frac{\partial E(V,S)}{\partial S})_{V,\ldots}$$

### Gibbs Energy

From F, we can use a Legendre transfromation to change our constraint
from constant V to a constant p.

$$G(\lambda,V)=\min_{V}(F-\lambda V)$$

$$\delta F)_{T,V}\rightarrow\delta G)_{\lambda,T}=0$$

The Gibbs Free Energy is one of the best potentials of all.

Escaping Potential.

Analog of Free boundary conditions vs Fixed boundary conditions in mec
hanics

### Systems of changing N

Let's say we have a block of homogenous goo at pressure p and
temperature T. If we draw an imaginary boundary around a subpice of the
good, it then has a volume V, an entropy S, and a Gibbs Energy G. If we
redraw our our boundary, we do not change the pressure, we do not change
the temperature, but we do change the number, volume and entropy in the
interior of our imaginary boundary

### Ideal gas

$$Pv=RT$$

$$U=\frac{3}{2}PV$$

$$du=c_{V}dT$$

$$ds=\frac{1}{T}du+\frac{p}{T}dv$$

$$ds=\frac{c_{v}}{T}dT+\frac{R}{v}dv$$
$$s=s_{0}+c_{V}\ln(\frac{T}{T_{0}})+R\ln(\frac{v}{v_{0}})$$

$$s=s_{0}+c_{p}\ln(\frac{T}{T_{0}})-R\ln(\frac{p}{p_{0}})$$

$$G=\mu N$$

$$\mu=g$$

$$G=U-TS-PV$$

$$g=\mu=c_{V}T-RT-Ts$$

$$dG=-SdT+Vdp+\mu dN=\mu dN+Nd\mu$$

$$d\mu=vdp-sdT$$

$$\mu=\mu_{0}+kT\ln(\frac{p}{p_{0}})$$

### Electricity and Chemical Potential

Thermodynamic potentials are potentials in the viscous sense. In
mechanics, potentials cause forces, which are second derivatives. In
viscous situations, like terminal veleocity, potential differences cause
velocities and hence are the first derivative of x. This is the proper
way to think about thermodynamic potentials, and is applicable to the
kinetics of reactions. Chemical potentials are the potentials that cause
velcities of reaction (rates of reaction), not acceleration of
reactions.

If the consituents are charged, then increasing the number inside a
volume will raise the electrostatic potential as we as any pressures
tmepuratures etc.

We tend to think that some of the thermodynamic force on a subatnce is
due to entropic force and some is due to electrical force, although they
are not particularly seperable.

We could imagine connecting a capacitor made of the same material, then
firing an electron beam between the plates and measuring the deflection.

Condider a gas of charged particles. They will be tempted to stick to
the boundaries of the container, yet entropy will tend to make them fill
the volume. The two will strike a balance. At high tmepratures, entropy
domiantes and the gas will fill the volume. At low tempuratures,
electrostatics will dominate and

We pretend that if the charged particles were neutral. Then this change
in energy per number added would be the chemical potential. The
electrochemical potential is

If we suppose the charged gas is instead in a container containing a
unifrom fixed charge denisty, then the electron like to spreadout like
they should.

What if we have a container with two different fixed charge densities
adhjoined? what is the equibiium then? We should have a fight between
electrostatics and entropy.

The electrostatic energy is due to self interaction of the electron gas
and interaction to the fixed background.

$$E=\int\rho G\rho+\phi_{f}\rho$$

Enetropy wins at high tempuratures, this is why extrinsic goes to
intrinsic behavior.

We can construct a variational model of this with four regions. The two
side lobes and the depletion region.

The field from a unform block of charge increases linearly from 0 in the
center of the block to
$\frac{\sigma}{2\epsilon_{0}}=\frac{\rho L}{2\epsilon_{0}}$external to
the block. Hence the potential from a block positioned at a with width L
and denisty $\rho$

$$\phi(x,a,L)=\begin{cases}
(x-a)^{2}+(x-a)\\
(x-a-\frac{L}{2}) & x\ge a+\frac{L}{2}
\end{cases}$$

$$\phi(x)=\begin{cases}
\frac{\rho L}{2\epsilon_{0}}x & x\le0\\
x^{2}+\frac{\rho L}{2\epsilon_{0}}x & 0\le x\ge L\\
\frac{\rho L}{2\epsilon_{0}}(x-L)
\end{cases}$$

a gut feeling tells me to use the entropy as

$$S=\sum_{i}N_{i}k\ln L_{i}$$

$$F=E-TS$$

### Field Thermodynamics

Now the thermodynaimc potentials become functionals abnd we use caclulus
of variations

$$\delta E=\phi\delta\rho$$

We can take the limit of a ton of little pistons. T(x) is the
tmepurature of the piston at position x for example.

$$\delta E=\int dVT(x)\delta s-\nabla P(x)\cdot\delta\epsilon+\mu(x)\delta n$$

$$\mu(x)=q\phi+\mu_{c}$$

Now $\delta v$ is a strange one. It is change of volume per volume. If
volume increases in one spot, it must decrease elsewhere

$\epsilon$ is a displacement of the underlying coordinates

Since these are all imaginary boundaries in a roughly homogenous
material, it makes more sense to start from the Gibbs potential

$$\delta G=\int dVs\delta T-\delta p+\mu(x)\delta n$$
