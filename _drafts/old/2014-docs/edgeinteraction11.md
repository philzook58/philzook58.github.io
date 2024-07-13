The technique of bosonization is a powerful one for investigating the
properties of stronly interacting 1-D systems.

The effective theory of the bulk of the quantum hall fluid is described
by a set of vector potentials $a_{I\mu}$, which can be intuitively
though of as the magnetization ($M_{zI}=a_{I0})$ and polarization
$(\epsilon_{ij}P_{Ij}=a_{Ii})$. The magnetization and polarization are
potentials for charge density and current so likewise is $a_{\mu}$ a
potential for charge and current. It is most convenient to normal
$a_{\mu}$ such that it describes number density and number current.

The concept of binding flux to charge can be written as

$B=\frac{1}{\nu}\rho$

Which is the standard definition of filling factor for a quantum hall
state.

It follows by the conservation of charge and Faraday's Law that

$E_{i}=\frac{1}{\nu}\epsilon_{ij}j_{j}$

In terms of the vector potentials $A_{\mu}$and $a_{\mu}$

For more than one fluid, these equations can be updated

$B=K_{IJ}\rho_{J}$

$E_{i}=K_{IJ}\epsilon_{ij}j_{jJ}$

The total charge density is $\rho=q_{I}\rho_{I}$. The filling factor is
$\nu=\frac{\rho}{B}=q_{I}K_{IJ}^{-1}q_{J}$

Like gravitational waves in a deep lake, the edges of the system can
possess dynamics. From elementary electrostatics on the edges of any
system, $P\cdot\hat{n}$ gives the amount of surface charge and
$M\times\hat{n}$ gives surface current. Hence nonzero $a_{\mu}$ on the
edges implies excitations on the edge of the droplet. If the fluid is of
constant density $P\cdot n$ corresponds to a height $h$ that the liquid
has sloshed around the equilbrium surface of the droplet.

### Where to go next

Polarization is not well defined locally. The conception of polarization
as abunch of little dipoles that we could actually see with a microscope
does not apply here. The polarization is merely an integral of the
density, which means it depends on the influence of density at far away
positions. These changes correspond the standard gauge changes in the
potential $a_{\mu}$.

What are the dynamics of these surface waves? One is in a magnetic field
and a binding potential, so one expects naively that they will move
perpendicular to the binding force with a constant velcoity v. If we
assume our system is truly galilean or lorentz invariant (which is not
true due to fixed background. There is definitly always a porferred
reference frame inside a material), we can boost into a frame where the
electric field is gone. This means

At this level, we anticipate that the edge will posssess waves that move
in one direction at constant velocity.

It is puzzling how to quantize such a thing. One clue is the scalar
bosonic field. Using the D'alembert decomposition

The canonical momentum

One knows that the full solution of the wave equation (which we can
quantize easily) is the sum of leftward and rightward parts.

$\phi(x,t)=\phi_{L}(x-vt)+\phi_{R}(x+vt)$

The D'alembert solution

$\Pi=\partial_{t}\phi$

$\phi_{L}=\phi+\int\Pi dx$

All properites are moving leftward, so which should we associate with
the implied commutation relations of $\phi_{L}$?

$\int P\cdot ndx=\phi_{L}$

Perhaps going microscopic at this point is clarifying.

### The Abelian Edge theory

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
