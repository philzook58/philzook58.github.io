Condensor lens: before specimen, transforms between angular spread of
source and area of source. Varying the strength is achieved by the
brightness knob. Gi ven fixed aperture area

Condsnor aperture - Placed at the focus?

Brightness - current per unit area per solid angle. current per etendue.
Small source are bright. Highly angularly concentrated are birght. and
high power (current) output are bright. Brightness is a merasure of how
much power (current)per unit area can be concentrated on a screen.

Point Spread Function
---------------------

The point spread function is the blobbiness of a point source. for an
out of focus lens, it would be a circle of diameter $r=\alpha\Delta f$.
In fourier space, this is a multplication by a bessel function. The
zeros (or small places) of the bessel function are the unrecoverable
spots. Gaussian blur has wiener filtering. The PSF can also have the
airy disk business.

When electron passes through sample it experiences eikonal phase shift
(we're assuming it blasts right down the z-axis)

$$\int pdz=\int\sqrt{2m(E+V)}dz$$

As opposed to a free space shift

$$d\phi=\sqrt{2mE}dz$$

For big energies, we can approximate the square root.

$$d\phi=\frac{\pi}{\lambda E}Vdz$$

and basically the phase shift is just the integral of V along z, times
some constants.

Weak phase object approximation

$$e^{iV}\approx1-iV$$

This is the modification factor for the field after the specimen plane.
Then it gets jumble by the optics.

Total Field = Condensors to specimen \* specimen phase adjust\*
objective

$E=E_{1}+E_{2}$

$$I=|E|^{2}$$

The two seperate terms have the PSF to calculate them. However sources
may interact if coherent, and since nothing is really a point source and
will typically have at least some coherency, the PSF is not the whole
story.

Phase contrast: The PSF isn't quite right. Phase contrast is more
subtle. We want just the cross term from different sources.

Phase contrast function is linear approixmation to how phase differences
transforms to instenity on screen if phase shift is weak. Has to go to 0
at k=0 since net phase is irrelevant.

The phase contrast is quite similar in appearance to the T matrix. They
also use the letter T. How suspicious. Similarity to the phase angles in
partial wave expansion S-Matrix. Connection to Optical Theorem?

Fresnel
-------

A sphere is written in power series as

$$z=z_{0}+\frac{1}{2R}s^{2}$$

Basically, all of fresnel optics (the algebraic/analytic part anyhow)
stems from this approximations

The total path length between two points that has to go through a point
on a plame

$$\delta=a+b+(\frac{1}{2a}+\frac{1}{2b})s^{2}$$

You could also get this from binomial theorem on pythorgorean theorem.

The zones are areas that differ in phase by $\pi$. You can sort of just
count zones to get a gist of what's happening

Kirkhoff diffraction integral

$$\phi=\int\phi\frac{\partial}{\partial n}G-\frac{\partial}{\partial n}\phi GdS$$

$$G=\frac{e^{ikr}}{r}$$

Now, why does underfocus give bright fringes and overfocus give dark?

Fresnel diffraction can be thought of as free particle propgation of the
schrodinger equation. We're paraxial in the same sense that galilean
mechanics is paraxial to special relativty. The wave equation can be
transformed into the shcordinger equation by assuming the ansatz
$\phi(x,y,z)e^{ikz}e^{i\omega t}$where the derivatives of $\phi$ with
respect to z are small.

$$e^{i\frac{(x-x')^{2}}{2(t-t')}}$$

is the free particle porpagator whereas

$$e^{i\frac{(x-x')^{2}}{2(z-z')}}$$

Is the fresnel propagator.

Phase contrast under defocus can be interpetted as due to free particle
"clumping". Pure translation (the first derivative of phase $e^{ikx}$)
will not change the density of particles. However changes in velcity
will lead to clumping, which leads to an image. If we let free particles
of different phase rates propagate for just a little time, they will
clump.

What an ideal lens does is tweak instantaneously all the momentum of the
bits from an exploding bomb to converge back to a point. In classical
pahse space, this is the tilting of a momentum line to slope

particle in a box = waveguide.
