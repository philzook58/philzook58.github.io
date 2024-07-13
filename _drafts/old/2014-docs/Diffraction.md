Light is made of ray bundles or superposed wavefronts. Etendue cannot be
compressed indefitnely

Optical momentum $p=\hbar k$. Classical Hamiltonian mechanics of the
photon =\> quantize to get diffraction theory. Etendue is phase space
integral Thing is massless, so never at rest. Hence the device of the
optical axis. Axis momentum, and transverse momentum. To go to the more
general non-axis theory is tougher. How does spatial (optical axis)
coherence in optics translate to time coherence in QM?

Diffraction from Screens. Fourier transform into optical momentum

$$\int dxdyI(x,y)e^{-ipx+-iqy}$$

Diffraction from 3D objects - Still a fourier transform, except we can
only get at a sphere of wavevectors. We see slices. Could take this as a
case of the screen scattering, where the z loaction gives you extra
phase factor

$$\int dxdyI(x,y,z)e^{-iz\sqrt{n^{2}-p^{2}-q^{2}}}e^{-ipx+-iqy}$$

TEM - coulomb scattering combined with.

Fresnel diffraction = paraxial diffraction

The zone construction, the path length change is the sum of the two
curvatures

The rate a surface pulls away from its tangent plane is
$\frac{1}{2}k_{1}x^{2}$

$m\lambda=\frac{1}{2}(k_{a}+k_{b})s^{2}=\frac{1}{2}(\frac{1}{a}+\frac{1}{b})s_{m}^{2}$

The 90 degree phase shift that occurs is due to the fact that in the
zone construction, The mean value of the zone is 90 degrees out out
phase with the value in the middle.

Total amplitude is 1/2 that of first zone.

As you look through a hole, image what zones you can see. if off axis,
you see an off axis slice of zones, which have a tendency to cancel. The
first zone is a big deal

The first zone is essentially the beam width.

Lorentz Reciprocity is one foundation of etendue.

Remove time dependance with energy condition E go to maupertuis
pricniple.

Optical axis z.

Amplitude prop to Z

Born approximation

Ewald Sphere

Laue Condition

$$\Delta k=G$$

Bragg Condition $$2d\sin\theta=n\lambda$$

Atomic factors convolved lattice delta comb =\> multiplication

The Recipricol Lattice
----------------------

The lattice vectors are not neccessarily an orthonormal set of vectors.

$$a\cdot a$$

The Grammian is a matrix composed of all the dot products of the basis

$$G=\left[\begin{array}{ccc}
a\cdot a & a\cdot b & a\cdot c\\
b\cdot a & b\cdot b & b\cdot c\\
c\cdot a & c\cdot b & c\cdot c
\end{array}\right]$$

$$\vec{v}=pa+qb+rc$$

or we could write it with the basis vectors understood as a column
vector

$$v=\left[\begin{array}{c}
p\\
q\\
r
\end{array}\right]$$

To compute the inner product

$$v\cdot u$$

We can use our grammian

$$v^{T}Gu$$

$$a=\left[\begin{array}{c}
1\\
0\\
0
\end{array}\right]$$

The inverse of the grammian will get you some nice things. Use Cramer's
rule and you can see that the columns of the inverse matrix will be the
recirpol lattice vectors.

Kind of annoying though. G is also a metric if you like that
temrinology. We love that old fashioned sum of squares.

Well what we can do is define the dual lattice (recipricol lattice)

To every periodic lattice there is a dual lattice. Pretty remarkable. If
we take the forueir transform of a dirac comb, we get another dirac
comb.

1-forms are defined to be linear scalar valued functions on vectors.
They can be represented by series of planes ( which look like local
contours of a function).

Describing atoms with hkl numbers. Is this correct? What kind of planes
can an atom be involved in?

Crystals
--------

### cubic 

all 90 all equal

Examples: pyrite silver gold diamond garnet galena halite spinel
fluorite

### tetragonal - 

all 90, two sides equal

Example: zircon

Orthorhombic all 90 degrees all different sides

monoclinic - one angle is not 90

triclinic - no angles are 90

rhomobohedral - cube stretched along diagonal. all angles equal, all not
90. all sides equal.

Thermal scattering
==================

If we want to consider thermal scattering we could consider a random
hamiltonian. However, what makes more sense is to consider a desnity
matrix under a fixed hamiltonian

The density matrix for the incoming state will factorize into the
incoming momentum state (which we may want to give a little bradth in
momentum and positioning anyhow) and the density matrix of

$$\rho_{0}=|k><k|e^{-\beta H_{crystal}}$$

The probabiltiy of a transition to final momentum kf

$$tr\rho(t)(|k_{f}><k_{f}|\otimes I)$$

Classically I could build the disitrubiton for deterministic dynamics

$$P(f,i)=\delta(f-f(i))P(i)$$

$P(f|i)=$

Its real tempting to do

$$tr\rho_{f}\rho_{0}(t)$$

Where $\rho_{f}$ is the final distrubiton

as the analog of the ampltidue calculation

$$<f|e^{iHt}|i>$$

However, The set of $\rho_{f}$ isn't really a basis type thing.

Anyhoo, you can do a partial trace over the crystal basis to produce an
effective scattering ampltidue includding debye waller factors

You get an effective hamilltonian

$$tr_{crystal}U_{int}(x_{crystal}-x_{wave})e^{-\beta H_{crystal}}$$

For a harmonic crystal H crystal is diagonalized in plane phonon waves.
