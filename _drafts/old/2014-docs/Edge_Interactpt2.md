Explanation of 7/3 8/3 States
-----------------------------

The Bonderson-Slingerland states are hierachical states built upon the
pfaffian state in a manner similar to the haldane-halperin hierarchy
being built upon simpler fractional quantum hall states. For the
purposes of the edge, they retain the two integer edges modes and
inherit the majorana edge mode from the pfaffian state.

The pfaffian state is given by

$$\text{Pf}[\frac{1}{z_{i}-z_{j}}]\prod_{i<j}(z_{i}-z_{j})^{2}e^{-\sum_{i}\frac{1}{4}|z_{i}|^{2}}$$

Using this wavefunction as a starting point, one can introduce
parametric adjustments to the wavefunction called quasiparticles whose
locations are given by $w_{j}$. The $w_{i}$ will go into places in the
wavefunction that makes them look very similar to the electron
coordinates $z_{i}$, but their interpretation is different. They
parametrize a location of probable deficit, or surplus of charge of the
electrons and their movement parametrizes curious quantum ampltidue

As an example of this consider the quasihole (Nayak)

Hierearchical states are constructed by condensing these quasiparticles
into highly correlated

Similarly to how one can project out the component of a wavefunction
that has a particle with momentum k by integrating against $\psi_{k}$
for example, the component of a many body wavefunction overlapping with
the laughlin state $\psi_{\frac{1}{3}}$ by taking the inner product of
this waevfunction with the entire wavefunction. We can build a hierarchy
by projecting out the quasiparticle coordinates $w_{i}$ rather than the
electron coordinates $z_{i}$.

If a quasipartcile is written $\psi=Oe^{\sum i\phi_{j}l_{j}}$, then from
the vector $l$ we can read off it's properties

The Charge density operator is
$\rho=\frac{e}{2\pi}\sum_{i}q_{i}\partial_{x}\phi_{i}$ . The charge of
the quasiparticle is $Q=l_{I}K^{-1}q_{I}$. The topological spin
$\Theta=l_{I}K^{-1}l_{I}$.

Considering $K^{-1}$ as a metric all quasiparticles with an $l$
orthogonal to $q$ are neutral. We can also sepearate quasiparticles into
their neutral and charged part $l=\alpha q+\beta n_{i}$. $nK^{-1}q=0$.

### $L_{\frac{1}{3}}$

The simplest proposed state is the abelian Laughlin state with filled
Landau Levels.

The action for the bosonic mode is given by
$S=\frac{1}{4\pi}\int dxdt3\partial_{t}\phi\partial_{x}\phi_{1}+v\partial_{x}\phi\partial_{x}\phi$.
Leading to the commutation relation
$[\phi(x),\phi(x')]=\frac{i\pi}{3}\text{sign (x-x')}$

There is a single type of charge $\frac{e}{3}$ quasiparticle given by
$$\psi_{q}=e^{i\phi}$$

### $BS_{\frac{1}{3}}^{\psi}$

The $BS_{\frac{1}{3}}^{\psi}$ state is a nonabelian hierarchical state
built from the Pfaffian state by leaving the nonabelian parts of the
thoery alone and the abelian bosonic modes. The K matrix is
$\left[\begin{array}{cc}
2 & 1\\
1 & -1
\end{array}\right]$ leading to the expression for the bosonic part of
the action
$S=\int dxdt\frac{1}{4\pi}[2\partial_{t}\phi_{1}\partial_{x}\phi_{1}+\partial_{t}\phi_{2}\partial_{x}\phi_{1}+\partial_{t}\phi_{1}\partial_{x}\phi_{2}-\partial_{t}\phi_{2}\partial_{x}\phi_{2}]+i\psi(\text{\ensuremath{\partial}}+v\text{\ensuremath{\partial}})\psi$.
where $\psi$ s a majorana mode. There are two quasiparticles given by
$$\psi_{q1}=\sigma e^{i\frac{1}{2}\phi_{1}+i\frac{1}{2}\phi_{2}}$$
$$\psi_{q2}=e^{i\phi_{1}}$$

where the operator $\sigma$ changes the boundary conditions for the
Majorana fermion from periodic to antiperiodic and has the scaling
dimension 1/16.

This state has a backwards propagating modes, which must be considered
in order to calculate the tunnelling exponenets.

The charge vector is $q=\left[\begin{array}{c}
1\\
0
\end{array}\right]$

The neutral vector is $n=\left[\begin{array}{c}
1\\
-1
\end{array}\right]$. Note that $n^{T}K^{-1}q=0$

$l_{1}=\left[\begin{array}{c}
1\\
0
\end{array}\right]+\left[\begin{array}{c}
-\frac{1}{2}\\
\frac{1}{2}
\end{array}\right]$

$l_{2}=\left[\begin{array}{c}
1\\
0
\end{array}\right]+\left[\begin{array}{c}
-1\\
1
\end{array}\right]$

We can caluclate $g_{n}$ for $\psi_{q1}$by adding
$|\left[\begin{array}{cc}
-\frac{1}{2} & \frac{1}{2}\end{array}\right]K^{-1}\left[\begin{array}{c}
-\frac{1}{2}\\
\frac{1}{2}
\end{array}\right]|=|-\frac{1}{4}|+\frac{1}{8}=\frac{3}{8}$. The factor
of $\frac{1}{8}$ comes from the external nonabelian factor
$<\sigma\sigma>\propto\frac{1}{t^{\frac{1}{8}}}$ .

### $BS_{\frac{2}{3}}$

The $BS_{\frac{2}{3}}$ is built similarly to the
$BS_{\frac{1}{3}}^{\psi}$ state. The K matrix is
$\left[\begin{array}{cc}
2 & -1\\
-1 & 2
\end{array}\right]$.
$S=\int dxdt\frac{1}{4\pi}[2\partial_{t}\phi_{1}\partial_{x}\phi_{1}-\partial\phi_{2}\partial_{x}\phi_{1}-\partial_{t}\phi_{1}\partial_{x}\phi_{2}+2\partial_{t}\phi_{2}\partial_{x}\phi_{2}]+i\psi(\text{\ensuremath{\partial}}+v\text{\ensuremath{\partial}})\psi$.
The two quasiparticles are $$\psi_{q1}=\sigma e^{i\frac{1}{2}\phi_{1}}$$
$$\psi_{q2}=e^{i\phi_{1}}$$

$$\psi_{q3}=e^{i\phi_{2}}$$

### Particle Hole Conjugate States

Particle Hole conjugation is achieved by projecting out a many-body
state $\psi^{\dagger}(\{z_{i}\}_{0\le k\le m})$ against a fully filled
Landau level $\psi_{LL}(z)$.
$\bar{\psi}(\{z_{k}\}_{m<k\le N})=\int\prod_{i=0}^{m}dz_{i}\psi^{\dagger}(\{z_{i}\}_{0\le k\le m})\psi_{LL}(\{z_{i}\}_{0\le k\le N})$

This may result in a new topological state.

   QuasiParticle   $g_{c}$   $g_{n}$   $e^{*}$   g
  --------------- --------- --------- --------- ---
                                                
                                                
                                                
                                                

Estimating Parameters
---------------------

What is physical picture of what is going on? Alternating strips of
compressible and incompressible stripes. What is composition of these
stripes? The simplest model (and one that cannot be correct) is that
they are locally simple slater derminant. Using a basis of states that
have support only in a region where we can consider the electrostatic
potential to be close to flat (a slowly varying field or adiabatic
approximaiton), we can perform the slater determinant. In the
incompressible regions It is a fully filled landau level. In the
compressible regions, a thermal assembly of partially filled landau
levels. FQHE states cannot be written as slater determinants however
(except perhaps with the composite fermion picture, in which case they
are kind of, except the projection step to the LLL is nontrivial).

It is suggested that the edge has the behvaior of sweeping out the
filling factors from the current maximal filling factor to $\nu=0$.

Effect of the Finite region of Across Gate coulomb interaction
--------------------------------------------------------------

Temperature
-----------
