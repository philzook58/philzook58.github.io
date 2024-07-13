Short List of Things to just KNOW about Fourier solution of Dirac
=================================================================

$$p^{\mu}=i\partial^{\mu}$$

$$(i\gamma^{\mu}\partial_{\mu}-m)\psi=0$$

Is Dirac conjugation similar to the
$\overleftrightarrow{\partial_{0}}$thing?

$$\bar{\psi}=\psi^{\dagger}\gamma^{0}$$

Interpreting $\gamma^{0}$as a relativstic gamma factor ($u^{0}$). Does
this make sense?

$$\psi=\int\frac{d^{3}k}{(2\pi)^{3}2\omega_{k}}\sqrt{\omega_{k}}a_{k}^{s}u^{s}(k)e^{-ikx}+\sqrt{\omega_{k}}b_{k}^{s\dagger}v^{s}(k)e^{ikx}$$

$\psi$is hard to interpret by itself. Really we should think of $\psi$as
two fields, an electron field $u$ and a positron field $v$.

$$\psi(x,t)=u(x,t)+v^{\dagger}(x,t)$$

This is very evocative of leftward and rightward decomposition of wave
equation into G and F. And D'alembert Decomposition

Why the dagger on $v$? Conjugation corresponds to a time and parity flip
by CPT.

The electron equation is

$$\gamma_{\mu}p^{\mu}u=mu$$

This is very natural from the perspective of $\gamma^{\mu}$ as a
4-velocity operator.

$$\partial_{x}F=\partial_{t}F$$

$$\partial_{x}F=-\partial_{t}F$$

$$m\approx i\partial_{\tau}$$

The positron equation is

$$\gamma_{\mu}p^{\mu}v=-mv$$

Because in wave equation frequencies are squared, there is not such a
distinction between positive and negative freq solutions

Positive frequency solutions

$$e^{-i\omega t}$$

$$u_{p}^{s}e^{i\vec{p}x}$$

$$e^{-ipx}$$

$$(-m+\gamma_{\mu}p^{\mu})u=0$$

Negative Frequency solutions

$$e^{-i(-\omega)t}$$

3-vector

$$v_{p}^{s}e^{-i\vec{p}x}$$

4-vector

$$e^{ipx}$$

$$(-m-\gamma_{\mu}p^{\mu})v=0$$

THESE ARE THE FUNDMENTAL EQs. Start Here

$$\gamma^{\mu}k_{\mu}u=mu$$

$$\gamma^{\mu}k_{\mu}v=-mv$$

$$(\gamma^{\mu}k_{\mu}-m)(\gamma^{\mu}k_{\mu}+m)=0$$

We have both our positive and negative freqeuncy solutions, so this
isn"t quite the dirac equation.

So if we apply $(\gamma^{\mu}k_{\mu}+m)$ to something and it doesn't
kill it, we get a vector that obeys $(\gamma^{\mu}k_{\mu}-m)u=0$ And
Vice Versa.

That's slick. Then we normalize these newly produced vectors.

$$u(k)=\frac{(\gamma^{\mu}k_{\mu}+m)}{u(0)^{\dagger}(\gamma^{\mu}k_{\mu}+m)^{\dagger}(\gamma^{\mu}k_{\mu}+m)u(0)}u(0)$$

$$(\gamma^{\mu}k_{\mu}+m)^{\dagger}(\gamma^{\mu}k_{\mu}+m)=$$

u and v are the direct product of two observable spaces. Spin space and
charge space. Interpretation of $S_{x}$ and $S_{y}$in charge space if
$S_{z}$ is charge operator?

Which Gamma Matrices to use?
----------------------------

### Nonrelativistic Basis

$$\beta=\left[\begin{array}{cc}
I & 0\\
0 & -I
\end{array}\right]=\sigma_{3}\otimes I$$

$$\alpha_{i}=\left[\begin{array}{cc}
0 & \sigma\\
\sigma & 0
\end{array}\right]=\sigma_{1}\otimes\sigma_{i}$$

### Dirac Basis

Texts: Bjorken and Drell, Griffiths, Ryder?

$$\gamma^{0}=\left[\begin{array}{cc}
I & 0\\
0 & -I
\end{array}\right]=\sigma_{3}\otimes I$$

$$\gamma^{i}=\left[\begin{array}{cc}
0 & \sigma_{i}\\
-\sigma_{i} & 0
\end{array}\right]=i\sigma_{2}\otimes\sigma_{i}$$

$$\gamma^{5}=i\gamma^{0}\gamma^{1}\gamma^{2}\gamma^{3}=\left[\begin{array}{cc}
0 & I\\
I & 0
\end{array}\right]=\sigma_{1}\otimes I$$

$$u^{1}=\left[\begin{array}{c}
1\\
0\\
0\\
0
\end{array}\right]$$

$$u^{2}=\left[\begin{array}{c}
0\\
1\\
0\\
0
\end{array}\right]$$

$$v^{1}=\left[\begin{array}{c}
0\\
0\\
1\\
0
\end{array}\right]$$

$$v^{2}=\left[\begin{array}{c}
0\\
0\\
0\\
1
\end{array}\right]$$

Chiral Reps:

Particle Antiparticle:

Advantages of Basis: Upper spinor is particle positive frequency state,
lower is antiparticle in Nonrelativistic Limit.

Disadvantages:

### Weyl Basis

Texts: Peskin and Schroeder, Ryder?

$$\gamma^{0}=\left[\begin{array}{cc}
0 & I\\
I & 0
\end{array}\right]=\sigma_{1}\otimes I$$

$$\gamma^{i}=\left[\begin{array}{cc}
0 & \sigma_{i}\\
-\sigma_{i} & 0
\end{array}\right]=i\sigma_{2}\otimes\sigma_{i}$$

$$\gamma^{5}=i\gamma^{0}\gamma^{1}\gamma^{2}\gamma^{3}=\left[\begin{array}{cc}
-I & 0\\
0 & I
\end{array}\right]=-\sigma_{3}\otimes I$$

Advantages of Basis: Effectively decouples spinors in relativstic limits
(or in zero mass limit)?

Disadvantages:

### Majorana Basis

$$\gamma^{0}=\left[\begin{array}{cc}
0 & \sigma_{2}\\
\sigma_{2} & 0
\end{array}\right]=\sigma_{1}\otimes\sigma_{2}$$

$$\gamma^{1}=\left[\begin{array}{cc}
i\sigma_{3} & 0\\
0 & i\sigma_{3}
\end{array}\right]=I\otimes i\sigma_{3}$$

$$\gamma^{2}=\left[\begin{array}{cc}
0 & -\sigma_{2}\\
\sigma_{2} & 0
\end{array}\right]=-i\sigma_{2}\otimes\sigma_{2}$$

$$\gamma^{1}=\left[\begin{array}{cc}
-i\sigma_{1} & 0\\
0 & -i\sigma_{1}
\end{array}\right]=-I\otimes i\sigma_{1}$$

$$\gamma^{5}=i\gamma^{0}\gamma^{1}\gamma^{2}\gamma^{3}=\left[\begin{array}{cc}
\sigma_{2} & 0\\
0 & -\sigma_{2}
\end{array}\right]=\sigma_{3}\otimes\sigma_{2}$$

Advantages of Basis:

Disadvantages:

A stroll down intuition street
==============================

my little story about the factored wave equation

Green's functions of

$$\left[\begin{array}{cc}
\partial_{t}-\partial_{x} & 0\\
0 & \partial_{t}+\partial_{x}
\end{array}\right]$$

The velocity operator.
----------------------

The $\gamma$matrices are very similar in a sense to some sort of
velocity operator. For example

$$\gamma^{\mu}\gamma_{\mu}=\delta_{\mu}^{\mu}=4$$

just like the 4-velocity is a unit vector

$$u^{\mu}u_{\mu}=1$$

$$(a^{\mu}\gamma_{\mu})^{2}=a^{\mu}a_{\mu}$$

$$$$

$$\{\gamma^{\mu},\gamma^{\nu}\}=2g^{\mu\nu}$$

What this means is that gammas mostly anticommute. This implies that

Spinors: Da fuq?
================

Topology: Double Cover.

Visualizations

Lorentz Group
