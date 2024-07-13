The objective is to obtain the quantum correlation function
$<\phi(x,t)\phi(x',t')>$for a function $\phi$ obeying the Lagrangian
$L=\frac{-1}{4\pi}(\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi+\partial_{x}\phi u(x)P\partial_{x}\phi)$.

The general plan is to ignore fancier formulations of quantum field
theory and quantize as if we were dealing with an inhomogeneous chain of
harmonic oscillators. We'll be working in the time independent
$\omega-x$ domain. Since the equations of motion are not translation
invariant, the $k$ domain does not appear to have significant advantage
over the spatial domain. In the spatial domain we can use the simple
method of matched solutions for piecewise inter-edge potential $u(x)$.

The more unusual term in the action is the last one, which corresponds
to a point interaction directly across the peninsula that the quantum
hall edge state is flowing around. $P$ is the parity operator defined by
$Pf(x)=f(-x)$. It is used because $\partial_{x}\phi(-x)$ is slightly
ambiguous notation that makes it difficult to keep signs correct
throughout a calculation. When I write $\partial_{x}\phi(-x)$, do I want
to take the derivative first or flip the sign of the argument first? The
two operators $\{P,\partial_{x}\}=0$ anti-commute, so the choice
matters. The correct prescription based on the physical interpretation
of $\rho=\partial_{x}\phi(x)$ is to take the derivative and then reverse
the sign of the argument, since we want to couple to the density
$\partial_{x}\phi$ at the opposite side of the contact.

Measuring Edge Velocity
-----------------------

Previous meaurements of edge mode velocities are subtle. There is the
time domain measurment of Ashoori which measures the time it takes to
traverse a circular mesa of diameter 500$\mu m$. The time it takes is
very short requiring the use of veyr high freqeuncies. That in itself is
nonideal. Naively, high frequency is just plain more complicated the
drive and record, but also one can have more phenomenon at play, either
other physical responses of the system or perhaps mysterious and
uninteded LC couplingsto apparatus (although presumably the
experimenters ruled out such things. That's exactly what a practical man
would worry about). Oscillations in the Fabry Perot interferometer can
come from different souces. Coulomb blockade is a famous one. I'm not
sure. The size of the quantum dot will reduce the charging energy,
making it less relevant.

The geoemtry and physics of a narrow gate make it into an interferometer
of sorts. A typical interferometer has multiple pathways by which a
particle can move from source to detector. In this device however, there
is only one. The electrons must move in only one direction due to the
magnetic field. (Question: is the tunnelling contact a necessary
component of this setup? Or is it just letting us observe the
interference occurring?) Rather than electrons interfering, it feels
more intuitive to think of it as plasma oscillations that are
interfering. Since electrons are indistinguishable, it is not clear that
there is a observable distinction between a coulomb interaction and a
tunnelling (this fact is one of a number of possible physical origins of
bosonization. A point split coulomb interaction in 1-D looks like 2
applications of a hopping term). The equivalent optical interferometer
is that of a single strange beam splitter (that breaks time reversal
symmettry) and one arm of the interferometer goes straight to the
detector while the other bounces off a mirror.

The Physical Picture
--------------------

The underlying flow of electron is one directional, however when a pulse
reaches the first edge it immediately excites a charge across the edge
which continues and dresses itself with an image charge on the opposite
side of the contact. It can then continue flowing up the edge until it
comes out the other side, where it needs to undress itself, which
excites a charge (releases its image charge) back at the other side.

Can I clearly demonstrate this explicitly? Not to my satisfaction.

U=0
---

For review we'll show how to get the correlation function with the
$u(x)$ term set to 0. The Lagrangian is then
$L=\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi$.
Taking the variation of the action we get the equations of motion

$$\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi=0$$

Replacing with the identity
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(x,\omega)e^{i\omega t}\frac{d\omega}{2\pi}$
we transform this equation to

.

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi=0$$

We can substitute in the function with two undetermined parameters
$Ae^{-ikx}+C$.

$$i\omega(-ik)Ae^{-ikx}+v(-ik)^{2}Ae^{-ikx}=0$$

This implies that $k=\frac{\omega}{v}$ . The constant solution $C$ is
swept under the rug and ignored.

Putting into a periodic box of size L restricts k to $\frac{n\pi}{L}$.

The bosonic mode operators have the standard commutation relation
$[b_{\omega},b_{\omega'}^{\dagger}]=\delta_{\omega\omega'}$.

Putting $\psi_{\omega}(x)=e^{-ikx}$ into the mode expansion we have

$$\phi(x,t)=\sum_{n>0}\frac{1}{\sqrt{n}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))=\sum_{n>0}\frac{1}{\sqrt{n}}(e^{i\omega t-ikx}b_{\omega}^{\dagger}+e^{-i\omega t+ikx}b_{\omega})$$

Evaluating $<\phi(x,t)\phi(x',t')>$is easily done by inserting this
expression into the brackets. The only term to survive are those with
operator ordering **$bb^{\dagger}$**

$<\phi(x)\phi(x')>=<(\sum_{n>0}\frac{1}{\sqrt{n}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))(\sum_{n'>0}\frac{1}{\sqrt{n'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{n}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

We need to explain our chosen normalization conventions. The overall
normalization of each mode is not specified by the equations of motion.
The normalization is determined by the Lagrangian in the path integral
formulation.

However we choose the normalization such that the commutation relation
$[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$.

$[\sum_{n>0}\frac{1}{\sqrt{n}}(e^{i\omega t-ikx}b_{\omega}^{\dagger}+e^{-i\omega t+ikx}b_{\omega}),\sum_{n'>0}\frac{1}{\sqrt{n'}}(e^{i\omega t''-ik'x'}b_{\omega'}^{\dagger}+e^{-i\omega't'+ik'x'}b_{\omega'}]=\sum_{n>0}\frac{1}{n}(e^{-ik(x-x')}[b_{\omega}^{\dagger},b_{\omega}]+e^{ik(x-x')}[b_{\omega},b_{\omega}^{\dagger}])$

$\sum_{n>0}\frac{1}{n}(-e^{-ik(x-x')}+e^{ik(x-x')})=\ln\frac{2\pi i}{L}(x-x'-i\alpha)-\ln\frac{-2\pi i}{L}(x-x'+i\alpha)=\ln\frac{ix-ix'+\alpha}{-ix+ix'+\alpha}\approx i\pi\text{sign}(x-x')$

I-V from Correlation Function
-----------------------------

The method of Bosonization allows us to calculate properties of an
interacting 1-d Fermi system from calculations using a free boson field.
The correspondence is roughly $e^{i\phi}\rightarrow\psi$ and
$\frac{e}{2\pi}\partial_{x}\phi\leftarrow\rho$.

The reasonableness of various operations can be seen in the
non-interacting case, where we can easily explicitly evaluate both sides
of the bosonization equivalence.

The chiral field $\phi$ counts the charge total charge
$Q=\int dx\rho=\frac{e}{2\pi}(\phi(\infty)-\phi(-\infty))$.

The simplest way to check your conventions and demonstrate that the
bosonized creation operator is correct is to show that it increases the
charge by one. To do this is should satisfy the commutation relation
$[Q,\psi^{\dagger}]=e\psi^{\dagger}$, the analog of
$[N,a^{\dagger}]=a^{\dagger}$

$[Q,e^{-i\phi(x)}]=\frac{e*}{2\pi}[\phi(\infty),e^{-i\phi(x)}]-\frac{e*}{2\pi}[\phi(-\infty),e^{-i\phi(x)}]=\frac{\pi e*}{2\pi}\text{sign(\ensuremath{\infty}-x) }e^{-i\phi}-\frac{\pi e*}{2\pi}\text{sign(-\ensuremath{\infty}-x) }e^{-i\phi}=e*e^{-i\phi}$

To evaluate this, it is useful to use the following identity: Given
$[A,B]=C$ and C commutes with A and B, we have $[A,e^{B}]=Ce^{B}$. The
simplest example of this is
$[\partial_{x},ax]=a$,$[\partial_{x},e^{ax}]=ae^{ax}$.

We can show that a commutation relation of
$[\phi_{R}(x),\phi_{R}(x')]=i\pi\text{sign(x-x') }$ implies that
$e^{-i\phi_{R}}=\psi_{R}^{\dagger}$ and $\psi_{R}=e^{i\phi_{R}}$

$\frac{e*}{2\pi}[\phi(\infty),e^{-i\phi(x)}]-\frac{e*}{2\pi}[\phi(-\infty),e^{-i\phi(x)}]=\frac{\pi e*}{2\pi}\text{sign(\ensuremath{\infty}-x) }e^{-i\phi}-\frac{\pi e*}{2\pi}\text{sign(-\ensuremath{\infty}-x) }e^{-i\phi}=e*e^{-i\phi}$

Similarly a commutation relation of
$[\phi_{L}(x),\phi_{L}(x')]=-i\pi\text{sign(x-x') }$ implies that
$e^{i\phi_{L}}=\psi_{L}^{\dagger}$

One way to insert biasing of the edges is to include an oscillating
exponential term $e^{-i\omega_{0}t}\psi_{L}$,
$e^{i\omega_{0}t}\psi_{L}^{\dagger}$with the left moving field
operators. This can be understood as due to changing an overall constant
potential on only the left side. For example for a single particle
Schrodinger equation, given $i\partial_{t}\psi=H\psi$, then
$e^{-i\omega_{0}}\psi$satisfies the equation with a new overall constant
potential
$i\partial_{t}e^{-i\omega_{0}}\psi=(H+\omega_{0})e^{-i\omega_{0}}\psi$.
This extends to many-particle wavefunctions and then to the language of
second quantization with the prescription already given.

The tunneling term in the Hamiltonian will inject particles from the
left moving to right moving
edges$H_{\Gamma}=\Gamma(\psi_{L}^{\dagger}\psi_{R}e^{i\omega_{0}t}+\psi_{R}^{\dagger}\psi_{L}e^{-i\omega_{0}t})$,
where $\omega_{0}=eV$ the biasing voltage. The bosonized form of this
term is

$H_{\Gamma}=\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}+e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t})$
Recheck this convention.

The tunneling current $I=\dot{Q}=i[H,Q_{L}]=i[H_{\Gamma},Q_{L}]$. The
charge operator commutes with all parts of the Hamiltonian except the
tunneling part $H_{\Gamma}$.

$I=i[\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}+e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t}),\frac{e}{2\pi}(\phi_{L}(\infty)-\phi_{L}(-\infty))]=i\frac{e}{2\pi}\Gamma(e^{i\phi_{L}}e^{i\phi_{R}}e^{i\omega_{0}t}-e^{-i\phi_{R}}e^{-i\phi_{L}}e^{-i\omega_{0}t})$

Essentially, the the L annihilation operator term in $H_{\Gamma}$ gets
its sign reversed and an i gets tacked on.

(I should recheck this. It seems that the $2\pi$ should be cancelled now
that I'm looking at it. If so, propagate change through rest of ducment.
Not an egregious error. Can be reabsorbed into $\Gamma$, which is
totally unknown anyhow.)

To perturbation calculate the current, we can work in the interaction
representation and evaluate the
expression$<U(-\infty,t)I(0)U(t,-\infty)>=$

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

$<e^{A}e^{B}>=e^{<AB>+\frac{1}{2}<AA>+\frac{1}{2}<BB>}$

$-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})e^{<\phi(t)\phi(0)-\frac{1}{2}\phi(t)\phi(t)-\frac{1}{2}\phi(0)\phi(0)>}$

Thus once we have calculated the correlation function for the bosonic
field $\phi$, we can exponentiate and Fourier transform it to calculate
the tunneling I-V characteristic.

U$\protect\ne0$
---------------

Now we return to the case with $u(x)$.

Taking the variation of the action we have the equation of motion for
the field $\phi$

$$\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

Replacing with the identity
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(x,\omega)e^{i\omega t}\frac{d\omega}{2\pi}$
we transform this equation to

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

We'll treat the $u(x)=u$ constant case first and then match the interior
solution to the exterior solution. The equation is for heuristic
purposes roughly translation invariant, so we still anticipate plane
waves. However, if $e^{ikx}$ appears in an eigenfunction so must
$e^{-ikx}$, since the P operator turns $x\rightarrow-x$. Hence, we can
make the guess $Ae^{ikx}+Be^{-ikx}$ with A and B being unknown
coefficients that will be constrained by the equations of motion.

It turns out that if one uses the equivalent expansion
$\phi=C\sin(kx)+D\cos(kx)$ things come out a tad cleaner.

The equation expands

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

$$i\omega Ck\cos(kx)-i\omega Dk\sin(kx)-k^{2}vC\sin(kx)-k^{2}vD\cos(kx)-uk^{2}C\sin(kx)+uk^{2}D\cos(kx)=0$$

Collecting up the Sine and Cosine terms separately gives the matrix
equation

$$\left[\begin{array}{cc}
-vk^{2}-uk^{2} & -i\omega k\\
i\omega k & -vk^{2}+uk^{2}
\end{array}\right]\left[\begin{array}{c}
C\\
D
\end{array}\right]=0$$

Taking the determinant we will get a constraining equation on k.

$$(-vk^{2}-uk^{2})(-vk^{2}+uk^{2})+i\omega ki\omega k=0$$

$$v^{2}k^{4}-u^{2}k^{4}-\omega^{2}k^{2}=0$$

Removing the possibility of $k^{2}=0$ we get the dispersion relation

$$(v^{2}-u^{2})k^{2}=\omega^{2}$$

The ratio of C/D can be determined by using either row of the matrix.

$$\frac{C}{D}=\frac{i\omega k}{-vk^{2}-uk^{2}}=\frac{-vk^{2}+uk^{2}}{-i\omega k}$$

Substituting in the relation $\omega=k\sqrt{v^{2}-u^{2}}$

$$\frac{C}{D}=-i\sqrt{\frac{v-u}{v+u}}$$

An easy way to achieve this is to set, $C=-i\sqrt{v-u}$ $D=\sqrt{v+u}$,
with the understanding that there is still an overall unspecified
normalization constant $A$.

We now expand back into complex exponentials

$\phi=C\sin(kx)+D\cos(kx)=-i\sqrt{v-u}\sin(kx)+\sqrt{v+u}\cos(kx)$

$=-i\sqrt{v-u}\frac{e^{ikx}-e^{-ikx}}{2i}+\sqrt{v+u}\frac{e^{-ikx}+e^{-ikx}}{2}=\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx}$

In the limit $u\rightarrow0$ the solution is $\sqrt{v}e^{-i\omega x}$,
which matches our previous result up to a normalization.

If we normalize the function out on the left where $u=0$ to $e^{-ikx}$
and matching $\phi(-a_{-})=\phi(-a_{+})$

$$e^{-i\omega(-a)}=A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)})$$

$$A=\frac{e^{-i\omega(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}$$

Therefore when $-a<x<a$

$$\psi(x)=\frac{e^{-i\omega(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx})$$

Defining $Z=\frac{\sqrt{v+u}-\sqrt{v-u}}{\sqrt{v+u}+\sqrt{v-u}}$. For
small $u$, $Z\approx u$, so expansions in Z will roughly correspond to
expansions in weak potentials u.

$$\psi=\frac{e^{-i\omega(-a)}}{e^{-ik(-a)}+Ze^{ik(-a)}}(e^{-ikx}+Ze^{ikx})=\frac{e^{-i(\omega-k)a}}{1+Ze^{-2ika}}(e^{-ikx}+Ze^{ikx})$$

$$<\phi(x)\phi(x')>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

We can assume that as the box size $L$ becomes much larger than the
interaction region $2a$ allowed eigenfrequencies
$\omega_{n}\approx\frac{vn\pi}{L}+\delta$. Consider the matching problem
of periodic boundary conditions $\phi(\frac{-L}{2})=\phi(\frac{L}{2})$.
The wavefunction accumulates phase
$e^{-i\frac{\omega}{v}(\frac{L}{2}-a)}$in the left region,
$e^{-i\frac{\omega}{\sqrt{v^{2}-u^{2}}}2a}$in the middle $u\ne0$ region
(the middle region wavefunction is tracing out an complex elliptical
corkscrew. The ellipticity (added by the $e^{ikx}$term) is irrelevant
for finding the phase accumulated) and another
$e^{-i\frac{\omega}{v}(\frac{L}{2}-a)}$ in the right region. Hence the
periodic boundary condition puts the constraint on $\omega$ that
$e^{-i\frac{\omega}{v}(L-2a)-i\frac{\omega}{\sqrt{v^{2}-u^{2}}}2a}=1$,
or that
$\omega=\frac{vn2\pi}{L-2a+\frac{2a}{\sqrt{1-\frac{u^{2}}{v^{2}}}}}$.

The expansion in annihilation and creation operators reads
$\phi=\sum_{\omega}\frac{1}{\sqrt{n}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))$

$<\phi(x)\phi(x')>=<(\sum_{\omega}\frac{1}{\sqrt{n}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x)(\sum_{\omega'}\frac{1}{\sqrt{n'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{\omega}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

For the $u=0$ case this supplies (Note to self: recheck signs of the x
and x') (also compare with calculation of free green's function by other
methods)

$$\sum_{\omega}\frac{1}{n}e^{ik(x-x')}e^{-i\omega(t-t')}$$

$$\psi^{*}(x)\psi(x')=\frac{e^{i(k_{0}-k)a}}{1+Ze^{2ika}}(e^{ikx}+Ze^{-ikx})\frac{e^{-i(k_{0}-k)a}}{1+Ze^{-2ika}}(e^{-ikx'}+Ze^{ikx'})$$

$$\frac{1}{1+Ze^{-2ika}}\frac{1}{1+Ze^{2ika}}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

We will expand the denominator of this expression so that we may right
the expression as a sum of exponential terms, which we know how to
regularize and compute the sum over all frequencies for.

$$\frac{1}{1+Ze^{-2ika}}=\sum_{n\ge0}(-Ze^{-2ika})^{n}$$

$$\frac{1}{1+Ze^{-2ika}}\frac{1}{1+Ze^{2ika}}=\sum_{m\ge0}(-Ze^{2ika})^{m}\sum_{n\ge0}(-Ze^{-2ika})^{n}=\sum_{m,n\ge0}(-Z)^{m+n}e^{2ika(m-n)}$$

Changing summation indices to

$$r=m+n$$

$$q=m-n$$

By checking cases we can see that if r is odd, so must be q. The lower
limit of $r=|q|$ is achieved by

$$\sum_{m\ge0}\sum_{n\ge0}=\sum_{q\text{ odd}}\sum_{r\text{ odd\ensuremath{\ge}|q|}}+\sum_{q\text{even}}\sum_{r\text{ even\ensuremath{\ge}|q|}}$$

$$\sum_{q\text{even}}\sum_{r\text{ even\ensuremath{\ge}|q|}}(-Z)^{r}e^{2ikqa}$$

$$\sum_{q\text{ even}}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}$$

Likewise for the odd summation

$$\sum_{q\text{ odd}}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}$$

Which can be combined into

$$\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}$$

$$\psi^{*}(x)\psi(x')=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

Now we can do the $\omega$ summation term by term using the approximate
identity$\sum_{n>0}\frac{1}{n}e^{-q(ix+\alpha)}\approx-\ln\frac{2\pi i}{L}(x-i\alpha)$

$$<\phi(x,t)\phi(x',t')>=\sum_{\omega}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

$$=\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)+Z(-\ln\frac{2\pi i}{L}(\frac{x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$-\ln\frac{2\pi i}{L}(\frac{-x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)-Z^{2}\ln\frac{2\pi i}{L}(\frac{x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

As $Z=0$, the only term to survive is the $q=0$ term
$-\ln\frac{2\pi i}{L}(-x+x'+t-t'-i\alpha)$

Setting $x=x'=0$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)+Z(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha))-Z^{2}\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha))(1+2Z+Z^{2})$$

$$=\frac{1+Z}{1-Z}\sum_{q\text{ }}(-Z)^{|q|}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha))$$

Multistep
---------

We now consider multiple steps, which can be treated very similarly to
the single step potential.

In the nth step the function will have the form

$\psi_{n}=A_{n}(\frac{\sqrt{v+u_{n}}+\sqrt{v-u_{n}}}{2}e^{-ik_{n}x}+\frac{\sqrt{v+u_{n}}-\sqrt{v-u_{n}}}{2}e^{ik_{n}x})=A_{n}\eta_{n}(x)$

$k_{n}=\frac{\omega}{\sqrt{v^{2}-u_{n}^{2}}}$

If we define the transition from step $n$ to step $n+1$ to occur at
positions $a_{n}$ giving the matching condition equation

$\psi_{n}(a_{n})=\psi_{n+1}(a_{n})$

$A_{n}\eta_{n}(a_{n})=A_{n+1}\eta_{n+1}(a_{n})$

Rearranging we have a very simple recursion relation for the coefficient
$A_{n}$

$A_{n}\frac{\eta_{n}(a_{n})}{\eta_{n+1}(a_{n})}=A_{n+1}$

Which can be immediately solved.

$A_{j}=A_{0}\prod_{j>n\ge0}\frac{\eta_{n}(a_{n})}{\eta_{n+1}(a_{n})}$

We will only need the correlation function $<\phi(0,t)\phi(0,t')>$ at
positions $x=x'=0$ to calculate the tunneling current. To calculate this
correlation function we need $\psi_{\omega}^{*}(0)\psi_{\omega}(0)$

$A_{n}(\frac{\sqrt{v+u_{n}}+\sqrt{v-u_{n}}}{2}e^{-ik_{n}a_{n}}+\frac{\sqrt{v+u_{n}}-\sqrt{v-u_{n}}}{2}e^{ik_{n}a_{n}})=A_{n}(\frac{\sqrt{v+u_{n}}+\sqrt{v-u_{n}}}{2}e^{-ik_{n}x}+\frac{\sqrt{v+u_{n}}-\sqrt{v-u_{n}}}{2}e^{ik_{n}x})$

The region furthest to the left is free so we can start the recursion
with

$u_{0}=0$

$\psi_{0}=e^{-ik_{0}x}$

$\eta_{0}(x)=\sqrt{v}e^{-ik_{0}x}$

$k_{0}=\frac{\omega}{v}$

$A_{0}=\frac{1}{\sqrt{v}}$

Defining $a_{N}=0$

$\psi_{\omega}^{*}(0)\psi_{\omega}(0)=\prod_{N\ge m\ge1}|\frac{\eta_{m}(a_{m})}{\eta_{m}(a_{m-1})}|^{2}$

Each denominator can be expanded similarly to the single step case

$|\frac{\eta_{m}(a_{m})}{\eta_{m}(a_{m-1})}|^{2}=|1+Z_{m}e^{2ik_{m}a_{m}}|^{2}\sum_{q_{m}\text{ }}\frac{(-Z_{m})^{|q_{m}|}}{1-Z_{m}^{2}}e^{2ik_{m}q_{m}a_{m-1}}$

While we are exact the expressions get unwieldy after this point. To
conbat this, we expand to first order in weak potential $Z_{n}$

$|\frac{\eta_{m}(a_{m})}{\eta_{m}(a_{m-1})}|^{2}\approx1+Z_{m}(e^{2ik_{m}a_{m}}+e^{-2ik_{m}a_{m}}-e^{2ik_{m}a_{m-1}}-e^{-2ik_{m}a_{m-1}})$

Therefore the first order correlation function is

$<\phi(t)\phi(t')>=\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}\prod_{N\ge m\ge1}(1+Z_{m}(e^{2ik_{m}a_{m}}+e^{-2ik_{m}a_{m}}-e^{2ik_{m}a_{m-1}}-e^{-2ik_{m}a_{m-1}}))$

Again, keeping only first order terms

$\approx\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}(1+\sum_{N\ge m\ge1}Z_{m}(e^{2ik_{m}a_{m}}+e^{-2ik_{m}a_{m}}-e^{2ik_{m}a_{m-1}}-e^{-2ik_{m}a_{m-1}}))$

Applying the same identity as before

$=-\ln\frac{2\pi i}{L}(t-t'-i\alpha)+\sum_{N\ge m\ge1}Z_{m}(-\ln\frac{2\pi i}{L}(t-t'-2k_{m}a_{m}-i\alpha)-\ln\frac{2\pi i}{L}(t-t'+2k_{m}a_{m}-i\alpha)+\ln\frac{2\pi i}{L}(t-t'-2k_{m}a_{m-1}-i\alpha)+\ln\frac{2\pi i}{L}(t-t'+2k_{m}a_{m-1}-i\alpha))$

We see that this matches the single step solution if $N=1$, $a_{0}=-a$
and $a_{1}=0$. Also we see that if any steps have the same Z as their
previous step (which is actually no step at all), the series telescopes
as it should.

Perturbative Calculation
------------------------

A perturbative calculation can be done along the same lines as the
previous methods or using other formalisms. However, using the previous
method makes for a very simple calculation. We expand the frequency
eigenfunctions coefficients of the operator $\phi(x)$ in powers of a
weak across-contact potential $u(x)$

$$\psi=\psi_{0}+\psi_{1}+...$$

The equations of motion for $\psi$ are

$$i\omega\partial_{x}\psi+v\partial_{x}\partial_{x}\psi=-\partial_{x}u(x)P\partial_{x}\psi$$

The zeroth order solution has been shown to be
$\psi_{0}=e^{-i\frac{\omega}{v}x}$. The first order in $u(x)$ expansion
of the equations of motion is

$$i\omega\partial_{x}\psi_{1}+v\partial_{x}\partial_{x}\psi_{1}=-\partial_{x}u(x)P\partial_{x}\psi_{0}=i\omega\partial_{x}u(x)e^{i\frac{\omega}{v}x}$$

We can integrate both sides

$$\frac{i\omega}{v}\psi_{1}+\partial_{x}\psi_{1}=\frac{i\omega}{v}u(x)e^{i\frac{\omega}{v}x}$$

Apply an integrating factor of $e^{i\frac{\omega}{v}x}$

$$\partial_{x}e^{i\frac{\omega}{v}x}\psi_{1}=\frac{i\omega}{v}u(x)e^{i2\frac{\omega}{v}x}$$

Integrate again and divide out the integrating factor

$$\psi_{1}(x)=e^{-i\frac{\omega}{v}x}\int_{-\infty}^{x}\frac{i\omega}{v}u(x')e^{i2\frac{\omega}{v}x'}dx'$$

For comparison, we can calculate the result for the step potential
$u(x)=u(\theta(x+a)-\theta(x-a))$. For $x<-a$, there is no correction.
For $x>a$ $\psi_{1}(x)=C\psi_{0}(x)$, which are the beginnings of a
phase shift. For $-a<x<a$

$$\psi_{1}(x)=e^{-i\frac{\omega}{v}x}u\int_{-a}^{x}\frac{i\omega}{v}e^{i2\frac{\omega}{v}x'}dx'=\frac{u}{2v}(e^{i\frac{\omega}{v}x}-e^{-i\frac{\omega}{v}(x+2a)})$$

Using the same expansion for the correlation function as before

$<\phi(x)\phi(x')>=\sum_{n}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

$=\sum_{n}\frac{1}{n}(\psi_{0\omega}^{*}(x)+\psi_{1\omega}^{*}(x))(\psi_{0\omega}(x')+\psi_{1\omega}(x'))e^{-i\omega(t-t')}$

$=\sum_{n}\frac{1}{n}(\psi_{0\omega}^{*}(x)\psi_{0\omega}(x')+\psi_{1\omega}^{*}(x)\psi_{0\omega}(x')+\psi_{0\omega}^{*}(x)\psi_{1\omega}(x')+O(u^{2}))e^{-i\omega(t-t')}$

Inserting the calculated step potential $\psi_{1\omega}(x)$

$=\sum_{n}\frac{1}{n}(e^{-i\frac{\omega}{v}(x'-x)}+\frac{u}{2v}(e^{-i\frac{\omega}{v}x}-e^{i\frac{\omega}{v}(x+2a)})e^{-i\frac{\omega}{v}x'}+e^{i\frac{\omega}{v}x}\frac{u}{2v}(e^{i\frac{\omega}{v}x'}-e^{-i\frac{\omega}{v}(x'+2a)}))e^{-i\omega(t-t')}$

$=\sum_{n}\frac{1}{n}(e^{-i\frac{\omega}{v}(x'-x)}+\frac{u}{2v}(e^{-i\frac{\omega}{v}(x+x)}-e^{i\frac{\omega}{v}(x-x'+2a)})+\frac{u}{2v}(e^{i\frac{\omega}{v}(x'+x)}-e^{i\frac{\omega}{v}(x-x'-2a)}))e^{-i\omega(t-t')}$

$=\sum_{n}\frac{1}{n}(e^{-i\frac{\omega}{v}(x'-x)}+\frac{u}{2v}(e^{-i\frac{\omega}{v}(x+x')}+e^{i\frac{\omega}{v}(x'+x)})-\frac{u}{2v}(e^{i\frac{\omega}{v}(x-x'+2a)}+e^{i\frac{\omega}{v}(x-x'-2a)}))e^{-i\omega(t-t')}$

The exact expression at this stage is

$<\phi(x)\phi(x')>=\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$

We expand the definition of
$Z=\frac{\sqrt{v+u}-\sqrt{v-u}}{\sqrt{v+u}+\sqrt{v-u}}$ to first order
in $u$, $Z=\frac{u}{2v}$

To first order in u $k=\frac{\omega}{v}$

$\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})-Ze^{ik(x-x')}(e^{i2ka}+e^{-i2ka}))$

$\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}(e^{i\frac{\omega}{v}(x-x')}+\frac{u}{2v}(e^{-i\frac{\omega}{v}(x+x')}+e^{i\frac{\omega}{v}(x+x')})-\frac{u}{2v}e^{i\frac{\omega}{v}(x-x')}(e^{i2\frac{\omega}{v}a}+e^{-i2\frac{\omega}{v}a}))$

Which we can see match the expression above.

Current of Step
---------------

We have derived that
$I(\omega_{0}=\frac{eV}{\hbar})=-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})e^{<\phi(t)\phi(0)-\frac{1}{2}\phi(t)\phi(t)-\frac{1}{2}\phi(0)\phi(0)>}$and
we have derived the correlation function for the rightward moving edge
(we've previously been suprressing the R index).
$$<\phi_{R}(0,t)\phi_{R}(0,t')>=\frac{1+Z}{1-Z}\sum_{q\text{ }}(-Z)^{|q|}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha))$$

Now we may put these two ingredients together. To make the calculation
tractable, we may expand in powers of Z, which to first order is
equivalent to expansion in small $u(x)$. From this we lose terms with
$q>1$, which physically would correspond to repeated echoes of a charge
entering and exiting the step region, similar to the bouncing waves
resonating in a pipe. The inclusion of these terms would presumably
would lead to more transitional behavior between conductance powers at
higher multiples of $\omega_{0}$. For weak $u(x)$, the effects of these
higher echoes will cause changes in the exponent of order $u^{2}$ and
higher so they may indeed be experimentally unnoticeable.

$$<\phi_{R}(0,t)\phi_{R}(0,t')>\approx-(1+2Z)\ln(\frac{2\pi i}{L}(t-t'-i\alpha))+Z\ln(\frac{2\pi i}{L}(\frac{-2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$+Z\ln(\frac{2\pi i}{L}(\frac{2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

Before we have only been considering the right moving edge. To include
the left moving edge in our correlation function we add together the
correlation functions for the individual edges. The correlator
$<\phi_{R}\phi_{L}>=0$. For with a left moving edge with $u=0$ this
becomes

$$<\phi(0,t)\phi(0,t')>\approx-(2+2Z)\ln(\frac{2\pi i}{L}(t-t'-i\alpha))+Z\ln(\frac{2\pi i}{L}(\frac{-2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$+Z\ln(\frac{2\pi i}{L}(\frac{2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

If both edges have have

$$I=-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})\frac{(\frac{t}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}(\frac{t}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}}{(\frac{t}{-i\alpha}+1)^{2+2Z}}$$

The three branch points occur above the real axis in the upper t plane.
Let us assume $\omega_{0}>0$. We wrap the contour around each branch
point and push up in the $it$ direction.

The term with $e^{-i\omega_{0}t}$ can be have its contour deformed
downward and thus does not contribute to the integral. The
$e^{i\omega_{0}t}$term's contour must be deformed upward, but it gets
caught on the branch points, leaving three terms.

If both edges have $u\ne0$ then the single edge correlation function is
doubled.

$$<\phi(0,t)\phi(0,t')>\approx-(2+4Z)\ln(\frac{2\pi i}{L}(t-t'-i\alpha))+2Z\ln(\frac{2\pi i}{L}(\frac{-2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$+2Z\ln(\frac{2\pi i}{L}(\frac{2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

Changing integration variables to $t=\frac{is}{\omega_{0}}+i\alpha$, the
term from the central branch point is

$$\frac{e}{2\pi}\Gamma^{2}(e^{-i\pi(2+2Z)}-e^{i\pi(2+2Z)})\int_{\beta\omega_{0}}^{\infty}\frac{ids}{\omega_{0}}e^{-s}\frac{(\frac{\frac{is}{\omega_{0}}+i\alpha}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}(\frac{\frac{is}{\omega_{0}}+i\alpha}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

The phase of $\frac{\frac{is}{\omega_{0}}}{-i\alpha}+1$ is not single
valued for the incoming and outgoing sections of the contour. This leads
to the factor out front. The phase is measured relative to the $-i$
t-axis. The numerator factors have equal and opposite phase and the same
magnitude, hence we can replace both with a absolute value squared.

There is also a small ball near the origin of radius $\alpha$

$t=-i\beta e^{i\theta}+i\alpha$

$$+\frac{e}{2\pi}\Gamma^{2}\int_{-\pi}^{\pi}-ii\beta e^{i\theta}d\theta e^{i\omega_{0}(-i\beta e^{i\theta}+i\alpha)}\frac{(\frac{-i\beta e^{i\theta}+i\alpha}{-\tau-i\alpha}+1)^{Z}(\frac{-i\beta e^{i\theta}+i\alpha}{\tau-i\alpha}+1)^{Z}}{(\frac{\beta}{\alpha}e^{i\theta})^{2+2Z}}$$

We can expand to only include the expressions which do not go to 0 as
$\beta$ goes to 0. Whether the $\beta^{-2Z}$ term goes to 0 or not
depends on the sign of Z.

$$\approx\frac{e}{2\pi}\Gamma^{2}\int_{-\pi}^{\pi}e^{i\theta}\beta^{-1-2Z}\alpha^{2+2Z}(1+\omega_{0}\beta e^{i\theta})e^{-i(2+2Z)\theta}d\theta$$

$$=\frac{-e}{2\pi}\Gamma^{2}\alpha^{2+2Z}\sin(2Z\pi)(\beta^{-1-2Z}\frac{2}{1+2Z}-\beta^{-2Z}\omega_{0}\frac{1}{Z})$$

For convenience define $\tau=\frac{2a}{\sqrt{v^{2}-u^{2}}}$. This is the
time it takes for charge to travel across the entire step region of size
$2a$.

$$\frac{e}{2\pi}\Gamma^{2}(e^{-i\pi(2+2Z)}-e^{i\pi(2+2Z)})\int_{\beta\omega_{0}}^{\infty}\frac{ids}{\omega_{0}}e^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

$$\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\int_{\beta\omega_{0}}^{\infty}\frac{ds}{\omega_{0}}e^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

$$=\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\int_{\beta\omega_{0}}^{\omega_{0}\tau}dse^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{\infty}dse^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}})$$

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\int_{\beta\omega_{0}}^{\omega_{0}\tau}dse^{-s}\frac{1}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{s}{\omega_{0}\tau})^{2Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}})$$

Or to next order in the binomial expansions

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\int_{\beta\omega_{0}}^{\omega_{0}\tau}dse^{-s}\frac{1+Z(\frac{s}{\omega_{0}\tau})^{2}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{s}{\omega_{0}\tau})^{2Z}(1+Z(\frac{\omega_{0}\tau}{s})^{2})}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}})$$

So we're missing a contribution $\omega_{0}^{2Z}$ from the first
expression and a $\omega_{0}^{4}$ in the second. No, we're losing higher
order corrections in powers of Z.

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\alpha^{2+2Z}\omega_{0}^{2+2Z}\int_{\beta\omega_{0}}^{\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+2Z}}+\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}})$$

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\alpha^{2+2Z}\omega_{0}^{2+2Z}(\int_{\beta\omega_{0}}^{\infty}-\int_{\tau\omega_{0}}^{\infty})ds\frac{e^{-s}}{s^{2+2Z}}+\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}})$$

For small lower integration limits we can integrate by parts to remove
the divergent part from these integrals

$$\int_{\beta\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+2Z}}=\frac{-1}{1+2Z}\int_{\beta\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{1+2Z}}-\frac{1}{-1-2Z}(\beta\omega_{0})^{-1-2Z}e^{-\beta\omega_{0}}$$

$$=\frac{1}{(1+2Z)2Z}\int_{\beta\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2Z}}-\frac{1}{2Z(1+2Z)}(\beta\omega_{0})^{-2Z}e^{-\beta\omega_{0}}+\frac{1}{1+2Z}(\beta\omega_{0})^{-1-2Z}e^{-\beta\omega_{0}}$$

The left over integral is finite as $\beta\rightarrow0$, so we can pull
out this contribution

$$\int_{\beta\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2Z}}=\int_{0}^{\infty}ds\frac{e^{-s}}{s^{2Z}}-\int_{0}^{\beta\omega_{0}}ds\frac{e^{-s}}{s^{2Z}}=\Gamma(1-2Z)-\int_{0}^{\beta\omega_{0}}ds\frac{e^{-s}}{s^{2Z}}$$

Giving the entire expression from the integral as

$$=\frac{1}{(1+2Z)2Z}(\Gamma(1-2Z)-\int_{0}^{\beta\omega_{0}}ds\frac{e^{-s}}{s^{2Z}})-\frac{1}{2Z(1+2Z)}(\beta\omega_{0})^{-2Z}e^{-\beta\omega_{0}}+\frac{1}{1+2Z}(\beta\omega_{0})^{-1-2Z}e^{-\beta\omega_{0}}$$

This integral has a simple power series best for small $\beta$ found by
expanding the exponential. As $\beta$ relly does go to 0 and is not just
merely small, we will not have need for this expression but we write it
down for later.

$$\int_{0}^{\beta\omega_{0}}s^{-2Z}e^{-t}ds==\int_{0}^{\beta\omega_{0}}s^{-2Z}\sum_{k=0}^{\infty}\frac{(-s)^{k}}{k!}ds=\beta\omega_{0}^{-2Z+1}\sum_{k=0}^{\infty}\frac{(-\beta\omega_{0})^{k}}{k!(k+1-2Z)}$$

Putting all this in we have

$$\int_{\beta\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+2Z}}=\frac{1}{1+2Z}(\beta\omega_{0})^{-1-2Z}e^{-\beta\omega_{0}}-\frac{1}{2Z(1+2Z)}(\beta\omega_{0})^{-2Z}e^{-\beta\omega_{0}}+\frac{1}{2Z(1+2Z)}(\Gamma(1-2Z)-(\beta\omega_{0})^{-2Z+1}\sum_{k=0}^{\infty}\frac{(-\beta\omega_{0})^{k}}{k!(k+1-2Z)})$$

The magnitude of $\beta\omega_{0}$ is always small, so we will use this
method of expansion. For integrals with endpoints $\omega_{0}\tau$ we
have two expansions to use depending on whether it is small or large.

The total order $\beta^{-1-2Z}$terms in the current from this integral
is

$$\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{2+2Z}\frac{1}{1+2Z}(\beta\omega_{0})^{-1-2Z}=\frac{e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\frac{2}{1+2Z}\beta^{-1-2Z}$$
which we see cancels the same term from the small circular integral.

To get the order $\beta^{-2Z}$ term we must expand
$e^{-\beta\omega_{0}}\approx1-\beta\omega_{0}+...$

$$\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{2+2Z}(-\frac{1}{1+2Z}(\beta\omega_{0})^{-2Z}-\frac{1}{2Z(1+2Z)}(\beta\omega_{0})^{-2Z})=-\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}\beta^{-2Z}\frac{1}{2Z}$$
, which we see cancels the same term from the circular integral meaning
that we have successfully cancelled all parts diverging as
$\beta\rightarrow0$

There remains a finite contribution independant of $\beta$,

$$\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{1+2Z}\frac{1}{2Z(1+2Z)}\Gamma(1-2Z)$$

### $\omega_{0}\tau\ll1$

Likewise for $\omega_{0}\tau\ll1$ we use the same expansion to expand
the integral

$\int_{\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+2Z}}=\frac{1}{1+2Z}(\tau\omega_{0})^{-1-2Z}e^{-\tau\omega_{0}}-\frac{1}{2Z(1+2Z)}(\tau\omega_{0})^{-2Z}e^{-\tau\omega_{0}}+\frac{1}{2Z(1+2Z)}(\Gamma(1-2Z)-(\tau\omega_{0})^{-2Z+1}\sum_{k=0}^{\infty}\frac{(-\tau\omega_{0})^{k}}{k!(k+1-2Z)})$

The same finite contribution
$-\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{1+2Z}\frac{1}{2Z(1+2Z)}\Gamma(1-2Z)$
cancels that from the $\beta$ term.

The dominant contribution at $\omega_{0}\tau\ll1$ is the first
$-\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{2+2Z}\frac{1}{1+2Z}(\tau\omega_{0})^{-1-2Z}=-\frac{e}{2\pi}\Gamma^{2}\sin(2\pi Z)\tau^{-1-2Z}\alpha^{2+2Z}\frac{2}{1+2Z}$,
which will largely be cancelled the next integral, which requires
seperate consideration.

The next order term is

$-\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{1+2Z}(-\frac{1}{1+2Z}(\tau\omega_{0})^{-2Z}-\frac{1}{2Z(1+2Z)}(\tau\omega_{0})^{-2Z})=\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\tau^{-2Z}\omega_{0}\frac{1}{2Z}$

We can integrate by parts

$$\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}=-\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s}+\frac{e^{-\tau\omega_{0}}}{\tau\omega_{0}}$$

to put in terms of$\int_{x}^{\infty}\frac{e^{-t}}{t}dt$ which is the
exponential integral $E_{1}(x)$ which possesses the convergent expansion

$$E_{1}(x)=-\gamma-\ln|x|-\sum_{k=1}^{\infty}\frac{(-x)^{k}}{k\cdot k!}$$

Where $\gamma\approx0.5772$ is the Euler-Mascheroni constant.

$$\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}=(\tau\omega_{0})^{-1}e^{-\tau\omega_{0}}+\gamma+\ln(\tau\omega_{0})+\sum_{k=1}^{\infty}\frac{(-\tau\omega_{0})^{k}}{k\cdot k!}$$

$$=(\tau\omega_{0})^{-1}\sum_{k=0}^{\infty}\frac{(-\tau\omega_{0})^{k}}{k!}+\gamma+\ln(\tau\omega_{0})+\sum_{k=1}^{\infty}\frac{(-\tau\omega_{0})^{k}}{k\cdot k!}$$

$\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}(\tau\omega_{0})^{-1}=\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\frac{1}{\tau^{2Z+1}}$.
This term nearly cancels the $O(\omega_{0}^{0})$ term from the previous
integral

$-\frac{e}{2\pi}\Gamma^{2}\sin(2\pi Z)\tau^{-1-2Z}\alpha^{2+2Z}\frac{2}{1+2Z}+\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\frac{1}{\tau^{2Z+1}}=\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\tau^{-1-2Z}\alpha^{2+2Z}\frac{2Z}{1+2Z}$.
This is second order in $Z$.

The next term is

$$(\gamma-1)\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}=(\gamma-1)\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}\frac{1}{\tau^{2Z}}$$

, which is linear in $\omega_{0}$and $O(Z)$.

Combining the two terms that are $O(\omega)$

$$(\gamma-1+\frac{1}{2Z})\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}\frac{1}{\tau^{2Z}}$$

### $\omega_{0}\tau\gg1$

For large values of $\omega_{0}\tau$, the expoential factor inside the
integral drastically reduces the value. We can use the asymptotic
expansion dervied from integration by parts to see this

$$\int_{\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2}}\sim e^{-\tau\omega_{0}}(\frac{1}{(\tau\omega_{0})^{2}}-\frac{2}{(\tau\omega_{0})^{3}}+\frac{6}{(\tau\omega_{0})^{4}}+...)$$

$$\int_{\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+2Z}}\sim e^{-\tau\omega_{0}}(\frac{1}{(\tau\omega_{0})^{2+2Z}}-\frac{2+2Z}{(\tau\omega_{0})^{3+2Z}}+\frac{(2+2Z)(3+2Z)}{(\tau\omega_{0})^{4+2Z}}+...)$$

For $\omega_{0}\tau\gg1$, the $\beta\omega_{0}$ term dominates since the
others are supressed by an exponential factor $e^{-\tau\omega_{0}}$.
hence the largest contribution is the finite contribution of the $\beta$
term from before,

$$\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\alpha^{2+2Z}\omega_{0}^{1+2Z}\frac{1}{2Z(1+2Z)}\Gamma(1-2Z)$$
,

which shows the changed power law behavior due to the interaction.

### Putting it all together

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\alpha^{2+2Z}\omega_{0}^{2+2Z}(\int_{\beta\omega_{0}}^{\infty}-\int_{\tau\omega_{0}}^{\infty})ds\frac{e^{-s}}{s^{2+2Z}}+\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}})$$

$\omega_{0}\tau\ll1$

### Left and Right

Now the left and right branch cut integrals

The small circle around the branch point does not make a nonzero
contribution and extending the integrals on each side of the branch cut
to the branch point itself does not introduce any nonzero corrections,
thus we only need consider the branch cut parts of the integral.

Changing integration variables to $t=\frac{is}{\omega_{0}}-\tau+i\alpha$
gives the left integral

$$\frac{e}{2\pi}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})\int_{0}^{\infty}\frac{ids}{\omega_{0}}e^{i\omega_{0}(\frac{is}{\omega_{0}}-\tau+i\alpha)}\frac{(\frac{\frac{is}{\omega_{0}}-\tau+i\alpha}{-\tau-i\alpha}+1)^{Z}(\frac{\frac{is}{\omega_{0}}-\tau+i\alpha}{\tau-i\alpha}+1)^{Z}}{(\frac{\frac{is}{\omega_{0}}-\tau+i\alpha}{-i\alpha}+1)^{2+2Z}}$$

Changing integration variables to $t=\frac{is}{\omega_{0}}+\tau+i\alpha$
gives the right integral

$$\frac{e}{2\pi}\Gamma^{2}(-e^{-i\frac{\pi}{2}Z}+e^{i\frac{3\pi}{2}Z})\int_{0}^{\infty}\frac{ids}{\omega_{0}}e^{i\omega_{0}(\frac{is}{\omega_{0}}+\tau+i\alpha)}\frac{(\frac{\frac{is}{\omega_{0}}+\tau+i\alpha}{-\tau-i\alpha}+1)^{Z}(\frac{\frac{is}{\omega_{0}}+\tau+i\alpha}{\tau-i\alpha}+1)^{Z}}{(\frac{\frac{is}{\omega_{0}}+\tau+i\alpha}{-i\alpha}+1)^{2+2Z}}$$

The left and right integrals are complex conjugates of each other. Their
combination gives the real contribution

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}\int_{0}^{\infty}dse^{-s}\frac{(\frac{is}{\tau\omega_{0}}+2)^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha}+\frac{-i\tau}{\alpha})^{2+2Z}})$$

With the phase of the complex arguments restricted to the domain

$0\le\arg(\frac{is}{\tau\omega_{0}}+2)\le\frac{\pi}{2}$

$-\pi\le\arg(\frac{-s}{\omega_{0}\alpha}+\frac{-i\tau}{\alpha})\le-\frac{\pi}{2}$

We can split the integral into 3 parts

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(\int_{0}^{\omega_{0}\tau}+\int_{\omega_{0}\tau}^{2\omega_{0}\tau}+\int_{2\omega_{0}\tau}^{\infty})dse^{-s}\frac{(\frac{is}{\tau\omega_{0}}+2)^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha}+\frac{-i\tau}{\alpha})^{2+2Z}})$$

$$\approx-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(\int_{0}^{\omega_{0}\tau}dse^{-s}\frac{2^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-i\tau}{\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{2\omega_{0}\tau}dse^{-s}\frac{2^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha})^{2+2Z}}$$

$$+\int_{2\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{is}{\tau\omega_{0}})^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha})^{2+2Z}}))$$

### The first term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\frac{\pi}{2}(2+2Z)}2^{Z}\alpha^{2+2Z}\omega_{0}^{-Z}\tau^{-2-3Z}\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(-\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)+\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{-Z}\tau^{-2-3Z}\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}))$$

No tricks are necessary since the integral is convergent for all
allowable Z and we can merely expand the expoential into a power series
and do the integral term by
term.$\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}=-(\omega_{0}\tau)^{Z}\sum_{k=0}^{\infty}\frac{(-\omega_{0}\tau)^{k+1}}{k!(k+1+Z)}$if
$\omega_{0}\tau\ll1$.

The lowest orders are

$\frac{(\omega_{0}\tau)^{Z+1}}{1+Z}$

$\frac{-(\omega_{0}\tau)^{2+Z}}{2+Z}$

Taking just the very first term

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(-\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)+\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{-Z}\tau^{-2-3Z}(\frac{1}{1+Z})(\omega_{0}\tau)^{1+Z}\label{eq:term-1 omega << 1}$$

$$-\frac{2e}{2\pi}\Gamma^{2}(-\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)+\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\tau^{-1-2Z}(\frac{1}{1+Z})$$

If $\omega_{0}\tau\gg1$

$\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}=\Gamma(Z+1)-\int_{\tau\omega_{0}}^{\infty}dse^{-s}s^{Z}$

Then we can use the asympotic series for large
arguments[\[eq:term-1 omega \<\< 1\]](#eq:term-1 omega << 1){reference-type="ref"
reference="eq:term-1 omega << 1"} before

$$\int_{\tau\omega_{0}}^{\infty}dse^{-s}s^{Z}\sim e^{-\tau\omega_{0}}((\tau\omega_{0})^{Z}+(Z-1)(\tau\omega_{0})^{Z-1}+(Z-1)(Z-2)(\tau\omega_{0})^{Z-2}+...)$$

Hence up to terms exponentially small in $e^{-\tau\omega_{0}},$
$\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}=\Gamma(Z+1)$

$$\frac{-2e}{2\pi}\Gamma^{2}(-\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)+\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{-1-Z}\tau^{-2-3Z}\Gamma(Z+1)$$

### The second term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\pi(2+2Z)}2^{Z}\alpha^{2+2Z}\omega_{0}^{2+Z}\tau^{-Z}\int_{\omega_{0}\tau}^{2\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+Z}}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)-\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{2+Z}\tau^{-Z}\int_{\omega_{0}\tau}^{2\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+Z}}$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)-\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{2+Z}\tau^{-Z}(\int_{\omega_{0}\tau}^{\infty}-\int_{2\omega_{0}\tau}^{\infty})ds\frac{e^{-s}}{s^{2+Z}}$$

We've evaluated this integral for the two cases already, just replace 2Z
with Z.

$\int_{\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+Z}}=\frac{1}{1+Z}(\tau\omega_{0})^{-1-Z}e^{-\tau\omega_{0}}-\frac{1}{Z(1+Z)}(\tau\omega_{0})^{-Z}e^{-\tau\omega_{0}}+\frac{1}{Z(1+Z)}(\Gamma(1-Z)-(\tau\omega_{0})^{-Z+1}\sum_{k=0}^{\infty}\frac{(-\tau\omega_{0})^{k}}{k!(k+1-Z)})$
if $\tau\omega_{0}\ll1$

The lowest orders in this expression are

$\frac{1}{1+Z}(\tau\omega_{0})^{-1-Z}$ This cancels the same order from
the first term

$\frac{1}{1+Z}(\tau\omega_{0})^{-Z}-\frac{1}{Z(1+Z)}(\tau\omega_{0})^{-Z}=-\frac{1}{Z}(\tau\omega_{0})^{-Z}$

$\frac{1}{Z(1+Z)}\Gamma(1-Z)$

Likewise

$\int_{2\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+Z}}=\frac{1}{1+Z}(2\tau\omega_{0})^{-1-Z}e^{-2\tau\omega_{0}}-\frac{1}{Z(1+Z)}(2\tau\omega_{0})^{-Z}e^{-2\tau\omega_{0}}+\frac{1}{Z(1+Z)}(\Gamma(1-Z)-(2\tau\omega_{0})^{-Z+1}\sum_{k=0}^{\infty}\frac{(-2\tau\omega_{0})^{k}}{k!(k+1-Z)})$

if $\tau\omega_{0}\gg1$
$\int_{\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+Z}}\sim e^{-\tau\omega_{0}}(\frac{1}{(\tau\omega_{0})^{2+Z}}-\frac{2+Z}{(\tau\omega_{0})^{3+Z}}+\frac{(2+Z)(3+Z)}{(\tau\omega_{0})^{4+Z}}+...)$

Likewise

$\int_{2\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2+Z}}\sim e^{-2\tau\omega_{0}}(\frac{1}{(2\tau\omega_{0})^{2+Z}}-\frac{2+Z}{(2\tau\omega_{0})^{3+Z}}+\frac{(2+Z)(3+Z)}{(2\tau\omega_{0})^{4+Z}}+...)$

### The third term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\pi(2+2Z)+i\frac{\pi}{2}Z}\alpha^{2+2Z}\omega_{0}^{2}\tau^{-2Z}\int_{2\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(2\pi Z-\omega_{0}\tau)-\sin(-\omega_{0}\tau))\alpha^{2+2Z}\omega_{0}^{2}\tau^{-2Z}\int_{2\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}))$$

This integral is also already evaluated

$\int_{2\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}=(2\tau\omega_{0})^{-1}e^{-2\tau\omega_{0}}+\gamma+\ln(2\tau\omega_{0})+\sum_{k=1}^{\infty}\frac{(-2\tau\omega_{0})^{k}}{k\cdot k!}$
if $2\tau\omega_{0}\ll1$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(2\pi Z-\omega_{0}\tau)-\sin(-\omega_{0}\tau))\alpha^{2+2Z}\omega_{0}^{2}\tau^{-2Z}((2\tau\omega_{0})^{-1}e^{-2\tau\omega_{0}}+\gamma+\ln(2\tau\omega_{0}))))$$

$\int_{2\tau\omega_{0}}^{\infty}ds\frac{e^{-s}}{s^{2}}\sim e^{-2\tau\omega_{0}}(\frac{1}{(2\tau\omega_{0})^{2}}-\frac{2}{(2\tau\omega_{0})^{3}}+\frac{6}{(2\tau\omega_{0})^{4}}+...)$
if $2\tau\omega_{0}\gg1$

### Putting it All Together

$\omega_{0}\tau\ll1$

$\omega_{0}\tau\gg1$ All these terms are less important than that from
the first section due the the only nonexpentitally suppressed term being
$\omega_{0}^{-1-Z}$ which is small for large $\omega_{0}$

Modifications for $\nu=\frac{1}{3}$
-----------------------------------

Now the charged excitations have charge $\frac{e}{3}$.

There are a couple of conventions to work with here. You can maintain
the commutation relations

$[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$

$\psi_{q}=e^{i\sqrt{\nu}\phi}$ The operator removes the fractional
quasiparticle. $\psi_{e}=e^{i\frac{\phi}{\sqrt{\nu}}}$ removes an
electron. $\psi_{q}^{\frac{1}{\nu}}=\psi_{e}$, which is the same as
cubing for $\nu=\frac{1}{3}$

$Q=\frac{e\sqrt{\nu}}{2\pi}(\phi(\infty)-\phi(-\infty))$

$\rho=\frac{e\sqrt{\nu}}{2\pi}\partial\phi$

We can see this by $[Q,e^{i\sqrt{\nu}\phi}]=e\nu e^{i\sqrt{\nu}\phi}$.

Correlation functions are unchanged since the form of the lagrangian and
commutation relations are unchanged. The magnitude of v and u and other
parameters in the lagrangian may take on new values. Naively one
anticipates that minimzally the self interation should be modified by
$\nu^{2}$. The tunnelling operator needs the choice of electron or
quasiparticle tunnelling. The choice depends on the channel it would
have to cross. If it has to tunnel through the FQH liquid then it is
quasiparticle tunnelling, since only quasipartcles are the excitation
that exists in the bulk. If it has to travel thorugh a normal later,
then electron tunneling.

$H_{q\Gamma}=\Gamma(e^{i\mbox{\ensuremath{\sqrt{\nu}}}\phi(0,t)}e^{i\omega_{0}t}+e^{-i\sqrt{\nu}\phi(0,t)}e^{-i\omega_{0}t}$

$H_{e\Gamma}=\Gamma(e^{i\frac{1}{\sqrt{\nu}}\phi(0,t)}e^{i\omega_{0}t}+e^{-i\frac{1}{\sqrt{\nu}}\phi(0,t)}e^{-i\omega_{0}t}$

$\omega_{0}=\frac{eV}{\hbar}$ for electron tunnelling

$\omega_{0}=\frac{\nu eV}{\hbar}$ for quasiparticle tunnelling.

For the situation that is in my head and seems to represent the
experiments thus far

An alternative is to absorb the $\nu$ factor into the definition of the
field. $\xi=\sqrt{\nu}\phi$ Then the $\psi=e^{i\xi}$.
$[\xi,\xi]=\nu i\pi\text{sign}$. etc. This requires a change of the
lagrangian as well since lagrangian conventions are connected to
commutations relation conventions by the path integral. Roughly
speaking, $G=L^{-1}=<\phi\phi>=[\phi,\phi]$. So to change the
commutation relations to have a factor of $\nu$ out front, we need to
change the lagrangian to have a factor of $\frac{1}{\nu}$ out front. In
this alternative convention (which matches the K matrix conventions so
it is preferable really), $\psi_{e}=e^{3i\phi}$ $\psi_{q}=e^{i\phi}$. It
takes three quasiparticles to make an electron.
$\rho=\frac{e}{2\pi}\partial\phi$ with the factor of 1/3 charge
appearing due to the commutation relation in the quasiparticle insertion
operator.

The relation for current follows through except for an extra factor of
$\nu$ out front.

$$-\frac{\nu e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})e^{\nu<\phi(t)\phi(0)-\frac{1}{2}\phi(t)\phi(t)-\frac{1}{2}\phi(0)\phi(0)>}$$

Since we have not changed the lagrangian or commutation relations, any
evaluation of the correlation function remains valid. (is the effective
velocity adjust by a factor of $\nu$?)

$$I=-\frac{e\nu}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})\frac{(\frac{t}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{\nu Z}(\frac{t}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{\nu Z}}{(\frac{t}{-i\alpha}+1)^{2\nu+2\nu Z}}$$

The evaluation of this expression is unchanged. The branch points are at
the same locations, however the order of the branch points is different.

There is a drastic difference between quasiparticle tunnelling and
electron tunnelling.

K Matrix Formalism
------------------

The go beyond the simplest Laughlin states and the integer states we
need to add in some more. The K matrix describes the theory at the edge,
the quasiparticle statistics and charges.

Okay, So what is the K-matrix.; The K-matrix encodes the topological
properties of the order.

$$\begin{pmatrix}1 & 3\\
3 & 1
\end{pmatrix}$$ This is the matrix corresponding to the 113 order.

The equations of motion are $K_{IJ}\rho_{J}=q_{I}B$. Instead of a simpl
binding of charge to vortex, there is a matrix of locking. The total
charge density is $\rho=q_{I}\rho_{I}$. The filling factor is
$\nu=\frac{\rho}{B}=q^{T}K^{-1}q$

The charge vector is $\ensuremath{q=(1,1)}$

Two kinds of quasiparticles exist, $\ensuremath{l_{1}=(1,0)}$
and$\ensuremath{l_{2}=(0,1)}$.

The filling factor is $\ensuremath{\nu=q^{T}K^{-1}q}$

The mutual statistics phase accumulated is
$$\theta_{12}=2\pi l_{1}K^{-1}l_{2}^{T}$$

My current thinking in regards the the field $\ensuremath{a_{\mu}}$. is
that $\ensuremath{a_{0}=M_{z}}$ and
$\ensuremath{a_{i}=\epsilon_{ij}P_{j}}$. The connection to the current
is
$\ensuremath{J_{\mu}=\frac{1}{2\pi}\epsilon^{\mu\nu\sigma}\partial_{\nu}a_{\sigma}}$.

The connection to current is $\ensuremath{\nabla\times M+\dot{P}=J}$ and
$\ensuremath{\nabla\cdot P=\rho}$

$\ensuremath{\epsilon_{ij}\epsilon_{jk}=-\delta_{ik}}$

Conversion to the edge theory requires a gauge choice. Physically, it is
not clear that the magnetization or polarization are gauge symmettric
quantities. Very often they seem to have a very natural choice. I
suppose there is some choice in that they are defined with respect to a
reference or equilibrium state (The undistorted atom or something. When
P=0 then $\rho=0$). This may also have to do with the fact that they are
usually in a fnite brick of material.

Rasta says that polarization is geometric phase.

### Diagonalization of K-matrix equations

The lagrangrian is the vector analog of the lagrangian for the integer
mode.
$L=-\frac{1}{4\pi}(K_{IJ}\partial_{t}\phi_{I}\partial_{x}\phi_{J}+V_{IJ}\partial_{x}\phi_{I}\partial_{x}\phi_{J})$,
with summation implied over capitalized roman indices. Variation of the
equation leads to the equations of motion

$$K_{IJ}\partial_{tx}\phi_{J}+V_{IJ}\partial_{xx}\phi_{J}=0$$

$\phi_{I}(x,t)=\int_{-\infty}^{\infty}\int_{-\infty}^{\infty}\phi_{I}(q,\omega)e^{i\omega t-iqx}\frac{d\omega dq}{(2\pi)^{2}}$

$$K_{IJ}(i\omega)(-iq)\phi_{J}+V_{IJ}(-iq)^{2}\phi_{J}=0$$

There is one solution for $q=0.$ Defining $v_{\lambda}=\frac{\omega}{q}$

$$(K_{IJ}v_{\lambda}-U_{IJ})\phi_{J}=0$$

Which is in the form of a generalized eiegenvalue problem. An eigenvaue
problem of the form $(A\lambda-B)u=0$ can be reduced to the standard
form by the substitutions $y=\sqrt{A}u$. The square root can be defined
by diagonalizing A, then taking the positive square root of each of it's
eigenavlues, then going back to the original basis.
$(\sqrt{A}\lambda-B\sqrt{A^{-1}})y=0$ can be multiplied out front with
$\sqrt{A^{-1}}$.

$$(I\lambda-\sqrt{A^{-1}}B\sqrt{A^{-1}})y=0$$

If A and B were symmettric, so is the matrix
$\sqrt{A^{-1}}B\sqrt{A^{-1}}=C$. Then we can use the slightly more
familiar eigenvector theory to determine some useful identities.

$$y_{\lambda}^{T}y_{\lambda^{'}}=\delta_{\lambda\lambda^{'}}\rightarrow u_{\lambda}^{T}Au_{\lambda^{'}}=\delta_{\lambda\lambda^{'}}$$

$$\sum_{\lambda}y_{\lambda}y_{\lambda}^{T}=I\rightarrow\sum_{\lambda}u_{\lambda}u_{\lambda}^{T}=A^{-1}$$

Going back we have a set of eigenvectors$\phi_{I}=\alpha_{I\lambda}$such
that

$$\alpha_{I\lambda}\alpha_{J\lambda}=K_{IJ}^{-1}$$

$$\alpha_{I\lambda}K_{IJ}\alpha_{J\lambda^{'}}=\delta_{\lambda\lambda'}$$

To quantize this solution, we can proceed as before, treating each
independant mode as a harmonic oscillator. $q=\frac{n\pi}{L}$

$\phi_{I}(x,t)=\sum_{n\ge0}\sum_{\lambda}\frac{1}{\sqrt{n}}(b_{n\lambda}^{\dagger}\alpha_{I\lambda}e^{-iqv_{\lambda}t+iqx}+b_{n\lambda}\alpha_{I\lambda}^{*}e^{iqv_{\lambda}t-iqx})$

$<\phi_{I}(x,t)\phi_{J}(x',t')>=\sum_{\lambda}\sum_{n\ge0}\alpha_{I\lambda}^{*}\alpha_{J\lambda}\frac{1}{n}e^{iqv_{\lambda}(t-t')-iq(x-x')}$

Or in other words, in terms of the integer results

$\phi_{I}=\alpha_{I\lambda}\phi_{\lambda}$.

Now each $\phi_{\lambda}$can be treated as an independant integer mode
of velocity $v_{\lambda}$.

Then we can reconstruct giving.

The different $\lambda$ modes are uncorrelated, so their expectation
value is 0.

For $t=t'$ this reduces to

$<\phi_{I}(x,0)\phi_{J}(x',0)>=K_{IJ}^{-1}\ln(\frac{2\pi i}{L}(x-x'-i\alpha))$

Giving the equal time commutation relation
$[\phi_{I}(x,0),\phi_{J}(x',0)]=i\pi K_{IJ}^{-1}\text{sign}(x-x')$

The perturbations to the hamiltonian will have the form of eponentials
of sums of fields.

$H_{\Gamma}\propto e^{il_{I}\phi_{i}}+H.C.$

$Q=\frac{e}{2\pi}q_{I}[\phi_{I}(\infty)-\phi_{I}(-\infty)]$

The quasiparticle creation and annihilation operators are of the form
$e^{il_{I}\phi_{i}}$. (A concern: The Left side may not inject into the
identical channel on the right side? This would lead to different
$l_{I}$ for L and R in the creation and anihitlation operators.) The
charge created by an operator $e^{il_{I}\phi_{I}}$is
$Q_{l}=eq_{I}K_{IJ}^{-1}l_{J}$ which we can see from

$$[Q,e^{il_{I}\phi_{I}}]=q_{I}K_{IJ}^{-1}l_{J}e^{il_{M}\phi_{M}}$$

The oscillatory addition to represent applied voltage will
be$\omega_{0}=\frac{Q_{l}V}{\hbar}$.

The current can be calculated as before

$$I=i[H,Q]=i[H_{\Gamma},Q]$$

$$[A,e^{B}]=[A,B]e^{B}$$

$$I=\frac{ie}{2\pi}q_{I}K_{IJ}^{-1}i\pi l_{J}i(-1-1)e^{il_{M}\phi_{M}}+H.C.=ieq_{I}K_{IJ}^{-1}l_{J}(e^{il_{M}\phi_{M}}-e^{-il_{M}\phi_{M}})$$

$<I>\approx<i\int_{-\infty}^{0}dt[H_{\Gamma}(t),I(0)]>$

### $U\protect\ne0$

A difficulty with the $U\ne0$ case is the nonuniversality of the IV
curve. It the effective scaling law will depend on the coefficient

$L=-\frac{1}{4\pi}(K_{IJ}\partial_{t}\phi_{I}\partial_{x}\phi_{J}+V_{IJ}\partial_{x}\phi_{I}\partial_{x}\phi_{J}+U_{IJ}\partial_{x}\phi_{I}P\partial_{x}\phi_{J})$

Equations of motion.

$K\partial_{x}\partial_{t}+V\partial_{x}^{2}\phi=-\partial_{x}UP\partial_{x}\phi$

We can expand to orders in U to attempt a perturbation theory as before
for small U

$v_{\lambda}=v_{\lambda0}+v_{\lambda1}+v_{\lambda2}+...$

$K^{-1}V\phi_{0}=v_{\lambda}\phi_{0}$

$\phi_{0}=\alpha_{\lambda I}e^{iv_{\lambda}qt-iqx}$

$\phi=\phi_{0}+\phi_{1}+\phi_{2}+...$

We can lose one spatial derivative by integrating once

$K\partial_{t}\phi_{1}+V\partial_{x}\phi_{1}=-UP\partial_{x}\alpha_{\lambda I}e^{iv_{\lambda}qt-iqx}$

### Generalized Eigenvalue perturbation

$(A-\lambda B)v=Cv$ where $C$ is a perturbatively small quantity.
$v=v_{0}+v_{1}+v_{2}+v_{3+...}$

$\lambda=\lambda_{0}+\lambda_{1}+\lambda_{2}+\lambda_{3}+...$.

Collecting order by order

$(A-\lambda_{0}B)v_{0}=0$

$(A-\lambda_{0}B)v_{1}-\lambda_{1}Bv_{0}=Cv_{0}$

Multiplying the first order equation on the left by
$v_{0\lambda}^{\dagger}$

$-\lambda_{1}=v_{0\lambda}^{\dagger}Cv_{0}$

Multplying on the left by $v_{0\lambda'}^{\dagger}$

$v_{0\lambda'}^{\dagger}(\lambda'_{0}-\lambda_{0})Bv_{1}=v_{0\lambda'}^{\dagger}Cv_{0}$.

Using completeness and orthogonality relation

$v_{1\lambda}=\sum_{\lambda'\ne\lambda}v_{0\lambda'}\frac{v_{0\lambda'}^{\dagger}Cv_{0\lambda}}{\lambda'_{0}-\lambda_{0}}$

The orthogonality relations

$v_{\lambda}^{\dagger}Bv_{\lambda'}=\delta_{\lambda\lambda'}$ should
also be maintained order by order.

$v_{\lambda0}^{\dagger}Bv_{\lambda'1}+v_{\lambda1}^{\dagger}Bv_{\lambda'0}=0$.

Applying this to the $U\ne0$ case.

The initial problem has two eigenvectors with eigevalues $\pm\lambda$.

$\left[\begin{array}{c}
a\\
b\\
0\\
0
\end{array}\right]\left[\begin{array}{c}
0\\
0\\
a\\
b
\end{array}\right]$ where $(V+\lambda K)\left[\begin{array}{c}
a\\
b
\end{array}\right]=0$

Because $B=\left[\begin{array}{cc}
0 & U\\
U & 0
\end{array}\right]$, $\lambda_{1}=0$.

Macroscopic Theory
------------------

We can add the effects of an underlying materials to the . If its
nondissipative, we have an even better shot of creating an effective
lagrangian for which the motion of the . We're quite used to this in the
permittivty approximation. A polarizable material changes the effective
equations of motion for the electromagnetic field. The quantum hall
states are similar although now we can have real macroscopic
nondissipative currents flowing, which from a classical resistive
perspective feels wrong. Similar to how the lorentz force and a drag
type force. The drag force is poroptional to velocity but disspative
while the lorentz force never lies in the direction of the velcoity so
it is nondisspative and can be included in a lagrangian formulation.

$\sigma E_{i}=\epsilon_{ij}j_{j}$

Consider putting a charge in. The charge will have it's coulomb field
spraying out. But then by the hall relation there is current swirling
around the charge.
$\sigma Q=\int\sigma E\times dx=\int jdx=\int\nabla\times Bdx=\int B\cdot dA$
by the Maxwell equation. Hence a charge has an amount of flux that is
bound to it.

Likewise, we can insert some flux. The insertion of the flux will create
a radial current.

We can easily image more than one type of fluid that responds.

We don't have any quantization

### Some Simple Chern Simons

Potentials are an interesting and useful concept. Potentials are a way
of defining fields such that they by defitintion maintain a condition.
For example, merely by defining $\nabla\times A=0$, we automatically
satisfy $\nabla\cdot B=0$. Typically also potentials simplify the
equations or reduce the equations to an equivalent form for which we are
more familiar. The relation between a potential and the filed of
interest is also typically that of differentation connecting the two
$\nabla\phi=E$. There is a long history of strange potentials and
potentials for potentials and so forth. One useful potential we don't
call a potential often is the polarization as a denisty potential. The
potential equations are $\nabla\cdot P=-\rho$, $\dot{P}=j$. This
potential is defined such that it automatically satisfies the continuity
equation. $\partial_{t}\rho+\nabla\cdot j=0$. A very similar definition
is that of the magnetization $M$. $\nabla\times M=j$. This also
automatically does not allow for charge build up.

### Duality

Duality is a fancy word. However it can be invoked at the point when one
notices a similarity between 2 different things and may imply nothing
more than that. The most famous duality is that of $E$ and $B$ in empty
3+1 space-time. If one replaces $E\rightarrow-B$, $B\rightarrow E$, the
Maxwell equations remain true

$\nabla\times E=-\partial_{t}B$

$\nabla\times B=\partial_{t}E$

$\nabla\cdot E=0$

$\nabla\cdot B=0$

People cannot help but notice that superficially, E and B seem so
similar, even though their intepreation differs by so much.

From theoretical physicists standpoint E and B are not the central
fields of Maxwell's theory, $A_{\mu}$is. Going from the standpoint of
$\partial_{\nu}A_{\mu}-\partial_{\mu}A_{\nu}=F_{\mu\nu}$, we can
generalize Maxwell's equations to other dimensions and see what happens.

The conceptually simplest way to measure fields is to watch a particle
travelling according to the Lorentz force laws, and inferring the fileds
from there

Does this make physical sense as an approach? While I have no clue as to
how to physically make a 5 or 34 dimensional electrodynmic system in a
lab, when we confine a particle to move in a two dimensional surface
does our definition make sense?

In 2D our defitnition only has $E=(E_{x},E_{y})$ and $B_{z}$. The
particle is confined to 2d by whatever magic force is doing so, so
$E_{z}$is inconsequential and so are the in plane components of B, both
of which only apply forces perpendicular to the surface.

The numbers of our old duality no longer match up. B has one component
and E has 2 and it is hard to imagine how we could swap the two.

However there is a curious new duality.

In 2D $\rho$ has 1 component and $j$ has 2. That's a good sign. The
density must obey the continuity equations

$\dot{\rho}+\nabla\cdot j=0$ and some more to specify the response of
the substance to external fields.

In tandem with the rest of the equations

$\nabla\times E=-\partial_{t}B$

$\nabla\times B=j+\partial_{t}E$

$\nabla\cdot E=\rho$

$\nabla\cdot B=0$ This one is irrelevant in 2D

Under the duality relation $E\rightarrow j_{i}\epsilon_{ij}$,
$\rho\rightarrow B$.

Gausses law transforms into

$\nabla\times j=B$

This is a relation from superconductivity. It is one of the London
equations. I believe this holds when you can count on an adiabatic
wavefunction change (gapped ground state). It fallows if you assume
$\psi=e^{i\phi}$.

Does the effective force law hold?

$F=eD+ev\times H$

### Duality and Quantum Mechanics

Translation invariance is the brother of the fourier transform. When
something is translation invariant, we know we should fourier trasform
the function to a new function defined on a new domain. In this new
domain, we don't see the massive interconnectedness of the differential
equations, instead we have completely independant things happening at
each freqeuncy. We can do similar things for other symmettries such as
rotational invriance etc. The things we're most used to are symmettries
of coordinates. What about if there is only symmettry in some particular
direction? Then we hsould only fourier transfrom that direction.

What is the fourier transform of gauge symmettry? By this I mean that
two different functions or field configurations have the same physical
properties. Now we're talking about symmettry of functions themselves
rather than the domain.

In the path integral, what we can do is transform over to a new dual
field.

$L=\cos(\partial_{x}\phi(x))$

The classic grad curl duality.

Suppose $E=\nabla\phi$. Then $E=\nabla\times F$.

$\int[D\phi]e^{-S[\phi]}$

Then $\delta[E-\nabla\phi]$

E are defined on edges.

$\delta[E-\nabla\phi]=\int[DF]e^{iF\cdot(E-\nabla\phi)}$

Then $\delta[E-\nabla\times F]$

F is defined on faces

$\delta[\nabla\times F-\nabla\phi]$

Normalize this.

$\int[D\phi][DE][DF]e^{-S[\phi]}\delta[E-\nabla\phi]\delta[E-\nabla\times F]$

The gauge invariance is that

Path integral, delta function, exchanging potentials.

A new labelling of physical states.

overcomplete basis. Slide a metric in.

the chemical potential and energy denisty.

The rough chart of correspondence

$\begin{array}{cc}
\rho & B_{z}\\
Q & \Phi\\
C & L\\
V & I\\
E & \epsilon j\\
\epsilon P & A\\
\phi & M_{z}
\end{array}$

Magnetization is the mesh current. The columns do not mean anything. You
just have to swap all, or rotate between the options.

It is easy to imagine having different polarizations accounting for
different species of things. Different Electromangetic fields is a bit
stranger, but we can imagine effective D and H including different
polarizations and magnetizations.

The magnetization defined from the wavefunction.

The microscopic formulation of polarization and magnetization. We need
to window and add. Difference between ensemble averaging and sum of
delta.

Including hall effect is like rotating between these two fellows. The
hall effect is not dissipative and can be described via a lagrangian and
hailtonian. What happens when we insert charge into the classical
theory? The charge has an electric field, which generates a current that
whirls around the charge. Similarly, if we thread some flux in there, an
E field builds up and a net charge ends up in the center. The two
situations are the same.

Quantum Mechanics comes in when we show that one flux quantum of
magnetic field cannot change the system. Equivalently that the angluar
momentum of the vortex flow must be quantized?

This dualistic perspective brings in the question, where does the
wavefunction fit in this? $\psi\psi^{\dagger}=\rho$

Quantization of chern simons theory. Should demonstrate the same
degeneracy as landau levels?

### g

$<O_{1}O_{1}>\propto\frac{1}{t^{g}}$. An example of $O_{1}=e^{i\phi}$.
To convert to a current calculation via wqausiparticle tunnelling, we'll
need both edges, which will double g, and do a forueir transform which
will remove one power $I\propto V^{2g-1}$. To get conductance, we need
to remove another power of V $G\propto V^{2g-2}$. The g for an integer
state is 1 and the g for a simple laughlin fractional state is $g=\nu$.

g is also used for density of states on one edge. The fourier transform
of $<\psi^{\dagger}\psi>$is essentially the density of states, so
$\rho=E^{g-1}$. The integration of fourier transform makes the -1, and
the $\frac{1}{t^{g}}$turns to $\omega^{g}$.

Interpreting g. I believe g is not universal

### K=8

The K = 8 state is identical to what one would expect from a
$\nu=\frac{1}{8}$ edge state desciption. Except the denisty is now
$\rho=\frac{e}{\pi}\partial\phi$. Which means that the application of
$e^{i\phi}$gives twice the charge that it does in the $\nu=1/8$, e/4.
The current voltage relation is then $I\propto V^{\frac{2}{\nu}-2}$. The
correlator of the field is $\propto\nu\ln$, hence the scaling dimensions
g = $\frac{1}{8}$. $<\phi\phi>\propto\nu$

### 331

$K=\left[\begin{array}{cc}
3 & 1\\
1 & 3
\end{array}\right]$

eigenvalue 2 $\frac{1}{2}\left[\begin{array}{c}
1\\
-1
\end{array}\right]$

eigenvalue 4 $\frac{1}{\sqrt{8}}\left[\begin{array}{c}
1\\
1
\end{array}\right]$

$L=\frac{-1}{4\pi}\sum_{IJ}K_{IJ}\partial_{t}\phi_{I}\partial_{x}\phi_{J}+V_{IJ}\partial_{x}\phi_{I}\partial_{x}\phi_{J}+L_{2}+\partial_{x}\phi_{I}PU_{IJ}\partial_{x}\phi_{J}$

The correlator of $<e^{i\phi_{1}}e^{i\phi_{1}}>\propto\frac{1}{t^{g}}$
$g=\left[\begin{array}{cc}
1 & 0\end{array}\right]K^{-1}\left[\begin{array}{c}
1\\
0
\end{array}\right]=\frac{3}{8}$. This is for quasiparticle tunnelling.
Also this is the best definition of the scaling dimension g.

$K^{-1}=\frac{1}{8}\left[\begin{array}{cc}
3 & -1\\
-1 & 3
\end{array}\right]$

The 331 state is

$$

### Pfaffian

The pfaffian edge state has the bosonic lagrangian part
$\nu=\frac{1}{2}$. The creation operator of is
$\sigma e^{i\frac{\phi}{2}}$. The upstairs has a factor of 1/2. The
$\sigma$ have scaling dimension of $\frac{1}{16}$
($<\sigma\sigma>\propto\frac{1}{t^{\frac{1}{8}}}$), which we'll take as
a given. $<\sigma e^{i\frac{\phi}{2}}\sigma e^{i\frac{\phi}{2}}>=$

We have a factor of $\frac{1}{2}\frac{1}{2}$from the exponent in the
expontnetal \* a factor of $\frac{1}{2}$ from the effective $\nu$ in the
correlation function. + $\frac{1}{8}$from the $\sigma$.

This gives $g=\frac{1}{4}$

So set $\nu=1/2$

$$I=-\frac{e\nu}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})\frac{(\frac{t}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{\nu Z}(\frac{t}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{\nu Z}}{(\frac{t}{-i\alpha}+1)^{2\nu+2\nu Z+\frac{1}{4}}}$$

The factor of $\frac{1}{4}$ comes from the four factors of $\sigma$.
Each H or I contains 2, and the current is the commutator of two.

### SU2

the chrged $\phi_{\rho}$ is effective in $\nu=\frac{1}{2}$. $\phi_{n}$
is in effetive integer. The both go into expoentials with 1/2 in them.

$g=\frac{1}{8}+\frac{1}{2}\frac{1}{2}+\frac{1}{2}\frac{1}{2}\frac{1}{2}=\frac{1}{2}$

### anti331

$\frac{1}{4}+\frac{1}{4}+\frac{1}{2}\frac{1}{2}\frac{1}{2}=\frac{5}{8}$

### V,U

How do the nonuniversal V and U affect the correlation functions? V does
not affect? It changes velocities which go inside logsarithms. outside
are the eigenvector $\alpha$.
