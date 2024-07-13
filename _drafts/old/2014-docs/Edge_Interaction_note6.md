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

The mode operators have the standard commutation relation
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
$e^{-i\omega_{0}}\psi$satisfies the equation
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
$<\phi(t)\phi(0)>=<\phi(-t)\phi(0)>$. We can collect terms to obtain
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

$$<\phi_{R}(0,t)\phi_{R}(0,t')>\approx-(1+2Z)\ln(\frac{2\pi i}{L}(t-t'-i\alpha))+Z\ln(\frac{2\pi i}{L}(\frac{-2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)+Z\ln(\frac{2\pi i}{L}(\frac{2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

Before we have only been considering the right moving edge. To include
the left moving edge with $u=0$ in our correlation function

$$<\phi(0,t)\phi(0,t')>\approx-(2+2Z)\ln(\frac{2\pi i}{L}(t-t'-i\alpha))+Z\ln(\frac{2\pi i}{L}(\frac{-2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)+Z\ln(\frac{2\pi i}{L}(\frac{2a}{\sqrt{v^{2}-u^{2}}}+t-t'-i\alpha)$$

$$I=-\frac{e}{2\pi}\Gamma^{2}\int_{-\infty}^{\infty}dt(e^{-i\omega_{0}t}-e^{i\omega_{0}t})\frac{(\frac{t}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}(\frac{t}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}}{(\frac{t}{-i\alpha}+1)^{2+2Z}}$$

The three branch points occur above the real axis in the upper t plane.
Let us assume $\omega_{0}>0$. We wrap the contour around each branch
point and push up in the $it$ direction.

The term with $e^{-i\omega_{0}t}$ can be have its contour deformed
downward and thus does not contribute to the integral. The
$e^{i\omega_{0}t}$term's contour must be deformed upward, but it gets
caught on the branch points, leaving three terms.

Changing integration variables to $t=\frac{is}{\omega_{0}}+i\alpha$, the
term from the central branch point is

$$\frac{e}{2\pi}\Gamma^{2}(e^{-i\pi(2+2Z)}-e^{i\pi(2+2Z)})\int_{0}^{\infty}\frac{ids}{\omega_{0}}e^{-s}\frac{(\frac{\frac{is}{\omega_{0}}+i\alpha}{\frac{-2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}(\frac{\frac{is}{\omega_{0}}+i\alpha}{\frac{2a}{\sqrt{v^{2}-u^{2}}}-i\alpha}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

The phase of $\frac{\frac{is}{\omega_{0}}}{-i\alpha}+1$ is not single
valued for the incoming and outgoing sections of the contour. This leads
to the factor out front. The phase is measured relative to the $-i$
t-axis. The numerator factors have equal and opposite phase and the same
magnitude, hence we can replace both with a absolute value squared.

For convenience define $\tau=\frac{2a}{\sqrt{v^{2}-u^{2}}}$. This is the
time it takes for charge to travel across the entire step region of size
$2a$.

$$\frac{e}{2\pi}\Gamma^{2}(e^{-i\pi(2+2Z)}-e^{i\pi(2+2Z)})\int_{0}^{\infty}\frac{ids}{\omega_{0}}e^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

$$\frac{2e}{2\pi}\Gamma^{2}\sin(2\pi Z)\int_{0}^{\infty}\frac{ds}{\omega_{0}}e^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}$$

$$=\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\int_{0}^{\omega_{0}\tau}dse^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{\infty}dse^{-s}\frac{((\frac{s}{\omega_{0}\tau})^{2}+1)^{Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}})$$

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\int_{0}^{\omega_{0}\tau}dse^{-s}\frac{1}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{s}{\omega_{0}\tau})^{2Z}}{(\frac{s}{\omega_{0}\alpha})^{2+2Z}})$$

$$\approx\frac{2e}{2\pi\omega_{0}}\Gamma^{2}\sin(2\pi Z)(\alpha^{2+2Z}\omega_{0}^{1+2Z}\int_{0}^{\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+2Z}}+\alpha^{2+2Z}\omega_{0}^{2}\frac{1}{\tau^{2Z}}\int_{\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}})$$

For different cases different terms dominate. For $\omega_{0}\tau\ll1$,
the second term dominates. For $\omega_{0}\tau\gg1$, the first term
dominates

'

Now the left and right branch cut integrals

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

$$\approx-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(\int_{0}^{\omega_{0}\tau}dse^{-s}\frac{2^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-i\tau}{\alpha})^{2+2Z}}+\int_{\omega_{0}\tau}^{2\omega_{0}\tau}dse^{-s}\frac{2^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha})^{2+2Z}}+\int_{2\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{is}{\tau\omega_{0}})^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha})^{2+2Z}}))$$

$$\approx-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\frac{\pi}{2}(2+2Z)}\alpha^{2+2Z}2^{Z}\tau^{-2-Z}\omega_{0}^{-Z}\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}+e^{i\pi(2+2Z)}2^{Z}\omega_{0}^{2+Z}\alpha^{2+2Z}\tau^{-Z}\int_{\omega_{0}\tau}^{2\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+Z}}+\int_{2\omega_{0}\tau}^{\infty}dse^{-s}\frac{(\frac{is}{\tau\omega_{0}})^{Z}(\frac{s}{\tau\omega_{0}})^{Z}}{(\frac{-s}{\omega_{0}\alpha})^{2+2Z}}))$$

The first term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\frac{\pi}{2}(2+2Z)}2^{Z}\alpha^{2+2Z}\omega_{0}^{-Z}\tau^{-2-3Z}\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(-\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)+\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{-Z}\tau^{-2-3Z}\int_{0}^{\omega_{0}\tau}dse^{-s}s^{Z}))$$

The second term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\pi(2+2Z)}2^{Z}\alpha^{2+2Z}\omega_{0}^{2+Z}\tau^{-Z}\int_{\omega_{0}\tau}^{2\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+Z}}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(\frac{3\pi}{2}Z-\omega_{0}\tau)-\sin(-\frac{\pi}{2}Z-\omega_{0}\tau))2^{Z}\alpha^{2+2Z}\omega_{0}^{2+Z}\tau^{-Z}\int_{\omega_{0}\tau}^{2\omega_{0}\tau}ds\frac{e^{-s}}{s^{2+Z}}$$

The third term

$$-2\text{Im}(\frac{e}{2\pi\omega_{0}}\Gamma^{2}(e^{i\frac{\pi}{2}Z}-e^{-i\frac{3\pi}{2}Z})e^{-i\omega_{0}\tau}(e^{i\pi(2+2Z)+i\frac{\pi}{2}Z}\alpha^{2+2Z}\omega_{0}^{2}\tau^{-2Z}\int_{2\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}))$$

$$\frac{-2e}{2\pi\omega_{0}}\Gamma^{2}(\sin(2\pi Z-\omega_{0}\tau)-\sin(-\omega_{0}\tau))\alpha^{2+2Z}\omega_{0}^{2}\tau^{-2Z}\int_{2\omega_{0}\tau}^{\infty}ds\frac{e^{-s}}{s^{2}}))$$
