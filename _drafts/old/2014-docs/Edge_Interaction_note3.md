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
which connitues and dresses itself with an image charge on the opposite
side of the contact. It can then continue flowing up the edge until it
comes out the other side, where it needs to undress itself, which
excites a charge (releases its image charge) back at the other side.

Okay. Can I clearly demonstrate that explicitly? Not to my satisfaction.

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

Putting this into the mode expansion we have

$$\phi(x,t)=\sum_{n>0}\frac{1}{\sqrt{n}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))$$

Evaluating $<\phi(x,t)\phi(x',t')>$is easily done by inserting this
expression into the brackets. The only term to survive are those with
ordering **$bb^{\dagger}$**

$<\phi(x)\phi(x')>=<(\sum_{n>0}\frac{1}{\sqrt{n}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))(\sum_{n'>0}\frac{1}{\sqrt{n'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{n}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

We need to explain our chosen normalization conventions. The overall
normalization of each mode is not specified by the equations of motion
nor are the . The normalization is determined by the Lagrangian in the
path integral formulation.

However we choose the normalization such that the commutation relation
$[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$

I-V from Correlation Function
-----------------------------

The method of Bosonization allows us to calculate properties of an
interacting 1-d fermi system from calculations using a free boson field.
The creation operators $\psi\approx e^{i\phi}$ and
$\rho\approx\partial_{x}\phi$. This is reasonable upon: 1. comparing
green's functions (except that we cannot necessarily a priori calcaute
them for anything but the free fermi field) 2. checking commutators and
seeing that they match. 3.

The reasonableness of various operations can be seen in the
noninteracting case, where we can easily explicitly evaluate both sides
of the bosonization equivalance.

The hamiltonian is

One way to different biasing of the edges is to include an exoential
term $e^{-i\omega_{0}t}\psi_{L}$
$e^{i\omega_{0}t}\psi_{L}^{\dagger}$with the left moving field
operators.

The tu neling term is the hamiltonian will inject partciels from the
left moving to right moving
edges$H_{\Gamma}=\Gamma(\psi_{L}^{\dagger}\psi_{R}e^{i\omega_{0}t}+\psi_{R}^{\dagger}\psi_{L}e^{-i\omega_{0}t})=\Gamma e^{\phi}stuff$

$H_{\Gamma}=\Gamma(\psi_{L}^{\dagger}\psi_{R}e^{i\omega_{0}t}+\psi_{R}^{\dagger}\psi_{L}e^{-i\omega_{0}t})=\Gamma(e^{-i\phi_{L}}e^{-i\phi_{R}}e^{i\omega_{0}t}+e^{i\phi_{R}}e^{i\phi_{L}}e^{-i\omega_{0}t})$
Recheck this convention.

$[\phi_{R}(x),\phi_{R}(x')]=i\pi\text{sign(x-x') }$

The creation operator ought to increase the charge by one and should
satisfy $[Q,\psi^{\dagger}]=e\psi^{\dagger}$, the analog of
$[N,a^{\dagger}]=a^{\dagger}$

The total charge
$Q=\int dx\rho=\frac{e}{2\pi}(\phi(\infty)-\phi(-\infty))$.

The tunneling current $I=\dot{Q}=i[H,Q_{L}]=i[H_{\Gamma},Q_{L}]$. The
charge operator commutes with all parts of the hmailtonian except the
tunneling part $H_{\Gamma}$.

Given $[A,B]=C$ and C commutes with A and B, we have $[A,e^{B}]=Ce^{B}$.
The simplest example of this is
$[\partial_{x},ax]=a$,$[\partial_{x},e^{ax}]=ae^{ax}$.

$[Q,e^{-i\phi}]=\frac{e*}{2\pi}[\phi(\infty),e^{-i\phi}]-\frac{e*}{2\pi}[\phi(-\infty),e^{-i\phi}]=\frac{\pi e*}{2\pi}\text{sign(\ensuremath{\infty}-x) }e^{-i\phi}-\frac{\pi e*}{2\pi}\text{sign(-\ensuremath{\infty}-x) }e^{-i\phi}=e*e^{-i\phi}$

$I=i[\Gamma(e^{-i\phi_{L}}e^{-i\phi_{R}}e^{i\omega_{0}t}+e^{i\phi_{R}}e^{i\phi_{L}}e^{-i\omega_{0}t}),\frac{e}{2\pi}(\phi_{L}(\infty)-\phi_{L}(-\infty))]$

Essentially, one term in $H_{\Gamma}$ gets its sign reversed.

$i[H_{\Gamma},Q_{L}]=i[\Gamma e^{-i\phi_{L}}e^{-i\phi_{R}}e^{i\omega_{0}t},Q_{L}]+i[\Gamma e^{i\phi_{R}}e^{i\phi_{L}}e^{-i\omega_{0}t},Q_{L}]=ie*\Gamma(e^{-i\phi_{L}}e^{-i\phi_{R}}e^{i\omega_{0}t}-e^{i\phi_{R}}e^{i\phi_{L}}e^{-i\omega_{0}t})$

$[e^{A},e^{B}]=[$

Hence we conclude that $\psi_{R}^{\dagger}=e^{-i\phi_{R}}$ and
$\psi_{R}=e^{i\phi_{R}}$

If $[\phi_{L}(x),\phi_{L}(x')]=-i\pi\text{sign(x-x') }$, then these
relations are reversed $\psi_{L}^{\dagger}=e^{i\phi_{L}}$ and
$\psi_{L}=e^{-i\phi_{L}}$

$<U(-\infty,t)I(0)U(t,-\infty)>=$

$U(t,-\infty)=1+i\int_{-\infty}^{t}dt'H_{\Gamma}(t')U(t',-\infty)$.
Sign? I think this makes sense but its the opposite of Dima's paper.

$e^{A}e^{B}=e^{B}e^{A}e^{[A,B]}$ This can easily be checked to at least
first order, for memory purposes.

$e^{i\phi(x)}e^{i\phi(x')}=e^{i\phi(x')}e^{i\phi(x)}e^{-[\phi(x),\phi(x')]}=e^{i\phi(x')}e^{i\phi(x)}e^{\pm i\pi}=-e^{i\phi(x')}e^{i\phi(x)}$
Hence these operators anticommute as fermion operators should.

The $i\pi$commutation relation is actually regularized as
$\ln\frac{x+i\alpha}{x-i\alpha}$. If x is comparable to $\alpha$ as in
the equal position commutation relation

$e^{i\phi(x)}e^{-i\phi(x')}=e^{-i\phi(x')}e^{i\phi(x)}e^{[\phi(x),\phi(x')]}=e^{i\phi(x')}e^{i\phi(x)}e^{\pm i\pi}=-e^{i\phi(x')}e^{i\phi(x)}$

$\nu=1/3$
---------

$\nu=1/3$ can be bosonized similarly to the integer case, with some
slight changes made to. First off, a creation operator should create a
object with charge e/3. Secondly,

Nothing of the green function is change? Essentially I'll just boost
down expoenents by 1/3

Hmm are the operators phase commuting?

Laughlin State connection

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
waves. However, if $e^{ikx}$ appears so must $e^{-ikx}$, since the P
operator turns $x\rightarrow-x$. Hence, we can make the guess
$Ae^{ikx}+Be^{-ikx}$ with A and B being unknown coefficients that will
be constrained by the equations of motion.

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

$\phi=C\sin(kx)+D\cos(kx)=-i\sqrt{v-u}\sin(kx)+\sqrt{v+u}\cos(kx)=-i\sqrt{v-u}\frac{e^{ikx}-e^{-ikx}}{2i}+\sqrt{v+u}\frac{e^{-ikx}+e^{-ikx}}{2}=\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx}$

In the limit $u\rightarrow0$ the solution is $\sqrt{v}e^{-i\omega x}$

If outside we normalize the function on the left side to $e^{-ikx}$ and
matching $\phi(-a_{-})=\phi(-a_{+})$

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
$\phi=\sum_{\omega}\frac{1}{\sqrt{n}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x)$

$<\phi(x)\phi(x')>=<(\sum_{\omega}\frac{1}{\sqrt{n}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x)(\sum_{\omega'}\frac{1}{\sqrt{n'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{\omega}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

For the $u=0$ case this supplies (check signs of the x and x') (also
compare with calculation of free green's function by other methods)

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
identity$\sum_{n>0}\frac{1}{n}e^{-q(ix+a)}\approx-\ln\frac{2\pi i}{L}(x-ia)$

$$<\phi(x,t)\phi(x',t')>=\sum_{\omega}\frac{1}{n}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

$$=\sum_{\omega}\frac{1}{n}e^{-i\omega(t-t')}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)+Z(-\ln\frac{2\pi i}{L}(\frac{x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)-\ln\frac{2\pi i}{L}(\frac{-x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))-Z^{2}\ln\frac{2\pi i}{L}(\frac{x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)$$

As $Z=0$, the only term to survive is the $q=0$ term
$-\ln\frac{2\pi i}{L}(-x+x'+t-t'-ia)$

Setting $x=x'=0$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)+Z(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))-Z^{2}\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)$$

$$=\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))(1+2Z+Z^{2})$$

$$=\frac{1+Z}{1-Z}\sum_{q\text{ }}(-Z)^{|q|}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))$$

### Multi Step

The essence of the matching procedure is one direction.

Perturbative Calculation
------------------------

$L=L_{0}+V$

$\phi V\phi=\frac{-1}{4\pi}\int dxdt\partial_{x}\phi u(x)P\partial_{x}\phi$

$\phi L_{0}\phi=\frac{-1}{4\pi}(\int dxdt\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi)$

$G_{0}=L_{0}^{-1}$

$LG=I$

$(L_{0}+V)G=I$

Apply $G_{0}$ to the left of both sides

$G+G_{0}VG=G_{0}$

$G=G_{0}-G_{0}VG$

The first order approximation replacing the actual green's function G on
the right hand side with $G_{0}$

$G\approx G_{0}-G_{0}VG_{0}$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int dx''dt''G_{0}(x-x'',t-t'')VG_{0}(x''-x',t''-t')$

$G_{0}(x-x',t-t')$=$\frac{1}{2i}\int\frac{dkd\omega}{(2\pi)^{2}}e^{i\omega(t-t')-ik(x-x')}\frac{4\pi}{k(\omega+i\epsilon\text{sign}(\omega))-vk)}$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int dx''dt''\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'd\omega'}{(2\pi)^{2}}e^{i\omega(t-t'')-ik(x-x'')}P_{x''}e^{i\omega'(t''-t')-ik'(x''-x')}u(x'')(-ik')(-ik)G_{0}(\omega,k)G_{0}(\omega',k')$

what about -1/4pi. I think inlcusion in green's function will net cancel
it out so theres only one overall factor.

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int dx''dt''\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'd\omega'}{(2\pi)^{2}}e^{i\omega(t-t'')-ik(x-x'')}e^{i\omega'(t''-t')-ik'(-x''-x')}u(x'')(-ik')(-ik)G_{0}(\omega,k)G_{0}(\omega',k')$

$u(k)=\int dxe^{ikx}u(x)$

$u(k)=u\int_{-a}^{a}dxe^{ikx}=\frac{u}{ik+\delta}(e^{ika}-e^{-ika})$

The sign of the$\delta$ prescription does not matter. The difference
between the two signs is representing the box function as
$-\theta(x-a)+\theta(x+a)$ or as $-\theta(-x+a)+\theta(-x-a)$

$\int dt''\rightarrow2\pi\delta(\omega-\omega')$

$\int dx''\rightarrow u(k+k')$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'd\omega'}{(2\pi)^{2}}2\pi\delta(\omega-\omega')e^{i\omega t-ikx}e^{-i\omega t')+ik'x'}u(k+k')(-ik')(-ik)G_{0}(\omega,k)G_{0}(\omega',k')$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega t-ikx}e^{-i\omega t'+ik'x'}u(k+k')(-ik')(-ik)G_{0}(\omega,k)G_{0}(\omega,k')$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}u(k+k')(-ik')(-ik)G_{0}(\omega,k)G_{0}(\omega,k')$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}u(k+k')(-i)(-i)\frac{4\pi}{\omega+i\epsilon\text{sign}(\omega)-vk}\frac{4\pi}{\omega+i\epsilon'\text{sign}(\omega)-vk'}$

Need to be more careful with $\omega$

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int\frac{dkd\omega}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}u(k+k')\frac{-4\pi}{\omega+i\epsilon\text{sign}(\omega)-vk}\frac{4\pi}{\omega+i\epsilon\text{sign}(\omega)-vk'}$

$t>t'$We close the contour upwards gaining $2\pi i$and only collecting
poles $\omega=vk-i\epsilon\text{sign}(\omega)$, in other words $k<0$.

$G(x,x',t,t')\approx G_{0}(x-x',t-t')+2\pi i\int\frac{dk}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}u(k+k')(4\pi)^{2}(e^{ivk(t-t')}\frac{\theta(-k)}{vk+i(\epsilon-\epsilon')-vk'}+e^{ivk'(t-t')}\frac{\theta(-k')}{vk'+i(\epsilon'-\epsilon)-vk})$

Relabeling dummy indices k and k'

$2\pi i\int_{-\infty}^{0}\frac{dk}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{ivk'(t-t')}u(k+k')(4\pi)^{2}(e^{-ikx+ik'x'}\frac{1}{vk+i(\epsilon-\epsilon')-vk'}+e^{-ik'x+ikx'}\frac{1}{vk+i(\epsilon'-\epsilon)-vk'})$

$2\pi i\int_{-\infty}^{0}\frac{dk}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{ivk'(t-t')}\frac{u}{i(k+k')+\delta}(e^{i(k+k')a}-e^{-i(k+k')a})(4\pi)^{2}(e^{-ikx+ik'x'}\frac{1}{vk+i(\epsilon-\epsilon')-vk'}+e^{-ik'x+ikx'}\frac{1}{vk+i(\epsilon'-\epsilon)-vk'})$

We now can do the contour integral over k'. This can expand out to 4
terms, each of which possesses 2 poles.

The direction to close the contour depends on the signs of combinations
of x,x' and $\pm a$. Let us pick $x=x'=0$ for simplicity and $t>t'$.

Doesn't it depend on whether $t-t'\pm a$ is positive or negative?

$e^{ik'a}$closes upwards and $e^{-ik'a}$closes downwards. The $u(k+k')$
pole is in the lower half plane. Hence it only gets included

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-2\pi i\int\frac{dk}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}\frac{u}{i(k+k')+\delta}(e^{i(k+k')a}-e^{-i(k+k')a})((-4\pi)\frac{4\pi\theta(-k)}{vk+i(\epsilon-\epsilon')-vk'}+\frac{-4\pi\theta(-k')}{vk'+i(\epsilon'-\epsilon)-vk}4\pi)$

We combine the two terms

The two terms are quite similar

$-2\pi i\int_{-\infty}^{\infty}\frac{dk}{(2\pi)^{2}}\int\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}\frac{u}{i(k+k')+\delta}(e^{i(k+k')a}-e^{-i(k+k')a})(-4\pi)\frac{4\pi}{vk+i(\epsilon-\epsilon')-vk'}$

$-2\pi i\int\frac{dk}{(2\pi)^{2}}\int_{-\infty}^{\infty}\frac{dk'}{2\pi}e^{i\omega(t-t')-ikx+ik'x'}\frac{u}{i(k+k')+\delta}(e^{i(k+k')a}-e^{-i(k+k')a})\frac{-4\pi\theta}{vk'+i(\epsilon'-\epsilon)-vk}4\pi$

Now we can do the k contour
