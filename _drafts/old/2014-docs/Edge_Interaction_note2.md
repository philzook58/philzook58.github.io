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

The correlation function for
$L=\frac{-1}{4\pi}(\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi)$
is.

The Green's function for
$\partial_{t}\partial_{x}G+v\partial_{x}\partial_{x}G=4\pi\delta(t-t')\delta(x-x')$\
Using the expansion
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(k,\omega)e^{i\omega t-ikx}\frac{d\omega dk}{(2\pi)^{2}}$

$$(-iki\omega+v(-ik)^{2})G=4\pi$$

$G=\frac{4\pi}{k\omega-vk^{2}}=\frac{4\pi}{k(\omega-vk)}$

$<\phi(x,t)\phi(0,0)>$ for $t>0$ can be determined by using the time
ordered prescption
$\omega\rightarrow\omega+i\epsilon\text{sign}(\omega)$ and the identity
$<\phi(x,t)\phi(0,0)>=\frac{1}{2i}G$

$G_{0}$=$\frac{1}{2i}\int\frac{dkd\omega}{(2\pi)^{2}}e^{i\omega t-ikx}\frac{4\pi}{k(\omega+i\epsilon\text{sign}(\omega))-vk)}$

First the $\omega$ integral may be done. The pole is
$\omega=vk-i\epsilon\text{sign}(\omega)$. For $t>0$ we close our contour
in the upper half of the $\omega$ plane. The pole is located in the
upper half plane when $\text{sign}(\omega)=-1$ , hence with only
negative values of k.

$$G_{0}=\frac{2\pi i}{2i}\int\frac{dk}{(2\pi)^{2}}e^{ivkt-ikx}\frac{4\pi\theta(-k)}{k}$$

Cancelling constants

$$G_{0}=\int dke^{ivkt-ikx}\frac{\theta(-k)}{k}$$

Changing $k\rightarrow-k$

$$G_{0}=-\int_{0}^{\infty}dke^{-ivkt+ikx}\frac{\theta(k)}{k}$$

Putting in a finite box would chnage the integral in k-space to a sum of
spacing $\frac{2\pi}{L}$, avoiding the divergence due to the origin. The
short distance divergence can be removed by putting in a convergence
factor of $e^{-ka}$.

$\int_{0}^{\infty}\frac{dk}{k}e^{-k(ix+a)}\rightarrow\sum_{n>0}\frac{1}{n}e^{-\frac{2\pi}{L}n(ix+a)}\approx-\ln\frac{2\pi i}{L}(x-ia)$

$$<\phi(x,t)\phi(0,0)>=-\ln(\frac{2\pi i}{L}(vt-x-ia))$$

From this we can determine the equal time commutation relation

$[\phi(x,0),\phi(0,0)]=<\phi(x,\epsilon)\phi(0,0)>-<\phi(0,\epsilon)\phi(x,0)>=-\ln(\frac{2\pi i}{L}(v\epsilon-x-ia))+\ln(\frac{2\pi i}{L}(v\epsilon+x-ia))=i\pi\text{sign}(x)$

As a conistency check we can show the Hamiltonian equations

$H=v\int dx\partial_{x}\phi\partial_{x}\phi=-v\int dx\phi\partial_{x}^{2}\phi$

$\partial_{t}\partial_{x}\phi=i[H,\partial_{x}\phi(x)]=i\int dy\partial_{y}^{2}\phi(y)[\phi(y),\partial_{x}\phi(x)]=$

$$\int dte^{-i\omega t}<\phi(x,t)\phi(0,0)>=-\int dte^{-i\omega t}\ln(\frac{2\pi i}{L}(vt-x-ia))$$

$$-\frac{1}{-i\omega}e^{-i\omega t}\ln(\frac{2\pi i}{L}(vt-x-ia))]+\int\frac{1}{-i\omega}e^{-i\omega t}\frac{v}{vt-x-ia}$$

Ignoring the first term or maybe adding in a $e^{-b|t|}$ convergence
factor

$$\frac{2\pi i}{-i\omega}e^{-i\frac{\omega}{v}(x+ia)}\theta(-\omega)$$

### With U

The more unusual term in the action is the last one, which corresponds
to a point interaction directly across the peninsula that the quantum
hall edge state is flowing around. $P$ is the parity operator defined by
$Pf(x)=f(-x)$. It is used because $\partial_{x}\phi(-x)$ is slightly
ambiguous notation that makes it difficult to keep signs correct
throughout a calculation. When I write $\partial_{x}\phi(-x)$, do I want
to take the derivative first or flip the sign of the argument first. The
two operators $\{P,\partial_{x}\}=0$ anti-commute, so the choice
matters. The correct prescription based on the physical interpretation
of $\rho=\partial_{x}\phi(x)$ is to take the derivative and then reverse
the sign of the argument, since we want to couple to the density
$\partial_{x}\phi$ at the opposite side of the contact.

Taking the variation of the action we have the equation of motion for
the field $\phi$

$$\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

The analogous calculation with u inserted is

Replacing with the identity
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(x,\omega)e^{i\omega t}\frac{d\omega}{2\pi}$
we transform this equation to

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

We'll treat the $u(x)=u$ constant case first and then match the interior
solution to the exterior solution. The equation is for heuristic
purposes roughly translation invariant, so we still anticipate plane
waves. However, if $e^{ikx}$ appears so must $e^{-ikx}$, since there is
a term that turns $x\rightarrow-x$. Hence, we can make the guess
$Ae^{ikx}+Be^{-ikx}$ with A and B being unknown coefficients that will
be constrained by the equations of motion.

It turns out that if one uses the equivalent expansion
$\phi=C\sin(kx)+D\cos(kx)$ things come out a tad cleaner, so we will.

The equation expands

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

$$i\omega Ck\cos(kx)+-i\omega Dk\sin(kx)-k^{2}vC\sin(kx)-k^{2}vD\cos(kx)+-uk^{2}C\sin(kx)+uk^{2}D\cos(kx)=0$$

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

$$(-vk^{2}-uk^{2})(-vk^{2}+uk^{2})--i\omega ki\omega k=0$$

$$v^{2}k^{4}-u^{2}k^{4}-\omega^{2}k^{2}=0$$

Removing the possibility of $k^{2}=0$ we get the relation

$$(v^{2}-u^{2})k^{2}=\omega^{2}$$

The ratio of C/D can be determined by using either row of the matrix.

$$\frac{C}{D}=\frac{i\omega k}{-vk^{2}-uk^{2}}=\frac{-vk^{2}+uk^{2}}{-i\omega k}$$

Substituting in the relation for $\omega=k\sqrt{v^{2}-u^{2}}$

$$\frac{C}{D}=-i\sqrt{\frac{v-u}{v+u}}$$

An easy way to achieve this is to set, $C=-i\sqrt{v-u}$ $D=\sqrt{v+u}$,
with the understanding that there is still an overall unspecified
normalization.

We now expand back into complex exponentials

$\phi=C\sin(kx)+D\cos(kx)=-i\sqrt{v-u}\sin(kx)+\sqrt{v+u}\cos(kx)=-i\sqrt{v-u}\frac{e^{ikx}-e^{-ikx}}{2i}+\sqrt{v+u}\frac{e^{-ikx}+e^{-ikx}}{2}=\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx}$

In the limit $u\rightarrow0$.

Outside the solution is $e^{-i\omega x}$

If outside we normalize the function on the left side to $e^{-ikx}$ and
matching $\phi(-a_{-})=\phi(-a_{+})$

$$e^{-i\omega(-a)}=A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)})$$

$$A=\frac{e^{-i\omega(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}$$

Therefore when $-a<x<a$

$$\psi(x)=\frac{e^{-i\omega(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx})$$

Defining $Z=\frac{\sqrt{v+u}-\sqrt{v-u}}{\sqrt{v+u}+\sqrt{v-u}}$. For
small $u$, $Z\approx u$, so expansions in Z will roughly be expansions
in weak potentials u.

$$\psi=\frac{e^{-i\omega(-a)}}{e^{-ik(-a)}+Ze^{ik(-a)}}(e^{-ikx}+Ze^{ikx})=\frac{e^{-i(\omega-k)a}}{1+Ze^{-2ika}}(e^{-ikx}+Ze^{ikx})$$

$$<\phi(x)\phi(x')>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

The expansion in annihilation and creation operators reads
$\phi=\sum_{\omega}\frac{1}{\sqrt{2\omega}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x)$

$<\phi(x)\phi(x')>=<(\sum_{\omega}\frac{1}{\sqrt{2\omega}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x)(\sum_{\omega'}\frac{1}{\sqrt{2\omega'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

For the $u=0$ case this supplies (check signs of the x and x') (also
compare with calculation of free green's function by other methods)

$$\sum_{\omega}\frac{1}{2\omega}e^{ik(x-x')}e^{-i\omega(t-t')}$$

$$\psi^{*}(x)\psi(x')=\frac{e^{i(k_{0}-k)a}}{1+Ze^{2ika}}(e^{ikx}+Ze^{-ikx})\frac{e^{-i(k_{0}-k)a}}{1+Ze^{-2ika}}(e^{-ikx'}+Ze^{ikx'})$$

$$\frac{1}{1+Ze^{-2ika}}\frac{1}{1+Ze^{2ika}}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

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

Now we can do the $\omega$ summation term by term.

$\sum_{n>0}\frac{1}{n}e^{-q(ix+a)}\approx-\ln\frac{2\pi i}{L}(x-ia)$

$$<\phi(x)\phi(x')>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

$\int\frac{dk}{k}=\sum\frac{1}{n}$ since the conversion factor between k
and n ($\frac{2\pi}{L}$), cancel. $\omega=\frac{2\pi n}{T}$?

$$=\sum_{\omega}\frac{1}{2\omega}e^{-i\omega(t-t')}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikqa}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

$-\ln\frac{2\pi i}{L}(\frac{-x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)$

$$=\frac{T}{2\pi2}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)+Z(-\ln\frac{2\pi i}{L}(\frac{x+x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)-\ln\frac{2\pi i}{L}(\frac{-x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))-Z^{2}\ln\frac{2\pi i}{L}(\frac{x-x'-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)$$

Setting $x=x'=0$

$$=\frac{T}{2\pi2}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)+Z(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))-Z^{2}\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia)$$

$$=\frac{T}{2\pi2}\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))(1+2Z+Z^{2})$$

$$=\frac{T}{2\pi2}\frac{1+Z}{1-Z}\sum_{q\text{ }}(-Z)^{|q|}(-\ln\frac{2\pi i}{L}(\frac{-2qa}{\sqrt{v^{2}-u^{2}}}+t-t'-ia))$$

The Shankar prescription probably makes more sense rather than the von
delft.

### No U

For review and to show that the steps taken in the above work in the
already solved case we'll show how to get the correlation function with
the $u(x)$ term set to 0. The Lagrangian is then
$L=\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi$.
Taking the variation we get the equations of motion

$$\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

Replacing with the identity
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(x,\omega)e^{i\omega t}\frac{d\omega}{2\pi}$
we transform this equation to

.

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi=0$$

Without the edge bridging term the solution would be $Ae^{-ikx}+C$.

$$i\omega(-ik)Ae^{-ikx}+v(-ik)^{2}Ae^{-ikx}=0$$

Hence $k=\frac{\omega}{v}$ . The constant solution is swept under the
rug and ignored.

Putting this into the mode expansion.

$$\phi=\sum_{\omega}\frac{1}{\sqrt{2\omega}}(e^{i\omega t}b_{\omega}^{\dagger}\psi_{\omega}(x)+e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))$$

Evaluating $<\phi(x,t)\phi(x',t')>$is easily done by inserting this
expansion into

$<\phi(x)\phi(x')>=<(\sum_{\omega}\frac{1}{\sqrt{2\omega}}e^{-i\omega t}b_{\omega}\psi_{\omega}^{*}(x))(\sum_{\omega'}\frac{1}{\sqrt{2\omega'}}(e^{i\omega't'}b_{\omega'}^{\dagger}\psi_{\omega'}(x'))>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$

The after expansion only term to survive are those with the creation
operator and then the annihilation operator **$bb^{\dagger}$**reducing

$$<\phi(x)\phi(x')>=\sum_{\omega}\frac{1}{2\omega}\psi_{\omega}^{*}(x)\psi_{\omega}(x')e^{-i\omega(t-t')}$$

We need to explain our chosen normalization conventions. The overall
normalization of each mode is not specified by the equations of motion
nor are the . Th normalization is determined by the Lagrangian in the
path integral formulation.

However we choose the normalization such that the commutation relation
$[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$

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

$G(x,x',t,t')\approx G_{0}(x-x',t-t')-\int dx''dt''G_{0}(x-x',t-t')VG_{0}(x-x',t-t')$

$G_{0}(x-x',t-t')$=$\frac{1}{2i}\int\frac{dkd\omega}{(2\pi)^{2}}e^{i\omega(t-t')-ik(x-x')}\frac{4\pi}{k(\omega+i\epsilon\text{sign}(\omega))-vk)}$
