Fastest most straightforward route. Then a bajillion appendices.

Get it all down, then edit for clarity in new file.

$S=\int\int dxdt(\partial_{t}\phi\partial_{x}\phi+v\partial_{x}\phi\partial_{x}\phi+\partial_{x}\phi u(x)P\partial_{x}\phi$

$4\pi$?

Chamon and Freed Convention:
$L=\frac{1}{4\pi}\partial_{x}\phi(\pm\partial_{t}-v\partial_{x})\phi$

A right mover has a constant value on the line $x=vt+b$. Hence it can be
written $\phi_{R}(b)$ or $\phi_{R}(x-vt)$. Consequently The right mover
obeys the differential equation
$(\partial_{t}+v\partial_{x})\phi_{R}=0$.

Using the expansion
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(k,\omega)e^{i\omega t-ikx}\frac{d\omega dk}{(2\pi)^{2}}$

The operator becomes
$\frac{-1}{4\pi}\partial_{x}(\pm\partial_{t}-v\partial_{x})=\frac{-1}{4\pi}(-ik)(\pm i\omega-vik)=\frac{1}{4\pi}(\mp k\omega+vk^{2})$

The gaussian identity
$\int_{-\infty}^{\infty}e^{-ax^{2}+bx}dx=\sqrt{\frac{\pi}{a}}e^{-b^{2}/4a}$

The Path Integral $\int D[\phi]e^{iS[\phi]}$comes out to

The time ordered green's function

$G_{0}$=$\frac{4\pi}{2i}\int\frac{dkd\omega}{(2\pi)^{2}}e^{i\omega t-ikx}\frac{1}{-k(\omega+i\epsilon\text{sign}(\omega))+vk^{2}}$

$G_{0}$=$\frac{4\pi}{2i}\int\frac{dkd\omega}{(2\pi)^{2}}e^{i\omega t-ikx}\frac{1}{-k(\omega+i\epsilon\text{sign}(\omega)-vk)}$

$\frac{}{}$

There's a a pole at $\omega=k-i\epsilon\text{sign}(\omega))$

We close the contour upwards when $t>0$ to make the $e^{i\omega t}$
converge. This catches when $\omega<0$ which adds as $i\epsilon$ to the
pole position putting it in the upper half plane. This means we only
catch this $t>0$ pole when $k<0$. The contour is counterclockwise giving
a factor of $2\pi i$. Also we flip $k\rightarrow-k$

$G_{0}$=$\frac{4\pi2\pi i}{2i}\int_{-\infty}^{0}\frac{dk}{(2\pi)^{2}}e^{i(-kv)t-ikx}\frac{1}{-k}=\frac{4\pi}{2}\int_{0}^{\infty}\frac{dk}{2\pi}e^{ik(tv+x)}\frac{1}{k}=\int_{0}^{\infty}dke^{ik(tv+x)}\frac{1}{k}$

The factor of $i$ comes from $iS$. The factor of $4\pi$ comes from the
normalization out front of the Lgrangian and the 1/2 comes from the
Gaussian identity $\int x^{2}e^{-ax^{2}}dx=\frac{\sqrt{\pi}}{2a^{3/2}}$
when applied to the path integral.

The $4\pi/2$ cancels with an extra factor of $2\pi$ in my foureir
convention and the $1/i$ gets killed by the contour integral residue
$i$.

Doing the k integral first leads to

$\int\frac{dk}{k}=\sum\frac{1}{n}$ since the conversion factor between k
and n ($\frac{2\pi}{L}$), cancels.

Putting into a finite box quantizes the momentum turning integrals over
k into sums over k. Von Delft
$\sum_{n>0}\frac{1}{n}e^{-q(ix+a)}\approx-\ln\frac{2\pi i}{L}(x-ia)$

Ultimately we get $<\phi(x,t)\phi(0,0)>=-\ln\frac{2\pi i}{L}(-t-x-ia)$

Using translation innvariance we have
$<\phi(x,t)\phi(x',t')>=-\ln\frac{-2\pi i}{L}(t-t'+x-x'+ia)$

Equal time commutation relations
$\phi(x,0)\phi(0,0)-\phi(0,0)\phi(x,0)=-\ln\frac{2\pi i}{L}(-x-ia)+\ln\frac{2\pi i}{L}(x-ia)$.

This is z-z\* so it is $2i\Im(z)$ and since we're talking about a
logaithm it is the phase of the agrument, while the $\ln|z|$ gets
cancelled off.

Checking consistency of Choice. Commutation Relations, Heisenberg
equations.

Creation operator for charge

$[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$

$[Q,e^{i\phi}]=e^{*}e^{i\phi}$

Density operator $\rho=\partial_{x}\phi$. Maybe with some e

$H=\partial_{x}\phi\partial_{x}\phi$

$\partial_{t}\partial_{x}\phi=i[H,\partial_{x}\phi]$

$P$ is the parity operator defined by $Pf(x)=f(-x)$. It is used because
$\partial_{x}\phi(-x)$ is slightly ambiguous notation that makes it
difficult to keep signs correctly. The correct prescription is the take
the derivative and then reverse the sign of the argument, since we want
to couple the the density $\partial_{x}\phi$ at the opposite side of the
contact.

$u(x)=u(-x)$

$[P,u]=0$

$\{P,\partial_{x}\}=0$

$P^{2}=I$

It is helpful to imagine the matrix form of this equation. P is a very
very large matrix with ones on the skew diagonal.

$$P=\left[\begin{array}{cccc}
... & 0 & 0 & 1\\
0 & 0 & 1 & 0\\
0 & 1 & 0 & 0\\
1 & 0 & 0 & ...
\end{array}\right]$$ /

Taking the variation of the action we have the equation

$$\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

With the Ansatz
$\phi(x,t)=\int_{-\infty}^{\infty}\phi(x,\omega)e^{i\omega t}\frac{d\omega}{2\pi}$

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

Without the edge bridging term the solution would be $Ae^{-ikx}+C$.

$$i\omega(-ik)Ae^{-ikx}+v(-ik)^{2}Ae^{-ikx}=0$$

$k=\frac{\omega}{v}$ The Constant solution remains valid, but is treated
seperately.

We'll treat the $u(x)=u$ constant case first and then match the interior
solution to the exterior solution. The equation remains more or less
translation invariant despite $x=0$ being singled out as a special
position, wo we still anticipate plane waves. However, if $e^{ikx}$
appears so must $e^{-ikx}$, since there is a term that turns
$x\rightarrow-x$. Hence, we can make the guess $Ae^{ikx}+Be^{-ikx}$.
With explicit substituion one gets

$$i\omega\partial_{x}Ae^{ikx}+i\omega\partial_{x}Be^{-ikx}+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}Ae^{ikx}+=0$$

$$i\omega ikAe^{ikx}+i\omega(-ik)Be^{-ikx}+v(ik)^{2}Ae^{ikx}+v(-ik)^{2}Be^{-ikx}+(-ik)uikAe^{-ikx}+(ik)u(-ik)Be^{ikx}=0$$

Collecting terms with the same exponentials we can write this in matrix
form

$\left[\begin{array}{cc}
-\omega k-vk^{2} & uk^{2}\\
uk^{2} & \omega k-vk^{2}
\end{array}\right]\left[\begin{array}{c}
A\\
B
\end{array}\right]=0$

Taking the determinant of this matrix

$$(-\omega k-vk^{2})(\omega k-vk^{2})-u^{2}k^{4}=0$$

Two solutions are taken care of by $k^{2}=0$. The others are

$$(-\omega-vk)(\omega-vk)-u^{2}k^{2}=0$$

$$(v^{2}-u^{2})k^{2}=\omega^{2}$$

In all that follows $k$ will denote the positive solution
$k=\frac{\omega}{\sqrt{v^{2}-u^{2}}}$, with the negative solution coming
with the explicit minus sign, such as with the $Be^{-ikx}$term above.

$$\frac{A}{B}=\frac{uk^{2}}{\omega k+vk^{2}}=\frac{vk^{2}-\omega k}{uk^{2}}$$

This can be saitsfied for example by

$A=u$

$B=\sqrt{v^{2}-u^{2}}+v$

or

$B=u$

$A=-\sqrt{v^{2}-u^{2}}+v$

These expressions are somewhat ugly though. Also the limit
$u\rightarrow0$ does not behave well. Actually, the first isn't so bad.
By taking the product of the two expressions we get

$$(\frac{A}{B})^{2}=\frac{1-\sqrt{v^{2}-u^{2}}}{1+\sqrt{v^{2}-u^{2}}}$$

We may determine the ratio $A/B$

One can also use $\phi=C\sin(kx)+D\cos(kx)$ if one prefers.

The nthe equation expands

$$i\omega\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$$

$$i\omega Ck\cos(kx)+-i\omega Dk\sin(kx)-k^{2}vC\sin(kx)-k^{2}vD\cos(kx)+-uk^{2}C\sin(kx)+uk^{2}D\cos(kx)=0$$

Collecting up the Sine and Cosine terms seperately gives the matrix
equation

$$\left[\begin{array}{cc}
-vk^{2}-uk^{2} & -i\omega k\\
i\omega k & -vk^{2}+uk^{2}
\end{array}\right]\left[\begin{array}{c}
C\\
D
\end{array}\right]=0$$

Taking the determinant

$$(-vk^{2}-uk^{2})(-vk^{2}+uk^{2})--i\omega ki\omega k=0$$

$$v^{2}k^{4}-u^{2}k^{4}-\omega^{2}k^{2}=0$$

We again get the relation

$$(v^{2}-u^{2})k^{2}=\omega^{2}$$

The ratio of C/D

$$\frac{C}{D}=\frac{i\omega k}{-vk^{2}-uk^{2}}=\frac{-vk^{2}+uk^{2}}{-i\omega k}$$

Substituting in the relation for $\omega=k\sqrt{v^{2}-u^{2}}$

$$\frac{C}{D}=-i\sqrt{\frac{v-u}{v+u}}$$

Giving the natural solution

$C=-i\sqrt{v-u}$

$D=\sqrt{v+u}$

We can reexpand in terms of eponential terms to get

$\phi=C\sin(kx)+D\cos(kx)=-i\sqrt{v-u}\sin(kx)+\sqrt{v+u}\cos(kx)=-i\sqrt{v-u}\frac{e^{ikx}-e^{-ikx}}{2i}+\sqrt{v+u}\frac{e^{-ikx}+e^{-ikx}}{2}=\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx}$

In order to determine the total normalization for the interior region,
we need to mathc to the exterior solution.

We've thrown away the constant solution. We should have two mathcing
conditions since the equation is second order.

The simplest choice of matching condition is $\phi(a^{-})=\phi(a^{+})$.
Why is this sufficient? Doesn't seem like it should be. Given ansatz the
deriavtives are then related by

$$-ike^{-ik(-a)}$$

$$-ike^{-ik(-a)}+ike^{ik(-a)}$$

The matching condition on the derivatives involves both $P\partial\phi$
and $\partial\phi$

Integrating around a small region the equations of motion

$\int_{-a-\epsilon}^{-a+\epsilon}\partial_{t}\partial_{x}\phi+v\partial_{x}\partial_{x}\phi+\partial_{x}u(x)P\partial_{x}\phi=0$

$\partial_{t}\phi+v\partial_{x}\phi+u(x)P\partial_{x}\phi]_{-a_{-}}^{-a_{+}}=0$

$(i\omega-i\omega)e^{-ik(-a)}=0=A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}(-ivk)e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}ivke^{ik(-a)})+A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}(-iuk)e^{ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}iuke^{-ik(-a)})$

NO

$\phi=A(-i\sqrt{v-u}\sin(k(-a))+\sqrt{v+u}\cos(k(-a)))$

$Avk(-i\sqrt{v-u}\cos(k(-a))-\sqrt{v+u}\sin(k(-a)))+Auk(-i\sqrt{v-u}\cos(k(a))-\sqrt{v+u}\sin(k(a)))$

$Avk(-i\sqrt{v-u}\cos(k(-a))-\sqrt{v+u}\sin(k(-a)))+Auk(-i\sqrt{v-u}\cos(k(-a))+\sqrt{v+u}\sin(k(-a)))$

$Ak(-i(v+u)\sqrt{v-u}\cos(k(-a))-(v-u)\sqrt{v+u}\sin(k(-a)))$

$Ak\sqrt{(v^{2}-u^{2}}(-i\sqrt{v+u}\cos(k(-a))-\sqrt{v-u}\sin(k(-a)))=-ik\sqrt{v^{2}-u^{2}}\phi=-i\omega\phi$

Hence
$(i\omega+v\partial_{x}+uP\partial_{x})\phi=(i\omega-i\omega)\phi=0$

We also can see that The constant solution and the other solution never
interplay. The overall $\partial_{x}$ that allows the constant solution
is removed by the matching condition. Does that make sense? This reduced
operator Must be some constant f you took the indefnite integralk
throughout the thing, which would come from the $i\omega$ term, but we
set the constant to 0.

$A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}(-ivk+iuk))e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}(ivk-iuk)e^{ik(-a)})$

$k=\frac{\omega}{\sqrt{v^{2}-u^{2}}}$

$A\frac{\omega}{\sqrt{v^{2}-u^{2}}}(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}(-i)e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}ie^{ik(-a)})$

If outside we normalize the function on the left side to $e^{-ikx}$
(Should it be starting on the left or the right? It should start on the
left since $e^{-ikx+i\omega t}$ is rightward moving wave)

$$e^{-ik_{0}(-a)}=A(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)})$$

Replace $k_{0}$ with $\omega$? They are identical

$$A=\frac{e^{-ik_{0}(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}$$

When $-a<x<a$

$$\psi(x)=\frac{e^{-ik_{0}(-a)}}{\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ik(-a)}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ik(-a)}}(\frac{\sqrt{v+u}+\sqrt{v-u}}{2}e^{-ikx}+\frac{\sqrt{v+u}-\sqrt{v-u}}{2}e^{ikx})$$

Defining $Z=\frac{\sqrt{v+u}-\sqrt{v-u}}{\sqrt{v+u}+\sqrt{v-u}}$

For small $u$, $Z\approx u$

$$\psi=\frac{e^{-ik_{0}(-a)}}{e^{-ik(-a)}+Ze^{ik(-a)}}(e^{-ikx}+Ze^{ikx})=\frac{e^{-i(k_{0}-k)a}}{1+Ze^{-2ika}}(e^{-ikx}+Ze^{ikx})$$

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

$$\sum_{q\text{even}}\sum_{r\text{ even\ensuremath{\ge}|q|}}(-Z)^{r}e^{2ikq}$$

$$\sum_{q\text{ even}}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikq}$$

Likewise for the odd summation

$$\sum_{q\text{ odd}}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikq}$$

Which can be combined into

$$\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikq}$$

$$\sum_{q\text{ }}\frac{(-Z)^{|q|}}{1-Z^{2}}e^{2ikq}(e^{ik(x-x')}+Z(e^{-ik(x+x')}+e^{ik(x+x')})+Z^{2}e^{-ik(x-x')})$$

Each inidividual $\frac{e^{i\omega(b)}}{\omega}$can be done in a
conventional way leading to a logarithmic term.

The $\omega$ spacing and Regularization procedure

$\int_{0}^{\infty}\frac{dp}{p}(e^{ipx}-1)e^{-ap}=\ln(\frac{a}{a-ix})$
(Shankar)

$<\phi(x)\phi(x')-\frac{1}{2}\phi(x)\phi(x)-\frac{1}{2}\phi(x')\phi(x')>$

or summation regularization (Von Delft)

We can perform the simple exponential integrals

We can expand the normalization factor into a geometric series. In

The first order response for arbitrary potential.

Analogy to Beam equation. A beam resists flexing because roughly
speaking. curvature tends to stretch the outer half of the crossection
and compress the inner half of the cross-section. You can get the
essence of a beam with two couple springs, an upper and a lower. The
difference in the compression between the two gives the curvature of the
beam. The compression (strain) is given by $\epsilon=\partial_{x}u$.
$\epsilon_{t}-\epsilon_{b}=\frac{a}{R}$ if the two are spearted by a
distance a.

$L_{0}(1+\epsilon_{t})=\theta(R+\frac{a}{2})$

$L_{0}(1+\epsilon_{b})=\theta(R-\frac{a}{2})$

Dividning the two removes $L_{0}$ and $\theta$. Taking
$\frac{a}{R},\epsilon_{t},\epsilon_{b}\ll1$.

Of course, the beam equation is not chiral. Its dynamical term is
$\partial_{t}^{2}$ and not $\partial_{tx}$. Can we split up the coupled
spring to ahieve this?

Vertex Function and order preserving identities. Exponential identities
and exmpales using x,p

$[A,B]=C$

$[C,A]=[C,B]=0$

$e^{-B}Ae^{B}=e^{-[B,]}A=A+C$

This is familiar as the relation sayign the momentum genreates
translations

$e^{A}e^{B}=e^{A+B}e^{C/2}$

$e^{A}e^{B}=e^{B}e^{A}e^{C}$

$p=\frac{\hbar}{i}\partial_{x}$

$[p,x]=\frac{\hbar}{i}$

Physical interpeation and bosonization. The physical inteetpreation of
stationary $(\omega,x)$ space depends of the conisderation of packets.
From this we derive concepts such as the group velocity annd we can
demonstrate that reflection and transmission coeffecients really reflect
their intutiive understanding when tranasformed over to the time
depdendant (x,t) domain. What does a group or cluster or packet around
ik do? $\partial_{x}\phi=\rho$. Current j = $\phi(x)+\phi(-x)?$ Packet
comes in, instantly influences sloshes in other side, dresses self with
image charge. Wave packet coherent state
$e^{i\int e^{-ak^{2}}\phi(k)}|0>$ or do I want
$\int dke^{-k^{2}}e^{-\phi(k)}|0>$

$\phi=\phi_{L}+\phi_{R}$

D'Alembert's principle

$P_{L}=\partial_{t}-c\partial_{x}$$P_{R}=\partial_{t}+c\partial_{x}$ May
want to actually check these conventions

$\partial_{x}^{-1}P_{L}\phi=\phi_{L}$

Proof of $[\phi(x),\phi(x')]=i\pi\text{sign}(x-x')$. Weighted Sturm
Liouville theory.
