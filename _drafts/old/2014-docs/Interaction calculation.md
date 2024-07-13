Current/Tunnelling Operator
---------------------------

(See Feldman 2003)

Mahan pg.

$\omega_{0}=eV$

$\psi_{L}\rightarrow\psi_{L}e^{-i\omega_{0}t}$

$\psi_{L}^{\dagger}\rightarrow\psi_{L}^{\dagger}e^{-i\omega_{0}t}$

Current is the change of number from one side to anothe

$I=\frac{i}{\hbar}[H,N_{L}]=\frac{-i}{\hbar}[H,N_{R}]$

Feldman eq 4

$I=-i\psi_{L}^{\dagger}(0)\psi_{R}(0)e^{i\omega_{0}t}+i\psi_{R}^{\dagger}(0)\psi_{L}(0)e^{-i\omega_{0}t}$

Free Boson Field
----------------

Feldman eq 5

$L=\int dxdt\frac{1}{8\pi}[(\partial_{t}\Phi)^{2}-(\partial_{x}\Phi)^{2}]+I$

Free Boson field operator obeys. (Working in interaction picture. The
tunnelling and and inhomogenous electrons interaction perturbations not
included in operator evolution.

$(\partial_{t}^{2}-\partial_{x}^{2})\Phi=0$

implies

$\Phi(x,t)=\phi_{L}(x-t)+\phi_{R}(x+t)$

$\Phi=\phi_{R}+\phi_{L}$

$\phi_{R}=\chi_{R}+\chi_{R}^{\dagger}+N_{R}x$ guess

, Bosonization
--------------

$\hat{\rho}=\frac{e\sqrt{g}}{2\pi}\partial_{x}\Phi$

$\psi_{R/L}=e^{\pm i\sqrt{g}\phi_{R/L}}$(Wen Chamon Freed under eq 8)

Correlation Functions
---------------------

$<T\phi(x_{1},t_{1})\phi(x_{2,}t_{2})>=-2\ln(\delta+i|t_{1}-t_{2}|)$ Wen
freed eqation 21

Senechal 62 $G=-\frac{1}{4\pi}\ln(x^{2}+v^{2}\tau^{2})$

$\tau=it+\delta$. Discrepancy of $4\pi$. Wen seems to have field scaled
differently by a factor of $\sqrt{4\pi}$ then everybody else.
Commutation relation below Wen 11
$[\phi,\partial_{x}\phi]=4\pi i\delta(x-y)$, Or for example, check out
Senechal 75

(Rao also has an extra i in his deifnition, leading to a positive sign
outside his green's function)

Long story short, take Wen result, bring 2 inside and add $x^{2}$

$<T\phi(x_{1},t_{1})\phi(x_{2,}t_{2})>=-\ln((\delta+i|t_{1}-t_{2}|)^{2}+(x_{1}-x_{2})^{2})$

Across gate interaction
-----------------------

Point interaction

$V(x,x')=u\delta(x-x')$

Mirror about x=0 point interaction (across gate interaction)

$V(x,x')=u\delta(x+x')$

$H=\int\rho(x)\rho(x')V(x,x')dxdx'$

$H=u\int_{-\infty}^{\infty}dx\rho(x)\rho(-x)=2u\int_{-\infty}^{0}dx\rho(x)\rho(-x)$

With $\partial_{x}\Phi\approx\rho$

Leads to Bosonized Lagrangian Term (Feldman 2003 16)

$L=\frac{-1}{8\pi}\int dt\int_{-\infty}^{0}dxU\partial_{x}\phi(x)\partial_{x}\phi(-x)$

$V(x,x')=\begin{cases}
u_{1}\delta(x+x') & |x|>L\\
u_{2}\delta(x+x') & |x|\le L
\end{cases}$

$L=\frac{-1}{8\pi}\int dt\int_{-\infty}^{0}dx\frac{U_{1}+U_{2}}{2}\partial_{x}\phi(x)\partial_{x}\phi(-x)+\frac{-1}{8\pi}\int dt\int_{-\infty}^{-L}dx\frac{U_{1}-U_{2}}{2}\partial_{x}\phi(x)\partial_{x}\phi(-x)+\frac{-1}{8\pi}\int dt\int_{-L}^{0}dx\frac{-U_{1}+U_{2}}{2}\partial_{x}\phi(x)\partial_{x}\phi(-x)$

We will assume $U_{1}=-U_{2}=U$

$L=\frac{-1}{8\pi}\int dt\int_{-\infty}^{-L}dxU\partial_{x}\phi(x)\partial_{x}\phi(-x)+\frac{1}{8\pi}\int dt\int_{-L}^{0}dxU\partial_{x}\phi(x)\partial_{x}\phi(-x)$

$L=\frac{-U}{8\pi}\int dt\int_{-\infty}^{0}dx\text{sign(x+L)}\partial_{x}\phi(x)\partial_{x}\phi(-x))$

Current Calculation
-------------------

$<0|S^{\dagger}(t,-\infty)IS(t,-\infty)|0>$

$H_{int}(t)=e^{i\sqrt{g}\Phi(t,x=0)}e^{i\omega_{0}t}+e^{-i\sqrt{g}\Phi(t,x=0)}e^{-i\omega_{0}t}+\int_{-\infty}^{-L}dxU\partial_{x}\phi(t,x)\partial_{x}\phi(t,-x)-\int dt\int_{-L}^{0}dxU\partial_{x}\phi(t,x)\partial_{x}\phi(t,-x)$

($\frac{1}{8\pi}?)$

$S=Texp[-i\int H_{int}(t)dt]$

$S\approx1-i$
