WKB
---

Do path integral steepest descent. This gives you powers of $\hbar$

Or assume phase form in schordinger equation and solve equations order
by order in $\hbar$

Or assume discrete specturm is actually clumped contiunous.

WKB Green's function

$$\frac{1}{E-}$$

WKB is also why classical partition functions are same as quantum in
High Temp limit

Coherent States
===============

Overcomplete basis. We can inject into a higher dimensional orthogonal
basis with a rectangular matrix.

The ground state of a SHO is a nice lump state. It is a gaussian. In the
phase plane, its an elliptical lump. We can displace any state with a
combination of $e^{iap}$and $e^{ibx}$ two different unitary translation
operators. For Oscillator purposes, it is highly convenit to rexpress
these in terms of crration and annihilation operatores. Suitably
displaced, we then have lumps located at new positions of phase space.
We could think of these as ground states of displaced SHO.

The limit of a super loose harmonic oscillator is the free particle.
Displaced versions of this ground state are the ommentum eigenstates

Super tight oscillator are position eigenstates.

$$a^{\dagger}|n>=\sqrt{n+1}|n+1>$$

$$a|n>=\sqrt{n}|n-1>$$

This is eadsy to remeber if you know that the counting operator is
$N=a^{\dagger}a$

$$e^{\alpha a^{\dagger}}|0>=\sum_{n=0}\frac{\alpha^{n}}{n!}\sqrt{n!}|n>=\sum_{n=0}\frac{\alpha^{n}}{\sqrt{n!}}|n>$$

$0!=1$

This state is unnormalized

$$<\bar{\alpha}|\alpha>=(\sum_{n'}\frac{\bar{\alpha}^{n'}}{\sqrt{n'!}}<\bar{\alpha}|)\sum_{n=0}\frac{\alpha^{n}}{\sqrt{n!}}|n>=\sum\frac{\alpha^{n}\bar{\alpha}^{n}}{n!}=e^{\alpha\bar{\alpha}}$$

Similarly

$<\bar{\beta}|\alpha>=e^{\bar{\beta}\alpha}$

The resolution of the identity

$I=\int\frac{dzd\bar{z}}{2\pi i}e^{-z\bar{z}}|z><\bar{z}|$

Path Integral
-------------

Expand out
$e^{iHt}=(I+iH\frac{t}{N})I(I+iH\frac{t}{N})I(I+iH\frac{t}{N})$. Replace
those intermediate I with the coherent state expansion of the identity.

What are they?
--------------

Coherent States are the most classical purely quantum states. They can
be thought of as little balls in phase space of area about $\hbar$
located at position (x,p) which is often described by a complex
parameter $\alpha=x+ip$ . This is a conceptually irrelevant trick that
allows you to think of the phase plane as the complex plane. They result
from oscillators responding to classical external forces. They are also
eigenstates of annihilation operators (The annihilation operator being
the quantization of the $\alpha$ parameter).

MORE
----

Spatial Translation is provided by the operator
$e^{-i\frac{ap}{\hbar}}=1-a\partial_{x}+(-a\partial_{x})^{2}+yadayadayada$.
This generates the power series for $\psi(x-a)$. Likewise $e^{-ibx}$
will translate p by b. So if we apply these operators we can move any
state that is locaized at $(x_{0},p_{0})$. Now the order which we apply
them matters, since $[x,p]\ne0$. We could choose to translate p
first$e^{-iap}e^{-ibx}$, x first $e^{-ibx}e^{-iap}$, or go in the
staright line in phase space connecting the origin. This last case is
the $e^{-ibx+-iap}$. All of them are quite similar to one another, the
difference being basically a phase factor $e^{iab}$, which we can see
through Baker Hausdorff type matrix expoentnial Identities. This phase
factor is porbably an example of Berry's Phase. Actually, very much so,
since adiabtic magnetic field would do something quite similar. We can
translate the Simple harmonic oscillator hamiltonian in a loop in phase
space. The phase space area enclosed is the flux. We can rearrange that
exponent in terms of annihilation and creation operators to get
$e^{i(\alpha a+\alpha^{*}a^{\dagger})}$. This applied to the ground
state gives

You can think of $e^{ip^{2}t}$ very roughly as the operator translating
(one power of p) a distance $a=pt$. This is what we expect from free
particle motion.

Spin Coherent States
--------------------

Use maximal spin vector ans then rotate it around using two J
$e^{iJ_{z}\phi}e^{iJ_{x}\theta}|s>$ . The maximal z spin state is the
most pointy out of all of them since it has less space to wander in the
phi direction on the sphere. This will remain the maximal eigenstate for
some other axis. shockingly these sates form an overcomplete basis just
like how you'd guess

$$I=\int d\theta d\phi\sin(\theta)|\theta\phi><|$$

Using different paths along the sphere probably gets you an extra phase
factor propotional to the solid angle enclosed by the loop.
