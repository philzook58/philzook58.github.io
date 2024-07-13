The Underived Rules and Scattering
==================================

Its easiest to understand the Feynman rules without worrying where they
came from first. They're damn simple, but figuring out how to get at
them from first pricniples can be a nightmare.

Relativistic Normalization
--------------------------

Let's just list all the relativstic combos first of all. There are
secret ones that do not appear relatvistic on first glance, but are. The
index notation is not the final word. They should all just be memorized
by wrote. Try writing them each out ten times. Do it. They need to come
instantly to the fingertips. After that, never write down a $d^{3}p$ or
delta of creation operator without its friednly companions or you will
get so confused.

What does it mean to be invariant? Replace all orignal quantities with
their expression in terms of the boosted system.

$$E^{2}-p^{2}$$

$$(\gamma(E'-vp'))^{2}-(\gamma(p'-vE'))^{2}$$

Rearrange to get

$$E'^{2}-p'^{2}$$

The form must remain the same. Geometrically this can get very
confusing, for example in the geometrical location of the integral.

$d^{4}p$ is invariant because the Jacobian of a lorentz transfromation
is 1. Think about why $d^{3}x$ is rotationally invariant. Same reason

$\omega_{k}$ is just shorthand for $\sqrt{\vec{p}^{2}-m^{2}}$. It is not
a free variable in any of these. It's a function of the p 3-vector. THIS
INCLUDES WHEN YOU NEED IT IN YOUR LORENTZ TRANSFORMATION. This is akin
to writing $x'=x\cos(\theta)-\sin(\theta)\sqrt{1-x^{2}}$ for rotated
coordinates on a unit circle. $P_{0}$might be a independant variable in
situations where you are integrating over $d^{4}p$.

The invariant momentum measure

$$\frac{d^{3}p}{(2\pi)^{3}2\omega_{p}}$$

The invariant $\delta$. This one is subtle to derive, straightforward
but opaque to verify.

$$(2\pi)^{3}2\omega_{k}\delta^{3}(k-k')$$

The annihilation and creation are basically the square roots of delta
functions so

$$(2\pi)^{3/2}\sqrt{2\omega_{k}}a_{k}^{\dagger}$$

The scalar field itself is also invariant

$$\Phi$$

Its conjugate momentum $\Pi$is not however. It transforms like a time
component of a 4-vector.

Obviously, anything that obeys standard index contraction rules is also
an invariant.

Remember that $\Phi$basically looks like a harmonic oscillator
decomposition, so it is a sum of $a$ and $a^{\dagger}$. Most of the
factors can be gotten by using invariant objects throughout. This also
happens to match the way the $\omega$ appears in the harmonic
oscillator, but that is pretty hard to get right too. Remembering the
signs in the exponents can be done by sandwiching it between a vacuum
and a p state. That should match how $<x|p>$appears in regular quantum
mechanics.

$$\Phi(x)=\int\frac{d^{3}p}{(2\pi)^{3}2\omega_{k}}(\sqrt{2\omega_{k}}a_{k}e^{ipx}+\sqrt{2\omega_{k}}a_{k}^{\dagger}e^{-ipx})$$

There is this $\overleftrightarrow{\partial_{0}}$ which is a tricky way
of using Green's identity to make invariant 3-space integrals for things
that satisfy wave equations. I think is how you can make the Fourier
transform covariant. Putting $\omega_{k}$in the dominator makes the
3-momentum covairant, so similarly $\partial_{0}$makes space-volume
integrals covariant. We use a boundary value problem decomposition of
the thing. Sinilar to the Legendre series.

$$\phi(x,t)=\int d^{4}x(\phi\square^{2}G-G\square^{2}\phi)$$

Is obviously invariant. But by Green's theorem we can connect it to a
surface integral on a space-like wedge. The equivlanence of these
Integrals is what is important and the disinterest in the exact volume
of integration

$$0=\int_{\Gamma}d^{4}x(\phi^{\dagger}\square^{2}\phi-\phi\square^{2}\phi^{\dagger})$$

$$=\int_{\partial\Gamma}d^{3}x(\phi^{\dagger}\frac{\partial}{\partial n}\phi-\phi\frac{\partial}{\partial n}\phi^{\dagger})$$

I'm not sure how to write this covariantly.

This is a demonstration of the conservedness of the 4-current. What is
the conection between Green's theorem and Noether's?

First to Second - A Nontrivial Triviality
=========================================

If you use the singly occupied states of second quatization (i.e. you
restrict yourself to working in only that subspace), you get a replica
of single particle quantum mechanics. Like wise if you restrict yourself
to the vairous N particle subspaces, you get a replica of first
Quantized N particle dynamics

There is a classical analog to second quantization. Going from a
particle representation to a densty representation. If we really twist
our arms and consider the variables

$$a=\sqrt{\frac{J}{\hbar}}e^{i\theta}$$

which are the classical analogs of the annihilation and creation
operators. We can deconstructed a field into its normal modes, or take
the "square root" of proability and construct a distribution with the
weighting factor

$e^{-J}$.

2x2, and 4x4 Interacting, a la QFT
==================================

Do feynman diagrams and perturbation theory, and green's functions,
Interaction picture, and Schwinger, $i\epsilon$, S-Matrix, Dyson, Wick,
Generating function, and functional integral for spin 1/2 and
interacting spin 1/2. There aren't really any interesting perturbations.
Basically all the advanced QM concepts minus field operators and minus
relativtiy. Probably no reasonable renormalization analog. Goldstone
modes maybe? ehhhhhh.

Left Right Sides of a box. Use pyramid FEM functions. Or Left Right
Center so we can have tunnelling and things?

$$H_{0}=B\sigma_{z}=\left[\begin{array}{cc}
B & 0\\
0 & -B
\end{array}\right]$$

$$H'=C\sigma_{x}=\left[\begin{array}{cc}
0 & C\\
C & 0
\end{array}\right]$$

$$H_{I}(t)=e^{iH_{0}t}H'e^{-iH_{0}t}$$

$$i\hbar\frac{\partial}{\partial t}|\Psi_{I}>=H_{I}(t)|\Psi_{I}>$$

$$|\Psi_{I}(t)>=|\Psi(0)>+(-i)\int_{0}^{t}dt'H_{I}(t')|\Psi_{I}(t')>$$

We can iterate this equation

$$|\Psi_{I,n+1}(t)>=|\Psi_{0}(0)>+(-i)\int_{0}^{t}dt'H_{I}(t')|\Psi_{I,n}(t')>$$

$$|\Psi_{I}(t)>=|\Psi(0)>+(-i)\int_{0}^{t}dt'H_{I}(t')|\Psi_{I}(0)>+(-i)^{2}\int_{0}^{t}dt'H_{I}(t')\int_{0}^{t'}dt''H_{I}(t'')|\Psi_{I}(t'')>$$

$$S=1+(-i)\int_{-T}^{T}dt'H_{I}(t')+(-i)^{2}\int_{-T}^{T}dt'H_{I}(t')\int_{-T}^{t'}dt''H_{I}(t'')+\ldots$$

Concretely

$$\left[\begin{array}{c}
a(t)\\
b(t)
\end{array}\right]=$$

$$|0>=\left[\begin{array}{c}
1\\
0
\end{array}\right]$$

$$|1>=\left[\begin{array}{c}
0\\
1
\end{array}\right]$$

$$a^{\dagger}=\left[\begin{array}{cc}
0 & 0\\
1 & 0
\end{array}\right]$$

$$a=\left[\begin{array}{cc}
0 & 1\\
0 & 0
\end{array}\right]$$

$$a_{I}(t)=e^{iH_{0}t}ae^{-iH_{0}t}=a$$

$$<out|S|in>=<0|S|0>$$

$$$$

Second Quantization
===================

$$\Diagram{fA}$$

Put it on a Lattice
-------------------

Sound, baby. That is something I can get behind. It smacks of being
perhaps not total bullshit, something that is can rarely found in any
physics created after 1895. A periodic crystal with a stable equiblirum
position for its consitutent atoms is a well accepted fact of nature.
Stretch one of the atoms out of its quilbirium slightly and the rest of
the crystal will get dragged towards it.

$$x_{n}=na+\eta_{n}$$

There is a small displacement from its equilbirium position $\eta_{n}$

$$H=\sum_{n=0}^{N-1}\frac{p_{n}^{2}}{2m}+U(x_{n}-x_{n+1})$$
$$U(x_{n}-x_{n+1})=U(a)+(\eta_{n}-\eta_{n+1})U'(a)+\frac{1}{2}(\eta_{n}-\eta_{n+1})^{2}U''(a)+\ldots$$

$$U'(a)=0$$

$$U(a)=\text{Worthless}$$

Periodic Boundary Conditions don't suck. Let's use them.

$$x_{0}=x_{N}$$

$$H\approx\sum_{n=0}^{N-1}\frac{p_{n}^{2}}{2m}+\frac{1}{2}(\eta_{n}-\eta_{n+1})^{2}U''(a)$$

Mazel Tov, your problem is now tractable.

If we could make a change of variables so that

$$H=\sum_{n=0}^{N-1}H_{n}(a_{n},b_{n})$$

Boy would that make us happy. The equation of motions for such a system
are

$$\frac{\partial H}{\partial a_{n}}=\frac{\partial H_{n}}{\partial a_{n}}=\dot{b_{n}}$$

$$\frac{\partial H}{\partial b_{n}}=\frac{\partial H_{n}}{\partial b_{n}}=-\dot{a_{n}}$$

This is a collection of uncoupled one variable problems, which we can
solve with more familiar techniques. Uncoupled equations are the
American Dream. A classic example of such a transformation is the center
of mass transformation

$$H=\frac{p_{1}^{2}}{2m_{1}}+\frac{p_{2}^{2}}{2m_{2}}+V(r_{1}-r_{2})$$

$$M=m_{1}+m_{2}$$

$$R=\frac{m_{1}r_{1}+m_{2}r_{2}}{M}$$

$$r=r_{2}-r_{1}$$

$$P=(\frac{p_{1}}{m_{1}}+\frac{p_{1}}{m_{2}})M$$

$$\frac{1}{\mu}=\frac{1}{m_{1}}+\frac{1}{m_{2}}$$

$$\mu=\frac{m_{1}m_{2}}{M}$$

$$p=(\frac{p_{2}}{m_{2}}-\frac{p_{1}}{m_{1}})\mu=\frac{m_{1}p_{2}-m_{2}p_{1}}{M}$$

$$H=\frac{P^{2}}{2M}+\frac{p^{2}}{2\mu}+V(r)$$

There is a trick to solve problems of this kind. How the hell do you
motivate it though. The equations of motion

$$\dot{p}_{n}=-\frac{\partial H}{\partial x_{n}}=U''(a)(\eta_{n-1}-2\eta_{n}+\eta_{n+1})$$

$$\dot{x}_{n}=\frac{\partial H}{\partial p_{n}}=\frac{p_{n}}{m}$$

We worked

In the end of the day, just about everybody ansatzes the ever loving
bejeezus out the problem. That's how we know we want to work with the
discrete fourier transform.

$$P_{q}=\frac{1}{\sqrt{N}}\sum_{n=0}^{N-1}e^{iqn}p_{n}$$

$$U_{q}=\frac{1}{\sqrt{N}}\sum_{n=0}^{N-1}e^{-iqn}\eta_{n}$$

$$q=\frac{2\pi m}{N}=\frac{2\pi ma}{Na}=\frac{2\pi x_{n}}{L},m=0,1,\ldots,N-2,N-1$$

These need to be canonical variables, meaning the Hamilton equations of
motion should still work or the quantum equivalent, we want the
commutation relations to still hold.

$$[\eta_{m},p_{n}]=i\hbar\delta_{nm}\rightarrow[U_{q,}P_{r}]=i\hbar\delta_{qr}$$

$$[p_{m},p_{n}]=0\rightarrow[P_{q,}P_{r}]=0$$

$$[\eta_{m},\eta_{n}]=0\rightarrow[U_{q,}U_{r}]=0$$

The second two are pretty obviously true, I believe. The expressions for
$U_{q}$and $P_{q}$contain only $\eta_{n}$and $p_{n}$respectively, which
all commute with each other, so the new expression commute as well. The
first is a little less obvious, but not hard.

$$[U_{q,}P_{r}]=\frac{1}{N}[\sum_{n=0}^{N-1}e^{-iqn}\eta_{n},\sum_{m=0}^{N-1}e^{irm}p_{m}]=\frac{1}{N}\sum_{n=0}^{N-1}\sum_{m=0}^{N-1}e^{irm-iqn}[\eta_{n},p_{m}]=\frac{1}{N}\sum_{n=0}^{N-1}\sum_{m=0}^{N-1}e^{irm-iqn}i\hbar\delta_{mn}=\frac{1}{N}\sum_{n=0}^{N-1}e^{i(r-q)n}i\hbar=\frac{N}{N}\delta_{rq}i\hbar=i\hbar\delta_{rq}$$

In words, plug in our definitions, distirbute those sums out of the
commutator, use the commutation relation for the origional variables,
destroy one sum with the kronecker delta, and finally use the identity

$$\sum_{n=0}^{N-1}e^{i(r-q)n}=\delta_{rq}N$$

Looking at each of this sum's terms in the complex plane, each term is a
vertex of a regular polygon circumscribed by the unit circle. By
symmettry, it is pretty clear this must add up to zero unless $r=q$,
when each term is 1 and it adds constructively N times, giving N.

The Hamiltonian is diagonalized to

$$H=$$

NO DON'T PUT IT ON A LATTICE. LATTICES ARE HARD AND GAY

Classical string of length L

$$\mathcal{L=}(\partial_{t}\phi)^{2}-(\nabla\phi)^{2}$$

Assume seperable solution

$$\phi=\sum_{n}\sin(\frac{n\pi}{L}x)q_{n}(t)$$

$$H=\int dx(\partial_{t}\phi)^{2}+(\nabla\phi)^{2}=\sum\sin(\frac{n\pi}{L}x)\sin(\frac{m\pi}{L}x)\dot{q_{n}}(t)\dot{q_{m}}(t)+(\frac{n\pi}{L})^{2}\cos^{2}(\frac{n\pi}{L}x)q_{n}(t)q_{m}(t)$$

We got that lovely orthoghonality property to give us a $\delta_{mn}$

$$H=\sum\dot{q_{n}}(t)^{2}+q_{n}(t)^{2}$$

Good 2 go.

This is how you count
---------------------

Here's a rule of thumb: Anytime you are doing quantum mechanics, and
something in your system seems like it ought to be counted, find some
annihilation and creation operators.

$$\hat{a}_{+}|m>=c_{+}(m)|m+1>$$

$$\hat{a}_{-}|m>=c_{-}(m)|m-1>$$

$$\hat{a}_{+}=\left(\begin{array}{ccccccc}
0 & 0 & 0 & 0 & \cdots & 0 & 0\\
c_{+}(1) & 0 & 0 & 0 & \cdots & 0 & 0\\
0 & c_{+}(2) & 0 & 0 & \cdots & 0 & 0\\
0 & 0 & c_{+}(3) & 0 & \cdots & 0 & 0\\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots\\
0 & 0 & 0 & 0 & \cdots & c_{+}(N) & 0
\end{array}\right)$$

$$\hat{a}_{+}=\left(\begin{array}{ccccccc}
0 & 0 & 0 & 0 & \cdots & 0 & 0\\
c_{+}(1) & 0 & 0 & 0 & \cdots & 0 & 0\\
0 & c_{+}(2) & 0 & 0 & \cdots & 0 & 0\\
0 & 0 & c_{+}(3) & 0 & \cdots & 0 & 0\\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots\\
0 & 0 & 0 & 0 & \cdots & c_{+}(N) & 0
\end{array}\right)$$

Why the heck not. That will define our raising and lowering operators.

The combo of the two will give us back our orignal vector times some
constant

$$\hat{N}_{\pm}|m>=\hat{a}_{+}\hat{a}_{-}|m>=c_{+}(m-1)c_{-}(m)|m>$$

$$\hat{N}_{\mp}|m>=\hat{a}_{-}\hat{a}_{+}|m>=c_{-}(m+1)c_{+}(m)|m>$$

$$\hat{N}_{\pm}-\hat{N}_{\mp}=[\hat{a}_{+},\hat{a}_{-}]=c_{+}(\hat{m}-1)c_{-}(\hat{m})-c_{-}(\hat{m}+1)c_{+}(\hat{m})$$

If we want $\hat{N}$ to be hermitian, we'll need

$$\hat{N}_{\mp}^{\dagger}=\hat{a}_{+}^{\dagger}\hat{a}_{-}^{\dagger}$$

$$\hat{N}_{\pm}^{\dagger}=\hat{a}_{-}^{\dagger}\hat{a}_{+}^{\dagger}$$

$$a_{+}^{\dagger}=a_{-}$$

Okay, so these counting operators are pretty darn general. The trick is
to figure our their relation to the other physical things in the theory.
Here's some examples of how that is done.

### Angular Momentum

Angular momentum comes in chunks of $\hbar$. That one got guessed pretty
early on by Bohr, way before we had any of this cockamamie Hilbert Space
and probability ampliutude nonsense. Thus, we ought to be able to count
the chunks of angular mementum we have.

We have the commutations relations

$$[J_{i},J_{j}]=i\hbar\epsilon_{ijk}J_{k}$$

Focusing on $J_{z}$, we fortuitously pick out the combination

$$J_{\pm}=J_{x}\pm iJ_{y}$$

Defining some eigenvector of $J_{z}$

$$J_{z}|m>=m\hbar|m>$$

We take a peak at what the eigenvector $J_{\pm}|m>$looks like.

$$J_{z}J_{\pm}|m>=J_{z}(J_{x}\pm iJ_{y})|m>=((J_{x}J_{z}-i\hbar J_{y})\pm i(J_{y}J_{z}-i\hbar J_{x}))|m>=J_{\pm}J_{z}\pm\hbar J_{\pm}|m>=(m+1)\hbar J_{\pm}|m>$$

Hey! We got a higher or lower eigenvalued eigenvector by using
$J_{\pm}$.! Sweet.

### Harmonic Oscillator

The Harmonic Oscillator has energy that comes in chunks of
$\hbar\omega$. This is in essence the very first suspicion of quantum
theory we had, guessed at by Planck and Einstein. We ought to be able to
count the chunks of energy we have.

In order to end the ladder we pick a fortuitous choice of coefficents

$$c_{-}(0)=0$$

### Periodic Free Particle

$$\Psi(x)=\Psi(x+L)$$

We can counts chunks of momentum, which comes in chunks of
$\frac{2\pi\hbar}{L}$

$$p=\frac{n2\pi\hbar}{L},n=\pm0,1,2,3,\ldots$$

$$\Psi_{n}(x)=\frac{1}{\sqrt{L}}e^{\frac{i2\pi nx}{L}},n=\pm0,1,2,3,\ldots$$

$$\hat{p}\Psi_{n}(x)=\frac{\hbar}{i}\frac{d}{dx}\Psi_{n}(x)=\frac{2\pi n\hbar}{L}\Psi_{n}(x)$$

$$\hat{a}_{+}=e^{\frac{i2\pi x}{L}}$$

$$c_{+}=1$$

Quantum Fourier Components
--------------------------

Your brain has been touched by the finger of god
------------------------------------------------

You are a genius. You saw quantum theory and thought, "There ought to be
a version of this for classically continuous systems." You looked at the
math and just cooked up a generalization to fields, knowing that you
weren't just performing mathemtical masturbation.

Miscellaneous Pains in the Ass
==============================

normal ordering. Even if it is proof the devil exists, you should know
the nature of the devil to better defend against him.

Relativistic Scalar Field
-------------------------

normalization, all those dumb conventional functions

The Dirac Delta function nmoralization

Suppose we have motion cnstrained to a circle, like a rock being twirled
on a string.

$$p_{x}^{2}+p_{y}^{2}=(mv)^{2}=\frac{L^{2}}{R^{2}}$$

$p_{x}$ and $p_{y}$are not independant in this case. $dp_{x}dp_{y}$is a
nice roationally invariant measure.

$$\int\delta(\frac{L^{2}}{R^{2}}-p_{x}^{2}-p_{y}^{2})dp_{x}dp_{y}=\frac{dp_{x}}{2\sqrt{\frac{L^{2}}{R^{2}}-p_{x}^{2}}}$$

Okay. Maybe just going for the circle would be better

$$y(x)=\sqrt{R^{2}-x^{2}}$$

$$y'(x)=\frac{-x}{\sqrt{R^{2}-x^{2}}}$$

The arclength is given by

$$dx\sqrt{1-y'(x)^{2}}=dx\sqrt{1-\frac{x^{2}}{R^{2}-x^{2}}}=dx\frac{\sqrt{R^{2}-2x^{2}}}{\sqrt{R^{2}-x^{2}}}$$

Translations, Boosts, and such
------------------------------

$$R_{x}(\theta)=\left(\begin{array}{cccc}
1 & 0 & 0 & 0\\
0 & 1 & 0 & 0\\
0 & 0 & \cos(\theta) & \sin(\theta)\\
0 & 0 & -\sin(\theta) & \cos(\theta)
\end{array}\right)$$

$$R_{z}(\theta)=\left(\begin{array}{cccc}
1 & 0 & 0 & 0\\
0 & \cos(\theta) & \sin(\theta) & 0\\
0 & -\sin(\theta) & \cos(\theta) & 0\\
0 & 0 & 0 & 1
\end{array}\right)$$

$$R_{y}(\theta)=\left(\begin{array}{cccc}
1 & 0 & 0 & 0\\
0 & \cos(\theta) & 0 & -\sin(\theta)\\
0 & 0 & 1 & 0\\
0 & \sin(\theta) & 0 & \cos(\theta)
\end{array}\right)$$

$$B_{t}(\theta)=\left(\begin{array}{cccc}
\cosh(\theta) & -\sinh(\theta) & 0 & 0\\
-\sinh(\theta) & \cosh(\theta) & 0 & 0\\
0 & 0 & 1 & 0\\
0 & 0 & 0 & 1
\end{array}\right)=\left(\begin{array}{cccc}
\gamma & -\beta\gamma & 0 & 0\\
-\beta/\gamma & \gamma & 0 & 0\\
0 & 0 & 1 & 0\\
0 & 0 & 0 & 1
\end{array}\right)$$

All of these matrices are identity matrix when $\theta=0$. We can take a
taylor series of these matrices, because BY GOD WE CAN TAKE A TAYLOR
SERIES OF ANYTHING, AND I WILL KILL THE MAN WHO CLAIMS OTHERWISE. NOT IN
MY HOUSE!

$$dR=R^{-1}(\theta)R(\theta+\epsilon)$$

If we smack a whole bunch of these together, we can get the group
equivalent of a telescoping series (which is the foundation of the
Fundamental Theorem of Calculus)

$$R^{-1}(\theta)R(\theta+\epsilon)R^{-1}(\theta+\epsilon)R(\theta+2\epsilon)R^{-1}(\theta+2\epsilon)R(\theta+3\epsilon)=R^{-1}(\theta)R(\theta+3\epsilon)$$

Set the orignal $\theta$to 0 and then you can pound the quantity $dR$ on
itself over and over again until you've got the rotation you wanted.

What's really surprising is that this captures the whole structure of
all possible rotations.

Noether's Theorem
-----------------

Feynman Path Integral
---------------------

Schwinger Action Principle
--------------------------

Classical version?

The Propagator

$$i\hbar\frac{d}{dt}\Psi=H\Psi$$

In the words of the allmighty Bob, let's do the dumbest thing you can
do.

$$\frac{d}{dt}\Psi\approx\frac{\Psi(t+dt)-\Psi(t)}{dt}$$

Use this to Rearrange your Schroedginer equation a tad.

$$\Psi(t+dt)\approx(1-\frac{iH}{\hbar}dt)\Psi(t)$$

So in order to move the state ahead by an amount of time $dt$ you slap
some operator on it. Since we approximated our derivative this is only
close to being right, but as $dt\rightarrow0$ it becomes more and more
accurate. We can keep going too

$$\Psi(t+2dt)\approx(1-\frac{iH}{\hbar}dt)\Psi(t+dt)\approx(1-\frac{iH}{\hbar}dt)(1-\frac{iH}{\hbar}dt)\Psi(t)$$

We can keep going and going until we have a whole crap ton of these
operators being applied

$$\Psi(t+T)\approx(1-\frac{iH}{\hbar}dt)(1-\frac{iH}{\hbar}dt)(1-\frac{iH}{\hbar}dt)\ldots\Psi(t)=(1-\frac{iH}{\hbar}dt)^{\frac{T}{dt}}\Psi(t)$$

Now, let's expand that sucker out using the binomial theorem.

$$(1+x)^{n}\approx1+\frac{n}{1!}x+\frac{n(n-1)}{2!}x^{2}+\frac{n(n-1)(n-2)}{3!}x^{3}+\ldots$$

$$(1-\frac{iH}{\hbar}dt)^{\frac{T}{dt}}\approx1+\frac{T}{dt}(\frac{-iHdt}{\hbar})+\frac{1}{2!}(\frac{T}{dt})(\frac{T}{dt}-1)(\frac{-iHdt}{\hbar})^{2}+\ldots$$

Now we want to keep T to be some regular old number, like 3, but let
$dt\rightarrow0$. In that limit, only the terms with no $dt$ in the
numerator survive (by the good grace of the Lord there are no $dt$ in
the downstairs, which would explode in our face like a hot tub of
grease).

$$\lim_{dt\rightarrow0}(1-\frac{iH}{\hbar}dt)^{\frac{T}{dt}}=1+\frac{-iHT}{\hbar}+\frac{1}{2!}(\frac{-iHT}{\hbar})^{2}+\ldots\equiv e^{\frac{-iHT}{\hbar}}$$

We notice that this series looks exactly like the Taylor series for
$e^{x}$, and define the exponential of an operator as this series for
notational convenience.

Now, we've been a little loosy goosy by saying that H has no time
dependance. This is indeed the case for most elementary problems you'll
get out of your textbook. Those problems are in those textbooks because
they're easy, not because they're all there is. Everybody is confused as
it is without the extra details.

When H has time dependance, that argument no longer works. We treated H
just like a regular old number because there was nothing around that it
wouldn't commute with. H may now not commute with H at other times. For
example

$$H(t)=\frac{p^{2}}{2m}+g\sin(t)x$$

$$H(0)=\frac{p^{2}}{2m}$$

$$H(\frac{\pi}{2})=\frac{p^{2}}{2m}+gx$$

$$[H(0),H(\frac{\pi}{2})]=[\frac{p^{2}}{2m},gx]\ne0$$

We can't be galled by a little problem like this! We're physicists
goddamnit, with big burly chests and little bird-like waists!

Schroedinger, Heisenberg, and Interaction Pictures
--------------------------------------------------

Dyson's Formula
---------------

$$U_{I}(t,-\infty)=1-i\int_{-\infty}^{t}H(t')dt'+\frac{(-i)^{2}}{2!}\int_{-\infty}^{t}\int_{-\infty}^{t}T(H(t')H(t''))dt'dt''+\ldots$$

Let's see what purtubation theory tells us about

$$H=\frac{p^{2}}{2m}+\frac{1}{2}m\omega^{2}x^{2}-F(t)x$$

This is the hamiltonian of a simple harmonic oscillator with a kicking
function $F(t)$, which applies an external force to the oscillator

$$\dot{p}=-\frac{\partial H}{\partial x}=-m\omega^{2}x+F(t)$$

$$\dot{x=\frac{\partial H}{\partial p}=\frac{p}{m}}$$

The classical solution to this problem is more easily epxressed in these
variables

$$a=\sqrt{\frac{m\omega}{2}}(\omega x+\frac{i}{m}p)$$

$$a*=\sqrt{\frac{m\omega}{2}}(\omega x-\frac{i}{m}p)$$

$$H=a*a+J(t)(a*+a)$$

$$J(t)=F(t)\sqrt{\frac{2}{m\omega^{3}}}$$

$$U_{I}(t,-\infty)=T(e^{-i\int_{-\infty}^{t}H_{I}(t)dt})$$

Let's pick a simple $J(t)$

$$J(t)=J\delta(t)$$

Now the series compresses very easily. Every integral gets killed by the
delta function and all the exponentials get replaced by $1$ since they
are evaluated at $t=0$. The time ordering can be ignored because all
operators will be evaluated at $t=0$

$$\int_{-\infty}^{t}J\delta(t')dt'=J\theta(t)=\begin{cases}
1 & t>0\\
0 & t<0
\end{cases}$$

$$U_{I}=1-i(a^{\dagger}+a)J\theta(t)+\frac{(-i)^{2}}{2!}((a^{\dagger}+a)(a^{\dagger}+a))(J\theta(t))^{2}+\ldots=e^{-iJ\theta(t)(a^{\dagger}+a)}$$

Wow! That is pleasingly succinct. All that $\theta(t)$ implies is that
the changes to the system occur only after the kick occurs.

Now, for computational reasons, it would be nice to put all creation
operators to the left and all annihilation operators to the right. I can
never remember the various exponential identities or the various vectors
calculus identities and other bull of that sort, so I'll just state it:

$$e^{-iJ\theta(t)(a^{\dagger}+a)}=e^{\frac{-\theta(t)J^{2}}{2}}e^{-iJ\theta(t)a^{\dagger}}e^{-iJ\theta(t)a}$$

This one is called the Zassenhaus expansion, truncated significantly
because the commutator $[a^{\dagger},a]$is not an operator, but a
regular old number.

Let's see what happens when you apply this operator to the ground state

$$e^{\frac{-\theta(t)J^{2}}{2}}e^{-iJ\theta(t)a^{\dagger}}e^{-iJ\theta(t)a}|0>=e^{\frac{-\theta(t)J^{2}}{2}}e^{-iJ\theta(t)a^{\dagger}}|0>=e^{\frac{-\theta(t)J^{2}}{2}}\sum_{n=0}^{\infty}\frac{(-i\theta(t)J)^{n}}{\sqrt{n!}}|n>=|\Psi>$$

These kinds of states are called coherent states, and they are really
neato. The probability that the oscillator gets kicked up into any
particular energy state $n$ is

$$P_{n}=|<n|\Psi(t>0)>|^{2}=\frac{e^{-J^{2}}J^{2n}}{n!}$$

This is a poisson distribution with a parameter $J$. The larger J is,
the higher the distribution is pushed.

$$U_{I}(t,-\infty)=1-i\int_{-\infty}^{t}H_{I}(t')dt'+\frac{(-i)^{2}}{2!}\int_{-\infty}^{t}\int_{-\infty}^{t}T(H_{I}(t')H_{I}(t''))dt'dt''+\ldots$$

$J(t)$ is just a regular old number, not an operator. It commutes with
everything.

$$H_{I}(t)=F(t)x(t)=F(t)e^{iH_{0}t}xe^{-iH_{0}t}=J(t)(a^{\dagger}(t)+a(t))=J(t)e^{iH_{0}t}(a^{\dagger}+a)e^{-iH_{0}t}=J(t)(a^{\dagger}e^{i\omega t}+ae^{-i\omega t})$$

Note to ole phil: double check sign on time evolution of creation ops.
Derive maybe?

So say we start out in the ground state $|0>$, where do we end up?

$$U_{I}|0>=1+-i\int_{-\infty}^{t}J(t')(e^{i\omega t'}a^{\dagger}+e^{-i\omega t'}a)dt'+\frac{(-i)^{2}}{2!}\int_{-\infty}^{t}\int_{-\infty}^{t}J(t')J(t'')T(a^{\dagger}(t')a^{\dagger}(t'')+a(t')a^{\dagger}(t'')+a^{\dagger}(t')a(t'')+a(t)a(t))dt'dt''+\ldots$$

Let's look a little closer at the time ordering. The first and last
terms contain two annihilation or two creation operators, which commute,
so the time ordering can be ignored.

$$T(a^{\dagger}(t')a^{\dagger}(t''))=e^{i\omega(t'+t'')}a^{\dagger}a^{\dagger}$$

$$T(a(t')a(t''))=e^{-i\omega(t'+t'')}aa$$

The other two terms actually do something interesting under time
ordering.

$$[a,a^{\dagger}]=aa^{\dagger}-a^{\dagger}a=1$$

$$T(a(t')a^{\dagger}(t'')+a^{\dagger}(t')a(t''))=\begin{cases}
e^{-i\omega(t'-t'')}aa^{\dagger}+e^{i\omega(t'-t'')}a^{\dagger}a & t'>t''\\
e^{-i\omega(t'-t'')}a^{\dagger}a+e^{i\omega(t'-t'')}aa^{\dagger} & t'<t''
\end{cases}$$

The first term is the part that receives no kicks. The second term kicks
the ground state up to the first state by looking at the average amount
of kick it got and where in the oscillation cycle it received it. This
is very similar to the classical case. If you kick the oscillator in the
positive x direction to start an oscillator from the ground state but
then wait until half a cycle to kick it in exactly the same way, you
will stop the oscillator. If you wait a full cycle, you double the
effect of your kick.

$$U_{I}|0>=(1+-i\int_{-\infty}^{t}J(t')(e^{i\omega t'}a^{\dagger}+e^{-i\omega t'}a)dt'+(-i)^{2}\int_{-\infty}^{t}\int_{-\infty}^{t}J(t')J(t'')T(e^{i\omega(t'+t'')}a^{\dagger}a^{\dagger}+e^{i\omega(t'+t'')}a^{\dagger}a+e^{i\omega(t'+t'')}aa^{\dagger}+e^{i\omega(t'+t'')}aa)dt'dt''+\ldots)|0>$$

Wick's Theorem
--------------

The idea behind defining the Wick Contraction is the same as that behind
defining the commutator. When do we need the commutator? When we want to
flip two operators in an expression, we have to add in the commutator

$$AB\rightarrow BA+[A,B]$$

When do we need a Wick Contraction? Whenever we want to turn a time
ordering (which is kind of a pain) into a normal ordering (which makes
life algebriaccaly easy)

$$T(AB)\rightarrow:AB:+\overbrace{AB}$$

Hence the definition of the Wick Contraction

$$\overbrace{AB}=T(AB)-:AB:$$

Here's the cool part: Wick Contraction is a c-number for all the fields
that I know of (admittedly not many).

$$<0|\overbrace{AB}|0>=\overbrace{AB}<0|0>=\overbrace{AB}=<0|T(AB)-:AB:|0>=<0|T(AB)|0>$$

Now, the vacuum expactation of the time ordered product is something
that is going to come up a lot. Trust me on this. You'll see.

Guralnik has expressed distaste for Normal ordering, and by god, he's
right. It's kind of a low rent way to go about things. HOWEVER, I get
the sensation that this is the distaste of a unicyclist for training
wheels. The Wick's theorem method of deriving the Feynman rules is less
elegant than functional methods, but I personally think it is a lot
easier to follow. Nothing bad ever came from knowning multiple
perspectives to a problem anyhow, so let's proceed.

$$$$

$$T(\phi(x_{1})\phi(x_{2})\phi(x_{3})\phi(x_{4})\ldots\phi(x_{N}))$$

Let's randomly say that $x_{3}$is the one with the greatest time. If we
never explicity use this fact in any special way, then our derivation
will generalize to the cases where some other operator had the last
time. That means it should be out front and we can take it out of the
time ordering like so

$$T(\phi(x_{1})\phi(x_{2})\phi(x_{3})\phi(x_{4})\ldots\phi(x_{N}))=\phi(x_{3})T(\phi(x_{1})\phi(x_{2})\phi(x_{4})\ldots\phi(x_{N}))$$

Now we use an induction step. We assume that Wick's Theorem has already
worked for all cases with less $\phi(x)$ inside the time ordering guy.

$$\phi(x_{3})T(\phi(x_{1})\phi(x_{2})\phi(x_{4})\ldots\phi(x_{N}))=\phi(x_{3})W(\phi(x_{1})\phi(x_{2})\phi(x_{4})\ldots\phi(x_{N}))$$

Now we break $\phi(x)$ up into its annihilation and creation parts.

$$(\phi^{+}(x_{3})+\phi^{-}(x_{3}))W(\phi(x_{1})\phi(x_{2})\phi(x_{4})\ldots\phi(x_{N}))$$

Now we need to push through the annihilation operator in order to normal
order this expression

Fair, enough. But the truly useful form is

$$<0|T[\phi_{1}\phi_{2}\phi_{3}\phi_{4}\phi_{5}]|0>=\text{all possible Wick pairings}$$

This is related to the factorization of higher moments of gaussians in
terms of the variance. This follows from the previous discussion, since
any normal ordered operator kills the vacuum expactation (either on the
bra or on the ket).

Regardless of the original order, to convert a time ordered product to
normal order, we'll need to commute some things. Every operator has both
creation and annihilation in it, so it can never be in normal order to
begin with.

The Vac-to-Vac
==============

Functional Differentiation
--------------------------

The moment generating function trick: Average Powers go to derivatives

What the hell is a vac-to-vac and what the hell does One of the moments $<\phi(x)\phi(y)\phi(z)>$mean?
------------------------------------------------------------------------------------------------------

Correaltion functions are great. Everybody loves them. When you read in
the newspaper that feeding your kid applesauce everyday gives them a 35%
chance of becoming a sheep rapist, that's a correlation function. It
might look like this

$$A=cm^{3}\text{ of Applesauce/Day}$$

$$S=\text{Number of Sheep Raped}$$

$$<AS>=\int ASP(A,S)dAdS=\text{Some Number}$$

Sources and Green's Functions
=============================

Classical Sources and Green's Functions
---------------------------------------

Sources and Boundary Conditions are the same goddamn things and how to
use gren's functions to deal with both

Classicla harmonic oscillator

Green's Functions. Can't beat 'em. Join 'em.

Green's functions are the inverse operators to Linear Differential
operators.

Where for example

$$L=\frac{d^{2}}{dx^{2}}+x^{2}$$

or

$$L=\nabla^{2}$$

or

$$L=\square+m^{2}=\frac{\partial^{2}}{\partial t^{2}}-\nabla^{2}+m^{2}$$

I think you get the gyst.

Linear differential operators often go in equations like this

$$Lf=0$$

We call these homogenous differential equations, because why not. We can
add a bunch of different functions that satidfy this equatin, and get
another function that saitifies this equation.

$$Lf=0$$

$$Lg=0$$

$$L(f+g)=0$$

But we'll change what is happening on the boundaries

Green's Functions comes into the nonhomogenous equation

$$Lh=J(x)$$

Now if we add two functions that satisfy this equation, we don't get a
new function that satisfies the equation

$$Lh=J(x)$$

$$Lk=J(x)$$

$$L(h+k)=2J(x)\ne J(x)$$

However, we can add a homogenous solution

$$Lh=J(x)$$

$$Lf=0$$

$$L(h+f)=J(x)$$

Let's do the dumbest thing you can do. Did you or perhaps some kid you
know try to solve the equation

$$\sin(x)=1$$

by doing the following:

$$x=\frac{1}{\sin}$$

What a tard, right?!

NO. HE WAS A GENIUS AHEAD OF HIS TIME. If only he had tried to pull that
move in his differential equations class, because strangely enough it
works.

$\frac{1}{\sin}x$ would be an extremely sensible notation for
$\arcsin(x)$, if only arcsin was a linear function, like multiplication
is. Then your knee jerk algebraic manipulations would almost always be
correct. If you restrict your domain of questioining to near the origin.
then

$$\sin(x)\approx x+O(x^{3})$$

And you can set $$\sin\approx1$$

Then one would assume that

$$\frac{1}{\sin}\approx1$$

The series for arcsin is

$$\arcsin(x)\approx x+\frac{x^{3}}{6}+\frac{3x^{5}}{40}+O(x^{7})$$

Which makes your naive substitution fairly accurate.

An extremely underappreciated aspect of Green's Functions is that you
can get the homogenous functions you need to comply with the boundary
conditions of the problem from them. They are the gift the keeps on
giving, just like socks and handjobs.

1925 Style Quantum mechanics with Sources and green's Functions
---------------------------------------------------------------

The $i\epsilon$ prescription
----------------------------

Looks at this

$$\partial_{t}y=\epsilon y$$

Solution grows

$$y=e^{\epsilon t}$$

Now

$$\partial_{t}y=-\epsilon y$$

Solution shrinks

$$y=e^{-\epsilon t}$$

Let's try

$$\partial_{t}y=i\epsilon y$$

Solution rotates CCW (in complex plane)

$$y=e^{i\epsilon t}$$

Now

$$\partial_{t}y=-i\epsilon y$$

Solution rotates CW

$$y=e^{-i\epsilon t}$$

Okay. Now, we can use these as building blocks to put at infinity
boundary conditions on Fourier Transforms. If we put in a forcing term
on the shrinker

$$(i\omega+\epsilon)y=j$$

$$y=\int\frac{j}{\epsilon+i\omega}e^{i\omega t}\frac{d\omega}{2\pi}$$

Grabs up contour on $\omega=i\epsilon$which means only get term when
close up top half of complex plane, which we do when t is positive

$$G=\Theta(t)$$

$$y=\int_{t}^{\infty}jdt$$

Now for second order

$$\partial_{tt}y=i\epsilon y$$

The CCW grows and the CW part shrinks with time

$$y=e^{\pm\sqrt{i\epsilon}t}$$

You can vice cersa that. You can alse get CW and CCW for negative
epslion and grow and shrinking for positive epsilon. But the imaginary
case now has interesting intermixing of the two cases.

Questions: Does the integration order matter when position is involved?
1d wave is very symmettric between the two. If it sends one boundary to
zero, doesn't it send the other to infinity?

Classical Correlation Functions
-------------------------------

There is the classical example of light produced by a stochastic source
(see Born and Wolf, partially coherent light chpater). To study it, the
main object is the correlation funtion

$$G(x,y)=E[\phi(x)\phi(y)]$$

The $\phi$are random variables, but they inherit their radomness from
the random sources, not any intrinstic random behavior. So any
particular solution $\phi$ you sample out of the possible ones still
satisfies the wave equation.

$$\square^{2}\phi=0$$

Applying to either side of G gives zero by linearity of expectation. G
can't possibly be connected outside lightcone either since outside of
lightcone points can't correlate unless the random sources were slightly
correlated at some spacelike distance (which is possible). One would
expect this outside lightcone dependance to decay in a manner connected
to how spacelike source correlations decay.

NOw why is G a green's function? This reuiqres that a delta function
appears

$$\phi=\int Gj$$

$$<\phi\phi>=<GjGj>$$

For uncorrelated sources

$$<jj>=\delta$$

Could assume j has some spectrum (has time correlations) but still
spatial uncorrelated

Anyhow, correlation function is essentially **$G^{T}G$** integrated in
the region with sources. Curious

Possiblity of Hilbert Transform analytic completion being related to
operator juggling in QFT definition.

Feynman was kind of a dick, but he had good ideas: Perturbation Theory
======================================================================

The Regular ole diagram
-----------------------

Renormalization
---------------

Forthcoming. I still do not have the slightest clue how to renormalize
anything.

Vertex Functions
----------------

Partial Summation?

Have you heard the good news? The Higgs.
----------------------------------------

1 My Notes from Guralnik's Fall 2011 Adavnced Quantum Class

Sidney Coleman's QFT Notes http://arxiv.org/abs/1110.5013

L.H. Ryder. Quantum Field Theory 1987 Cambridge University Press

Mattuck "Feynman Diagrams"

Ziman "Advanced Quantum Mechanics"
