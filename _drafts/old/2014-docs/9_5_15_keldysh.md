The keldysh formalism is a proper and systematic way of dealing with
nonequilibrium systems. Actually, it makes a lot more conceptual sense
than the more standard way of doing things, but the conceptually
straightforward has no reason to coincide with the most algebraically
straightforward. Doing things right establishes distinctions that can
otherwise get swept under the rug

Wassup
======

To Evolve a state you apply the time evolution operator

$$U(t)$$

In time invriannt systems,
$U(t)=e^{-iHt}=(1-iHdt)(1-iHdt)(1-iHdt)(1-iHdt)(1-iHdt)(1-iHdt)...$

Times add inside the argument

$U(t+t')=U(t)U(t')$

$U(t)=U(dt)U(dt)U(dt)U(dt)U(dt)U(dt)U(dt)U(dt)U(dt)$

$U(t)=(1-iH(t6)dt)(1-iH(t5)dt)(1-iH(t4)dt)(1-iH(t3)dt)(1-iH(t2)dt)(1-iH(t1)dt)...$

In non time invariant systems you really do need to use this last form.
Each little step can be thought of as solving the schordinger equation
using a finite difference in the time domain

which can be written symbolically using the time ordering notation as
$U(t)=Te^{-i\int H(t)dt}$. This notation means nothing except it's
definition interms of a finite difference scheme really. (We're doing
quantum mechanics. Hamiltonaians at different times may not commute so
we have to be careful about the ordering. In this case, the earlier
hamiltonians fo to the right of later hmailtonains).

to propagate backards in time you apply

$U(-t)$

which is often related to

$U(-t)=U^{\dagger}(t)$

which is how you propgate bras forward in time. Bizarre but true.

To go backards in time requires reverse time ordering. This can also be
seen from taking the hermitian conjugate, which always reverse to order
of the factors of an operator.

$U(-t)=\bar{T}e^{-i\int H(t)dt}$.

The natural way to ask questions Q at time t is

What is the value of $<\psi(0)|U^{\dagger}(t)QU(t)|\psi(0)>$. Propgate
botth the bra and ket forward in time to the point in time you're
interested in. makes sense.

Now, the bizarre tricks that arestandard. First off, we push $|\psi(0)>$
alll the way back to $|\psi(-\infty)>$. This is a very nasty thing to
do. Infinities are scary and should be viewed with suspicion.

Next, even weirder, typical is to push $<\psi(0)|$out to positive
infity! $<\psi(\infty)|$. Why? Well, we're going to wave our hands
invthe air and talk baout adiabtaically turning pertubrations on and
off. The reasons this is good is check this out

$=<\psi(\infty)|U^{\dagger}(\infty,t)QU(t,-\infty)|\psi(-\infty)>=<\psi(\infty)|U(t,\infty)QU(t,-\infty)|\psi(-\infty)>=<TQ(t)e^{-i\int Hdt}>$

What you have at this point is the standard feynman equlibrium way of
doing things. You have your answer in all these nice integrals going
from $-\infty$ to $\infty$, which is very useful for contour integration
and other dfinite integral evlauation techniques. Now what is the
trouble? Basically the trouble is that assuming you know what
$<\psi(\infty)|$ is going to be is pretty damn questionable.

What is more honest is

$<\psi(-\infty)|U^{\dagger}(t,-\infty)QU(t,-\infty)|\psi(-\infty)>$

Now you can insert a 1 in there $1=U^{\dagger}(\infty,t)U(\infty,t)$

$<\psi(-\infty)|U^{\dagger}(t,-\infty)U^{\dagger}(\infty,t)U(\infty,t)QU(t,-\infty)|\psi(-\infty)>$

Now you've got a bunch of infiniites in there, which is nice.

Now, you can tell a funny story about what you've done. You can talk
about ordering on a time contour that goes from $-\infty$ to $\infty$
and then back again

$<T_{K}Qe^{-i\int Hdt}>$

Where the K is for Keldysh ordering.

Okay

There are two sets of functions that sort of go together and that are
natural in different contexts.

The upp and lower set

$iG^{>}=<\phi^{+}\phi^{-}>$. Is basically the occupation number

$iG^{<}=<\phi^{-}\phi^{+}>$. Is biascally the occupation number + 1

$iG^{T}=<\phi^{+}\phi^{-}>$

These functions are connected to each other.

### classical and quantum fields

Set two. The quantum and classical fields. The classical field kind is
the average of the top and bottom branch, blurring the disticntion. I
believe the classical field has something to do with the wigner
quasiprobiltiy distribution function?

$G^{R}=G^{A\dagger}$

The retarded and advanced greens function are the most familiar green's
functions (well at least the retarded one is). it is the green's
function encountered in the physical production of waves.

The Keldysh green's function is a

Under classical motion, where we merely minimize the aciton, the quantum
field can be set to 0.

### Fluctation Dissipation theorem

You're a big boy in a hot bath of tiny guys. The tiny guys bounce off of
you all the time. After long times, you're motion gets dragged down to
nothing. This is the equilibrium situation. Drag is your big energy
being sucked out as heat in the tiny guys. Hypothetically though, if you
were perfectly still, the tiny guys would bounce off of you and add
energy back into you, and there are so many tiny guys that this is a
certainty. In true equlibrium, on average this energy must be balanced
by the drag occurring.

$\dot{E}=W=Fv=\gamma v^{2}$

$\dot{E}=$

$<fv>=<\gamma v^{2}>$

There is nthing to say that the drag term has to have the form
$-\gamma v$

In equilbirium all net flows have to stop.

Also, they have to conform to boltzmann statistics

$D\nabla n=\sigma E$

$Dn=\sigma\phi$

$n\propto e^{-\beta\phi}$

$D\beta e=\sigma$
