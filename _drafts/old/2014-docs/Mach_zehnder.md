The rough picture of interferometers can be analyzed with no appeal to
partial differential equations or other sophisticated theories of waves.
One looks at the inteferomter and counts up the phase accumulated along
each possible path to the detection and after the fact, one can relate
this result to a semiclassical solutoin of the underlying theory.

This is exactly what occurs in the qunatum hall interferomters. There
are different edge modes. Tunnelling contacts take the place of half
silvered mirrors.

The unique thing about the mach zehnder interferometer is that one path
necessarily winds itself around

The phase accumulated by the particle is given by

The transission coeffecient through the contact is given by $\Gamma$.

The total amplitude is $\Gamma_{1}e^{i\theta}+\Gamma_{2}$.

Hence the total probability is
$|\Gamma_{1}|^{2}+|\Gamma_{1}|^{2}+(\Gamma_{1}\Gamma_{2}^{*}e^{i\theta}+c.c.)$

This $\theta$ has a part due to the aharonov bohm phase and a part due
to the particle statistics.

A poisson process ocurring at rate $r$ has the distribution.

in a time dt there is a porbability $rdt$ of an event occurring and
$1-rdt$ of an event not occurring.

The prbabilty of an event happening at a particular times looks like

$(1-rdt)(1-rdt)(1-rdt)(1-rdt)rdt(1-rdt)(1-rdt)rdt(1-rdt)$

If we sum over all times in which the event could have occurred we get
thdistrubtion of the number of events in time t

$P(n)=\frac{(rt)^{n}}{n!}e^{-rt}$

We can easily seee that this sums up to 1 by the Taylor series of
$e^{x}$.

A useful generating function is

$Z(\lambda)=\sum\frac{(\lambda rt)^{n}}{n!}e^{-rt}=e^{(\lambda-1)rt}$

Differentiation with resepct to $\lambda$ gives the moments of the
distribution.

$<n>=\lambda\partial_{\lambda}Z|_{\lambda=1}=rt$

$<n^{2}>=(\lambda\partial_{\lambda})^{2}Z|_{\lambda=1}=(rt)^{2}$

These expressions can be updated to more complicated random processes
occurring on a graph, a markov chain. Then depending on your location in
the graph, there may be multiple places to go

The new expression can be arrived at the same way. It takes a form quite
familiar from perturbation thoery in quantum mechanics.

Chart

$p_{k}=|\Gamma_{1}|^{2}+|\Gamma_{1}|^{2}+(\Gamma_{1}\Gamma_{2}^{*}e^{i\pi\Phi/2+i\pi k/2}+c.c.)$

An impotant identity is
$p_{0}+p_{2}=p_{1}+p_{3}=2|\Gamma_{1}|^{2}+2|\Gamma_{2}|^{2}$.

This is true because the interfernce patterns are negatives of each
other, exchanging constructive for destricutive interfernece.

The statistical phases that accumulated due to

The notation $\phi_{ab}$corresponds to the pase accumulated.

The oppoiste nonabelian phase the that accumulated in the pfaffian
state.

$\phi_{1\sigma}=0$

$\phi_{\epsilon\sigma}=-\pi$

$\phi_{\sigma1}=\pi/4$

$\phi_{\sigma\epsilon}=-3\pi/4$

Every time a $\sigma$ quasihole tunnels across the contact, the charge
on the inner island increases by $e/4$, and the topological charge
changes to a new value given by the fusion rules. For the purposes of
statistical phase, an increase of inner charge by e is irrelevant and
physical corresponds to one electron tunnelling between the edges, which
can be easily removed from the system by the drain contact.

$\sigma\times\sigma=1+\epsilon$

$\sigma\times\epsilon=\sigma$

$\sigma\times1=\sigma$

$\begin{array}{cc}
(-1,\sigma)\rightarrow(0,\epsilon) & \frac{p_{2}}{2}\\
(-1,\sigma)\rightarrow(0,1) & \frac{p_{0}}{2}\\
(0,\epsilon)\rightarrow(1,\sigma) & p_{2}\\
(0,1)\rightarrow(1,\sigma) & p_{0}\\
(1,\sigma)\rightarrow(2,\epsilon) & \frac{p_{3}}{2}\\
(1,\sigma)\rightarrow(2,1) & \frac{p_{1}}{2}\\
(2,\epsilon)\rightarrow(-1,\sigma) & p_{3}\\
(2,1)\rightarrow(-1,\sigma) & p_{1}
\end{array}$

$p_{0}+p_{2}=p_{1}+p_{3}=2|\Gamma_{1}|^{2}+2|\Gamma_{2}|^{2}$

The kinetic equation for the distribution of topological and electric
charge

$\dot{f_{a}}=\text{rate in}-\text{rate out}$

a is an index describing both the electric and topological charge, for
example $(-1,\sigma)$.

The rate that drains is proprtional to the amount in there and the rate
in is porpotional to the population of the stages that

In equilbirum the populations do not change, so all time derviatives are
0. Hence the rate in = rate out. This leads to a set of linear equations
for the equilbirum distribtuion, combined with the normalization
condtion

$1=\sum f_{a}$

$$

There is only one way in and one way out for the states that have
topological charge $\epsilon$ or $1$. Hence the rate in is equal to the
rate out in equilbirium. And we can directly solve for the proportion
between those populations and the the population that preceeds it.

Because of the symmettry of the rates, we immedaitely see that

$f_{0\epsilon}=f_{01}=\frac{1}{2}f_{-1\sigma}$

$f_{2\epsilon}=f_{21}=\frac{1}{2}f_{1\sigma}$

In addition everything must leave $(-1\sigma)$ at the same rate that it
arrives at $(1,\sigma)$, so we have the condition
$0=f_{1\sigma}(\frac{p_{3}}{2}+\frac{p_{1}}{2})-f_{-1\sigma}(\frac{p_{0}}{2}+\frac{p_{2}}{2})$.

Due to the previous identity $p_{0}+p_{2}=p_{1}+p_{3}$, we can see that
in fact the two populations must be equal. There is no dependance on
flux in any the the proportions between populations

The normalization condition then gives

$f_{-1\sigma}=f_{1\sigma}=\frac{1}{4}$

$f_{01}=f_{0\epsilon}=f_{21}=f_{2\epsilon}=\frac{1}{8}$

The current travelling in the system. Every tunnelling process transmits
$e/4$ charge from one side to the other.

$I=\frac{e}{4}\sum wf$

Once again, the identity comes in handy

At finite temperature, a very similar calculation progresses, except now
there is the possibility of travelling backwards along the graph, with
rates described by the principle of detailed balance.
$e^{\frac{-eV}{k_{B}T}}$.

For noise,
