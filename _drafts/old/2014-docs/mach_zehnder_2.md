Dam Son has recently suggested a new particle-hole symmetric state for
the filling factor $\nu=5/2$ that should be thrown in competition with
the other states, such as the 113, pfaffian, and anti-pfaffian states.

The fact that the edge theory of the anti-pfaffian state is not the same
as the pfaffian state was discussed in

A particle-hole symmettry puts constraints on both the electric quantum
hall conductance, but also the quantum hall thermal conductance.

The simplest suggestion for a particle hole symmetric edge theorythat
satisfies these contraints is one charged mode combined with one
upstream travelling majorana mode.

This is very similar to the edge theory of the pfaffian state so a great
deal of analysis that has been performed on the edge theory is directly
applicable.

In a Mach-zehnder interferomter arrangement, the tunneling quasipartilce
winds around an inner anti-dot that has topological charge $\alpha$.
This means that the interferometer quite directly inlcudes the
statistcal phaee between particles.

The phase $\phi_{ab}$ depends on the total topological charge before and
after the tunneling event of the island and includes an abelian part you
would expect from the abelian flux charge binding picture in addition to
a part that depends on the nonableian charge before the tunnelling event
and afterward.

Every time a $\sigma$ quasihole tunnels across the contact, the charge
on the inner island increases by $e/4$, and the topological charge
changes to a new value given by the fusion rules. For the purposes of
statistical phase, an increase of inner charge by e is irrelevant and
physical corresponds to one electron tunnelling between the edges, which
can be easily removed from the system by the drain contact.

The fusion rules for the topological charge are

$\sigma\times\sigma=1+\epsilon$

$\sigma\times\epsilon=\sigma$

$\sigma\times1=\sigma$

The total phase accumulated is given by $\phi_{ab}=n\pi/4+\phi'_{ab}$

The nonabelian phase accumulated is

$\phi'_{1\sigma}=0$

$\phi'_{\epsilon\sigma}=-\pi$

$\phi'_{\sigma1}=\pi/4$

$\phi'_{\sigma\epsilon}=-3\pi/4$

The transission coeffecient through the contact is given by $\Gamma$.

The total amplitude is $\Gamma_{1}e^{i\theta}+\Gamma_{2}$. $\theta$
includes both the stastitical phase and the ordinary aharanov bohm
phase.

The transmission probabilities come in the form
$p_{k}=|\Gamma_{1}|^{2}+|\Gamma_{1}|^{2}+(\Gamma_{1}\Gamma_{2}^{*}e^{i\pi\Phi/2+i\pi k/2}+c.c.)$.

The is one other important contribution to the current due to nonabelian
effects.

A full chart of the pobabilties is given by

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

For the purposes of the Mach-Zehnder interferometer, that main new thing
that has to be included is that the nonabelian statistical phase
$\phi_{ab}$ accumulate as as is the opposite of that accumulated

Quantum hall interferometers are largely the same as the less
intimidating and more familiar optical interferometers. They can be
qualitatively and quantitaively understood using simple calculations

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

Here using the very useful identity
$p_{0}+p_{2}=p_{1}+p_{3}=2|\Gamma_{1}|^{2}+2|\Gamma_{2}|^{2}$, we can
see that in fact the two populations must be equal. There is no
dependance on flux in any of the proportions between populations

The normalization condition then gives

$f_{-1\sigma}=f_{1\sigma}=\frac{1}{4}$

$f_{01}=f_{0\epsilon}=f_{21}=f_{2\epsilon}=\frac{1}{8}$

The current travelling in the system. Every tunnelling process transmits
$e/4$ charge from one side to the other.

$I=\frac{e}{4}\sum w_{a\rightarrow b}f_{a}$

Once again, the identity comes in handy

At finite temperature, a very similar calculation progresses, except now
there is the possibility of travelling backwards along the graph. Every
rate that occurs in the T=0 case is accompanied by the reverse operation
with rates described by the principle of detailed balance.
$e^{\frac{-eV}{4k_{B}T}}$.

The kinetic equations can be solved with the same procedure as before to
give a current of

$I=\frac{e}{4}\frac{(\sum_{k=0}^{3}p_{k})}{8+10e^{-eV/4k_{B}T}}(2-2e^{-eV/2k_{B}T})$
