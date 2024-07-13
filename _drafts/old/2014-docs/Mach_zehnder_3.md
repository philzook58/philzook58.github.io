In a Mach-Zehnder interferometer arrangement, the tunneling
quasiparticle winds around an inner anti-dot that has topological charge
$\alpha$. This means that the interferometer quite directly includes the
statistical phase between particles and is a very natural experiment to
use to try to determine the existence of anyonic quasiparticles in a
system.

Dam Son has recently suggested a new particle-hole symmetric state for
the filling factor $\nu=5/2$ that should be thrown in competition with
the other states, such as the 113, pfaffian, and anti-pfaffian states.
The particle-hole symmetry puts constraints on both the electric quantum
hall conductance, and the quantum hall thermal conductance.

The simplest suggestion for a particle hole symmetric edge theory that
satisfies these constraints is one charged mode combined with one
upstream traveling Majorana mode.

This is very similar to the edge theory of the pfaffian state so a great
deal of analysis that has been performed on that edge theory is directly
applicable.

Every time a $\sigma$ quasihole tunnels across the contact, the charge
on the inner island increases by $e/4$, and the topological charge
changes to a new value given, with the possibilities given by the fusion
rules.

The fusion rules for the topological charge are

$\sigma\times\sigma=1+\epsilon$

$\sigma\times\epsilon=\sigma$

$\sigma\times1=\sigma$

The statistical phase difference $\phi_{ab}$ depends on the total
topological charge before and after the tunneling event of the island
and includes an abelian part you would expect from the abelian flux
charge binding picture in addition to a part that depends on the
nonabelian charge before the tunneling event and afterward.

This total phase accumulated is given by $\phi_{ab}=n\pi/4+\phi'_{ab}$

For the purposes of statistical phase, an increase of inner charge by e
is irrelevant and physically corresponds to one electron tunneling
between the edges, which can be easily removed from the system by the
drain contact. All further electric charge will be referred to by the
number -1,0,1,2 which correspond to the charge on the island
$\frac{4Q}{e}\mod4$

The nonabelian phase accumulated is opposite of that in the Pfaffian
state, since the nonabelian majorana mode is travelling upstream.

$\phi'_{1\sigma}=0$

$\phi'_{\epsilon\sigma}=-\pi$

$\phi'_{\sigma1}=\pi/4$

$\phi'_{\sigma\epsilon}=-3\pi/4$

The transmission coefficient through a contact is given by $\Gamma(V)$.

The total amplitude is at the drain is then
$\Gamma_{1}e^{i\theta}+\Gamma_{2}$. The phase $\theta$ includes both the
statistical phase and the ordinary Aharonov-Bohm phase.

The transmission probabilities come in the form
$p_{k}=|\Gamma_{1}|^{2}+|\Gamma_{1}|^{2}+(\Gamma_{1}\Gamma_{2}^{*}e^{i\pi\Phi/\Phi_{0}2+i\pi k/2}+c.c.)$,
where $\Phi$ is the flux enclosed by the edge mode traversing around the
anti-dot. This analysis emphasizes the flux dependance and sweeps the
voltage dependance under the rug.

There is one other effect the non-abelian statistics has on the
tunneling probabilities. The rates coming out of a state with the
topological charge $\sigma$ are reduced by a factor of 2 due to the
fusion multiplicity.

A full chart of the probabilities is given by

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

The kinetic equation for the distribution of topological and electric
charge is simply

$\dot{f_{a}}=\text{rate in}-\text{rate out}$

Where $f_{a}$ is the probability of the inner island having a a given
topological and electric charge $a$.

The rate in is $w_{b\rightarrow a}f_{b}$ where b is the topological and
electric charge that precedes the charge a, and $w_{a\rightarrow b}$ is
the rate of that process given that the system is in state a. Similarly,
the rate out is $w_{a\rightarrow c}f_{a}$.

In equilibrium the populations do not change, so all time derivatives
are 0. Hence the rate in equals the rate coming out. This, combined with
the normalization condition $1=\sum f_{a}$ , leads to a set of linear
equations for the equilibrium distribution, which can be easily solved.

There is only one way in and one way out for the states that have
topological charge $\epsilon$ or $1$. Hence the rate in is equal to the
rate out in equilibrium. And we can directly solve for the proportion
between those populations and the the $f_{\sigma}$ population that
precedes it.

Because of the symmetry of the rates (both contain the same $p_{k}$,
with a factor of 2 due to fusion multiplicity), we immediately see that

$f_{0\epsilon}=f_{01}=\frac{1}{2}f_{-1\sigma}$

$f_{2\epsilon}=f_{21}=\frac{1}{2}f_{1\sigma}$

In addition, everything must leave $(-1,\sigma)$ at the same rate that
it arrives at $(1,\sigma)$, so we have the condition
$\dot{f}_{-1\sigma}=0=f_{1\sigma}(\frac{p_{3}}{2}+\frac{p_{1}}{2})-f_{-1\sigma}(\frac{p_{0}}{2}+\frac{p_{2}}{2})$.

Here using the very useful identity
$p_{0}+p_{2}=p_{1}+p_{3}=2|\Gamma_{1}|^{2}+2|\Gamma_{2}|^{2}$, we can
see that in fact the two populations must be equal. There is no
dependance on flux in any of the proportions between populations

The normalization condition then gives

$f_{-1\sigma}=f_{1\sigma}=\frac{1}{4}$

$f_{01}=f_{0\epsilon}=f_{21}=f_{2\epsilon}=\frac{1}{8}$

Using thing we can calculate the current traveling in the system. Every
tunneling process transmits $e/4$ charge from one side to the other.

$I=\frac{e}{4}\sum w_{a\rightarrow b}f_{a}$

Substituting in the values for rates and the distributions we get

$I=\frac{e}{16}(\sum_{k=0}^{3}p_{k})$

Once again, the identity
$p_{0}+p_{2}=p_{1}+p_{3}=2|\Gamma_{1}|^{2}+2|\Gamma_{2}|^{2}$ comes in
handy. We see that in fact this expression has no dependance on
Aharonov-Bohm flux whatsoever and shows no interference pattern. While
each individual step has flux dependance, the constructive interference
is balanced out by the destructive interference on average.

At finite temperature, a very similar calculation progresses, except now
there is the possibility of traveling backwards along the graph. By the
principle of detailed balance, every rate that occurs in the$T=0$ case
is accompanied by a reverse operation with a proportionality
$e^{\frac{-eV}{4k_{B}T}}$.

The kinetic equations can be solvedas before, although the claculation
is more lengthy, to give a current of

$I=\frac{e}{4}\frac{(\sum_{k=0}^{3}p_{k})}{8+10e^{-eV/4k_{B}T}}(2-2e^{-eV/2k_{B}T})$

The noise at $T=0$ can be calculated simply (Note: I'm still somewhat
uncertain about this calculation). At every juncture when the system has
$\sigma$ topological charge, the system has 2 choices, to fuse into $1$
or into $\epsilon$. From this, we can find the probability for any
particular of the 4 paths looping around the graph, given as the product
of the probabilities it took at each junction. The total variation in
time is the average of the variation of time for all the paths. The
variation in time for a single loop around the graph for a given path is
$\sum\frac{1}{w_{ab}^{2}}$, where the sum is over all the transitions of
the given path.

For example the $\delta t{}^{2}$ of the path where $\sigma$ fuses to
$\epsilon$ twice is

$(\frac{1}{(\frac{p_{2}}{2})^{2}}+\frac{1}{p_{2}^{2}}+\frac{1}{(\frac{p_{3}}{2})^{2}}+\frac{1}{p_{3}^{2}})$

And it's contribution to the total average $\bar{\delta t{}^{2}}$ is

$\frac{p_{2}}{p_{2}+p_{0}}\frac{p_{3}}{p_{3}+p_{1}}(\frac{1}{(\frac{p_{2}}{2})^{2}}+\frac{1}{p_{2}^{2}}+\frac{1}{(\frac{p_{3}}{2})^{2}}+\frac{1}{p_{3}^{2}})$

With the sum of all the factors of this form, we get the expression

$\bar{\delta t{}^{2}}=\frac{10}{\sum_{k=0}^{3}p_{k}}(\sum_{k=0}^{3}\frac{1}{p_{k}})$

The Fano factor can be calculated from this as
$\frac{e*}{e}=\frac{\bar{\delta t{}^{2}}I^{2}}{e^{2}}$.

This gives

$\frac{e^{*}}{e}=\frac{5}{128}(\sum_{k=0}^{3}p_{k})(\sum_{k=0}^{3}\frac{1}{p_{k}})$
