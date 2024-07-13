Interferometer experiments quite directly include the statistical phase
between particles and are natural way to determine the existence of
anyonic quasiparticles in a system. In a Mach-Zehnder interferometer
arrangement, the tunneling quasiparticle winds around an inner anti-dot
that has topological charge $\alpha$.

Dam Son has recently suggested a new particle-hole symmetric state for
the filling factor $\nu=5/2$ that should be thrown in competition with
the other states, such as the 113, pfaffian, and anti-pfaffian states.
The particle-hole symmetry puts constraints on both the electric quantum
hall conductance, and the quantum hall thermal conductance.

The simplest suggestion for a particle hole symmetric edge theory that
satisfies these constraints is one charged mode combined with one
upstream traveling Majorana mode.

This is very similar to the edge theory of the pfaffian state so a great
deal of analysis that has already been performed on that edge theory is
directly applicable.

The statistical phase difference $\phi_{ab}$ accumulated going around
the anti-dot island depends on the total topological charge before and
after the tunneling event of the island and includes an abelian part you
would expect from the abelian flux charge binding picture in addition to
a part that depends on the nonabelian charge before the tunneling event
and afterward.

This total phase accumulated is given by $\phi_{ab}=n\pi/4+\phi'_{ab}$.
$a$ is the topological and electric charge on the island before the
tunneling and $b$ is the topological and electric charge that the
tunneling $\sigma$ particle fuses to with $a$.

The nonabelian phase accumulated is opposite of that in the Pfaffian
state, since the nonabelian Majorana mode $\chi(\bar{z})$is traveling
upstream.

$\phi'_{1\sigma}=0$

$\phi'_{\epsilon\sigma}=-\pi$

$\phi'_{\sigma1}=\pi/4$

$\phi'_{\sigma\epsilon}=-3\pi/4$

The transmission coefficient through a contact is given by
$\Gamma_{i}(V)$ and the total amplitude is at the drain is then
$\Gamma_{1}e^{i\theta}+\Gamma_{2}$. The phase $\theta$ includes both the
statistical phase and the ordinary Aharonov-Bohm phase that are
accumulated as the quasiparticle traverses the inner anti-dot edge.

The transmission probabilities come in the form
$p_{k}=|\Gamma_{1}|^{2}+|\Gamma_{1}|^{2}+(\Gamma_{1}\Gamma_{2}^{*}e^{i\pi\Phi/\Phi_{0}2+i\pi k/2}+c.c.)$,
where $\Phi$ is the flux enclosed by the edge mode traversing around the
anti-dot. and $k$ is determined by the topological and electric charges
in the process.

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

The kinetic equations can be solved before, although the calculation is
more lengthy, to give a current of

$I=\frac{e}{4}\frac{(\sum_{k=0}^{3}p_{k})}{8+10e^{-eV/4k_{B}T}}(2-2e^{-eV/2k_{B}T})$

There is another approach to calculating the properties of the current
in this diagram. We can ask about the total time it takes to traverse
the diagram once. In that time, one electric charge tunnels across the
contacts giving the average current as $I=\frac{e}{\bar{t}}$. Similarly,
fluctuations in this time correspond to shot noise fluctuations in the
current.

The probability distribution of times staying at each node in the graph
given that a particle has traversed the path abcd through the diagram is
given by

$P(t_{a},t_{b},t_{c},t_{d}|abcd)=\Gamma_{a}\Gamma_{b}\Gamma_{c}\Gamma_{d}e^{-\Gamma_{a}t_{a}-\Gamma_{b}t_{b}-\Gamma_{c}t_{c}-\Gamma_{d}t_{d}}$

The rates $\Gamma_{a}$ at the nodes are given by $p_{k}$ corresponding
to the edge leaving that node. If there are two edges leaving the node,
such as at the $\sigma$ nodes, the rates add, for example
$\Gamma_{-1,\sigma}=\frac{p_{0}+p_{2}}{2}$.

The probability of any particular path is the product of the two choices
it must make at the forks of the $\sigma$ nodes which have the form

$P(abcd)=\frac{p_{1\text{or}3}}{p_{1}+p_{3}}\frac{p_{0\text{or}2}}{p_{0}+p_{2}}$

The total probability distribution is
$P(t_{a},t_{b},t_{c},t_{d}|abcd)P(abcd)$

We are interested in the statistics of the total time
$t_{a}+t_{b}+t_{c}+t_{d}$.

$\bar{t}=\sum_{(abcd)}\int dt_{a}dt_{b}dt_{c}dt_{d}(t_{a}+t_{b}+t_{c}+t_{d})P(t_{a},t_{b},t_{c},t_{d}|abcd)P(abcd)$

Where the sum $\sum_{(abcd)}$ is over all valid paths abcd through the
diagram

The probability given a path factorizes and the integrals can be
performed using the identity

$\bar{t_{n}}=\int dt_{n}t_{n}\Gamma_{n}e^{-\Gamma_{n}t_{n}}=\frac{1}{\Gamma_{n}}$

$\bar{t}=\sum_{(abcd)}(\frac{1}{\Gamma_{a}}+\frac{1}{\Gamma_{b}}+\frac{1}{\Gamma_{c}}+\frac{1}{\Gamma_{d}})P(abcd)$

We can then substitute in the probabilities to evaluate $\bar{t}$

$\bar{t}=\frac{2}{p_{0}+p_{2}}+\frac{2}{p_{1}+p_{3}}+\frac{p_{2}}{p_{0}+p_{2}}\frac{1}{p_{2}}+\frac{p_{0}}{p_{0}+p_{2}}\frac{1}{p_{0}}+\frac{p_{3}}{p_{1}+p_{3}}\frac{1}{p_{3}}+\frac{p_{1}}{p_{1}+p_{3}}\frac{1}{p_{1}}=\frac{4}{p_{0}+p_{2}}+\frac{4}{p_{1}+p_{3}}=\frac{16}{\sigma}$

This is using the identity that $p_{0}+p_{2}=p_{1}+p_{3}$ and defining
$\sigma=p_{0}+p_{1}+p_{2}+p_{3}$

The current is $I=\frac{e}{\bar{t}}=\frac{e\sigma}{16}$, which matches
the result from the previous method.

To discuss the the shot noise we calculate the variations of time it
takes to traverse the diagrams

$\bar{\delta t^{2}}=\bar{(\sum t_{i})^{2}}-(\sum\bar{t_{i}})^{2}$

The first term can be expanded as

$\bar{(\sum t_{i})^{2}}=\sum\bar{t_{i}^{2}}+2\sum_{i\ne j}\bar{t_{i}}\bar{t_{j}}$

We have already shown how to calculate $\bar{t}_{i}$, and
$\sum\bar{t_{i}^{2}}$ proceeds similarly.

$\sum\bar{t_{i}^{2}}=\sum_{(abcd)}\int dt_{a}dt_{b}dt_{c}dt_{d}(t_{a}^{2}+t_{b}^{2}+t_{c}^{2}+t_{d}^{2})P(t_{a},t_{b},t_{c},t_{d}|abcd)P(abcd)$

Which again factors, and we can use the identity

$\bar{t_{n}^{2}}=\int dt_{n}t_{n}^{2}\Gamma_{n}e^{-\Gamma_{n}t_{n}}=\frac{2}{\Gamma_{n}^{2}}$

To obtain

$\sum\bar{t_{i}^{2}}=\sum_{(abcd)}(\frac{2}{\Gamma_{a}^{2}}+\frac{2}{\Gamma_{b}^{2}}+\frac{2}{\Gamma_{c}^{2}}+\frac{2}{\Gamma_{d}^{2}})P(abcd)$

Substituting in for $P(abcd)$

$\sum\bar{t_{i}^{2}}=2(\frac{1}{(\frac{p_{0}}{2}+\frac{p_{2}}{2})^{2}}+\frac{1}{(\frac{p_{0}}{2}+\frac{p_{2}}{2})^{2}}+\frac{p_{2}}{p_{0}+p_{2}}\frac{1}{p_{2}^{2}}+\frac{p_{0}}{p_{0}+p_{2}}\frac{1}{p_{0}^{2}}+\frac{p_{3}}{p_{1}+p_{3}}\frac{1}{p_{3}^{2}}+\frac{p_{1}}{p_{1}+p_{3}}\frac{1}{p_{1}^{2}})=\frac{64}{\sigma^{2}}+\frac{4}{\sigma}(\sum_{k=3}^{3}\frac{1}{p_{k}})$

Now we turn to the second term in the $(\sum t_{i})^{2}$ expansion.
Every term that contributes to the sum
$\sum_{i\ne j}2\bar{t_{i}}\bar{t_{j}}$ is proportional to
$\frac{1}{\sigma^{2}}$. This is due to a cancellation of the numerator
of the probability in picking a path and the time at the node itself,
for example $\frac{p_{0}}{p_{0}+p_{2}}\frac{1}{p_{0}}$.

Altogether the various terms add up to
$\sum_{i\ne j}2\bar{t_{i}}\bar{t_{j}}=\frac{192}{\sigma^{2}}$.

Putting these results together we can get the $T=0$ fano factor.

$\bar{\delta t^{2}}=\sum\bar{t_{i}^{2}}+2\sum_{i\ne j}\bar{t_{i}}\bar{t_{j}}-(\sum\bar{t_{i}})^{2}=\frac{4}{\sigma}(\sum_{k=3}^{3}\frac{1}{p_{k}})$

$e^{*}=e\frac{\bar{\delta t^{2}}}{\bar{t}^{2}}=\frac{e\sigma}{64}(\sum_{k=3}^{3}\frac{1}{p_{k}})$

Using a computer algebra package Mathemtica, the finite temperature
noise can also be calculated according to the method found in D. E.
Feldman, Yuval Gefen, Alexei Kitaev, K. T. Law, and Ady Stern Phys. Rev.
B 76, 085333 (2007)

$\frac{e}{32p_{0}}(-\frac{9\left(p_{2}\left(p_{3}-p_{2}\right)+p_{1}\left(p_{2}+p_{3}\right)\right)\left(p_{1}+p_{3}\right){}^{2}}{p_{1}p_{2}p_{3}\left(4e^{\frac{eV}{4\text{kb}T}}+5\right)^{2}}+\frac{16\left(p_{1}-p_{2}+p_{3}\right)}{e^{\frac{eV}{4\text{kb}T}}-1}+$

$\frac{-4\left(p_{1}+p_{2}\right)p_{3}^{3}+4\left(-2p_{1}^{2}+5p_{2}p_{1}+p_{2}^{2}\right)p_{3}^{2}-4p_{1}\left(p_{1}-3p_{2}\right)\left(p_{1}-2p_{2}\right)p_{3}+4p_{1}^{2}p_{2}\left(p_{2}-p_{1}\right)}{p_{1}p_{2}p_{3}\left(2e^{\frac{eV}{4\text{kb}T}}+1\right)}+$

$\frac{4\left(\left(p_{2}+p_{3}\right)p_{1}^{3}+\left(-p_{2}^{2}+15p_{3}p_{2}+2p_{3}^{2}\right)p_{1}^{2}+p_{3}\left(-14p_{2}^{2}+15p_{3}p_{2}+p_{3}^{2}\right)p_{1}+p_{2}p_{3}^{2}\left(p_{3}-p_{2}\right)\right)}{p_{1}p_{2}p_{3}\left(4e^{\frac{eV}{4\text{kb}T}}+5\right)}-\frac{16\left(p_{1}-p_{2}+p_{3}\right)}{e^{\frac{eV}{4\text{kb}T}}+1}+\frac{\left(p_{2}\left(p_{3}-p_{2}\right)+p_{1}\left(p_{2}+p_{3}\right)\right)\left(p_{1}+p_{3}\right){}^{2}}{p_{1}p_{2}p_{3}})$

This expression reduces to the previous in the $T=0$ case.

To first order in $T/V$ the expression is $\frac{2k_{b}T}{V}$. This
shows that the expression obeys the fluctuation-dissipation theorem.
