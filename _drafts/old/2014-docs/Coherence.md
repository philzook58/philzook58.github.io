Maybe inseatd of correlation functions (expectations taken of two things
miltplied together) we want condition expectation more often? Its just a
tad less symmettric.

$$E[\phi(x_{1,}t_{1})|\phi(x_{2},t_{2})]$$

$<E(x_{1,t_{1}})E(x_{2},t_{2})>$tells us about how spatially correlated
and temporally correlated two positions are in the electric field. THIS
is the fundmental thingy in worries about for loight bulbs versus laser
beams. This is rough equivlenet of density matrix from ordinary quantum
mechanics. Complex off diagonal points because we use analytic extension
of E, which is technically bullshit.

Color - Why does Red plus Bue give purple, seems unintuitive from
physical perspective. Just weird mapping of brain from spectrum to cone
space to equivalent single wavelength space? How do you spoof colors?

Declan's Problem:
-----------------

If sun produces random waves with random phases, on average why don't
they cancel out? The expectation seems to be freqeuncy interpeation
realized by the massive number of photons being released? Or expectation
realized by using linear superposition to expand one E function into
many? $E[\phi(x,t)]=0$ Yet this somehow doesn't imply that the sun
produces no light. Some sort of sampling versus signle experiment
expectation paradox maybe. We sample on many identical distrbuted
sources. Do we need to use space $E[\phi(x_{2})|\phi(x_{1})=0]\ne0$ to
show that clamping one spot unclamps elsewhere (i.e. E at different
posiitons are correlated)? or in other words that the fact that the
sources are not exactly on top of one another is good enough. Do we need
that the sources are dynamically connected and hence correlate on short
distance and time scales? Appealling to intensity doesn't feel right.
(for the E feld to actually affect anything it needs to correlate with
itself over a large enough spatial or time region to collect it (perform
a noticaleable amount of work) So we don't detect intensity! We detcect
Amplitude given that correlation in a small region is large enough and
if intensity function is smooth off diagonal positions, then these two
are equivlenet If we coupled the field to the dynmaics of our detector,
the future path of the detctor would have field dependance.

The spatial integral over the osurces in not an expectation value. The
expectation is equivlent to haveing many many suns and a dude standing
relative to it at the same point. We collect the data of each dude and
sum them up. This is not what we do when we look at the sun. The sources
are what they are, but unknown! The porbability aspect is in regards to
this, not to their freuency of occurrence, although we construct
(deduce) the distribution by looking at what they frequently were and
use this information as to our guess as to what they will end up being
this time. More bayesian than frequentist. Also, Expectation of field is
not what we want. Perhaps more what we want is The maximum likelihood
field which is the field that is most indicative of the general
behavior, which will possess a circular symmettry (so no particular
direction is indicative of the distribution. (As an aside, does this add
to a discussion of godstone modes? This is an example of broken
symmettry. Is broken symmettry a sampling thing? That maybe you don't
have a suspicion for direction a priori but samples most definetly end
up somewhere in particular.)

So then the indicative field ends up looking very much like a partition
function esque thing. $\frac{\partial\ln P(\phi)}{\partial\phi}=0$.
Hmmm. It still seems like this would end up at zero? Yes. The
probability of the ring is larger in total, but too spread out, so the
center wins. maybe $E[|\phi|]$ is better. obivously nonzero, but still
misses the point just like $\phi$\^2 misses the point.

$P(\phi|j)$ vs $P(j|\phi)$ .Hmmm. First derived entirely from dynamics.

Maybe the issue is that coincidences and miracles are likely. Any
indiviudual miracle is unlikely, so many things are consdiered miracles
than any particular one hoappeing is quite liekly. What is the
porbability that we detect light? While the inidvidual probability of
radial points might be lower than the zero point, they add up to more.
Where does the CDF = 0.5? Then yes, CDF($\phi$=0)=0.5. Well, if light
has magnitiude greater than 2.3 or something, we detect it. So what is
the porbability of detection versus not detecting. P(detect)
$=\sum P\text{(|\ensuremath{\phi}|>2.3)}$. This is compatible with the
many suns ensemble. We don't ask what they detect because then we'd be
inclined to average the result, which is a physically deceptive
procedure (its true that we may predict this value though, it just
doesn't have much meaning for each individual dude? Why?), but how many
detect. Given detection, what is probability of each individual? Doesn't
change anything much. Just zeros out undetectable regions and
renormalizes.

Sources aren't random. They are unknown. There is a disctinction. Is
this the fundamental dilemna? Random implies they had random casues
(caused by probability distrbituoin in a sense, by plucking marbles out
of a hat). Unknown implies that the effects of the sourse can't narrow
down exactly what happened. They might also have random causation in the
sense that what the sources do cannot deduce whatever made them do it.
Is all randomness deductive randomness? Does it all come from that
effects cannot completely deduce casues? use only conditional
probasbility, never unconditional =\> using cross ratios in bayes rule
to delete the unwanted probabilties. Projective porbabiltiy. So cross
ratio is not necessary to delete pure nonconditional. Only need three
variables. for cyclic rule. How do you define a distribution on
porjective plane? dsitribution has to be homogenous in coordinates

Relation to problem of why causual propagators are good and acausal are
bad physically speaking.

Possible model - gaussian source functions in sphere, evaluate green's
function on them $<\phi=Gj>=0$. could use to evaluate
$E[\phi(x_{2})|\phi(x_{1})=0]$. reevaluating gaussian puts
$e^{-(L\phi)^{2}}$ up in exponent for field inside sphere, with reast
constarined by delta functions to match implied j. So don't do that.
COnditional probabiliity puts

Classical version of one broad wavefunction versus distrbuution of many
compact wavefunctions is big gaussian versus distribution of means for
tight gaussians. Reduce to same in marginaliztion for just position,
different in joint.

Can set points equal but use E field from different sources for slit
experiments.

Four point functions can tell us the correlation of energy or power at
one point compared to the other.

All these functions can be computed assuming gaussian business just like
QFT

A general prbability distribution of EM is a probability functional of
entire field. However, this is experimentally overzealous. What is the
correct way to formulate so that the only questions that can be asked
are ones that can be measured.

Declan's problem is also related to conditionally convergent series
(which occur all over the place in diffraction. Fresnel's sum I believe
is conditionally convergent). If there are finite sources, eventually
declan runs out of canclelations. On average something like $\sqrt{N}$
of N will not have a counterpart to cancel. If you truly have a
ocntinuum/inifnity of sources, then

Part of Declan's problem is that symmettry makes you coclude that the
probability distriubtion of Etotal must be symmetric, hence the average
value is zero. However, the bulk of the prbabolity lies not at zero,
even though it is symmettric about zero.

Quantum Statistical inference
-----------------------------

Estimating the denisty matrix can be done by the following analogy to
probability distributions. You work with identically prepared density
matrices and perform a bunch of experiments on them.

$$L(\rho)=\prod<n_{i}|\rho|n_{i}>$$

Where $n_{i}$ is the observed result of the ith experiment. If $n_{i}$is
not a complete set, use a trace over the rest that you didn't observe.

I wonder if there is an equivalent of the central limit thoerem for
quantum systems. That things tend to go to coherent states. under some
loose conditions (i.e. pure energy states and super spread states are
unlikely to persist) Or that it tends to go to a denisty matrix that is
diagonalized by coehrent states?

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
spatial uncorrelated. This is better model of light bulb or blackbody.
Autocorrelation function or use power spectrum if in fourier domain. If
we assume blackbody, effective source may be determined from taking
$\square$ on equilibrium field distrubtion. Sanity check is see if we
get stefan-botlzmann law.

Each mode gets bose einstein factor of energy.

Then we use this effective j to shine the light outside box (using
surface of box only? Use blackbody correlation function as boundary
value for exterior correlation problem).

$$<jj>=\delta^{3}(x-y)A(t-t')$$

Anyhow, correlation function is essentially **$G^{T}G$** integrated in
the region with sources. Curious That is not what I expect from QFT
analogy.

Intensity is the right thing to look at because of Poynting Theorem.
Integration of poynting vector gives energy dumping. Model: Antennas
stuck in calorimeters. We measure the incoming radio waves via
thermometer.
