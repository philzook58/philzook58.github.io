There are three aspects to consider: Observability, Controllability, and
Predictability. Given the Helmholtz equation, what is out ability to
observe source terms, predict future solutions, and control the field
values externally.

If I work with the full time dependant wave equation, I can use control
theory. The internals of the system are hidden state. External sources
control and external field observation.

To consider physical noise, we could use thermal johnson/blackbody or we
could use quantum zero point or otherwise.

To join an antenna to an electrical circuit, you have to include the
circuit as a driving term. You need to solve the antenna for all kinds
of boundary conditions, because you need to be able to construct the off
diagonal matrices. The antenna and the driving circuit are not spearate
systems. They effect each other. So you'll need

Its easier to say residuals get smaller than to say the solutions
converge, because residuals are easy to claculate. That's what this
energy norm thing is about

### Diodes

Before understanding transistors, we should understand a simpler device,
the diode.

A perfect rectifier could be placed between the two wires of a
transmission line. The transmission line possess thermal energy in each
of its fundamental freqeuncies.

$$E(\omega)=\frac{\hbar\omega}{1-e^{\frac{\hbar\omega}{k_{B}T}}}$$

$$\omega=\frac{n\pi c}{L}$$

However, a diode could connect two lines to each other or

A perfect rectifier would build up all the charge on one. We could then
disconnect the diode and connect a load to extract work.

How many energy and spatial states qwould I need to get the qulaitative
features of the diode right in a quantum matrix model.

The beat equation

$$\cos\theta\cos\phi=\frac{1}{2}(\cos(\theta-\phi)-\cos(\theta+\phi))$$

Is of vital importance.

$$I=I_{S}(e^{-\frac{V}{V_{T}}}-1)$$

Expanding to second order

$$I=I_{S}(-\frac{V}{V_{T}}+\frac{1}{2}(\frac{V}{V_{T}})^{2})$$

When we square the signal voltage, we create the two beats, one at
$(\omega_{c}+\omega_{s})-(\omega_{c}-\omega_{s})$ and one at
$(\omega_{c}+\omega_{s})+(\omega_{c}-\omega_{s})$ . The quartic term is
the first one that gives you the freqeuncies you need I guess.

Wait\... Is this the DFT? or rather DCT? The ampltiude mudlation process
is like forward transform (Signal times different exponential, Sum up in
same field), rectification is like backwards transform.

The phase detector. If you have them lined up right, the chopping will
act as a perfect rectifier. If you have them lined up wrong, chopping
will just make an f-ed up chopped sine wave. Low pass the result and
you've got

In the freqeuncy domain, this becomes a convolution equation. A cosine
is two delta functions, on at $\omega$ and one at $-\omega$. Convolution
with a delta function shifts.

### Cause and Effect

Cause and Effect in circuits. Difficult. However time inequlaities are
easier. There is often a useful idea of effective cause and effect. if
cause is way up chain from effect, or if two cuases from same effect.

cross-correlation - Energy in past minus power in future. Possibly
weighted by time from synchronized. The voltage in a rightward moving
wave. The left vltage will cause the right voltage.

This seems insufficient. Dleyaed effect from same source would regiater
as cause effect.

Fourth order expression using past A, past B, future A, future B

Should gaussians be capable of exhibitting cause and effect?

Better yet, how to determine cause effect directed graph, chain, tree.

Or relatedly, cross-infromation Given past of one, how much information
about future of other. Statistical hypthesis is time ordering of events.

Cause and effect, given past of one, how much infromation of the other -
the self infromation of the other's past on its future

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B})$$

Prediction gain

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B, Past A})$$

Back to my condition number conjecture

$$H(\text{Future B}|\text{Past A})-H(\text{Past A}|\text{Future B})$$

Since cause effect can only go one way, a number that is highly negative
or positive for likely cause effect relationship (like correlation in
this way).

$$H(\text{Future B}|\text{Past A})-H(\text{Future B}|\text{Past B, Past A})-(H(\text{Future A}|\text{Past B})-H(\text{Future A}|\text{Past B, Past A}))$$

Correlation does not imply causation, because this is a higher order
effect. Fourth order maybe? The question is if correlation does not
imply causation, what does?

Cause and Effect are not in the domain of logic. They are intuitive
ideas, inductive ideas.

Stiffness of cause from effect.

TIme domain. The start up properties of a circuit are often irrelevant
to most of its operation, and much startup is almost instanteanous.

Transmission Line has wavetrains. Transmission line feedback into
op-amp. Model as delay element dt in feedback loop. Cannot count on dt
as a paramter though, can only count to be small.

$$V_{n+1}=GV_{i}+FV_{n}$$

Big gain of op-amp means that G and F are huge

Geometric Series

$$V_{\infty}=\frac{GV_{i}}{1-F}$$

Convergence if $|F|<1$. Does that matter? Evidently not. Which means our
model is not so good. The wild oscillations caused by non convergence
get damped by a averaging or low pass properties f the circuit.

Negative feedback is somewhat reminscent of rejection sampling methods.
We make huge gain with weird proeprties but then accept only a small
amount of it, in order to approach whatever ideal gain we wanted.

Does voltage cause current? NOt in all cases, but It seems more likely
in many. Maybe a linear combination of voltage and current is real
input, which is approximately just one are the other in certain cases.

Transistor, Vbe causes Ic and causes Ib.
