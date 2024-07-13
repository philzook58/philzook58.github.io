The Disitinction between Fraunhofer and Fresnel Diffraction: HOW THE HELL DID WE DIFFRACT OFF OF A PENNY
--------------------------------------------------------------------------------------------------------

The two are not at odds with an underlying wave equation. However, I am
inclined to say they are distinct thoeries of the interference and
diffraction effects in that the intuition and methods do not particular
intersect other than a general sense of waviness makes wavy patterns on
screens.

Almost the exlusion, most of our time and intuition is buuilt upon the
thoery of Fraunhoffer or far field wave stuff. This is the theory of
double slits, single slits and fourier optics.

Let's list the dimensional quantities

$d$= source to screen distance

s = source to onjects distance (which will often assumed to be inifnite
for simpilicity. What baout vice versa? Fraunhoffer dffraction finite
close up sources)

x = object size

y = fringe size

$\lambda=wavelength$

The laws of phsyics are dimensionally consistent.

a = size of source

Apriori What can we say about these sizes?

Reciprocity says that exchangeing (d,y) and (a,s) must be equilvaent.

etendue connection between: source object, object screen, source screen.

### Fraunhofer

The fundamental relation of Fraunhofer diffraction is the Heisenberg
uncertatiny relation $\Delta x\Delta k_{x}\approx1$. Since $c|k|=\omega$
$k_{x}$ is really a standin in for the uncertainty of direction of the
ensuing beam.

Geometrical optics possesses absolutely not features of frunahofer
diffraction other that

A rearrangement of that

In taking the screen so far away, we insist that the thoeyr can only use
the ratio y/d, i.e. the angle from the object. We also are assuming that
the source is planar - inifnitely far away, so that it cannot appear in
the theory. (Is this true? The thoery of coherence might have something
to say about that)

Fraunshofer is squeeze dominated. Heisenberg uncertainty dominated.

The further the screen is away, the larger the pattern appears in the
intuitive manner of similar triangles. The distance between two peaks on
the diffraction pattern is proprtional to the distance the screen is
away from scattering object.

In a very restricted closeminded Hypoethetical sense, we could see
diffraction for very large objects. However, we'd need very long screen
distances to blow up the tight pattern. The reality upon further thought
is that we'll never see it. Coherence. Control of the object to the
order of a wavelength

The quantum mechanical analogy, Fraunhofer diffraction is the long time
limit for free partciles where the momentum compenents have sperated
themselves out.

### Fresnel

The fundamental notion is that of the Fresnel zone. The radius of the
nth zone is $r_{n}=\sqrt{n\lambda f}$. Where
$\frac{1}{f}=\frac{1}{d}+\frac{1}{s}$. d and s are the distance from the
source to the object and object to screen repsectively.

Analsyis of fresnel diffraction often relies on paraxial approximations
as clutch compoents.

What You need to remeber is $x\approx\sqrt{\lambda d}$. This means you
can compensate for large objects and small wavelengths by having large
distances.

This is backawats from the question we want to ask. We always want y
really. As a funnction of the rest.

You want to conisder a rotation of the object (about the source?) rather
than moving the screen point. The two are roughly equivlent? Fource
inifnitely far source, roatiion of the object is translation. The object
is then not center in the 0th fresnel zone. It's center in the higher
frsenel zone. As you cut higher fresnel zones, the cutting becomes
quicker. The width of frsensel zones decreases.

Fresnel is Geometry dominated? Fresnel is the wave corrections to images
and shadows.

In the qauntum mechanical analogy where initial position and velcoity
mix.

The Kirkhoff-Huygens integral
-----------------------------

How do we connect the intuitive idea of Huygens principle with the
calculus of the Wave eqution?

Green's Identity is a fancy version of integrating by parts.

$$\nabla^{2}(\psi\phi)=\phi\nabla^{2}\psi+\psi\nabla^{2}\phi+2\nabla\phi\cdot\nabla\psi$$

$$\nabla\cdot(\psi\nabla\phi)=\psi\nabla^{2}\phi+\nabla\phi\cdot\nabla\psi$$

$$\int\psi\nabla^{2}\phi+\nabla\phi\cdot\nabla\psi dV=\int\psi\nabla\phi\cdot dS$$

or we can subtract off the opptosite idneity

$$\int\psi\Delta\phi-\phi\Delta\psi dV=\int\psi\partial_{n}\phi-\phi\partial_{n}\psi dS$$

The Green's function for the Helmholtz eqution $\nabla^{2}+k^{2}=0$ is

$$\frac{e^{ikr}}{4\pi r}$$

Notice in the limit that k=0 that this reduces to the coulomb potential
and the laplace operator. That's how you can know the $4\pi$
normalization. Except at the origin you can explicity check that this
satisfies the helmholtzx equation

Cohering White Light
--------------------

The incoherent superposition of the different pieces of the source. Two
pieces of source that are within a fresnel zone repositioning are
spatial coherent.

Coherence
---------

Coherence time as width of power spectrum: Is this true? I believe so.
We can fourier transform back to get the Autocorrelation function.

What is the difference between blackbody radiation and a set of lasers
superposing on each other In the same kinds of proportions? The power
spectrums, (by design) would look Identical, whereas the interference
and diffraction patterns they are capable of seem quite different. Wait.
Maybe that many lasers WOULD look incoherent? As the width between
lasers beomces smaller than laser linewidth. Hmm.

Sodium lamp - coherence - 0.59mm. So that's doable. Maybe

Blackbody - 100um.

Coherence area?

The different models: Perfectly in phase all over source. Perfectly
sinusoidal, but out of sync (pretty non physical. Could be achieved by
seperate lasers taken as a signle source). The point temporally
incoherent source. The point source with many perfectly coherent
freqeuncies in it. Somehow Number of frequencies becomes a problem?
Essentially this is every combo of spatial and temporal incoherence.

Is the incoherent pattern just a blurred PSF? ONLY for model 2, the
arcane one. This is what happens if I have two different colored lasers
for example

What does the waveform coming out of the sun look like?

Does a red filter improve the coherence time?

Why does infrared not screw if its always there and coming in on the
same field?

Coherence zone: The area within a single point will act coherently.
Analogous to the fresnel zone replacing $\lambda$ with $c\tau$

Coherence area: what was that about?
