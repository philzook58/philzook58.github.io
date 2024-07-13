Bosons: clump, phase, helium 4, superfluidity, bose einstein condensate,
bose einstein statistics, wavelike, symmettric, integer spin, photons,
phonons, commuting fields, all in same wavefunction sometimes

Fermions: avoid each other, fermi sphere, all in different wavefunction,
fermi pressure, antisymmettric, half integer spin, particle-like,
electrons, anticommuting fields, grassmann,

Models
------

### Parameter model

### Dijkgraaf witten / torix code

### Chern-Simons Higgs

Chern simons terms bind flux to charge

quantization requires integer coefficients

All in all, higgs terns tend to make the thoery tractable

### bull

Conjectures:

Independant particles still seem correlated due to slater determinants.
Exchange holes and surpluses.

Define a Slater Cumulant that clearly shows that Slater states are as
independant as possible.

$\rho_{1}$=\> $\rho_{2}-\rho_{1}\rho_{1}$

$<x^{n}>$, $|<a|x^{n}|b>|^{2}$ any higher moment can be expanded in
terms of moment and exchange moment

Higher exhange moments for not quite slater states $<ab|x_{a}x_{c}|cd>$

Continuation to Free cumulants. Expansion is over all non crossing
partitions.

Direct Product, Free Product. Amalgamation. Direct Product Quotient
Subgroup

We can build composite fermion and boson states of N particles by just
multplying the two indvidual wavefunctions of particles m and N-m
together and summing up the N choose m permutations with appropriate
signs. This is significantly less than the N! terms in a full slater
determinant, which we could get at by recursively adding one more
particle.

$$\sum(\pm1)^{P}P\psi_{m}(x_{1},...,x_{m})\psi_{N-m}(x_{m+1},...x_{N})$$

$$\left(\begin{array}{c}
N\\
N-1
\end{array}\right)\left(\begin{array}{c}
N-1\\
N-2
\end{array}\right)\left(\begin{array}{c}
N-2\\
N-3
\end{array}\right)...\left(\begin{array}{c}
2\\
1
\end{array}\right)=N!$$

Making hole states is way easier

$$\int dx_{1}...dx_{m}\psi_{m}^{\dagger}\psi_{N+m}$$

Is this correct? Might be wrong.

In principle you could do the same thing, making a sum of all possible
integration and swapping, but what is left already has the requisite
symmettry.

Monopole. Two ways to evaluate your berry phase from adiabvtic transport
around a loop around the monopole. You get the flux from above or below
halves of the sphere. But these two halves must

Borrow a little quantum "energy" (perturb hamiltonian a tad). like two
fields borrow a little thermal energy

Consider Non-abelian gauge fields as berry phase of degenrate subspaces.
Then this adiabiatic picture makes more sense. Conjugacy classes of
Homotopy group

Intro
-----

Flux Charge Composite
---------------------

Charge glued to outside of flux. When its rotated, phase is increased
due to : AB phase, orbital angular momentum of particle and spin of
particle.

Roating generates the AB phase, so total angular momentum must add up
such that multiplying it by 2pi give an integer plus the AB phase amount

The eigenvalues of angular momentum are the phases by which a

In Wilczek He meantions that this non integer angular momentum is
compensated by the eventualy return of magnetic flux cross the electric
field of the particle, so universally angular momentum is not off.
Construction of the system must not Ruin the law of angular momentum
conservation.

Here we first encounter superselection: Symmettries so complete that NO
physical obervable can change it. No physical observables can see
interference between states. All are diagonal with respect to certain
conceptd

Spin and Statistics
-------------------

An exhange involves two halves of a rotation. One particle travels
halfway around the others flux and the other particle travels halfway
around A's flux. Hence we get the net phase from a complete travel
around a flux $e^{i\theta}$

The Braiding diagrams: Up is time, in and out of the page and left and
right are the 2d space. However, these conventions aren't that
important, as we have a weird kind of relativity going on where time
isn't all that different from space.

Combining Anyons
----------------

Each charge in a cluster gets 1 AB phase from each flux in the other
cluster leading to total exchange phase of
$n^{2}\theta=2n^{2}\frac{\theta}{2}$

Conclusion = we can get a boson out of two particles with exchange phase
i, -1, -i, 1.

We can get fermions out of $e^{i}$

Unitary Representations of the Braid Group
------------------------------------------

Exchanges can get twisted up in each other

The Braid Group is infnite, its memebers being listable I think? On two
strings its isomorphic to Z. On Three, god, I don't know. Name another
countable Inifnite nonableian group. Apparently it is the knot group
(the fundamental group of R3 with the knot romovoed) of the trefoil
knot.

Representations of inifnite groups?

Consider the location of a particle to be a puncture in the space, a
pole that strings can get tied up on.

$\sigma_{j}$ counterclockkwise exachnages particles j and j+1, the
inverse exchanges them clockwise

If two strands are not next to each other, their exchange commutes

The Yang Baxter is a mysterious beast. It shows up in integrable systems
and solvable models. Its equivlaent to the third redimeister move of
sliding a string underneath a crossing.

One dimensional abelian reps. each sigma gets a phase. Yang baxter
implies phases are all the same

GOAL: COnstruct irredicuble representations of braid group.

Image of representation may be dense. Since there are a ton of these
group elements, why not.

Topological Degeneracy
----------------------

Topological Degeneracy is met in Berry phase situations, where
encircling the degeneracy point results in nontrivial phase, proving
that the degeneracy exists.

The Torus Degeneracy.

There is a vacuum state

First off, we're working with curves in 2+1 space time.

The clean way to deal with a torus is to imagine a rectangulaar box with
time going upwards (See Wen)

Detecting degeneracy: Find a state

When operators commute they either have the same eigenvectors or they
have degenerate eigenvalues that mesh.

Ladder operators.

Suppose

Toric Code revisited
--------------------

Skip

Nonabelian Aharonohv Bohm
-------------------------

The loop transport matrix has eigenvalues with meaning, but only up to
similarioty due to different deficintions (choice of basis) or charge

FLUX takes group memeber values

Charge are unitary irredducible representations? Does this mean charge
are vectors in that space or matrices?

The suppoesed group of EM is U(1)

The $e^{i\theta}$ is a irreducible rep of that group

Going around a flux gives matrix corresponding to that gorup menber

Conjugacy classes have meaning only because if we started with a
different initial basis that shouldn't matter (initial phase doesn't
matter for EM abelian case), but you get at the different initial basis
by multiplying by the rep of a group member

flux Members of a conjugacy class are indistinguishable in that they can
not be defintively said to be a particular member. They may flip between
diffetent membersi n the class though. Conjugation by a group element is
what happens when they are exchanged.

Braiding of Nonableian Fluxons
------------------------------

Exchange is given by flipping the gorup assinments and conjugating one
by the other.

Fluxes are assigned conjugacy classes. Exchange conjugates them

There is always a trivial charge. (Corresponding to a trivial
representation). Wrpaping flux around it does nothing, not even a phase.
The trivial rep is just multplying by 1. This charge is made by
symmettrically summing over all elements in a conjugacy class (since
wrapping conjugates, an a conjugacy class s closed underconjugation)

Electromagnetic charge is a nontrivial 1-d representation of U(1)?

Charges can be made out of two inverse fluxes. Charge is associated with
irreducible representations. This is a statement that I barely
understand

when wrapped by a flux, charges arwe acted on by a representation of
that flux

Superslection sectors
---------------------

Particle Types or labels

We' e been considering pure charge and pure flux objects, but now we
want composites

Anyon Models Generalized
------------------------

Fusion rules list the combinatorics of generating c from b and a. In

The numbers are similar to decomposition of tensor porducts into
irreducible subchunks you see in spin combinations

unique conjugate that can fuse to give the trivial

rational - combinations of anyons are a finite list
