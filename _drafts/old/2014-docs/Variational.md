The Variational Method
======================

Variational methods are more trustworthy. It always does the very best
it can and will rarely blow up in your face.

Variational Solutions
---------------------

Parametized possible solutions. If linear then essentially glaerkin
methods and such. Chunkified vector spaces. Nonlinear can do interesting
things. Vector space concept becomes somewhat irrelevant

Born Oppenheimer: Solutions with delta functions for nuclei. Pair
potentials and cluster potentials? Adiabatic in some sense. Once we're
done is the effective potenytial still goood for schordinger eqution. Do
we have all the matrix elements? Partial trace of partition integral
over electronic degrees of freedom. Kind of like doing the dynamics of a
gas and piston.

Hartree - Assume seperable. Kronecker product

Hartree-Fock. Assume antisymmettric seperable

Is it possible to assume pair correlated Hartree (Some kind of
symmettric sum)? Pair correlated hartree fock? Cluster solutions

How to improve variational solutions systematically. Evaluate our
variationally smallest. Then Start functional power series of
improvements if we're close

$\psi+\delta\psi$. Iterater like newton's method.

As close to an eigenfunction as possible? Local minima of the quantity

$$(\psi-E\psi)^{2}$$

Use pseudo spectra like function

SOmehow Glaerkin does a good job of this but traditional cairational
doesn't

Equivlaent of charesteristic polynomial for varriational space?
resultant? trace - Integrate over all possible parameters. pseudo
spectra. Find Local maxima (or level curves) of resultant.

Effective Potentials
--------------------

Can partially minimize and leave other parts as free paraters. This is a
mixed method. Could be viewed as vaiational in some parts of the vector
sdpace, but complete in others. After partial minimzation.

Gibbs Principle - can create new degrees of freedom that effectivize to
real potentials. Stability conditions?

Bohm-Pines Splint degrees of freddom ,but then extend vector space -
Effective particles. RPA

Elimination/Presolving degrees of freedom (again born oppenheimer
presolve electronic, effective mass, etc)

Synthesis of degrees of freddom

Variational Hamiltonians
------------------------

Fitting parameters to data.

Least squares Hamiltonian

$\min tr(H-H(g))^{2}$

Actually most important that it gets ground state ( and low states)
right rather than everything

$<0|(H-H(g))^{2}|0>$

$\min tr(H-H(g))^{-2}$

$\min tr(G-G(g))^{2}$

Varitional calculations of partition functions

Perturbation and Variational
----------------------------

Could minimize to degree of approximation. ASympotitc sequence of
variational somultions. Different orders will not in general decouple
nicely like traditional perturbation theory.

Ladder Diagrams

Ring Diagrams
