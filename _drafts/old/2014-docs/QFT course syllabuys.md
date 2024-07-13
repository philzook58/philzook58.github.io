Classical Analogies: Particle Lagrangian, Eulerian Denisty,
classical/quantum

Annihilation and Creation: How you count

Random Variables and Random Fields: The Meaning of Correlation

Phonons

Putting Things on a grid: Functional Methods

The Path Integral and Interaction Picture. Time Ordering?

Linear Algebra: Blocks, Kronecker Products, Schur Complements. Low Rank
Update (Rayleigh Scattering, Anderson, RPA), Nonhermiticty.

Random QFT - Anderson etc. Incoherence.

Effective Physics

The Graphs and Tensor Multiplication . The Oscillator in graphs. Spin in
graphs.

The One particle picture and Vartiational Methods (They aren't just for
the ground state! Linear and Nonlinear. Variational Hamiltonians. )

The $i\epsilon$ and Impedance - The S-Matrix - Open Systems and
Reservoirs

Distinguishable, Bosons and Fermions - Effective Statistics - Clusters
and Superconductivity - Slater Determinants - Exchange Integrals

The Many Snarling Faces of Green's Functions - Density of States

The Many Snarling Faces of Renormalization - Scale Invariant Statistics.
Coarsening transfromations.

Partial Waves, Friedel Sum Rule.

Fermi Liquid Theory

Collective oscillations

Symmettry

Bloch Waves

Composite particles

What is a Quantum Field? What is a Statistical Field?
=====================================================

Density Matrix and Distributions
--------------------------------

The wavefunction is a lie.

Well, the wavefunction is a white lie.

A man hears aout all these phenomenal intererence experiments. He takes
two slits out into the sun. He is vastly disapppointed.

While at the core, we believe there are wvafunctions controlling all of
this, it idealizes the situation considerably.

Random Variables and Heisenberg operators, c-numbers

The Schrodinger Heisenberg and Interaction pictures

Density Matrix and Probability Distribution

Given a wavefuction, we can assign quantum probabilities of occurrences.

$Prob(x|\psi)=|\psi(x)|^{2}$

$Prob(\uparrow|\psi)=|<\uparrow|\psi>|^{2}$

$Prob(x|\psi)Prob(\psi)=P$

An assortment of spin 1/2. What answers do we get?

A reduced kron system. What do we get?

Alternative to Density Matrix: The Random Variable Wavefunction - The
Statistical Field

The classical Density matrix - The correlation function.

Wigner Quasi-probability

The Quantum Field.

(This is Kubo talk)

Canonical Ensemble Density Matrix

When to take Expectation: AT THE END.

Open Systems 
============

Open systems behave qualitiatively like disspative classical systems.
The ability of particlex to leave the system and possible coupling with
inifnite envornment leads to decay and broadening of the energy spectrum
from the discrete lines to lumps. Mathematically, the big thing to be
aware is that hamiltonians are no longer hermitian

Impedance
---------

Impedance is a concept used in many fields. The most prominent is that
of electrical circuits, but it can also be used in networks of balls and
springs and rotors and acoustics and optics. The big picture concept of
impedance is the ability to black box.

Annihilation and Creation
-------------------------

Relativistic quantum field thoery can introduce annihilation and
creation operators to insert or destro yparticles in a system qwuite
naturally. That fits to all appearancex the events that are occurring.
However, in a solid state systems, nucleii and electrons and such are
NEVER destroyed and always conserved. While we may introduce the
annihilation and creation opearators as a mere formal bookkeeping device
(mostly for the peurposes of mainitaining fermuion or boson statistics,
which are somewhat of a bear in the wavefunction langauge), it is more
pleasant to intrduce them from a natrual and physical perspecive.

An empty system is given by $|0>$

The system with one particle in it is $a_{k}^{\dagger}|0>=|k>$. We may
construct states that have one particle in any wavefunction we like.

The ocunting operator $N=\sum_{k}a_{k}^{\dagger}a_{k}$

Linear Algebra
==============

The tabulated function. By sampling values of a function we can create a
list of tabulated values. It makes sense to think of this as a column
vector filled with our tabulated values in order.

We can also consider more abstract qunatum systems such as spin.

Schur Complement

Non-Hermitian Operators

Low rank update

Kronecker Product and Block Matrices
------------------------------------

Insreatd of a matrix with number entires, we can consider a matrix with
matrix enetries.

$$\left[\begin{array}{cc}
A & B\\
C & D
\end{array}\right]\left[\begin{array}{cc}
E & F\\
G & H
\end{array}\right]=\left[\begin{array}{cc}
AE+BG & AF+BH\\
CE+DG & CF+DH
\end{array}\right]$$

We can infact consider any matrix to be such a matrix. This way of
thinking is powerful. Conceptually it allows us to consder subspaces in
a more high level wayt. For example we could use the left side of a box
and the right side of a box as different disjoint subspaces. Then A and
D and transfromations within those susbpaces and B and C are
trasferrances between subspaces. In computation it leads naturally to
divide an conquer methods. If we can find a way to do operations in
block matrix form, we

In the continuous case when we're working with polynomial functions, it
is trivial to create functions on 2d domains from functions on 1d
domains. Same goes for partial deriatives. The rules are that you just
ignore

Now from 2 tabulated lists $g_{i}$ and $f_{j}$ how do we create a new
list that has a natrual two index scturucte and in some sense the
equvalent of $g(x)f(y)$?

The answer is the kroncker product

How do we write two indepdnant operations occurring in parrallel on the
new ocmbined

How do we inject operations we had before into this new knrocker sized
product space.

Can vectors always be written as a kroonecker porduct. NO.

Discrete Schordinger and Tight Binding
--------------------------------------

QFT and the Wavefunction
========================

The roots of Quantum mechanics comes from more than one direction, but
the Schordinger wavefunction language is such a raging success because
it is highly visual and intuitive. For this reason as well, it is almost
universally where budding young quantum mechanicists get their teeth
cut.

The algebraic methods of quantums mechanics formally manipulating
commutators and operators in ultimately more powerful as a calulcational
tool and any situation of many body level complexity basically requires
its careful andf mechanical use to perform a calculation. Nevertheless
you probably do not undertsnad what you are doing if you cannot
transfrom your manipulations from the annihilation and creation
operators and green's function langauge into the more elementary forms.

Here's some handy charts

$$a_{k}^{\dagger}|0>\Leftrightarrow\psi_{k}(x)$$

$$a_{k'}^{\dagger}a_{k}^{\dagger}|0>\Leftrightarrow\frac{1}{\sqrt{2!}}(\psi_{k'}(x_{1})\psi_{k}(x_{2})\pm\psi_{k}(x_{1})\psi_{k'}(x_{2}))$$

$$\prod_{k}a_{k}^{\dagger}|0>=\text{Slater Determinant or Fully Symmettric Sum}$$

i.e. A function that can be written

Be aware that all antisymmettric functions are written in terms of
single Slater determinants.

### Converting Operators

$\psi^{\dagger}(x)\psi(x)$

### Example: Hartree Fock in QFT language

The Hartree Fock equartions can be found using the variational ansatz
that the ground state can be written as a single slater detemrinaqnt of
unspecified functions

$$|HF>=\prod_{n}\int dk\psi_{n}(k)a_{k}^{\dagger}|0>$$

Fun Perturbations to make on wavefunctions
------------------------------------------

Quasiparticles and collective excitations in both languages.

Zen koan: What is the sound of a molecule?

The oscillatory enevlope. Modulation of the ground state Thisi s the
equvilaent of sound waves in a fluid

$(1+\sum_{k}a_{k}e^{\sum ikx})\psi(\{x\})$

Multi-plasmon

$(1+\sum_{k}a_{k}e^{\sum ikx})\psi(\{x\})$

The added particle

$$\sum_{P}(-1)^{P}P\phi(x_{N+1})\psi(\{x\})$$

The subtraction

$$\sum_{P}P\int dx_{N}\phi^{\dagger}(x_{N})\psi(\{x\})$$

The Diagram and Time Dependant Perturbation Theory
==================================================

Matrix multiplication as a diagram. A line has two ends and a matrix has
two indices. We indeitify an end of a line with one index. The we can
start to write out matrix operations. A loop is a trace.

Born Series

Kornecker product can be repsresented by two lines side by side.

Einstein convention and tensors. Now we can have more complicated
objects that

Antisymmstrization/symmetrization vertices.

Penrose notation.

Circuits.

The Power Method and $i\epsilon$

Kinetic Theory
==============

The impingement rate z

The ideal gas

Boltzmann Transport
-------------------

Kubo and Polarization
---------------------

The first order pertubration of an atom gives dipole in response to
electric field term in hamiltonian. Kubo formalism is spiritual
extension of this. Use time depedant pertubraiton theory to find
perturbation of thermal equiblirum distribution function. Then use this
small variation. Quite similar to Boltzmann Transport in the end of the
day.

NEGF
----

Fermi Liquid Theory
-------------------

The Path Integral
=================
