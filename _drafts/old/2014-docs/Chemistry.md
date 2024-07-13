chemistry is an attempt to create a hierarchy of structure on something
which is strcutreless. we break down and break down. First we understnad
aotmic strucutre. then we fuse them to create

How do you do multielectroon domain decomposotion? In what mannner do
you encode your successful solution of the previous problem. Green's
functions?

23kcal/mol = 1ev = 100 kJ/mol

1kJ/mol = 0.0104eV

Thermodynamics
==============

The chemist is king of thermodynamics. Let's give them their due. The
fuckers. The physicist and chemist share statistical mechanics.

All thoermodynamics is a fight between energy minimization and entropy
maximization. Its often not clear which should win and shifts in
parameters may change the victor. Energy miniization can be consdered a
corrolary of entropy maximization in that Energy is conserved, so its a
currency to be spent to maximize universal entropy. If the enviroment
can spend this currency more fruitfully than the system, the energy will
rush out minimizing the energy inside the system.

Calorimetry

Enthalpy

Chemical Potential -escpang potential. connection to ideal vapor
pressure. Impingment rate should be proprtional to

Batteries

phase diagrams - must be bullshit. The hard lines do not exist. Like a
diode, it is expoential depednance, which can feel and effectivly be
like a dcirete shift.so we will treat it as such, but to avoid confusion
we state from the start that there is always some vapor in equiblirum
with a solid, even if it may be stupidly low. At a certain point if we
anticipate less than a sibgle atom in vapor for a bulk solid in
equibliurm, statistical treatment becomes a questionable approach.

Effetcive pressure = fugacity

effective concentration = activity

We want to use our ideal gas and solution intituition. Hence we can
reuse the equations if we replace the ideal qauntites with effetive
quantites.

Free energy is effective energy

If the partial pressure is $\partial_{V_{i}}F=$$\frac{NkT}{V}$ for ideal
gas. Use different ensemble (grand cancnonical amost certianly

$$\Omega=fV$$

So fugacity $e^{-\beta fV}=Q$

activity is similar

### Distillation 

\- kind of cool. Like the logistic equation. Hmm. If you somehow made a
substance autodistilling, couldn't you basially get chaotic composotion
changes? Eutectic point? Criticacility.

Substances are considered more volatile or less volatile

Lower boiling point or higher boiling point. Boiling point seems to be
determined by the intermolecular interaction strength. One anticipates
that Boiling point occurs when $E_{vanderwaals}\approx k_{B}T$. The
energy scale of van der waals forces.

How much intrinsic waste is there in distillation? Porbably in principle
none, but seperation of a mixture reduces entropy of mixing, which must
be compensated by waste heat. So there is some intrinsic carnot
limitations.

solubility salt water distillation

Trouton's Rule - The entropy of vaporization. The translational entropy
of a signle molecule in liquid is roughly $k_{b}\ln a^{3}$, it is bound
in a box of roghly molecular size. Afterwards it is roughly
$k_{b}\ln V=k_{b}\ln\frac{Nk_{B}T}{P}$ where an ordinary V might b on
the order of a meter cubed. This works out to be $\sim88\frac{J}{Kmol}$.
10.5\*R

Dalton's Law - Summation of Partial Pressures. $\sum p_{i}=p$. In an
ideal gas, the molecules do not interact with each other. Hence, they
hit the walls indepdnantly and apply forces indepdnantly like two dudes
pushing on a wall. This law is sort of Netwon's force law, where you sum
the indvidual forces to get the total force. Now in more complex
solutions this may not be true.

Raoult's Law - The law of escape. Pressure is porptional to impingement
rate. In an ideal solution, the chemial species have the same
energetics. The odds of a molecule in solutoin being ejected must be the
same then. Hence the escape rate from the solution must be equal. But
the exacpe rate is also propitoal tho the porptions in the olsution.

$$z_{i}\propto x_{i}$$

$$p_{i}\propto z_{i}$$

In addition to the law of

Solubility. Solution will olnly dissolve a ertain amount of salt per
liter of water. The qauntity solubility is the maximum amount that will
dissolve This is traveling in a line across a composition diagram. The
honogenous phase at the edge, then the mixed phase lever rule region
with the saturated solution on the left and solid salt on the right. The
solubility will change with tempurature.

Henry's Law - solubility propto partial pressure. pressure

.Atomic Structure
=================

Atoms are an illusion.

Born Oppenheimer - Why the atom is even a thing. The Maxwellian velocity
of gasesous atoms

atomic transitions

Molecular Structure
===================

Molecules are an illusion

Born Oppenheimer

The bond is an illusion on top of an illusion

Ionic Covalent and in Between.

Mulliken electrongtativty - Starts at ionic bond

Pauling electronegativity - starts at covelaent bond. consider two
orbital thoeyr of bonding. for disprate atoms.

LCAO and varitaional hamitloniains

Hybrdization.
-------------

We make various seperations

Core orbitals

bonding orbitals

how do we pick?

we do block similarity transformations. To rearrange wihtin each atom

jacobi iteration. We want the good preocinditioner. some are better than
others

Molecular orbitals and the tight biding model - On our way to Band
strcture. there is a ocntnuum between the

The bond length verses energy spectrum diagram. Band crossing points are
where different bases become dominate. Gaps die and develop.

Best average basis for a regime? integration average over parameter
(bond length, etc) (hybridized, vs atomic, versus bloch ,etc)

on atomic end of dagram, atomic orbital fillng rules tell you how much
each band is occupied.

Huckel Theory

Vibrations and Rotations

Molecular Reactions
===================

Molecular reactions are friends to inelastic scattering theory, but
really they are their own thing.

Typical reaction is strctures goes to new structures + heat.

Seqeunce of Elementary reactions

Landaur Buttiker formulation? The density matrix of electrons within the
molecules wil demonstrate a steady state current flow that corresponds
to the reqction proceeding.

The calculations may be daunting, but I think the question is possible
to phrase, and the form of solutions you may want

It is a time depednant phenomenon. Two structures are borught together.
The electrons rearrange. A new strcture comes out.

Amusingly, maybe considering it to be the same as a stuctural phase
change. The elastic bond strength parameters change as the reaction
occurs. A breaking bond is when the parameter goes close enough to zero
for the thing to come apart. A bond is formed when the elastic parameter
increases from near zero or negative. Goal then is compute time denednat
elastic parameters. Some reactions will be between symettry inequivalent
molecules. Indicates Goldstone modes? Transition complex symmetry?

The bringing together is probably adiabatic. Hence we could just solve
for structure at each stage

Acids and Bases. H+ as perturbation upon atom.

Potential energy surfaces. Partial summation of partition function.
Renormalization to effective energy surface

$$e^{-\beta F(x_{nucleii})}=\int dx_{electron}e^{-\beta H}$$

We can also do it just using ground state energies of cofnigurations if
electornic degrees of freedom cannot be sufficiently excited.

For fixed positions of nucleii, we can do steepest descent. Order
parameter = internuclear distance, or ?

Saddle points are transition states. Det of hessian at that point gives
a volume factor, but that is swamped by exponential dependance.

Those activation energy diagrams aren't bullshit surprisingly. They are
weird slices out of potential energy surface.
