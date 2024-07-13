A Green's function requires a field.

Classical
=========

The faces of Green's functions. Let us start with the classical

The Inverse: 
------------

First introduction. Think electrostatics.
$G=\sum\frac{1}{\lambda_{n}}|n><n|$. $\frac{1}{r}$

The freqeuncy domain inverse. 
-----------------------------

If we work with a time depednant problem, it often is time translation
invariant (no explicit occurence of the vairable t, only time
derivatives). In which case the logical thing to do . An exmaple is
string movement, or the kirkhoff $\frac{e^{ikR}}{R}$

Double poles = rates. Because bring down an extra t by differentiating
the epnonetial factor

Laplace versus Fourier

The Resultant aka the pole grabber
----------------------------------

The pole is the complex analysts delta function (The two are small
maniuplations away from each other). Projection operators can be formed
for energy subspaces.

$$P_{C}=\oint_{C}\frac{d\lambda}{H-\lambda}$$

The Resultant trace as a generating function

$$Tr(H-\lambda)^{-1}=\sum_{n}\frac{1}{E_{n}-\lambda}$$

The quantum green's functions
=============================

The Evolution operator $e^{-iHt}$
---------------------------------

The frequency domain evolution operator $\frac{1}{H-\omega}=\frac{1}{H-i\partial_{t}}$
--------------------------------------------------------------------------------------

The QFT Green's function $<\Omega|\psi^{\dagger}\psi|\Omega>$
-------------------------------------------------------------

Pulling particles out of the field.

The Finer points and Topics
===========================

Hermitian versus non hermitian. 
-------------------------------

Non-Hermitian is really a superset of hermitian. Anything that works for
nonhemeritian will work for hermitian, altough it moight be a somewhat
degenreate case. From the beginning any contour integral based methods
HAVE to be considered in a nonhermitian context, because there is no
freakin way that an analytic matrix function of a parameter can stay
hermitian on the entire domain of the contour

Boundary Conditions
-------------------

Time ordered, Normal Ordered, $i\epsilon$,Retarded and Advanced
---------------------------------------------------------------

Retarded is radiatation boundary conditions. Advanced is absorbtion
boundary conditions. How is it possible to have complete absportion in
an energy/probability conserving system? The key is impedance matching
and chopped domain. The energy has a secret siphon somwhere inside

THE IMPEDANCE or The Dirichlet Neumann Operator
-----------------------------------------------

One way of looking at Capacitance

The impedance has recprocity for thermal motion (The fluctuation
dissipation theorem). In equibrium a system squirts in as much as out.
Generalized Johnson Noise.

Domain Decomposition
--------------------

The main Physical Intepretations of Green's functions or functions
closely related

1.  The Correlation matrix (denisty matrix). Using the pole grabber, we
    can construct

2.  The autocorrelation function

3.  The source response function

4.  The boundary value response

The Density of states
---------------------

1.  The Scattering Matrix

2.  The Current Matrix

3.  Probability transfer - Markov Chains Not the green's function
    exxactly but has the right flavor
