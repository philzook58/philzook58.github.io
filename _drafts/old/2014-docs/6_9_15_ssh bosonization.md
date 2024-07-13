SSH edge state

Basically the same as the kitaev state with relabelling?

Basically the difference between the two equivlaent ways of dimerizing.
odd-even and even-odd

Let's say the edge states are connecting two different homogoenous
regions. Then there is a band sturcture. for both. If the two different
in their dimerization quantization, then the bloch enevelope is forced
to be a sine function with the node at the edge state site

In the limit of dimers, this edge site has no matrix elements connecting
it to its neighbors at all

One topological class is adiabatieclly conneted to one dimerization, the
other the the other

If we make the system chiral, then the finite matrix becomes upper
triangular and green's function can be found in closed-ish form

If we couple to the ising model, these bound states occur whenever
$\sigma_{i}\sigma_{i+1}=-1$.

$2N_{i}=\sigma_{i}\sigma_{i+1}+1$

and $\sigma=\prod N$

The sigma live on the edges between vertices. This is looking very
similar to jordan wigner transformaiton. Is the jordan wigner
transformation what I seek? an algebraically exact transfromaiton
between bosons and fermions? I suppose that's fine it I can understand
with clarity how this turns into the bosonization model

Instead of sigma, we can consider an alternating bonds of
$\sin(\phi/2)$, $\cos(\phi/2)$. Then a change of $2\pi$ will flip which
one is the stronger one.

We can insert (hopefully) a decomposiiotn of the idneity in terms of
these phi $\int P[\phi][D\phi]$

Certianly it seems to be the case for the ising model version.

Can I connect the ising and XY model

ising and xy are connectedt o gaussian model in mean field limit.
perhaps via that

or ising with many possibility becomes potts model (grouping variables
into blocks?) which becomes xy model in limit

polarization in LLL
-------------------

The polarization Px / Py do not commute. This is inheirtted from the non
commutation of x and y when projectedt o the LLL.

The potential $\phi$ can be solved in the basis where all source
densities are wvefunction densities in the LLL.

Perhaps also the location argument of $\phi$ should be interpretted as
an operator in the LLL for a second wavefunction.

eseentially, we want to calulate the electrostatics between two
independnt LLL $\psi\otimes\psi$ which makes a lot of sense. The
electrostatics of the haldane pseudopotential.

$\phi$ at different poistions do not commute? What does this mean if
$\phi$ is an operator in this double space? To evalaulate it at the
position $P\phi P$ we use projection oeprators that place a coherent
state at z. $<\phi>$ $|\alpha>|\psi>$.

We can trace out one of the wavefunctions $Tr_{1}G\rho_{1}=\phi_{2}$

$TrG\rho_{1}\otimes\rho_{2}=E$

Since coherent states can overlap, this projection will commute for far
away states, but will not for nearby
states.$[P_{\alpha}\phi P_{\alpha},P_{\beta}\phi P_{\beta}]\ne0$

Will "carrying" phi around do anything interesting? Surface integral
$\int\partial_{n}\phi=Q$. $\int d\alpha TrP_{\alpha}\phi P_{\alpha}=Q$
something like this. Or without the trace gives the Q operator.

$e^{iaY}$ as an X transport operator. Make integratio loops using these

what "differential equation" should phi solve?

$\partial_{y}\phi=[X,\phi]=P_{y}$

Green's thoerem? What differential euqaiton should G solve. G lives as
operator in the doubled space, $\phi$ lives in only one space, so does
$\rho$

How to put this on a lattice?

self interaction removed if double space is fermionic (anitsymmettric).

Does the laplacian have a convenitent form?$[X,[X,]]+[Y,[Y,]]$

$G=\ln Z\bar{Z}$

$G=\ln(z_{1}-z_{2})+\ln(\partial_{1}-\partial_{2})$

$G=\ln(\partial_{1}-\partial_{2})(z_{1}-z_{2})$
