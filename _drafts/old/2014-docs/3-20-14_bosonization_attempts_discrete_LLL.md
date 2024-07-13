I attempted a program of considering bosonization as destorying and
creating an electron shold be roughly equivalent to sliding a section of
the background between them. The sliding operator consists of a sum of
products of dsteroying a configuration and then creating the same
configuration slid over. I now htink that this description is uncrorect.
The picture I drew was of a uniform density. Sliding that over is the
same as making lumps. However, the quantum gas is more like a randomn
smattering of particles. Sliding these random smatterings over doesn't
seem like the same as guaranteeing a particle inserted at a spot except
in some rough average sense maybe.

Attemps were also made to cutoff the spectrum of bosonization to make it
finite. cutting off k specturm is same as discretizein in real space. It
seems reasonable we could speak of the operators
$\sum_{m}c_{k+mN}^{\dagger}$ as some kind of stand in. Couldn't find an
exact correspondence that makes a form of $c^{\dagger}c$ seem like a
bosonic creation and asnnihilation operator. The derivation of this in
von delft is very suspicious, seemingly requiring some finicky normal
ordering and inifte specturm. In the satial basis, $c^{\dagger}c$
commute with each other at different sites. Forueir transfroming does
not fix this. Perhaps point split form of density is needed, or perhaps
a truncated form on k-space that doesn't allow the excitation to wrap
around the brillouin zone.
$b_{q}=\sum_{k=0}^{N-q}c_{k}^{\dagger}c_{k+q}$,
$b^{\dagger}=\sum_{k=0}^{N-q}c_{k+q}^{\dagger}c_{k}$. This form doesn't
seem sufficient to really fix.

The half filled finite fermi gas. We can use shannon sampling thoerem
thinking to sepeate k space into fast and slow. Then using a sinc like
basis, we can trasnfrom into a spatial basis that is mostly centralized
around every other inidivdual site. Then ground state can be written
$\prod c_{iS}^{\dagger}|0>$ with product over every other site and just
sticking to slow variables. Normal ordering is easy. For slow variables,
put creation operastors on right, for fast put creation on left.

A lot of the torublesome and weird integrals in bosonization also occur
if one attemppt to do electrostatics in 1/2 D using foureir transforms
instead of gausses law. The integrals suck because logarithm explodes.

It is interesting that a charged sheet

Discrete LLL
------------

Straight model. $c_{x}^{\dagger}=\sum c_{y}^{\dagger}e^{ixy}$ Take the
\[x,y\]=\[q,p\] analogy seriously. Then we can immediately write down
the connection between pure x and y states. They are fourier transforms.
Hamiltonians can be written using wigner quasidistrubtion
$\sum_{xy}V\rho=\sum_{xy}V(x,y)c_{y}^{\dagger}c_{x}e^{-ixy}+c.c.$

A gauge thoery working at the same level could be quite interesting.
We'd have the x and y ness blurred out. The grid only exists at a blurry
magnetic length scale. Chern simons transformation restricted to LLL.

Maybe the pure-x gauge state currepsonds to the loop integral going all
the way around the torus.

Forueir transforming and duality seem like they should mix in a fun way.
Ghostly duality

A charged sheet has a potential that seems similar to what appears in
bosoinzation. Its string-like. a pure x state in landau gauge would have
a polarization that would look like this, but a more lumpy state would
have a polarization more like 2d electrostatics.

discrete Coherent states seem to be too sticky to use.

Discrete SHO = $\Delta^{2}+\sin(x)$. equivalent to harper's equation
(apparently is chaotic? torus leads to chaotic motion in sense that path
can densely pack torus easily). Related to fraction fourier transform.
In continuum limit becomes gaussians. too sticky to have closed forms.
Dead end.

We can find such states be considering the equivalent of discrte landau
gauge. $e^{\frac{2\pi iy}{N}}\hat{x}$. This choice leads to only one
state per value of x. Then rpojecting dwn to LLL. The k labels form a
complete set. we can consider the equivlanet gauge turned 90 degrees. We
can consoder sort of the half sum of the 2, which is the holomorphic
gauge. All of these are unmanageable to solve exactly.

Found something that might be a relative of haldane model. consider
landau gauge for exactly 1 flux per 2 unit cells. Then vector potential
is alternating +1 , -1. Take supercell.Now haldand model suppoesedly had
a net flux of zero. In my model, I can't tell the difference between the
two cases at exactly +-1. but if I want to continuosly transfrom into
the state, perhaps it might be best to be ocnsidering it to be an
atlernating field. Alternating +i, -i also works. Then we can consdering
$e^{i\theta},$$e^{-i\theta}$ and let theta go to $\pi/2$ to get my case.
Then it does seem more likely that we're discussing alternating field,
although does asliasing allow you to make the discinction?

The two different choices of supercell will lead to an overcomplete
basis = the equivalent of coherent states?

What happens when I project the gauge potential into the LLL basis? The
k-space chern simons potential in real space becomes a wanniner basis
gauge potential. Actually I'm quite unclear. I'd anticpate the result
going in an expoential which is a finite trasnlation?. Or following some
fourier logic, since the vector potential modifies$\partial_{k}-A(k)$
the real space version is $x-A(\Delta)$. The stripes where x and y are
equivalent to momentum is a singular case of this. $\Lambda=xy$ is the
transfromation that rotates the landau gauge. Does it get a LLL
noncommuting feel too? The overcompleteness
