Broken Symmettry

Explicitly broken: broken translational symmettry

broke rotational symmettry. Wigner eckart says many matrix elements are
zero. If "weakly" broken (first pertrubative term?) what does wigner
eckart say?

Net Attractive vs repulse - depends on net charge? No. electromagnetism
is always repulsive for any net positive of negative charge

Gauge Theory
------------

Gauge transfromations are truly mysterious beasts. The story goes like
so: God gives you the vector potential. You know, that weird one with no
simple physical interpreation that gives you magnetic field
$\nabla\times A=B$.

Now any $\nabla\times\nabla\Lambda=0$. This basically says that
$\partial_{x}\partial_{y}\Lambda=\partial_{y}\partial_{x}\Lambda$, which
is reasonable. But since A lives for the purpose of B, any
transformation $A\rightarrow A+\nabla\Lambda$ will give the same B. You
can even make $\Lambda$ depend on time if you extend the law for the
potential to to now inlcude A

$$E=-\nabla\phi+\dot{A}$$

Ok. Fine. Some smarty says that THIS is what electromagnetism is truly
about. That E and B are for children and that A and $\phi$ are where
it's at. It's so elegant! Relativistic! Gauge invariant! MALARKEY, you
cry!

Well, I have to say that even after all my readings, I still maintain a
tenderness for good ole B and E. Good ole Griffiths and Gaussian
pillboxes. But I do see the point of emphasizing A. And I do see
actually that gauge transformations can be phrased as a very beautiful
and ultimately simple concept.

HIstorical origins of gauge symmettry

The basic story is the same that you may have heard murmers of (or are
super familiar with). Parallel transport. How do you compare things from
different spots? Well, you bring them together.

To bring the vectors from A over to B we'll need a standardized
procedure for bringing it over. This can be encoded in a rotation
matrix.

$\nabla_{\mu}v_{\nu}=0$

$R(dx)=1+dx_{\sigma}\Gamma$

RRRRRRRR

Consider the cube. We splay it out. Crossing one of the cut edges turns
the vector by 90 degrees. so weassociate R(90) with every edge of that
sort.

A lot of the time it doesn't matter, but its a useful game to play.

Let us suppose that you aren't a god with an all seeing eye. Let us
suppose you can only see a small area around you.

The way that Feynman describes the double slit experiment is by saying
the electron is carrying a little phase, a little clock. He can go two
different ways (the two different slits) and the phase turns. To figure
out the probability we add the two phases. if the phases agree, we get
constructive interference and dsigarre we get destructive interference.

$\theta=\int kdx+\omega dt$

Phase is the same as a little arrow.
$e^{i\theta}=\cos(\theta)+i\sin(\theta)$. Any phase can be also
considered to be a little arrow on the complex plane.

$\theta_{AB}=\int A\cdot dx$

$e^{i\theta_{AB}}=U$

NOw what does a gauge change do? It just means that we changed our
standards. Quantum Phase by itself is not meaningful, only the
comparison of two different phases is. It can never cause interference
since the integral of a gradient is determined solely by the endpoints,
not by the path taken, so all paths will .

Now suppose we're carrying more than just one little arrow (one ocmplex
phase). Instead we can carry maybe a real vector or a higher dimensional
complex vector. The generalization of what we've been discussing is that
U now becomes a matrix.

In terms of the vector potential
$U=U(dx)U(dx)U(dx)U(dx)U(dx)=e^{iA\cdot dx}e^{iA\cdot dx}e^{iA\cdot dx}e^{iA\cdot dx}e^{iA\cdot dx}e^{iA\cdot dx}$.

Now the order we mutiply the little bits matter. That's the new twist
that makes the gauge field nonabelian.

Gauge thoery is NOT Maxwell's equations or Yang-Mills Theory.
Electromagnetism has 2 parts. Field is produced by charges and charge
feels fields. We CAN consider the field as an external given quantity
and that will drastically simply our lives.

Inaddition, effective gauge fields can occur. The most typical place is
Berry phase. Berry phase is the way in which we compare phases from
systems at different values of hamiltonian paramters. Berry phase is the
synchrony of clocks. Foucault pendulum. Coriolis force. Berry phase
clearly has no reason to have any impled lagrangian for the paramters,
but it does have a well defined effect on the system if they are
externally given.

Sound in external flow. The underlying velocity serves as a vector
potential. The doppler shift is the basic phenomenon. As the sound
crosses between regions of different underlying velcotiy of the medium,
the
