Ways of describing surfaces
===========================

Parametized
-----------

The in surface metric from the volumetric metric

$$G_{s}=\frac{\partial x}{\partial u}^{T}G\frac{\partial x}{\partial u}$$

May be useful to define the rectangular tall skinny injection operator

$$Q=\frac{\partial x}{\partial u}$$

$$ds^{2}=du^{T}G_{s}du$$

$$dA=\det(G_{s})^{1/2}dudv$$

Normal vector

$$\hat{n}\propto\frac{\partial x}{\partial u}\times\frac{\partial x}{\partial v}$$

A curved surface will have a varying normal

$$\partial_{x}\hat{n}$$

$$\partial_{y}\hat{n}$$

Weingarten map

Trace back along the n to see where they intersect

$$x+Rn=x+dx+R(n+dn)$$

$$\frac{1}{R}=\frac{dn}{dx}$$

Graph
-----

Technically, the graph is just a special parametization. But a real good
one.

A graph is also an implicit surface define by $S(x,y,z)=z-f(x,y)=0$.

So the graph is kind of in a class by its own.

$z(x,y)$

Arc length inside surface

$ds^{2}=dz^{2}+dy^{2}+dx^{2}=(1+(\partial_{y}z){}^{2})dy^{2}+(1+(\partial_{x}z)))dx^{2}$

If we set things up so that the derivatives are zero at the origin,
we're happier. Only in this case is the formula for the curvature simple

$$\partial_{i}\partial_{j}z$$

In 2D then the curvature is just the second derivative y". In 2D curve
formulae and surface fomulae coincide

$$\kappa=\frac{y''}{(1+y'^{2})^{3/2}}$$

$$a=(dx,0,dx\partial_{x}z)$$

$$b=(0,dy,dy\partial_{y}z)$$

$$\hat{n}\propto a\times b=dxdy(-\partial_{x}z,-\partial_{y}z,1)$$

Normalize that sucker.

$$\hat{n}=\frac{1}{\sqrt{(\partial_{x}z)^{2}+(\partial_{y}z)^{2}+1}}(-\partial_{x}z,-\partial_{y}z,1)$$

Examples using planes

$$z=ax+by+z_{0}$$

$$z-ax-by=D\hat{n}\cdot r=z_{0}$$

$$\hat{n}=(-a,-b,1)$$

Contraints
----------

$S(x)=0$

Just like the arc length parametized curve is good, so too is the unit
gradient contraint.

$$\nabla S^{T}G\nabla S=1$$

Do this sort of thing a lot in eikonals.

In 2D the N-1 surfaces are also 1D curves. The normal then is the N
vector. The in plane is the T vector. The curvature of the surface is
the curvature of the curve.

If we set up this normalization, then the formula for mean curvature

$$\frac{1}{2}\nabla\cdot\hat{n}$$

Makes more sense. The is the the ratio of the top and bottoms areas of a
litle normal vector tube.

This normalization also makes $\nabla n$ easy to compute. The normal
dirction will be a null eigenvector, and the other two will be the
proper curvy bits. Gaussian curvature is unpleasant to define however.
No longer simple determinant

Curvature
---------

Curves = Rate of change of angle

$$\frac{d\theta}{ds}=\kappa$$

Conjecture for surfaces $\frac{d\Omega}{dA}=\kappa$(gaussian curvature)
. Works for spheres. $A=r^{2}\Omega$. and $\kappa=\frac{1}{r^{2}}$ .
Maybe m odify with a cosine?

Curvature - rate of pull away from tangent plane or line. Normal
curvature of curves inside surface. Also rates of change of normal
vectors

Standard Tensorology
====================
