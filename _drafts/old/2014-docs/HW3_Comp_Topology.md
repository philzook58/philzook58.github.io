1\. Suppose 2 elements in $\pi(Y,y_{0})$ map to the same element
$\pi(X,x_{0})$ (i.e. $f_{*}$ is not injective). This implies that two
homotopically inequivalent curves in Y must map to two homotopically
equivalent curves in X. However, the homotopy lifting property says that
two homotopically equivalent curves in X must map up to two
homotopically equivalent curves in in Y. Therefore there is a
contradiction and $f_{*}$must be injective.

7\.

$$(\gamma_{0}*\gamma_{1})*\gamma_{2}=\begin{cases}
\gamma_{0}(4t) & 0\le t<\frac{1}{4}\\
\gamma_{1}(4(t-\frac{1}{4})) & \frac{1}{4}\le t<\frac{1}{2}\\
\gamma_{2}(2(t-\frac{1}{2})) & \frac{1}{2}\le t\le1
\end{cases}$$

$$\gamma_{0}*(\gamma_{1}*\gamma_{2})=\begin{cases}
\gamma_{0}(2t) & 0\le t<\frac{1}{2}\\
\gamma_{1}(4(t-\frac{1}{2})) & \frac{1}{2}\le t<\frac{3}{4}\\
\gamma_{2}(4(t-\frac{3}{4})) & \frac{3}{4}\le t\le1
\end{cases}$$

Now to construct the homotopy we notice that the new piecewise ranges of
t must depend on s and smoothly transform into one another. We do this
linearly. Then we replace the argument inside each $\gamma$such that t
is scaled by the s dependent interval size and translated such that the
origin is shifted to the beginning of the interval. It is important to
do this carefully to make sure continuity is maintained for all values
of s.

$$H(t,s)=\begin{cases}
\gamma_{0}(\frac{t}{\frac{1}{4}+\frac{s}{4}}) & 0\le t<\frac{1}{4}+\frac{s}{4}\\
\gamma_{1}(\frac{t-\frac{1}{2}}{\frac{1}{4}}) & \frac{1}{4}+\frac{s}{4}\le t<\frac{1}{2}+\frac{s}{4}\\
\gamma_{2}(\frac{t-(\frac{1}{2}+\frac{s}{4})}{1-(\frac{1}{2}+\frac{s}{4})}) & \frac{1}{2}+\frac{s}{4}\le t\le1
\end{cases}$$

8\.

We can construct a covering space of the mesh by essentially laying
another mesh over top the original and considering the two appearances
of the boundary vertices to be inequivalent points. If we blow this
shape up to three dimensions, it is a triangulation of a sphere with
opposite poles projecting to the same point. This satisfies the
requirements of being a covering space since the star of any point in
the original space is plane-like and so is the star of of any point in
the triangulated sphere. This projection is also surjective, hitting
each vertex in the covered space twice. Any loop in the covered space
must uniquely lift to a path that either is a loop in the covering space
or a path between poles in the covering space, since the endpoints in
the covering space must map down to the same point in the covered space.
By homotopy lifting, any homotopic paths in the covered space must lift
to homotopic paths in the covering space. These two endpoint options are
clearly not homotopic in the spherical covering space since they do not
start and stop at the same locations, therefore there are at least two
classes of homotopy in the covered space. Since all paths that start and
stop at opposing poles are homotopic to each other on the sphere and all
loops on the sphere are homotopic to each other, when these two classes
are projected down they remain only two classes. Therefore the homotopy
group of the given mesh is

$$\pi=Z\text{ mod }2$$
