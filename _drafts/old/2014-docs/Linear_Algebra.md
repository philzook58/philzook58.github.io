The Power Method
----------------

You can project out particular eigenvectors by repeated multiplication
by an operator. Let's say we have a hermitian operator $\hat{H}$.
Because its hermitian, we can guarantee that its eigenvalues are real
and that an orthogonal basis exists (and is unique if the eigenvalues
are non degenerate). Why? Their real because

$$<n|n>=1$$

$$H|n>=\lambda_{n}|n>$$

$$<n|(H|n>)=<n|\lambda_{n}|n>=\lambda_{n}$$

But because $H$ is hermitian $H=H^{\dagger}$

$$<n|(H|n>)=(<n|H^{\dagger})|n>=\lambda_{n}^{*}$$

Hence $\lambda_{n}^{*}=\lambda_{n}$ which is equivalent to saying it is
real.

As for orthogonality

$$<m|H|n>=\lambda_{n}<m|n>=<m|H^{\dagger}|n>=\lambda_{m}<m|n>$$

$$(\lambda_{n}-\lambda_{m})<m|n>=0$$

I guess we still haven't proven that there are a complete basis of
eigenvectors, but whatever.

Now if we repeatedly apply H to any vector, it will make the largest
eigenvalue term dominate

$$H|\psi>=HI|\psi>=H\sum_{n}|n><n|\psi>=\sum_{n}\lambda_{n}|n><n|\psi>$$

$$H^{N}|\psi>=\sum_{n}\lambda_{n}^{N}|n><n|\psi>$$

If a sum of terms is dominated by one term, the sum is approximately
equal to just the largest term in a relative error sense.

$$1+1+10000000\approx10000000$$

So that sum is approximately

$$\sum_{n}\lambda_{n}^{N}|n><n|\psi>\approx\lambda_{biggest}^{N}|biggest><biggest|\psi>$$

So that's how we can project out the largest eigenvector

To project out other eigenvectors, we will use a function of the matrix.
For a scalar variable, we can expand the function in a Taylor series

$$f(x)\approx a+bx+cx^{2}+\ldots$$

$$f(H)\approx aI+bH+cH^{2}+\ldots$$

Or we can figure out its action by using a complete set of vectors

$$f(H)|\psi>=\sum_{n}f(\lambda_{n})|n><n|\psi>$$

We already did this with the function $f(x)=x^{N}$, actually.

We pick our function so that its value at the eigenvalue we want to
project out is much larger than its value at the other eigenvalues. And
the more intense this inequality, the better it selects the eigenvector.

There are some standard functions.

$$(H-Ia)^{-1}$$

is the common choice if you have an estimate for $\lambda_{n}\approx a$.
This operator will pick out whichever eigenvector has its eigenvalue
closest to a, and the farther the eigenvalues are separated, the faster
it will do it. The closer a is to the correct eiegenvalue, the less
iterations you'll need. The function $f(x)$ clearly has a spike near the
eigenvalue of choice. You can iteratively apply this operator by
Gaussian elimination (or your linear equation solving algorithm of
choice) on the equation

$$(H-Ia)|\psi_{j+1}>=|\psi_{j}>$$

$$(H-Ia)^{-N}|\psi_{0}>=\sum_{n}\frac{1}{(\lambda_{n}-a)^{N}}|n><n|\psi_{0}>$$

If you want the lowest absolute value eigenvalue, then you can set $a=0$
and use $H^{-1}$or set a to some small constant if your Hamiltonian is
not invertible.

This general method corresponds to projecting via the so-called
imaginary time Schrodinger equation although the only reason to use such
semantics is because we have previous experience solving the Schrodinger
equation.

$$\frac{\partial}{\partial\tau}\psi=-H\psi$$

If we take a finite backwards difference approximation

$$\psi_{\tau+d\tau}-\psi_{\tau}=-d\tau H\psi_{\tau+d\tau}$$

$$\psi_{\tau}=(I+d\tau H)\psi_{\tau+d\tau}$$

$$\psi_{\tau+d\tau}=(I+d\tau H)^{-1}\psi_{\tau}$$

$$\psi_{\tau+d\tau}=\frac{1}{d\tau}(H-I(-\frac{1}{d\tau}))^{-1}\psi_{\tau}$$

This will project out the ground state, the state closest to
$a=-\frac{1}{d\tau}$, which heads towards $-\infty$. $d\tau$ has to be
small enough such that
$-\frac{1}{d\tau}<\frac{1}{2}(\lambda_{0}+\lambda_{1})$ to guarantee it
projects out the ground state (a has to be closer to $\lambda_{0}$than
it is to the next smallest $\lambda_{1}$). Again, the closer the two
eigenvalues are to each other, the more iterations is takes to project.

Or we can do forward difference

$$\psi_{\tau+d\tau}-\psi_{\tau}=-d\tau H\psi_{\tau}$$

$$\psi_{\tau+d\tau}=(I-d\tau H)\psi_{\tau}$$

And get a similar result.

Doing a whole bunch of iterations becomes

$$(I-d\tau H)^{N}\approx e^{-Nd\tau H}$$

$$\frac{1}{(I+d\tau H)^{N}}\approx\frac{1}{e^{Nd\tau H}}=e^{-Nd\tau H}$$

So this is how it connects to the familiar representation.

Minors
------

The notation used by Gantmacher for a minor of A is

$$A\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=|\left[\begin{array}{cccc}
a_{i_{1}k_{1}} & a_{i_{1}k_{2}} & a_{i_{1}k_{3}} & \ldots\\
a_{i_{2}k_{1}} & a_{i_{2}k_{2}} & a_{i_{2}k_{3}} & \ldots\\
a_{i_{3}k_{1}} & a_{i_{3}k_{2}} & a_{i_{3}k_{3}} & \ldots\\
\ldots & \ldots & \ldots & \ldots
\end{array}\right]|$$

The notation sucks, but there are a lot of options for what minors you
can take, so what are you gonna do. The upper row of i are the rows to
select, and the lower row of j are the columns to select. You pack them
in a square matrix and take the determinant.

For example

$$A\left(\begin{array}{c}
1\\
2
\end{array}\right)=a_{12}$$

$$A\left(\begin{array}{cc}
1 & 3\\
2 & 4
\end{array}\right)=|\left[\begin{array}{cc}
a_{12} & a_{14}\\
a_{32} & a_{34}
\end{array}\right]|$$

The Cauchy-Binet formula allows us to generalize the seperablity of the
detemrinant $\det C=\det AB=\det A\det B$ to minors. If $C=AB$ then

$$C\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\sum_{1<j_{1}<j_{2}<\ldots}A\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
j_{1} & j_{2} & j_{3} & \ldots
\end{array}\right)B\left(\begin{array}{cccc}
j_{1} & j_{2} & j_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)$$

It looks about right. The sum over column-rowness seems matrixy. It
reduces correctly in the full case.

What we can do is pack matrices with minors in such a way that this
relation becomes natural. The adjugate matrix is the canonical example.

But what about the grammian?

$$A^{T}A\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\sum_{1<j_{1}<j_{2}<\ldots}A^{T}\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
j_{1} & j_{2} & j_{3} & \ldots
\end{array}\right)A\left(\begin{array}{cccc}
j_{1} & j_{2} & j_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)$$

The dterminant of the grammian can be found as something that looks kind
of like a dot product. For example for an A with 2 columns

$$a=\left[\begin{array}{c}
A\left(\begin{array}{cc}
1 & 2\\
1 & 2
\end{array}\right)\\
A\left(\begin{array}{cc}
1 & 3\\
1 & 2
\end{array}\right)\\
A\left(\begin{array}{cc}
1 & 4\\
1 & 2
\end{array}\right)\\
\\
\\
\end{array}\right]$$

$$a\wedge b=\sum_{i<j}(a\wedge b)_{ij}\hat{e}_{i}\wedge\hat{e_{j}}$$

$$(a\wedge b)_{ij}=A\left(\begin{array}{cc}
i & j\\
1 & 2
\end{array}\right)$$

$$(a\wedge b\wedge c)_{ijk}=A\left(\begin{array}{ccc}
i & j & k\\
1 & 2 & 3
\end{array}\right)$$

$$A=\left[\begin{array}{ccc}
| & | & |\\
a & b & c\\
| & | & |
\end{array}\right]$$

$$B=\left[\begin{array}{ccc}
| & | & |\\
d & e & f\\
| & | & |
\end{array}\right]$$

$$(a\wedge b\wedge c)\cdot(d\wedge e\wedge f)=\sum_{i<j<k}A\left(\begin{array}{ccc}
1 & 2 & 3\\
i & j & k
\end{array}\right)B\left(\begin{array}{ccc}
i & j & k\\
1 & 2 & 3
\end{array}\right)=\det(A^{T}B)$$

Going to minors is moderately to highly retarded however. Determinants
are not calculated that way in practice, and that is only acceptable for
small dimensions.

Wedge Products are a method of describing subspaces. The exact vectors
that went in are immatterial, only their span and grammian determinant
magnitdue matter.

The closest equivlanet to the eiegevnalue representiation
$A=S^{-1}\Lambda S$ for rectangular matrices is the SVD

$$A=U\Sigma V^{\dagger}$$

The minor of A

$$A\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\sum_{1<j_{1}<j_{2}<\ldots}U\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
j_{1} & j_{2} & j_{3} & \ldots
\end{array}\right)V^{\dagger}\left(\begin{array}{cccc}
j_{1} & j_{2} & j_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)\sigma_{j_{1}}\sigma_{j_{2}}\sigma_{j_{3}}\ldots$$

Minors of Unitary Matrices?

$$V^{\dagger}V=I$$

Minors of Identity are 0,1,-1 depending on on oddness or evenness of
permutation inside symbol.

$$I\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\begin{cases}
1 & \text{even permutation}\\
-1 & \text{odd permutation}\\
0 & \text{not permutation (doubles or nonmatching)}
\end{cases}=\epsilon_{i_{1}i_{2}i_{3}\ldots}\epsilon_{k_{1}k_{2}k_{3}\ldots}$$

Via linearity of detemrinants

$$\Sigma\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\sigma_{i_{1}}\sigma_{i_{2}}\sigma_{i_{3}}\ldots I\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)$$

But since the sums in cauchy binet are order, the I will always be 1.
and its basically a delta function

When zero, cuachy binet says that every minor has to be zero of V.
Minors of V form orthonormal basis depdneig on index? Sort of. If we
insist i, k in ordered form, then yes.

$$I\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)=\sum_{1<j_{1}<j_{2}<\ldots}V^{\dagger}\left(\begin{array}{cccc}
i_{1} & i_{2} & i_{3} & \ldots\\
j_{1} & j_{2} & j_{3} & \ldots
\end{array}\right)V\left(\begin{array}{cccc}
j_{1} & j_{2} & j_{3} & \ldots\\
k_{1} & k_{2} & k_{3} & \ldots
\end{array}\right)$$

$$\sum_{J}^{n}=\sum_{1\le j_{1}<j_{2}<\ldots\le n}$$

$$J=(j_{1,}j_{2},j_{3},\ldots)$$

$$\sum_{J}U_{IJ}\Sigma_{JJ}V_{JK}^{\dagger}$$
