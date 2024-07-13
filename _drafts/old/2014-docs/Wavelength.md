Infomation Flux - Extension of shannon to 3d instead of signals.
Bandvolume instead of bandwidth? Numerical aperture as a cone of
available wavevector space (Born approximation).

There are three aspects to consider: Observability, Controllability, and
Predictability. Given the Helmholtz equation, what is out ability to
observe source terms, predict future solutions, and control the field
values externally.

If I work with the full time dependant wave equation, I can use control
theory. The internals of the system are hidden state. External sources
control and external field observation.

Error Bound for matrix or error bound for vector

$$|u-u_{h}|=e\le\left[\begin{array}{c}
f''(\xi_{1})\\
\\
\\
\\
\end{array}\right]$$

Or

$$|L-L_{h}|\le$$

$$|G-G_{h}|\le$$

What space to work in? Can project G into finite space or interpolate Gh
into total inifnite space. Or some combo thereof.

residual error (proably easier to work with) The so called error norm.

$$|Lu-f|=|r|\le h\left[\begin{array}{c}
f''(\xi_{1})\\
\\
\\
\\
\end{array}\right]$$

$$\frac{d^{2}}{dx^{2}}u-\frac{p(x-h)-2p(x)+p(x+h)}{h^{2}}\le\max_{x-h\le\xi\le x+h}f''($$

HOw does the relationship go?

$$r=Le$$

So condition number tells us how well relative residual bounds relate to
error bounds.

$$\frac{r}{f}=\frac{Le}{Lu}$$

$$\frac{e}{u}=$$

We need error to be nondimensional to be physical.

Early stopping in born series, conjugate gradient, asymptotic series.
Perhaps at some point in asymptotic series, we get weiner filter
condition (amplify signal with minimal noise amplification), but
afterwards we flip. I'm not super duper sure this is a thing in a
iterative linear solution. Best basis is noise in one subspace and
signal in another (as much as possible anyhow). SVD used usually to find
it.

Bounds of derivatives from bounds on fourier coefficients? something
like if k\>k0 $f(k)\le c\frac{1}{k^{p}}$ then $f'(x)\le c+k_{0}f_{max}$.
In the squared sense. Spectral optimiszation.

Connection to economization of series. Does this procedure regularize?

How much control do we really have over the boundary? Perfect derivative
delta functions needed for total control of boundary conditions. We can
approximate.

### Prediction error

So we build our estimator from a likelihood function. Now the estimator
is a random vasriable itself. Using the actual parameter, compare the
variance of a new smaple to the estimate.

Or compare properties of the new smapled to the porperties of something
pulled from our guess distribution. Bias and variance.

$$\int(x_{i+1}-x_{g})^{2}e^{(x_{i+1}-\mu)^{2}}e^{(x_{g}-\hat{\mu}(\{x_{i}\})^{2}\Sigma^{-1}}P(\{x_{i}\}|\mu)$$

$$$$

Gaussians
=========

### Completing Squares

We want to complete the squares on

$$ax^{2}+bx+c$$

i.e take it to the form

$$(qx+r)^{2}+d$$

Well, we expand it back out and collecty powers of x.

$$r^{2}+d=c$$

$$2rqx=bx$$

$$q^{2}x^{2}=ax^{2}$$

We solve for r, q, and d

$$q=\sqrt{a}$$

$$r=\frac{b}{2\sqrt{a}}$$

$$d=c-ar^{2}=c-(\frac{b}{2})^{2}$$

Alright. Straightforward, but complicated.

Now suppose we had a quadratic function in many variables. Sadly it
seems that our notion of completing the squares breaks down. Yet, we
could pick some of the variables, and then perform a completing the
squares operation on him. In that case b will be a linear function of
the other variables and c will be a quadratic function of the other
variables. This will then lead to r also being a linear function of the
other variables and d remaining a quadratic.

But then we can repeat this process on d. We can complete the squares on
a new variable in d and so on until we have a hierarchy of completed
squares.

A quadratic function of many variable can be convenitenly written in
vector notation.

$$x^{T}Ax+b^{T}x+c$$

By analogy with the single variable case to complete the squares on it
we'd like it to be in the form

$$(Lx+r)^{T}(Lx+r)+d$$

Equating the sides we have

$$L^{T}L=A$$

$$2L^{T}r=b$$

$$r^{T}r+d=c$$

The first equation is solved by taking the matrix square root of A in
some sense (Which is not unique btw). Here's the key though, this is
equivalent to gaussian elimination or LU factization or Cholesky
Factorization, to get some buzzwords in there.

This completing the square is just absolutely perfect as far as a
multivariable gaussian integral is concerned. PERFECT I TELL YOU.

The change of variables is

$$y=Lx+r$$

Then the Jacobian (the factor to account for the ratio of $d^{N}x$ to
$d^{N}y$) is just

$$d^{N}y=d^{N}x|J|=d^{N}xDet(L)$$

$$Det(L^{T}L)=Det(L)^{2}=Det(A)$$

Incidentally, this route is much much much better than sum of all entry
combos with -1 thrown in formula if you want to actually numerically
calculate a determinant of A for some godforsaken reason. Gaussian
elimination to produce L is pretty fast, and then the Det of a
triangular matrix is just the product of its diagonal. If you need the
Det of a really really big matrix though, this might not cut it. I am
not aware of any sparse matrix based techniques (The big guns) for Dets
but they got to be out there, right?

This gaussian elimination process is exactly the process that is
demonstrated in introduction to path integrals techniques for the free
classcial particle. The books show you iterating the square completing
process, and then integrating out each variables as it comes along, and
hope you can decipher the pattern. I think think about it at the matrix
level is siginifacntly more poweful as we'll see.

### Partitioned Matrices

It is highly useful to think of a matrix as being partitioned into
submatrices. Let's look at the sinplest partition first, into two
subspaces

$$M=\left[\begin{array}{cc}
A & B\\
C & D
\end{array}\right]$$

where A is $r\times r$, B is $r\times q$, C is $q\times r$ and D is
$q\times q$. Ruh Roh! Rectangular Matrices!

The great and remarkable thing about this idea is that most matrix stuff
works like it should. A good sanity check on most things is to make sure
the dimensions of the blocks jive together correctly. Matrix
multiplication is still rows times columns at the block level (Careful
with ordering though!). Matrix addition is still sum of components at
the block level.

Transpose is quite similar to its scalar counterpart

$$M^{T}=\left[\begin{array}{cc}
A^{T} & C^{T}\\
B^{T} & D^{T}
\end{array}\right]$$

$$tr(M)=tr(A)+tr(D)$$

How about the inverse though? Or the Determinant? Hmmm\... Now we're
getting somewhere interesting.

How about LU decomposition? Let's review the scalar case

$$M=\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]$$

You multiply a matrix on the right side to add columns to one another
and on the left side to add rows. See, the first column of this right
side matrix says take the first col of M and the Second col of M to
produce to first new col. The second col of the right side matrix says
to just keep the second col of M as is

$$\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]\left[\begin{array}{cc}
1 & 0\\
2 & 1
\end{array}\right]=\left[\begin{array}{cc}
a+2b & b\\
c+2d & d
\end{array}\right]$$

$$\left[\begin{array}{cc}
1 & 0\\
2 & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]=\left[\begin{array}{cc}
a & b\\
c+2a & d+2b
\end{array}\right]$$

Hence all those row operations you're used to in gaussian elimination
will be left side multiplcations by row summing matrices

$$\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]M=\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
c & d
\end{array}\right]=\left[\begin{array}{cc}
a & b\\
0 & d-cb/a
\end{array}\right]$$

So we got it into triangular form. Not super pretty though. Let's take
that matrix off of M

$$\left[\begin{array}{cc}
1 & 0\\
-c/a & 1
\end{array}\right]^{-1}=\left[\begin{array}{cc}
1 & 0\\
+c/a & 1
\end{array}\right]$$

This is true because the first row was untouched, so we just need to sum
that row onto row 2 in order to undo our previous subtraction from row
2. Or just matrix multiply them and you'll see its true.

Hence

$$M=\left[\begin{array}{cc}
1 & 0\\
c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & b\\
0 & d-cb/a
\end{array}\right]$$

Let's get it into a Nicer LDU form

$$M=\left[\begin{array}{cc}
1 & 0\\
c/a & 1
\end{array}\right]\left[\begin{array}{cc}
a & 0\\
0 & d-cb/a
\end{array}\right]\left[\begin{array}{cc}
1 & b/a\\
0 & 1
\end{array}\right]$$

Nice. Okay, we can follow our logic every step of the way through for
the block case, except now we need to make sure dimensions of matrices
match when we multiply them. If we're careful, we'll end up with this
form

$$M=\left[\begin{array}{cc}
I & 0\\
CA^{-1} & I
\end{array}\right]\left[\begin{array}{cc}
A & 0\\
0 & D-CA^{-1}B
\end{array}\right]\left[\begin{array}{cc}
I & A^{-1}B\\
0 & I
\end{array}\right]$$

This lower entry is very very important. Its called the Schur Complement

$$D-CA^{-1}B=M/A$$

Interpetation of Schur Complement (I need to think about this more): It
really IS aptly named. It is a complement in a true set like sense.
We've divided the space into two. The true and the false. The left and
the right. The black and the white. We've developed a dichotomy. If A
has dimension r, M has n, then M/A has n-r.

Hence

$$Det(M)=Det(A)Det(D-CA^{-1}B)=Det(A)Det(M/A)$$

Thinking about that slash as a division operation that seems mighty
plausible.

The beautiful thing about this block procedure is that you can remove
signifcant amounts of your variables by elimination all at once.

### Marginal Gaussians

$$\Sigma=\left[\begin{array}{cc}
A & C^{T}\\
C & B
\end{array}\right]$$

$$\Sigma^{-1}=\left[\begin{array}{cc}
I & -A^{-1}B\\
0 & I
\end{array}\right]\left[\begin{array}{cc}
I & 0\\
CA^{-1} & I
\end{array}\right]\left[\begin{array}{cc}
A & 0\\
0 & D-CA^{-1}B
\end{array}\right]\left[\begin{array}{cc}
I & A^{-1}B\\
0 & I
\end{array}\right]$$

$$P(x,y)=\frac{1}{\sqrt{(2\pi)^{N}\det\Sigma}}e^{-\frac{1}{2}\left[\begin{array}{cc}
(x-\mu_{x})^{T} & (y-\mu_{y})^{T}\end{array}\right]\left[\begin{array}{cc}
A & C^{T}\\
C & B
\end{array}\right]^{-1}\left[\begin{array}{c}
x-\mu_{x}\\
y-\mu_{y}
\end{array}\right]}$$

$$P(y)=\int dxP(x,y)=N(y|\mu_{y}\Sigma_{yy})$$

$$P(y|x)=N($$

### Least Squares from Probability

Let's say we want to determine the mean value of a random vector from
sampling. We assume a Gaussian Distribution

$$P(x)=\frac{1}{\sqrt{(2\pi)^{N}\det\Sigma}}e^{-\frac{1}{2}(x-\mu)^{T}\Sigma^{-1}(x-\mu)}$$

Where $\Sigma$ is the covairnace matrix

$$\Sigma=\left[\begin{array}{cccc}
\sigma_{1}^{2} & \sigma_{1}\sigma_{2} & \sigma_{1}\sigma_{3} & \ldots\\
\sigma_{2}\sigma_{1} & \sigma_{2}^{2} & \sigma_{2}\sigma_{3} & \ldots\\
\sigma_{3}\sigma_{1} & \sigma_{3}\sigma_{2} & \sigma_{3}^{2} & \ldots\\
\ldots & \ldots & \ldots & \ldots
\end{array}\right]$$

The Lieklihood function is

$$L(\{x_{i}\}|\mu,\Sigma)=\prod_{i}\frac{1}{\sqrt{(2\pi)^{N}\det\Sigma}}e^{-\frac{1}{2}(x_{i}-\mu)^{T}\Sigma^{-1}(x_{i}-\mu)}$$

$$\ln L(\{x_{i}\}|\mu,\Sigma)=\sum_{i}\frac{-N}{2}\ln2\pi-\frac{1}{2}\ln\det\Sigma-\frac{1}{2}(x_{i}-\mu)^{T}\Sigma^{-1}(x_{i}-\mu)$$

$$\frac{\partial}{\partial\mu}\ln L(\{x_{i}\}|\mu,\Sigma)=0$$

This will lead to minimization of the least squares looking quantity

$$\sum_{i}\frac{1}{2}(x_{i}-\mu)^{T}\Sigma^{-1}(x_{i}-\mu)=\sum_{i}\frac{1}{2}(x_{i}^{T}\Sigma^{-1}x_{i}+\mu{}^{T}\Sigma^{-1}\mu-2\mu{}^{T}\Sigma^{-1}x_{i})$$

The first factor is irrelevent since it cannot be minimized

We can pack our samples into a matrix for convenience

$$X=\left[\begin{array}{cccc}
| & | & | & \ldots\\
x_{1} & x_{2} & x_{3} & \ldots\\
| & | & | & \ldots
\end{array}\right]$$

$$\sum_{i}\Sigma^{-1}\mu-\Sigma^{-1}x_{i}$$

$$\mu=\frac{1}{n}\sum_{i}x$$

The best guess of the mean is indeed what we usually think of as the
mean. Good.

But a slightly change in the analysis makest hings more interesting.
Instead of using just the bare means $\mu$let us insetad use the means
linearly parametized by a smaller vector $A\mu$

$$P(x)=\frac{1}{\sqrt{(2\pi)^{N}\det\Sigma}}e^{-\frac{1}{2}(x-A\mu)^{T}\Sigma^{-1}(x-A\mu)}$$

$$\sum_{i}\frac{1}{2}(x_{i}-\mu)^{T}\Sigma^{-1}(x_{i}-\mu)=\sum_{i}\frac{1}{2}(x_{i}^{T}\Sigma^{-1}x_{i}+\mu{}^{T}A^{T}\Sigma^{-1}A\mu-2\mu{}^{T}A^{T}\Sigma^{-1}x_{i})$$

$$\sum_{i}A^{T}\Sigma^{-1}A\mu-A^{T}\Sigma^{-1}x_{i}=0$$

$$nA^{T}\Sigma^{-1}A\mu=\sum_{i}A^{T}\Sigma^{-1}x_{i}$$

$$\mu=\frac{1}{n}\sum_{i}(A^{T}\Sigma^{-1}A)^{-1}A^{T}\Sigma^{-1}x_{i}$$

In a curve fitting situation, the matrix A will be our tall and skinny
Vandermode Matrix and the vector $\mu$ will be our polynomial
coefficients.

6-5 {#section .unnumbered}
===

Log Infromation matrix times possible interval vector sqyared= bits

If we want to make an informed choice on the next experimental step we
should take, use conditional distriubtion on already taken sample.
F=$E[\partial_{\theta}^{2}L(x|x_{0},\theta)]$. Somehow include fisher
information matrix that we already have
$\partial_{\theta}^{2}L(x_{0}|\theta)$. Could use current sample as a
prior on

$I_{2}I_{1}^{-1}$infromation gain? $trI_{2}I_{1}^{-1}$. I think this
works. Since we can wraparound eigenespansions. Yes. Bits gained =
$\log trI_{2}I_{1}^{-1}$ . Strange that this forumula does not cascade
right. $\sum\log trI_{i+1}I_{i}^{-1}\ne\log trI_{N}I_{1}^{-1}$. If we
have experiment options, we could use this to find direction of maximal
gain. No. use det.

It is called D-optimality in optimal diesgin. Not quite actually.

Optimizing prediction and optimizing estimates may not be the same
thing?

eigenvectorts are sum of paramters we know best,worst.

Could be considered as encoding interval or a bayesian prior
distribution varaince

Hyoptheisis questions information matrix - fractions of bit

Encode floating point in prability exp and mantissa

On Binary expnasion, use percetpron, logistic, kernel trick. estimae
probability with paramter. Single rela number encoded as infitnite
discrete questons. can then use discrete learnng theory and VC
dimension. Calculate bits of accuracy from 10 Calculatre infromation
boost insetad of total infromation.

Typically we know the high digits and don't know low digits,
oscillatory, until end where probability falls to 1/2. Enevelopped
oscillation function. This looks like a logistic function. Logitstic
regression on a ln(x) scale.

Connection between Fisher infromation and Condition Number. Well, fisher
matrix may be modified by a double jacobian. This gives a factor of
absolute condition number squared possibly.

So the infromation on j is given by

$$e^{-(\phi-Gj)^{2}\Sigma^{-1}}$$

We could use An upsampled j, $Uj$, to reduce the number of parameters.
Or include smoothing term to make G not quite so harsh.

Information matrix $G\Sigma^{-1}G$. That seems fine? Roughly constant
info at and below wavelnegth, decays afterwards. maximal info at
wavelength. decays afterwards at $n^{-4}$. Then lesson seems to be that
you can do well below k with little precision, but after k you need more
lots more precision to do well.

Need to examine prediction estimates then. Even though the est imates of
j might be okay, they might go radically astrary.

Value inaccruacy is easy to deal with, but what about spatial
inaccruacy? (1,0,0,0,0) and (0,1,0,0,0) might be far vectorially, but
they are very close experimentally. Not quite so bad seeming if the lump
is more distributed.

The necessity of only receiving data on the exterior of the region
(boundary or perhaps volumetric. Volumetric might be overkill, but we
should be able to handle the degenreacy)

Okay. So it seems obvious that given complete field perfectly, we can
find complete j minus the cokernel of L. Wait\... maybe not. if the
field has vanishingly smal but nonzero $\Sigma$, the fast that G
Explodes with a pole might still kill all infromation.

What is the equivaent of the Helmhotlz kirchoff integral for matrix
version of wave equation?

The clebscjh gordon coeffcicents is the equivalent of the beat equations
for spehrical harmonics (rexpression products back into linear). Its
just that legendre polynomials are shitty functions of cosine. We could
reqrite legendre as a fourier series. Clebsch gordon come as
combinatorics for a bunch of uses of fundamental beat combos. fourier
series/taylor series on $CP^{1}$

### Sufficient Statistics

You can find a function of the samples that gives as much information
about the

I think the obvious analystic choice is the linear one, defining a fat
matrix S

$$t=Sx$$

for example, the matrix S that will construct the mean is

$$\frac{1}{N}\left[\begin{array}{ccc}
I & I & I\end{array}\right]$$

With all your samples packed into a single vector x, each vector
$x_{i}$being from sample i

$$x=\left[\begin{array}{c}
x_{1}\\
x_{2}\\
x_{3}
\end{array}\right]$$

Then if the smapples are i.i.d., the total joint probability
distribution is

$$\exp(-\frac{1}{2}(x-m)^{T}\left[\begin{array}{ccc}
\Sigma^{-1} & 0 & 0\\
0 & \Sigma^{-1} & 0\\
0 & 0 & \Sigma^{-1}
\end{array}\right](x-m))$$

Since we think that that there is really only one sample worth of
parameters, we can upsmple with a thin matrix

$$m=\uparrow\mu$$

$$\uparrow=\left[\begin{array}{c}
A\\
A\\
A
\end{array}\right]$$

Now we can easily use correlated samples using the off diagonals.

The information matrix for this is

$$F=\uparrow^{T}\left[\begin{array}{ccc}
\Sigma^{-1} & 0 & 0\\
0 & \Sigma^{-1} & 0\\
0 & 0 & \Sigma^{-1}
\end{array}\right]\uparrow$$

If we do some block summation over samples, we get 1 factor from each
sample giving n in total.

$$F=nA^{T}\Sigma^{-1}A$$

So to list the sizes at play:

n is the number of samples

j is the number of things measured per sample, the size of a vector
$x_{i}$

nj is the size of vector x, m

r is the number of parameters, the size of vector $\mu$

The matrix A is $j/r$

The matrix $\uparrow$ is $nj/r$

The matrix S will be $q/nj$

For polynomial regression

n is number of points evaluated at

j is 1, the value of the function at that point

r is the type of polynomial used.

If we also randomly pick the evalutation points, then this becomes a
mess.

So the objective is to pick S such that we maxmimize the new information
matrix in some manner. We can build a joint distribution
$P(x,t|\mu)=P(x|\mu)\delta(t-Sx)$. Then we will marginalize out x. We
hsould write that delta function as a gaussian.

$$\exp(-\frac{1}{2}(x-m)^{T}\left[\begin{array}{ccc}
\Sigma^{-1} & 0 & 0\\
0 & \Sigma^{-1} & 0\\
0 & 0 & \Sigma^{-1}
\end{array}\right]\left[\begin{array}{c}
s\\
x
\end{array}\right])$$

$$\exp(-\frac{1}{2}(x-m)^{T}\left[\begin{array}{ccc}
\Sigma^{-1} & 0 & 0\\
0 & \Sigma^{-1} & 0\\
0 & 0 & \Sigma^{-1}
\end{array}\right](x-m)+\alpha(t-Sx)^{2})$$

Rewrite this as a complete square. Then do schur complement trickery to
marginalize out x. We'll get a matrix something like this

$$\left[\begin{array}{cccc}
\Sigma^{-1} & 0 & 0 & |\\
0 & \Sigma^{-1} & 0 & \alpha S^{T}\\
0 & 0 & \Sigma^{-1} & |\\
- & \alpha S & - & \alpha I
\end{array}\right]$$

I'm guessing that the S will mostly be projecting operators. and that
essentially we want singular vectors of the A?

6-2 {#section-1 .unnumbered}
===

### Estimation of $\Sigma$

### Correlated Samples

### The Fisher Information

From the definition of Fisher information, we get the result that

$$I(\mu)=E[\partial_{\mu}^{2}\ln L(\{x_{i}\}|\mu)|\mu]=E[\sum_{i}A^{T}\Sigma^{-1}A]=nA^{T}\Sigma^{-1}A$$

### Recursive Least Squares

### Moments of Gaussians

### Solving Gaussians

Gaussian Elimination and Diagonilzation

The Gaussian is a linear algebra engine.

### Marginals of Gaussians

Generating function

5-31 {#section-2 .unnumbered}
----

A field of absolute conics, parameter estimation required for all of
them dscribes GR. Or dsicrete metric field

Assume we camputre enetire helmholtz field at noise level
$|\Delta\phi|<\epsilon$, spatisal accuracy $\Delta x$? Perhaps go point
by point estimates and regularize field by putting prior on it that
litted it going nuts. Since ntropy goes as logN, ratio of limit to
accuracy, adding a little to limit doesn't matter much. Also cross
validation. Maybe we could do analysis scaling $\Delta x$ down and
hitting a crossover somwhere. I would like to avoid requring spatial
accuracy. Then we have a bit content to field (via kullback-liebler)? To
determine j we apply L. Condition number of L subtracts off bits of
info. If we make L with lots of entires (finely spaced), condition
number gets worse and worse.

The question is, where does wavelnegth matter? Is it because we image
externally, or is does it occur even if we had all the marbles.

Is cross validation, regularization and such the way to save continuos
entropy? Bayesian wise, we can talk about entropy gain if we had prior.
But from just letting data talk for itself,

$\kappa(N),\kappa(\Delta x),\kappa(\Lambda)$ are quantities of interest
and their asymptotic behavir as a function of dimension and such.
$\kappa(\Delta x,L,k^{2})=\frac{\lambda_{\frac{L}{\Delta x}}}{\lambda_{0}}$.

$\lambda_{0}=-(\frac{\pi}{L})^{2}+k^{2}$

If you hit a pole in the spectrum at some point in increasing your
resolution, that would cap out the condition number.

$\kappa\le||G||||L||$

$\kappa=||L||\frac{||x||}{||Lx||}$

The number of entries in our vectors will be
$N=(\frac{L}{\Delta x})^{d}$

$||L||\propto N^{2/d},(\frac{\Delta x}{L})^{2}$

$||G||=pole/resonance$

$\frac{1}{-(\frac{N\pi}{L})^{2}+k^{2}}$

The less than equal is unconvincing though.

The Helmholtz equation kind of looks exactly like tikhonov
regularization with regulariuzation parameter $k^{2}$.

Helmholtz only solves for one $\omega$ component of source
$j(\omega,x)$. Should I work with full time varying wave equation?

why condition number is is inofrmation decay. Fisher infromation?

Relative Fisher information $I*\theta^{2}$$I*\theta$?
$I*\sigma_{\theta}^{2}$? estimates how close you are the rao bound.
bsically paramrtization invariant.

Could put floating point bounds in porbabilsitic language. A compact
support distribution of error. Markov bound type things.

what about taking just a simple derivative?

born series and decay of inoformation. The longer the chain of cause
effect, the tougher? GGG each time compounds condition number. If
condition number is really a physical thing.

How far should a series go?

Multiscale KL divergence. Use estimate from prior scale and see how much
more data is needed. Might cap out at $\lambda$scale.

The eikonal approximation fails for small feautre sizes. We could take
this as an indiciation. But it does not mean things can't be seen, maybe
we just need to change our analysis.

Condition Number
----------------

Fisher Information
------------------

The goal is to estimate a parameter in a probability distribution. For
example, the gaussian

$$N(\mu,\sigma^{2})$$

We could take samples from the distribution and then

Or even simpler, pulling blue and red balls from a box, estimate the
proportion of blue to red balls. The obvious estimate is that the
proptiopn of balls in the box is going to be close to the proprtion we
actually pull out and see. We intuitively feel that our estimate will
get better and better the more balls we pull.

If the ratio of red balls is

$$p=\frac{\text{\# Red Balls}}{\text{\# Total Balls}}$$

Then the porbability of picking a red ball is p and the porbability of
picking a blue ball is $1-p$. The probability of picking r red balls and
b blue balls is $p^{r}(1-p)^{b}$

### The Likelihood Function

The likelihood function is the porability of getting the data you get,
given as a function of the paramter you don't know. In our ball case

$$L(r,b|p)=p^{r}(1-p)^{b}$$

The classic method of parameter estimation is the maximum likelihood
approach. We fix r and b to the values we actually found and maximize
with respect to p. This makes sense as a principle, since it is good to
assume that what happened was likely to happen, but it is certainly not
proof of anything really. We often take the lograithm of the likelihood,
since the maximum of a log is the same as the maximum of the argument,
and typically likeihoods are composed of a large amount of
multiplicative factors.

$$\frac{\partial}{\partial p}\ln L(r,b|p)=0$$

$$\frac{r}{p}+\frac{b}{1-p}=0$$

$$p=\frac{r}{b+r}$$

We get exactly what our intutive guess of the estimate should have been.

If we consider r and b to be random variables, then we see that p is
also a random variable. We can therefore find the variance of p and
other stiastical porperties

### Information

How reliable is the estimate given by the maximum likelihood principle?
We use the maximum, but it is possible that this maximum is very steep
or shallow. If the function is very shallow, then a particular choice of
p may not be all that much better than another choice. The maximum
likeihood principle feels much safer when one choice dominates the other
ones. If not, then maybe a slightly different sample or a slightly
different estimation principle might give radically different results.

The steepness at the point of estimation is given by
$$\frac{\partial^{2}}{\partial p^{2}}\ln L$$

Since this is the term in the taylor expansion about that point

$$L\approx\ln L(p_{0})+0\Delta p+\frac{1}{2}(\Delta p)^{2}\frac{\partial^{2}}{\partial p^{2}}\ln L$$

If we want to conisder all the possibitites we might have had to deal
with, we can look at the average sharpness of the Log-Likelihood

$$I(p)=E_{r,b}[\frac{\partial^{2}}{\partial p^{2}}\ln L|p]$$

If we consider $\hat{p},$the estimator considered as a random variable,
then the Fisher Infromation is approximately given by

$$I(p)\sim\frac{1}{\sigma_{p}^{2}}$$

This statement is exactly true for the estimate of the mean parameter in
the gaussian drisribution. It is a statement for rough estimation and
understanding of the Fishera information, very similar to the identity

$$\Delta x\sim\frac{\hbar}{\Delta p}$$

Whereas the latter is dignified by assuming the best with the Heisneberg
Uncertasinty inequality, the first assume the best out of the Cramer-Rao
inequality.

If the samples are indepedant, then the infromation is proportional to
the number of samples. Thisd is the main vidnication to using the
Log-lieklihood instead of liekhoold.

$$I\propto N$$

### Data Reduction

Numerical Analysis
------------------

In the continuous case, it is not intrtsiniscally clear what doing a
good job entails.

If you want to work with relative quantities, use $\ln x$. Then an
overall scalling does not effect an interval size.
$\Delta\ln x=\Delta\ln\alpha x$

### Conditioning

The condition number gives a bound on how bad error can be amplified by
an operation. You may measure error however you want. You may work with
relative or absolute error or squared error or any cockammie system you
like.

An error in x gets multiplied by the Jacobian.

$\frac{\partial\ln f}{\partial\ln x}=\frac{\partial f}{\partial x}\frac{x}{f}$

What about a multivariable function?

### Stability

The definition of continuity is a little game. A stranger gives you a
little interval of size $\delta$ in around $y_{0}$ in the output of a
function. YOu have to provide a little range $\epsilon$ centered around
$x_{0}$that you can gurantee will map into his interval, regardless how
small. In other words, your job is to find a function$\epsilon(\delta)$
that will work.

5-30 {#section-3 .unnumbered}
====

Why Wavelength Bounds our Ability to see
----------------------------------------

One argument is that when we scatter light off of

What we see is the Energy in light. Light dumps energy (via the electric
field of the wave doing work) onto the retina. Once sufficent energy has
been dumped the nerve fires and sends a signal into the brain, from
which . I back this picture up with no experimental or anatomic data
whatsoever, except I belive this is the common picture we all have.
Because it takes multiple periods of the wave to dump in sufficient
energy into the eye, the eye does not detect phase of the wave. Like a
bamboo fountain in a zen garden, it collects energy and then dumps
repeatedly (or a drinky bird).

The eye is not sensitive enough to detect single photons. It takes a
couple to trigger. I feel that Quantum Mechanics of the electrodynamic
field is mostly an irrelevant complication a to our discussion and I
shall treat the field classically.

The intensity of the field is equivalent to the time averaged Poynting
Vector or the distribution of the time averaged Poynting Vector. Since
the Poynting vecotr indicates work done by the electromagnetic field,
intensity is the thing that we measure with our eye.

A simpler model might be measurement with a large number of thermometers
attached to a screen. As the field does work, it heats up the screen,
and thus we may indrectly detect light.

Is it truly fundamental that we may only see Intensity? No. We may build
detectors that are sensitive to phase. Classically speaking, there is no
distinction at all between RF scattering and light scattering except for
a trivial scaling. The scattering of RF off a 10m ball is the same as
red light scattering off a 500nm ball. Even the Field in a wire, which
is easily measured by an oscilloscope, is more or less just a scalings
difference from Light. Or light in an optical fiber compared to
mircowaves in a metallic waveguide.

Nevertheless in most ordinary situations, Intensity is the quantity of
interest.

What we need to see depends on our model of what we can possibly see. At
the extreme, if we knew exactly what we'll see, we don't need to look at
all. At the other end, if we allow any image to be present to our eyes,
we'll never be able to decrypt it in its entirety with the ultimately
fninte amount of data God gives us.

What we are able to discern also depends on how noisy our measurments
are. Even if an ideal camera could

If we need to only discern between one gaussian lump and two, we may be
able to do this even when the lumps are quite overlapped. This is a very
simple model two make. If we need to pick one out of 1000 possible
function to fit the data, then we may need more data and a clearer
signal.

$$Discernment=\frac{Datapoints-Noise}{ModelPossibilities}$$

Once we allow noise into consideration, then we're woorking
porbabilistically, so your discernement also depends on how often you're
willing to be wrong. I doubt you'll ever get to 50-50 on yes-no
questions

We deevelop of a model of everything we oculd possibly know, then we run
it through a grinder, chopping off limbs. Maybe we square so we only
have amplitudes, or stick ourselves outside the reigon of interest.

Thermodynmaics is ultimately a very simple model for some very complex
behavior with a massive amount of data points. That might be the origin
of its success.

The first order in the Born Approximation of the scattering of a wave is
given by

$$<f|V|i>$$

This is the same as Fermi's Golden Rule.

If we use plane waves as our incoming and outgoing, we get

$$\int d^{3}xV(x)e^{i(k-k')\cdot x}$$

If the scattering is elastic, then we have the condition

$$|k|=|k'|$$

$$q=(k-k')$$

It is clear then that (by Cauchy-Schwartz probably)

$$|q|\le2|k|$$

If we fix the incoming wavevector in the $\hat{z}$ direction, q
describes a circle of radius $2|k|$ resting on the $k_{z}$ axis.

If we allow the dirction to vary, we could in thoery by arranging the
incoming radation and outgoing detector determine the fourier coeffcient
of the potential for any $|q|<2|k_{0}|$. This means we achieve a banded
dtermination of the potential.

The Sampling Theorem
--------------------

There are a couple of preliminary results that are quite useful.

First off, in the vector space of periodic functions, the identity is
given by a complete set of states

$$I=\sum_{n=-\infty}^{\infty}|k_{n}><k_{n}|$$

A basis is a set of vectors $\{e_{n}\}$ that spans a space. A basis in
one space may not be a basis for a larger space. For example the
functions $e^{i2\pi nx}$ are a basis for functions in the interval
$[0,1]$, or for the set of functions with period 1, but not for any
function from $(-\infty,\infty)$. An orthonormal basis means that
$e_{n}^{\dagger}e_{m}=\delta_{mn}$. From any old basis we can rearrange
them into an orthonormal one if we desire.

### Dirac Comb

We can find a fourier series for a $\delta$ function at the origin.

$$f(x)=\sum_{n}a_{n}e^{i2\pi nx}$$

$$a_{n}=\int_{0}^{1}dxf(x)e^{-i2\pi nx}$$

$$a_{n}=\int_{0}^{1}dx\delta(x)e^{-i2\pi nx}=1$$

If we extend the domain to outside the interval $[0,1]$ what we insetad
have is the periodic extension of the Dirac Delta, the Dirac comb

$$\amalg(x)=\sum_{n=-\infty}^{\infty}e^{i2\pi nx}=\sum_{j=-\infty}^{\infty}\delta(x-j)$$

Wha about the Fourier Transfrom of this comb?

$$\tilde{\amalg}(\omega)=\int dxe^{-i2\pi x}\sum_{j=-\infty}^{\infty}\delta(x-j)=\sum_{j=-\infty}^{\infty}e^{-i2\pi jx}=\amalg(\omega)$$
We have the remarkable fact that the Dirac Comb is the fourier transform
of itself. Or in general by the scaling theorem, the trnasform of a
scaled dirac comb is given by an anti-scaled dirac comb

$$\mathsf{\mathrm{\mathscr{F}[\amalg(ax)]=\frac{1}{a}\amalg(\frac{\omega}{a})}}$$

### The Fourier transform of a box function

$$\Pi(x)=\begin{cases}
1 & -1<x<1\\
0 & \text{otherwise}
\end{cases}$$

$$\tilde{\Pi}(\omega)=\int e^{-i2\pi\omega x}\Pi(x)dx$$

$$=\frac{1}{-i2\pi\omega}e^{-i2\pi\omega x}]_{-1}^{1}=\frac{\sin(2\pi\omega)}{\pi\omega}$$

The Fourier Transform of a box is a sinc function.

### Convolution Theorem

### Sampling

By multiplying a function by our dirac comb, we leave behind a ssampling
of sorts by what is sometimes called the sifting property of the delta
function

$$f(x)\amalg(x)=f(x)\sum_{j=-\infty}^{\infty}\delta(x-j)=\sum_{j=-\infty}^{\infty}f(j)\delta(x-j)$$

Now we do not have any of the information left on our function between
our sample points.

Let us go to the Fourier domain. By the convolution theorem

$$f(x)\amalg(x)\Rightarrow\tilde{f}(\omega)*\tilde{\amalg}(\omega)$$

However

$$\tilde{\amalg}(\omega)=\amalg(\omega)$$

$$$$

### The ridiculous p\[arts of the theorem

No physical sampling is likely to take exact point-like samples. Nor are
signal expected to be bandlimitted often.

### Generalized Sampling

Appromxation in the context of vector spaces usually means least square
minimization, doing the best you can with what you're given. For
exmpale, if you're constrained to a subspace spanned by a fixed number
of vectors, you can pack them into A. Then multiplying A times a vector
of coeffcients will reconstitue your vector like orange juice.

$$A=\left[\begin{array}{cccc}
| & | & | & \ldots\\
a_{1} & a_{2} & a_{3} & \ldots\\
| & | & | & \ldots
\end{array}\right]\left[\begin{array}{c}
\lambda_{1}\\
\lambda_{2}\\
\lambda_{3}\\
\ldots
\end{array}\right]=\sum a_{n}\lambda_{n}$$

$$Lu=j$$

This can come from a minimization problem

$$\text{min}(Lu-j)^{2}$$

But now if we want constraint into the subspace spanned by A

$$\text{min}(LA\lambda-j)^{2}$$

One method for considering generalzied sampling is to look at the
interplay of vector subspaces.

Multiplying by the comb function is a projection onto a comb-like
subspace. Convolution by the dirac comb is an idenity operation on the
bandlmittied subspace. The subspace in particular is the bandlimitted
subspace. Mutlpiplciation by the box function in the Fourier domain is a
porjetion onto bandlmittied subspace.

Spin Feynman Diagrams
---------------------

Why $\lambda$= Probing Length
-----------------------------

In 2d you can see 2-d circle of foureir transform. From all possible
angles, this gives bandlimitting. Scaling Smapling theorem? Assume the
signal is a scaling signal. How much smapling do we need to reconstruct?
Equivlanet of dirac comb? Connection to renormalization procsdue.
$e^{r\frac{d}{dr}}$ is scaling operator. In what basis is this diagonal
(wavelet? Bessel?)? $e^{a\frac{d}{dx}}$ is translation
$\sum e^{na\frac{d}{dx}}$is dirac comb. Use to reconstruct from band.
$\sum\frac{1}{nr}e^{nr\frac{d}{dr}}$ use to reconstruct from band.
Bessel series in circle. What does it extend to outside circle?

are Bessel functions the natural fgunctions correposnding to radial
scaling the way fourier are to translations and spherical to rotations
and sine to fnite translation? Homogenous polynomials are linear scaling
functions.

Shattering VC dimsneion.

1.22L/D

Intensity vs. field
