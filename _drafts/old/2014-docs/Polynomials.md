### The Optimal Polynomial

For an error measure, we can find a polynomial that does as well or
better than every other polynomial of the same degree at aproximating a
function. Using the maximum error measure

$$e[f,p]=\max_{x\in[-1,1]}|f(x)-p(x)|$$

$$e[f,p*]=\epsilon$$

Meanse that the optimal polynomial does not ever get farther away from
the function than $\epsilon$ at any point. Typically, the polynomial
$p*$ will snake back and forth undershooting and overshooting the
function and will actually achieve that bound N+2 times.

The ideal sampling points are the points for which this polynomial
crosses the function we are evaluating

### Chebyshev Polynomials

Chebyshev Polynomials are the polynomials that are as flat as possible
for their degree, i.e. they are the optimal polynomials of the constant.

$$e[0,T_{n}]=1$$

This rippliness is very much like $\cos(nx)$, which do oscillate nicely
between 1 and -1. However, the cosine is decidedly not a polynomial of
degree n.

The asnwer turns out to be to reparametize the cosine

$$T_{n}(\cos\theta)=\cos(n\theta)$$

$$x=\cos(\theta)$$

$$T_{n}(x)=\cos(n\arccos x)$$

In this form it is not entirely obvious that it is indeed a polynomial.

$$z=e^{i\theta}=\cos(\theta)+i\sin(\theta)$$

$$z^{n}=e^{in\theta}=\cos(n\theta)+i\sin(n\theta)=(\cos(\theta)+i\sin(\theta))^{n}=\sum_{j=0}^{n}i^{j}\left(\begin{array}{c}
n\\
j
\end{array}\right)\cos(\theta)^{n-j}\sin(\theta)^{j}$$

Important Identities:

The Recurrence Relation

$$T_{k+1}=2xT_{k}-T_{k-1}$$

The Beat Identity

$$T_{m}T_{n}=\frac{1}{2}(T_{m+n}+T_{m-n})$$

$$\cos m\theta\cos n\theta=$$

Using $m=0$, $n=1$ this is also the recurrence relation.

If we place our samples at the zeros of a Chebyshev Polynomial

$$l(x)=\frac{T_{n}(x)}{2^{n-1}}$$

Very peculiarly, there exists a discrete analog of the Chebyshev Series.
The Chebyshev series os just the Foruier series in disguise, so perhaps
this is not that unusual.

Physical Basis of Chebyshev?

Taking a fourier series in $\theta$, then making the replacement

$$x=\cos(\theta)$$

Gives you chebyshev polynomials. In this way, you can find the
equivlaent of a great many things in Fourier theory in Chebyshev theory

Making a fourier series in x and then making the raplcement gives you
chebyshev fnctions of the second kind

Should we find full chebyshev and then economize until generlazition is
achieved? Similar to finding Fourier and low passing until
generallization

Newton Interpolation and Shadow Calculus
----------------------------------------

Shadow caclulus at unequal points would use unequal point inteprolation
formulas. Change of variables?

Lagrange Remainder

$$R(x)=\frac{1}{(n+1)!}f^{(n+1)}(\xi)l(x)$$

As the points get closer together

$$l(x)\rightarrow(x-a)^{n+1}$$

And this results compresses down to the result for Taylor Series.

This also expalins why chebyshev points are good, since they cause

$$l(x)=T_{n+1}(x)$$

Which means at least that factor of the remiander is bounded.

Can we use the sampling data itself to estimate $f^{(n+1)}$? Tempting.
And for unknown functions, difficult to see how you could avoid it.

Newton Series to get equivlant of Integral Representation of Error.

Extend These methods to other vector spaces. The pointwise max error
does not respect unitary tranaformation is the thing. That's why some
bases are better than others. Projection onto subspaces. Or sampling
coefficients in one basis (position), find best approximation in another
basis (polynomials) ideal to some other basis (max in position)

Lebesgue Constants

To Lagrange Inteprolate with more points than minimal, write effective
sampled values $f_{i}$ as linear combos of actual oversampled? No\....
That doesn't make sense.

Still, using the bare vandermonde seems naughty.

How does the condition number of vandermonde evolve with more samples?
If I use unfirom sampling, I can multiply columns by a factor, then
stack.

How do Newton Interp and Lagrange Interpolation play together?

$$[x_{1},x_{2},\ldots]l(x)=0$$

$$[x_{1},x_{2}](x-x_{1})(x-x_{2})=0$$

$$[x_{1},x_{2}]l(x)=$$

$$[x,x_{2}]l_{2}=l_{2}$$

$$[x,x_{1}]l(x)=\frac{l(x)}{x-x_{1}}$$

$$w_{j}=\frac{1}{[x_{j},x_{1}]l(x)}$$

Newton Interpolation as triganulat System

6-2 {#section .unnumbered}
===

### Orthogonal Polynomials

Ordinary orthogonal function theory wokrs on continuous intervals. For
exmaple, when we rothognalize the polynomials on the interval $[-1,1]$
with the inner product

$$<f,g>=\int_{-1}^{1}f*(x)g*(x)dx$$

We get the Legendre polynomials.

This is the equivlanet of QR factorization.

Weighted Inner Product is needed to produce certain types of series
(Hermite, Chebyshev, etc.)

$$<f,g>=\int_{-1}^{1}f*(x')g*(x)w(x,x')dx'dx$$

One could consider the sampled point inner product as letting
$w(x,x')=\delta(x-x')\sum_{i}\delta(x-x_{i})$

We can define orthogonal polymmials on the domain of points from the QR
of the Vandermonde matrix

$$\left[\begin{array}{ccccc}
1 & x_{1} & x_{1}^{2} & x_{1}^{3} & x_{1}^{4}\\
1 & x_{2} & x_{2}^{2} & x_{2}^{3} & x_{2}^{4}\\
1 & x_{3} & x_{3}^{2} & x_{3}^{3} & x_{3}^{4}\\
1 & x_{4} & x_{4}^{2} & x_{4}^{3} & x_{4}^{4}\\
1 & x_{5} & x_{5}^{2} & x_{5}^{3} & x_{5}^{4}
\end{array}\right]=V=QR$$

The columns of Q give the values at the point, but more important, the
$R^{-1}$matrix will take us from V to Q. The continuous domain
equlivaent of the Vandermonde matrix is a $\infty/5$ matrix.

$$\left[\begin{array}{ccccc}
| & | & | & | & |\\
1 & x & x^{2} & x^{3} & x^{4}\\
| & | & | & | & |
\end{array}\right]R^{-1}=\text{Something}$$

In this way, a set of points can be mapped to a set of polynomials.

The Lagrange polynomials are the delta function for finite domains

This domain extension is the same as using a fourier series on an
interval and then using the periodic extension outside the interval.

### Lebesgue Constant

It is strange, but the choice of sample points changes the behavior of
the apporximating polynomial drastically

### Chebyshev Points

6-1
===

Curve Fitting anf Interpolation
-------------------------------

The fitting of curves to expiermental data and the interpollation of
numerical data have more in common than they do differences.
Experimental data will be cloaked in the language of porbability, while
numerics are discussed in error bounds. In both cases though, you have
to infer the best you can from sampled values. You may only perform a
finite number of experiments and compute values for a finite number of
function positions.

### Least Squares

First of, we have to be specific about what kind of error we want to
optimize. The classic is the least squares error. We compare our
estimate function evaluated at our sample points$g(x_{i})$ with the
values it should ideally return $y_{i}$

$$E_{LS}=\sum_{i}(y_{i}-g(x_{i}))^{2}$$

### Chebyshev

Picking the points. Quadrature. Minimax. Miniripple

### What is Linear?

### Vandermonde

Consider the polynomials

$$y(x)=\sum a_{n}x^{n}$$

The coeffcients $\{a_{n}\}$ can be packed into a vector. This makes
sense in some ways, since we may add polynomials and perform operations
n polymoials that end up being linear in the coeffcients (such as
differentiation), and multpiplying polynomials is the same and
convolving their coeffcicents. Actually, the coefficients of polynomials
is one of the canonical examples of a vector space.

We could evaluate this polynomial at a set of point $\{x_{n}\}$ by using
a rather strange matrix

$$\left[\begin{array}{c}
y_{1}\\
y_{2}\\
y_{3}\\
y_{4}\\
y_{5}
\end{array}\right]=\left[\begin{array}{ccccc}
1 & x_{1} & x_{1}^{2} & x_{1}^{3} & x_{1}^{4}\\
1 & x_{2} & x_{2}^{2} & x_{2}^{3} & x_{2}^{4}\\
1 & x_{3} & x_{3}^{2} & x_{3}^{3} & x_{3}^{4}\\
1 & x_{4} & x_{4}^{2} & x_{4}^{3} & x_{4}^{4}\\
1 & x_{5} & x_{5}^{2} & x_{5}^{3} & x_{5}^{4}
\end{array}\right]\left[\begin{array}{c}
a_{0}\\
a_{1}\\
a_{2}\\
a_{3}\\
a_{4}
\end{array}\right]This$$ matrix is called the Vandermonde matrix. We can
rewrite this in vector notation

$$y=Va$$

This is quite a nice matrix since we can use it to find coefficients for
an N-degree polynomial from N sample points.

$$a=V^{-1}y$$

Even better, we can find fitting polynomials. Using the least squares
error

$$E_{LS}=\sum_{i}(y_{i}-P(x_{i}))^{2}$$

We can rewrite this in vectr form as

$$E_{LS}=(y-Va)^{T}(y-Va)$$

Note that V is now not square. It is tall and skinny. We may
differentiate with respect to a to find the minimum

$$V^{T}Va=V^{T}y$$

This is called the Normal equation. We solve it

$$a=(V^{T}V)^{-1}V^{T}y$$

The combination on the right hand side is called the pseudo-inverse of
the matrix.

$$V^{+}=(V^{T}V)^{-1}V^{T}$$

It is indeed the left inverse of the rectangular matrix in the sense
that

$$V^{+}V=(V^{T}V)^{-1}V^{T}V=I$$

In many rectangular matrix situations, you can blindly replace what
would ordinarily be the inverse with the pseudo inverse and get what you
wanted, hence its conceptual utility.

The simple monomial basis is not the only basis for polynmials. We could
also work with the Chebyshev polynomials, or Legendre Polynmoials, or
what have you. To estimate the coefficients in these other basis, they
are related to the coefficents in the monomial basis by linear
transfromations.

The Vandermonde matrix is a numerical shit pie however.

The eigenvalues of the Vandermonde matrix are

The determinant of the Vandermonde matrix

Lagrange polynomials

We can easily find a polynomial that has zeros at a set of points. If we
want a polynomial that is zero at all our sample points except $x_{j}$we
get

$$\tilde{l}_{j}(x)=(x-x_{1})(x-x_{2})(x-x_{3})\ldots(x-x_{j-1})(x-x_{j+1})\ldots$$

This function will have some wacky value at $x_{j}$ itself. We can
normalize it by the constant $\tilde{l}_{j}(x_{j})$

$$l_{j}(x)=\frac{\tilde{l}_{j}(x)}{\tilde{l}_{j}(x_{j})}$$

Now we have

$$l_{j}(x_{i})=\delta_{ij}$$

So, if we have

$$P(x)=\sum_{i}y_{i}l_{i}(x)$$

This polymmoial does fit exactly at the sample points

$$P(x_{j})=\sum_{i}y_{i}l_{i}(x_{j})=\sum_{i}y_{i}\delta_{ij}=y_{j}$$

$$l(x)=(x-x_{1})(x-x_{2})(x-x_{3})\ldots$$

$$\tilde{l}_{j}(x)=\frac{l(x)}{x-x_{j}}$$

$$w_{j}=\frac{1}{\tilde{l}_{j}(x_{j})}$$

We get the barycentric formula

$$P(x)=\sum w_{j}y_{j}\frac{l(x)}{x-x_{j}}$$

Newton Series

Barycentric algorthim

Matrix Properties

Sylvester Matrix

$V^{-1}$has monomial coefficents of Largange basis $VV^{-1}=I$

### Overfitting

Stability of error/intepolation. Why does more data points make SVD of
data more stable? Update formula for SVD, Recursive least squares

### Taylor Series Error

We start with s simple identity

$$f(x)=f(a)+\int_{a}^{x}f'(t)dt$$

We can integrate by parts.

$$u=f'(t)$$

$$dv=dt$$

$$v=t-x$$

$$du=f''(t)dt$$

$$f(x)=f(a)+f'(t)(t-x)]_{a}^{x}-\int_{a}^{x}f''(t)(t-x)dt$$

$$f(x)=f(a)+f'(a)(x-a)-\int_{a}^{x}f''(t)(t-x)dt$$

We can do so again

$$u=f''(t)$$

$$dv=(t-x)dt$$

$$v=\frac{1}{2}(t-x)^{2}$$

$$du=f'''(t)dt$$

$$f(x)=f(a)+f'(a)(x-a)-f''(t)\frac{1}{2}(t-x)^{2}]_{a}^{x}+\int_{a}^{x}f'''(t)\frac{1}{2}(t-x)^{2}dt$$

$$f(x)=f(a)+f'(a)(x-a)+\frac{1}{2}f''(a)(x-a)^{2}+\frac{1}{2}\int_{a}^{x}f'''(t)(t-x)^{2}dt$$

And so on. Clearly, we are developing the Taylor expansion, but what is
interesting is the error integral

$$E_{n}(x)=\frac{1}{n!}\int_{a}^{x}f^{(n+1)}(t)(t-x)^{n}dt$$

This term contains the difference between the function and the truncated
Taylor series $T_{n}(x)$. If tthis integral is directly evaluatable,
then approximations are silly. Its use is in bounding the error. Any
bound on this integral becomes a bound on the error of the Taylor
series. We could look at the pointlike error

$$|f(x)-T_{n}(x)|=|E_{n}(x)|<C$$

Or we could look at some kind of average square error

$$\int_{a}^{b}|f(x)-T_{n}(x)|^{2}dx=\int_{a}^{b}|E_{n}(x)|^{2}<C$$

A very simple bound of any integral is given by

$$\int_{a}^{b}g(x)dx\le\int_{a}^{b}\max_{t}g(t)dx=\max_{t}g(t)(b-a)$$

The integrand is always less than its maximum value, so if we replace
the function with its maximum value inside the integral, we get a bound.

For example, a bound on the error for $f(x)=e^{x}$,
$T_{2}(x)=1+x+\frac{1}{2!}x^{2}$ on the interval $[0,1]$ is given by

$$E_{n}(x)=\frac{1}{2!}\int_{0}^{x}e^{t}(t-x)^{2}dt\le\frac{1}{2!}\int_{0}^{1}e^{t}(t-x)^{2}dt\le\frac{1}{2!}\int_{0}^{1}e^{1}(1-x)^{2}dt=\frac{e}{2}(1-x)^{2}$$

### Lagrange Remainder

The mean value theorem says there is a place where the slop of the
secant matches the slope of a tangent somewhere inside the secant
region. Try it.

For some $a\le\xi\le b$

$$\frac{f(b)-f(a)}{b-a}=f'(\xi)$$

We can also constyruct the taylor series from the bottom up.

$$f^{(n-1)}(x)=f^{(n-1)}(a)+\int_{a}^{x}f^{(n)}(t)dt$$

$$f^{(n)}(x)-f^{(n)}(a)=(x-a)f^{(n+1)}(\xi)$$

$$f^{(n)}(x)=f^{(n)}(a)+(x-a)f^{(n+1)}(\xi)$$

$$$$

$$f^{(n-1)}(x)=f^{(n-1)}(a)+\int_{a}^{x}f^{(n)}(a)+(t-a)f^{(n+1)}(\xi)dt$$

We can do both of these integrals immediately

$$f^{(n-1)}(x)=f^{(n-1)}(a)+f^{(n)}(a)(x-a)+\frac{1}{2!}(x-a)^{2}f^{(n+1)}(\xi)$$

And so on until we get all the way back to the beginning

$$f(x)=f(a)+f^{1}(a)(x-a)+\frac{1}{2!}(x-a)^{2}f^{(2)}(a)+\ldots+\frac{1}{n!}f^{(n)}(a)(x-a)^{n}+\frac{1}{(n+1)!}(x-a)^{n+1}f^{(n+1)}(\xi)=T_{n}(x)+\frac{1}{(n+1)!}(x-a)^{n+1}f^{(n+1)}(\xi)$$

The point of knowing that $\xi$ exists is to find a bound

$$f(x)-T_{n}(x)=E_{n}(x,\xi)\le\max_{\xi}E_{n}(x,\xi)$$

### Regularization and Cross-Validation

We do not trust the computer, or at least you should not. Occasionally,
it spits back out somethng that you just know is total bullcrap, a
result that can't be right. Then you go back thorugh your code and see
where you went awry. This is an indication that we don't really go into
the process blind. We always have some kind of checks and balances, some
kind of rough idea what answer we're looking for, even if only a range
of magnitudes.

There are some interperations of this. The Bayesians say that you should
quantify your prior expectations as well as you can and include them in
your analysis. Then the computer will feel some weight to not defy them.

Another intepretation is that it is not that our intuition needs to be
included, but that our intuition stems from a principle of
generalization. Over the years, we get a feeling for when the amount of
data we have is sufficient to generalize outside of the data.

### Bernstein Polynomials

![image](bernstein.png)

The bernstein polynomials is sort of a nice clean polynomial version of
Gaussians.

$$b_{rn}=\left(\begin{array}{c}
n\\
r
\end{array}\right)x^{r}(1-x)^{n-r}$$

The form is chosen so that we can use and abuse the binomial expansions

$$(z+y)^{n}=\sum_{r=0}^{n}\left(\begin{array}{c}
n\\
r
\end{array}\right)y^{r}(z)^{n-r}$$

$$1=1^{n}=(x+(1-x))^{n}=\sum_{r=0}^{n}\left(\begin{array}{c}
n\\
r
\end{array}\right)x^{r}(1-x)^{n-r}=\sum_{r=0}^{n}b_{rn}$$

For large enough n, $b_{rn}$is mostly localized around $\frac{r}{n}$.
The maximum is located there

$$\partial_{x}b_{rn}=0=\left(\begin{array}{c}
n\\
r
\end{array}\right)rx^{r-1}(1-x)^{n-r}-\left(\begin{array}{c}
n\\
r
\end{array}\right)x^{r}(n-r)(1-x)^{n-r-1}=\left(\begin{array}{c}
n\\
r
\end{array}\right)x^{r-1}(1-x)^{n-r-1}(r(1-x)+(r-n)x)$$

$$r(1-x)+(n-r)x=r-nx=0$$

$$x=\frac{r}{n}$$

$$\partial_{x}^{2}b_{rn}=$$

The binomial coeffcients are connected to gaussians due to diffisuion.
Discrete diffusion is solved by binomial coefficients, whereas
continuous diffusion is solved by gaussians

$$B_{n}=\sum_{r}f(\frac{r}{n})b_{rn}(x)$$

Note that $B_{n}$ does not neccessarily match f at any of the sampled
points. This polynomial sort of has a different feel to it than the more
commonly seen approximating polynomials that exactly match at the
smapled points.

The Weierstrauss Approximation theorem says that polynomials can
converge uniformaly to any continuous function on the interval $[0,1]$.
This $B_{n}$ works.

Cauchy Integral Stuff
---------------------

The taylor series can be written as a contour integral

$$T_{n}(x)=\sum_{j=0}^{n}\frac{1}{2\pi i}\int\frac{(x-a)^{j}}{(z-a)^{j+1}}f(z)dz$$

$$f(x)-T_{n}(x)=\sum_{j=n+1}^{\infty}\frac{1}{2\pi i}\int\frac{(x-a)^{j}}{(z-a)^{j+1}}f(z)dz$$

$$\sum_{j=n+1}^{\infty}\frac{(x-a)^{j}}{(z-a)^{j+1}}=\frac{(x-a)^{n+1}}{(z-a)^{n+2}}\frac{1}{1-\frac{(x-a)}{(z-a)}}=\frac{(x-a)^{n+1}}{(z-a)^{n+1}}\frac{1}{z-x}$$

$$f(x)-T_{n}(x)=\frac{1}{2\pi i}\int\frac{(x-a)^{n+1}}{(z-a)^{n+1}}\frac{1}{z-x}f(z)dz$$

The obvious bound for any integral is

$$|g(z)|\le M$$

$$|\int g(z)dz|\le ML$$

This and the cuachy-schwartz inequality can both come under the umbrella
of Holder's inequlaity

### Rolle's Theorem

Rolle's theorem is a preliminary to the mean value thoerem.

It's easyish to show that the derivative must be zero at a minimum or
maximum if the function is differenitable.

To apply Rolle's thoerem, find a function that is zero at two endpoints
of an interval.

$$f(x)-p_{n}(x)-Ml(x)=g(x)$$

$$p_{n}(x)=\sum_{j}l_{j}(x)f(x_{j})$$

$$M=\frac{f^{(n+1)}(\xi)}{(n+1)!}$$

The Lagrange inteprolation is designed to match the function

$$f(x_{i})=p_{n}(x_{i})$$

g is presumably conttinuous and differentiable and whatnot. $l(x_{i})=0$
as well.

so we have

$$g(x_{i})=0$$

Thanks to Rolle's Theorem, we've got a point between each of our N+1
sample point $x_{i}<x_{1i}<x_{i+1}$for which $g'(x_{1i})=0$. So now
g'(x) definetly has N zeros. We can do this again to determine g"(x) has
N-1 zeroes and so on. Eventually we get $g^{N+1}(x_{N+1,1})=0$, which
gives us the desired reult.

From Taylor To Lagrange
-----------------------

Basically, to shift to the inteprolated equivlaent of a taylor series
concept, replace $(x-a)^{n}$ with $l(x)$ or $l_{i}(x)$

$$f(x)-L_{n}(x)=\frac{1}{2\pi i}\int\frac{l(x)}{l(z)}\frac{1}{z-x}f(z)dz$$

You pick up the poles, the unused terms in the l(z) become the weight
term and $\frac{l(x)}{x-x_{i}}$is $l_{i}(x)$. We also pick up the term

Perhaps I should look into a possible connection between secular
equation for eigenvalue update

$$L_{n}(x)=\sum_{j}\frac{1}{2\pi i}l_{j}(x)\int\frac{1}{z-x_{j}}f(z)dz$$

$$q(x,z)=\sum_{j}l_{j}(x)\frac{1}{z-x_{j}}$$

### Sinc

Lagrange interpolation on an inifnite number of points becomes the sinc
functions

I guarantee no convergence

$$l(x)=\sin(\pi x)=\pi z\prod_{n=-\infty}^{\infty}(1-\frac{z}{n})$$

$$sinc(x)=l_{0}(x)=\prod_{n=-\infty}^{\infty}(1-\frac{z}{n})$$

### Periodic Lagrange Becomes Fourier-esque

$$l(x)=\prod\sin(\frac{x-x_{i}}{2})$$

$$l_{i}(x)=l(x)\frac{1}{2l'(x_{i})\sin(\frac{x-x_{i}}{2})}$$

$$l(x)=\prod(e^{ix}-e^{ix_{i}})=\prod e^{i\frac{x_{i}+x}{2}}(e^{i\frac{x-x_{i}}{2}}-e^{i\frac{x_{i}-x}{2}})$$

$$w=w(x)$$

$$w_{i}=w(x_{i})$$

$$w(x)=e^{ix}$$

### Gauss Quadrature

zeros of those eigenfunctions baby

### Convergence Regions

The convergence of Taylor series is in annular regions. They get hung up
at the poles

Interpolation formulas converge in new regions

### Stability of Interpolation

Sensititvy - conitnuity

Ein is in sampled points, Emax is best polynomial error. Eout is actual
maximum error of fitted poly.

pseudospectra of vandermonde?

Rational Approximation
----------------------
