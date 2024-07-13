Introduction
============

Strings and Membranes: Why should we care? In terms of direct
applications to building better washing machines, many would say we
don't. This is an attitude that is common towards most physical models
and almost all mathematical techniques that the eggheads and four-eyes
of the world churn out. But upon reflection, even if brighter brights
and whiter whites are your goal, these things are worth looking into. A
washing machine or a car or steel beam or even the electromagnetic field
is essentially a big mixed-up membrane in essence and can be simulated
on a computer as such. The focus on strings and membranes is just
because they are a simple testing ground for our mathematical techniques
of solving partial differential equations. A string really can't have
much simpler dynamics. What could we cut out? We could perhaps cut the
string up into a finite number of balls and springs. Typically that's
how the subject is introduced. Honestly, such a situation is more
complicated, not less. Figuring out how to deal with 100 balls and
springs and the indexes they bring with them is a tad tougher than an
infinite number of them. Go figure.We could make the string inflexible,
but then it has no dynamics at all! Ignoring washing machines engineers
for the moment and focusing on the needs of physicists, you better have
a pretty darn good grasp of classical fields if you want to doggy paddle
your way through modern physics. So let's do it.

Strings
=======

We've got a rubber band stretched between two posts. I will use the term
string, rubber band, and spring interchangeably, because a dog is a cat
as far as its properties of elasticity and vibrational modes go. If we
want to make our string move, we can appeal to the least action
principle and Lagrangian mechanics.

The Least Action principle is a very strange stance to take on dynamics,
in that you assume knowledge of the initial and final configuration of
some system and how long it took to do it. But how exactly did it do it?
The answer takes the form of a game. We give points for certain
qualities of paths and take away points for others and try and figure
out which path gets the most points. Pretend you are watching a fat
child. He needs to walk to Arby's in twenty minutes to make the
breakfast deadline. The fatter he is, the less he'll like to go fast or
divert from his path. Going slow at any point along his path means he'll
have to go faster elsewhere to make the twenty minute deadline. So you
expect uniform speed. However, perhaps there are parks along the way
where he'd love to dawdle and smell the flowers. By assigning numerical
weights to all these factors (hungriness, love of flowers, etc.) you can
calculate which path he will take to.

Now, our fat boy shall become a string. We start by saying the action S
is the time integral of the Lagrangian, which is given by the kinetic
energy minus the potential energy.

$$S=\int Ldt$$

$$L=T-U$$ Let's write down the expression for the potential energy of
the system. The energy contained in your everyday spring is

$$U=\frac{1}{2}k(x-x_{0})^{2}$$

This is great, except that our rubber band may not be stretched
uniformly. So let's look at the big rubber band as a bunch of little
rubber bands tied together and add up the energy of each. The length of
a baby band is given by the Pythagorean theorem, a formula you may
recognize from the arclength of a curve y(x)

$$ds=\sqrt{dx^{2}+dy^{2}}=dx\sqrt{1+(\frac{dy}{dx})^{2}}$$

The baby band also has a equilibrium length. Here we'll already start
the approximations.We'll assume a uniform equilibrium length, (i.e. one
that isn't a function of where we are along the rubber band). For
stretching that is small in the horizontal direction, this is pretty
much true.

$$ds_{0}=\frac{L_{0}}{L}dx$$

We assign the constant in front of the $dx$ so that the sum of all the
equilibrium lengths equals the total equilibrium length $L_{0}$

$$\intop_{0}^{L}ds_{0}=\frac{LL_{0}}{L}=L_{0}$$

Another factor that we must take into account is that shorter springs
are stiffer. If you cut a spring in half, it takes twice the force to
stretch it the same distance, i.e. the spring constant is doubled. Cut
in thirds, the force is tripled. We can represent that by writing

$$dk=\frac{Lk}{dx}$$

Where $dk$ is the spring constant of one of our small springs. Amusingly
for small spring lengths, $dk$is not small, but will blow up. Luckily,
one we put our whole expression together, the small stretching sizes of
the little springs will avert this problem.

$$U=\sum\frac{1}{2}dk(ds-ds_{0})^{2}=\sum\frac{1}{2}\frac{Lk}{dx}(dx\sqrt{1+(\frac{dy}{dx})^{2}}-\frac{L_{0}}{L}dx)^{2}=\intop_{0}^{L}\frac{1}{2}Lkdx(1+(\frac{dy}{dx})^{2}-\frac{2L_{0}}{L}\sqrt{1+(\frac{dy}{dx})^{2}}+\frac{L_{0}^{2}}{L^{2}})$$

Let's do some handwaving approximations. We'll use the fact that the
stretching is small in the y direction to approximate that ugly square
root with the binomial theorem

$$\sqrt{1+(\frac{dy}{dx})^{2}}\approx1+\frac{1}{2}(\frac{dy}{dx})^{2}+\ldots$$

Integrate out the things we can

$$U=\frac{1}{2}(L^{2}+L_{0}^{2}-2L_{0}L)k+\frac{1}{2}k(L-L_{0})\intop_{0}^{L}(\frac{dy}{dx})^{2}dx=\frac{1}{2}k(L-L_{0})^{2}+\frac{1}{2}\tau\intop_{0}^{L}(\frac{dy}{dx})^{2}dx$$

Interesting! The first part is clearly the energy it takes to stretch
the string from $L_{0}$ to $L$. There is nothing we can do about this
energy since the ends of the strings are fixed, so we can ignore it. It
is unminimizable under the constraints of the problem. In the second
term, I have noticed that $k(L-L_{0})$ is just the tension in the spring
according to Hooke's law, which I have labeled as $\tau$.

The hard part is over. We found the potential of a rubber band. The
kinetic energy is a cinch by comparison. Again, we break the band up
into lots of little rubber bands. If we assume they only move vertically
then

$$dT=\frac{1}{2}dmv^{2}=\frac{1}{2}dm(\frac{dy}{dt})^{2}$$

The tiny bit of mass each bit of rubber band has can be written in terms
of a mass per unit length of string $\sigma$

$$dm=\sigma dx$$

$$T=\int dT=\intop_{0}^{L}\frac{1}{2}\sigma(\frac{dy}{dt})^{2}dx$$

The action for a free string is then

$$S=\int\left[T-U\right]dt=\iint\left[\frac{1}{2}\sigma(\frac{dy}{dt})^{2}-\frac{1}{2}\tau(\frac{dy}{dx})^{2}\right]dxdt$$

From this we get the differential equation

$$\sigma\frac{d^{2}y}{dt^{2}}-\frac{d}{dx}(\tau\frac{dy}{dx})=0$$

In our particular derivation, we've been assuming $\tau$is constant for
simplicity. It is possible to avoid this constraint and still get the
same equations up to this point. Here we utilize the fact $\tau$is
constant to pull it out of the derivative and rearrange some terms.

$$\frac{\sigma}{\tau}\frac{d^{2}y}{dt^{2}}-\frac{d^{2}y}{dx^{2}}=\frac{1}{c^{2}}\frac{d^{2}y}{dt^{2}}-\frac{d^{2}y}{dx^{2}}=0$$

By jove, we've done it.

Green's Functions
=================

The definition that is given for a Green's function is the following
differential equation

$$LG(x,a)=\delta(x-a)$$

Where L is a differential operator acting on the x variable. There are
two 1-D systems that provide a visual of what a Green's function looks
like that I believe we should examine before we put on our fancy hats
and write down differential equations.

The first is of a kicked particle. We guarantee that a particle is at
$x=0$ at time $t=0$ and time $t=T$, which are not strange conditions
when considering least action type problems. We also know that it gets
kicked with an impulse J at time t'. The equation of motion for this
situation is

$$m\frac{d^{2}x}{dt^{2}}=J\delta(t-t')$$

We can visualize this system and realize that under no force, the
particle goes in a straight line. The kick instantaneously changes the
velocity of the particle in just the right way that it gets where it
needs to go in the right amount of time. So we can tell that the

The second is the stationary string. We stretch our rubber band between
two posts. The two ends struck on the posts can't move (boundary
conditions). We hang a weight from a hook on this rubber band. What
shape does the rubber band take? It takes on this triangle shape.

![image](String_Forcediagram.png)

If you don't believe me, try it. Now, from Freshman physics, we can
solve for the numerical shape of this triangle.

All the forces ($\vec{W},\vec{T_{2}},\vec{T_{1}})$ acting on the point
must cancel each other for equilibrium to occur. Breaking this into
components

$$T_{1x}=T_{2x}$$

$$T_{1y}+T_{2y}=W$$

If we assume small displacement of the rubber band from its original
position, it is also safe to approximate that the x-component of the
tension has the same value of the tension in the rubber band before the
string was hung

$$T_{2x}\approx T\approx T_{1x}$$

Since the tensions $\vec{T_{1}}$and $\vec{T_{2}}$lie along the rubber
band, we can use similar triangle tricks to get the slopes of those two
lines.

$$m_{1}=\frac{-y}{a}=\frac{-T_{1y}}{T_{1x}}\approx\frac{-T_{1y}}{T}$$

$$m_{2}=\frac{y}{L-a}=\frac{T_{2y}}{T_{2x}}\approx\frac{T_{2y}}{T}$$

Combining these equations, we get the relation

$$\frac{y}{a}+\frac{y}{L-a}=m_{2}-m_{1}=\frac{W}{T}$$

So now we have three facts about the function y(x) describing the
vertical displacement of the rubber band at a point x.

1.  The difference between the two slopes is $\frac{W}{T}$.

2.  The rubber band has no displacement at either end of the rubber
    band. Thus $y(0)=0$ and $y(L)=0)$

3.  The two lines meet at the point where the weight hangs. Thus
    $y^{+}(a)=y^{-}(a)$

Using these three constraints, we can write out the function that
describes the y position of the rubber band at a point x with a weight
hanging at a

$$y_{a}(x)=\begin{cases}
\frac{-W}{TL}x(L-a) & x<a\\
\frac{-W}{TL}a(L-x) & x>a
\end{cases}$$

Problem solved!

Now, how is this useful? While a weight hanging on a rubber band problem
is extremely fascinating, what if we hung two weights, or some other
cockamamie collection of weights? We'll have to go over everything all
over again!

Not so!

Solving this problem for one weight essentially solves the entire
problem for any configuration of weights by a superposition principle.
This is perhaps not obvious by the Physics 101 arguments we've given so
far, but is extremely obvious from the perspective of the differential
equation or linear algebra.

We could say, "Well, the string and mass will configure itself into its
minimum energy configuration." We already derived the formula for the
potential energy of the spring.

$$U=\frac{1}{2}T\intop(\frac{dy}{dx})^{2}dx$$

Now, there is also the potential energy of the mass hanging on the
rubber band

$$U=mgy(a)=Wy(a)$$

So the total potential energy (ignoring the constant from the initial
stretching)

$$U=Wy(a)+\frac{1}{2}T\intop_{0}^{L}(\frac{dy}{dx})^{2}dx$$

We can use a Dirac Delta function to

$$U=\intop_{0}^{L}W\delta(x-a)y(x)+\frac{1}{2}T(\frac{dy}{dx})^{2}dx$$

And now the Euler Lagrange Equations

$$W\delta(x-a)=T\frac{d^{2}y}{dx^{2}}$$

Our previously derived solution should fit this differential equation.
When $x\neq a$, $y(x)$ is a linear function, so its second derivative
vanishes. We can integrate our equation across a small area around a

$$\intop_{a-\epsilon}^{a+\epsilon}dx\frac{W}{T}\delta(x-a)=\frac{W}{T}=\intop_{a-\epsilon}^{a+\epsilon}dx\frac{d^{2}y}{dx^{2}}=\frac{dy}{dx}^{+}-\frac{dy}{dx}^{-}=m_{2}-m_{1}$$

This is the same condition that we derived our solution from., so it all
hangs together. However, now it is clear that we can represent the
solution of many weights as the sum of solutions of one weight. We write
this as

$$y(x)=W_{1}y_{a_{1}}(x)+W_{2}y_{a_{2}}(x)+W_{3}y_{a_{3}}(x)+\ldots$$

Such that each individual $y_{a_{n}}(x)$satisfies the equation

$$\delta(x-a_{n})=T\frac{d^{2}y_{a_{n}}}{dx^{2}}$$

Then through the linearity of $\frac{d^{2}}{dx^{2}}$

$$\sum W_{n}\delta(x-a_{n})=T\frac{d^{2}y}{dx^{2}}$$

And running the Euler Lagrange equation backwards, we see that this
function minimizes

$$U=\intop_{0}^{L}\sum W_{n}\delta(x-a_{n})y(x)+\frac{1}{2}T(\frac{dy}{dx})^{2}dx$$

The other main way to look at Green's functions is purely as an
algebraic tool, totally abstracted from the physics of pumpkins and
rubber bands.

Let's start with the absolutely simplest class algebraic problem that I
know how to construct.

$$ay=0$$

In this equation, $a$ is a number, like 3 or 743507683, but not 0, and y
is an unknown number. This problem is so simple, that its solution may
even be considered an axiom of numbers. This equation has one solution

$$y=0$$

Great. Now suppose we add a "forcing term"

$$ay=b$$

What is the solution to this equation?

$$y=\frac{b}{a}$$

Awesome. Let's define the Green's Function (Green's Number?) for this
equation

$$aG=1$$

Which can be solved for $a\neq0$

$$G=\frac{1}{a}=a^{-1}$$

So now we know exactly how to solve any equation with a forcing term

$$y=0+Gb$$

I explicitly included the $0$ because that is the solution to the
unforced equation. This inclusion will make more sense as we go along.

As a side track, consider the new equation with a forcing term
proportional to y

$$ay=b+cy$$

There are two ways to go about this. We can define a new equation
similar to the first

$$a'=a-c$$

$$a'y=b$$

Then laboriously solve for the new Green's function

$$G'=\frac{1}{a'}=\frac{1}{a-c}$$

to get our solution

$$y=G'b=\frac{b}{a-c}$$

This was awful. We had to find a whole new Green's Function! A much
better approach is to find an infinite series solution to the problem by
iteration. Let's assume the forcing term wasn't special and write down
the solution

$$G=\frac{1}{a}$$

$$y=G(b+cy)$$

That didn't seem to get us very far. If that is a solution, you can
break my legs. Our solution looks like another problem, just as hard as
the original problem. However, let's write this down as a recurrence
relation

$$y_{n+1}=G(b+cy_{n})$$

We can dignify this as a solution scheme by saying that if this sequence
converges, then it has converged to a solution. We make no guarantees as
to whether it will converge however. Let's make an initial guess

$$y_{0}=0$$

Now let's iterate that sucker

$$y_{1}=G(b+0)=Gb(1)$$

$$y_{2}=G(b+cG(b+0))=Gb+G^{2}bc=Gb(1+Gc)$$

$$y_{3}=G(b+cG(b+cG(b+0)))=Gb+G^{2}bc+G^{3}bc^{2}=Gb(1+Gc+G^{2}c^{2})$$

$$y_{n}=Gb\sum_{i=0}^{n-1}(Gc)^{n}$$

That's a geometric series! It has the solution

$$y_{n}=Gb\frac{1-(Gc)^{n}}{1-Gc}$$

$$\lim_{n\rightarrow\infty}y_{n}=\frac{Gb}{1-Gc}\text{, for }|Gc|<1$$

Expanding G as $\frac{1}{a}$,

$$y=\frac{b}{a(1-\frac{c}{a})}=\frac{b}{a-c}$$

Which is the correct solution. This iterative series that we produced is
called the Neumann Series if you're a mathematician, or in physicist
term, the Dyson Series or the Born Series. It is obviously a ridiculous
way to go about things for our simple equation, but for complicated math
things it is sometimes your only hope. Even in this example the areas of
convergence are not trivial. We happened to know how it converged
because the geometric series is one of the few things we're pretty sure
we understand. Some very clever fellows have determined that power
series of that sort converge in circles in the complex plane, but what
about the equation

$$ay=b+cy^{5}$$

This equation is a quintic polynomial equation, which has 5 solutions.
Solving iteratively by the recurrence relation

$$y_{n+1}=G(b+cy_{n}^{5})$$

Computing a rough estimate of converging values of $y_{0}$in the complex
plane using values of G, b, and c picked out of a hat gives a graph like
this

![image](Python/convergenceregion.png)

Nonlinear iterative equations of this sort are a rabbit hole that you
could sink your whole life down and never fill. They are a classic
generator of fractal sets, such as the Julia set and the Mandelbrot set.
Definitely worth a Wikipedia search, but entirely off topic.

Let's look at the next level of complication, a matrix equation

$$A\underline{x}=0$$

$$A\underline{x}=\underline{b}$$

Now A is a matrix like this

$$A=\left(\begin{array}{cccc}
678 & 678 & 5 & 4\\
3 & 6 & 4 & 6\\
8 & 5 & 7 & 1\\
67 & 4 & 6 & 457
\end{array}\right)$$

and $\underline{x}$ and $\underline{b}$ are vector such as

$$\underline{x}=\left(\begin{array}{c}
6\\
7\\
5\\
20394
\end{array}\right)$$

A linear differential equation has a roughly equivalent matrix form. We
can split up the interval L into N chunks of length $\frac{L}{N}$. This
is the essence of the discrete step method for numerically solving
differential equations. We can write a vector that looks a lot lot like
our function by filling it with the values of the function at the edges
of our chunks. For example, if we broke the interval L into 4 chunks,

$$\underline{f_{4}}=\left(\begin{array}{c}
f(0)\\
f(\frac{L}{4})\\
f(\frac{2L}{4})\\
f(\frac{3L}{4})\\
f(L)
\end{array}\right)$$

As we break the interval into smaller and smaller chunks, the vector
will represent the function better and better. We can write a first
derivative matrix

$$f'(x)\approx\frac{f(x+\Delta x)-f(x)}{\Delta x},\;\Delta x=\frac{L}{N}$$

For the interval separated into 4 chunks this can be written out in
matrix form

$$\Delta=\frac{4}{L}\left(\begin{array}{ccccc}
-1 & 1 & 0 & 0 & 0\\
0 & -1 & 1 & 0 & 0\\
0 & 0 & -1 & 1 & 0\\
0 & 0 & 0 & -1 & 1
\end{array}\right)$$

As we let $N\rightarrow\infty$, this matrix will produce a vector that
is closer and closer to the first derivative of the function $f(x)$.
Notice that this matrix is not a square matrix, and thus not invertible.
The derivative throws away a constant from the function, so a little bit
of information is lost. This matrix does the same thing, reducing the
dimension of our function vector by one. Similarly, we can construct a
second derivative matrix

$$\Delta^{2}=\frac{16}{L^{2}}\left(\begin{array}{ccccc}
1 & -2 & 1 & 0 & 0\\
0 & 1 & -2 & 1 & 0\\
0 & 0 & 1 & -2 & 1
\end{array}\right)$$

We lost another dimension! How in the world can we solve the matrix
equation $\Delta^{2}\underline{f}=\underline{g}$ when
$\Delta^{2}$doesn't have the same dimensions as $\underline{f}$? The
answer is that we have to incorporate the boundary conditions. The
separation between a differential equation and boundary conditions is a
somewhat arbitrary one. One should really never be considered without
the other. Let's pad out our matrix with zeroes, to make it square.

$$\Delta^{2}=\frac{16}{L^{2}}\left(\begin{array}{ccccc}
0 & 0 & 0 & 0 & 0\\
1 & -2 & 1 & 0 & 0\\
0 & 1 & -2 & 1 & 0\\
0 & 0 & 1 & -2 & 1\\
0 & 0 & 0 & 0 & 0
\end{array}\right)$$

Now we create a boundary value matrix

$$B=\left(\begin{array}{rrrrr}
1 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 1
\end{array}\right)$$

This is the appropriate matrix for specifying values at the endpoints of
the interval. Now the matrix $B+\Delta^{2}$ is invertible. Notice that
the matrix B doesn't scale with the number of chunks, so as the number
of chunks gets large, it becomes more natural to think of B as separate
from $\Delta^{2}$until it ends up like this:

$$\frac{d^{2}y}{dx^{2}}=F(x),\;y(0)=0,\;y(L)=0$$

The following matrix is a good representation of this differential
equation

$$K=\frac{16}{L^{2}}\left(\begin{array}{ccccc}
1 & 0 & 0 & 0 & 0\\
0 & -2 & 1 & 0 & 0\\
0 & 1 & -2 & 1 & 0\\
0 & 0 & 1 & -2 & 0\\
0 & 0 & 0 & 0 & 1
\end{array}\right)$$

$$K\underline{y}=\frac{L^{2}}{16}\left(\begin{array}{c}
0\\
\underline{F}\\
0
\end{array}\right)$$

The first and last row of the matrix K guarantee that the
components$y_{0}$and $y_{L}$both equal zero, which is the same as our
boundary conditions in the differential equation. The middle section is
the second derivative matrix with some ones cut out of it. Why did I cut
out these ones? First of all, I was able to do it because those ones
didn't matter. Since we know$y_{0}$and $y_{L}$both equal zero, the ones
that have been removed added nothing to the equation. Secondly, it keeps
our matrix pleasingly symmetric, a property that is well worth seeking
out by any means necessary.

The matrix K possesses an inverse G such that

$$GK=I$$

With this G in hand, we can easily solve our matrix equation

$$\underline{y}=G\frac{L^{2}}{16}\left(\begin{array}{c}
0\\
\underline{F}\\
0
\end{array}\right)$$

To sate your curiosity, here is G for the K we've been considering

$$G=\frac{1}{4}\left(\begin{array}{ccccc}
4 & 0 & 0 & 0 & 0\\
0 & -3 & -2 & -1 & 0\\
0 & -2 & -4 & -2 & 0\\
0 & -1 & -2 & -3 & 0\\
0 & 0 & 0 & 0 & 4
\end{array}\right)$$

Not so interesting perhaps. Let's look at the plots of the rows of G

![image](Python/Green'sfunc4chunks.png)

Hmm, Interesting. Now let's take a look at the green's function of an
interval separated into 50 chunks.

![image](Python/50chunksgreen'sfunc.png)

We see that the rows of this matrix seem to form piecewise linear
functions, with an envelope that appears to be parabolic. That's exactly
what we got for our green's functions of strings earlier!

For natural boundary conditions $\frac{dy}{dx}=0$ at $x=0,L$

$$K=\frac{16}{L^{2}}\left(\begin{array}{ccccc}
-1 & 1 & 0 & 0 & 0\\
1 & -2 & 1 & 0 & 0\\
0 & 1 & -2 & 1 & 0\\
0 & 0 & 1 & -2 & 1\\
0 & 0 & 0 & 1 & -1
\end{array}\right)$$

Is a nice natural symmettric version of the matrix

I can do a similar derivation for what neumann condition solutions
should look like. Now on end of the stretched rubber band is freely
sliding on a slick pole. That end of the string will not support any
vertical force in equilibirum, but will take any horizontal force that
is required of it. If we hang a weight at point a, We still have three
forces in equilibrium, but the torque connecting to the sliding end must
be horizontal and all of the vertical weight must be held by the fixed
end of the string.

Why are these called natural boundary conditions? Because they're the
only ones that occur in nature of course! No. That's not even close to
true.

We call these Dirichlet, Neumann, and Robin Boundary conditions, because
we prefer to give credit than give them self-explanatory titles, not
that those guys didn't earn their keep. I predict that in 1000 years,
this will change. We don't call addition the "Cryntok the Babylonian
Operation".

Sturm-Liouville
===============

Sturm-Liouville Theory gives you the tools you need to solve linear
second-order differential equations. It is super mathy, but therein lies
its power and I would be doing you and it a disservice to try to avoid
the mathiness. Instead, I shall try to get to the essential, actually
useful points as simply and quickly as I can without worrying about
details of existance and convergence and measures and

If you are ever presented with a problem, a good first course of action
is to find a way to make it as much like the simple harmonic oscillator
as possible. If you approximate enough and make enough assumptions, you
can usually find on somewhere. We can dignify this for our partial
differential equation by using separation of variables, or the Fourier
transform, but we'd probably attempt it even if we didn't have a means
of dignifying it. We proceed to do this for our string equation

$$\sigma\frac{d^{2}y}{dt^{2}}-\frac{d}{dx}(\tau\frac{dy}{dx})=f(x)$$

We assume that there a solutions for which time derivatives can be
replaced by $i\omega$

$$-\sigma\omega^{2}y-\frac{d}{dx}(\tau\frac{dy}{dx})=f(x)$$

Eigenvalues and Eigenfunctions

The strangest, most beautiful, and most preposterously useful property
of Sturm-Liuoville equations is the existance of their eigenfunctions.
It turns out there are very special functions that you can apply the
differential equation to, and after turning all the cranks on your
product rules and chain rules, you get back the same function just
multiplied by some constant.

$$Lf=\lambda f$$

Pretty weird. Weirder yet, there are a whole lot of these functions.
Verging on unbelievably weird, there are enough of these functions that
you can write down any function your sweet little heart desires as the
sum of them (assuming your name isn't Weieirstrauss). And this is not
one of those "It exists but couldn't be found with a computer the size
of the universe" mathematical facts. We can construct this
representation pretty easily.

Why are the eigenfunctions and eigenvalues discrete?

We've seen that for the very simplest case of $P(x)=1$, $Q(x)=0$, the
solutions take the form of sine and cosine functions. This is not true
for any choice of $P(x)$ and $Q(x)$, but there are certain aspects of
these solutions that extend to every Sturm-Liouville problem.

1.  The nth eigenvalue $\lambda_{n}$has n zeros in between the
    endpoints.

2.  The functions reaches maximum and minimum only once between each
    zero.

Since we know the solution is kind of sine-like, let's guess a solution
that kind of looks like one, with some parameter functions. We've seen
some solutions in a book somewhere that have unequally spaced zeros or
we can guess that this might be the case, so we know that the function
inside the sine could be more comlicated than just a linear function of
x. Also, we know the total amplitude can do some fancy tricks, so the
amplitude out front might be a function of x as well.

$$u(x)=r(x)\sin(\theta(x))$$

$$u'(x)=r'(x)\sin(\theta(x))+r(x)\cos(\theta(x))\theta'(x)$$

But we have some wiggle room now. Two totally free functions is more
than is necessary to represent one function. We have a freedom to choose
another constraint if we can think of one that is useful. This is all
similar reasoning to the method of variation of parameters for solving
linear inhomogenous differential equations or picking a particular gauge
for solving electromagnetism problems. If that sentence is meaningless
to you, don't worry about it. The constraint that a man named Prufer
picked is

$$P(x)u'(x)=r(x)cos(\theta(x))$$

This transforms our Sturm Liouville equation into

$$\frac{d}{dx}(P(x)u'(x))-Q(x)u(x)=\frac{d}{dx}(r(x)cos(\theta(x)))-Q(x)r(x)sin(\theta(x))$$

$$=r'(x)cos(\theta(x))-r(x)sin(\theta(x))\theta'(x)-Q(x)r(x)sin(\theta(x))=$$

The only lesson you need to take away from your Calculus I course is
this: Use the product rule and slap an integral on it.

$$\int\frac{d(uv)}{dx}dx=\int u\frac{dv}{dx}dx+\int\frac{du}{dx}vdx$$

This is called integration by parts, and it is your friend.

The way you make a function inner product is like how you make a
sandwich. You apply peanut butter to the right piece of bread and then
you slap the left piece of bread on it. But there is an alternative! You
could have applied peanut butter to the left piece of bread, then
slapped the right on it to make the same sandwich. This is the idea
behind an adjoint operator.

The inner product between two functions is

$$\int u*vdx$$

You can apply an operator $L$ to change v to some new function

$$v\rightarrow Lv$$

There exists some adjoint operator $L^{\dagger}$that you could have
applied to u instead such that

$$\int u*(Lv)dx=\int(L^{\dagger}u*)vdx$$

Adjoint Operators and Boundary Conditions

Green's Identity

Green's Functions as Eigenfunction Series

Variational Principle

Mass on a String
================

Now that we have string down, let's make things hard by putting a bead
on it. We can write down the action fairly easily by adding in the
kinetic energy of the bead to our Lagrangian for the string

$$S=\int\left[\int\left[\frac{1}{2}\sigma(\frac{dy}{dt})^{2}-\frac{1}{2}\tau(\frac{dy}{dx})^{2}\right]dx+\frac{1}{2}m\dot{y}(a)^{2}+\frac{1}{2}m\dot{a}^{2}\right]dt$$

Where $\dot{y}(a)$ is the total time derivative given by

$$\dot{y}(a)\equiv\frac{\partial y(a)}{\partial t}+\dot{a}\frac{\partial y(a)}{\partial x}\equiv y_{t}+\dot{a}y_{x}$$

For the moment, we will focus on the dynamics of the particle. What
follows is some finicky derivative work. Let's start by using the
Euler-Lagrange equations

$$\frac{\partial L}{\partial a}-\frac{d}{dt}\frac{\partial L}{\partial\dot{a}}=0$$

$$m\dot{y}\frac{\partial\dot{y}}{\partial x}-\frac{d}{dt}(my_{x}\dot{y}+m\dot{a})=0$$

Luckily $\frac{\partial}{\partial x}$ commutes with the
$\frac{d}{dt}$operator, allowing some term cancellation. Also we divide
by m because it is worthless.

$$y_{x}\ddot{y}+\ddot{a}=0$$

We expand out those total derivatives.

$$y_{x}\frac{d}{dt}(y_{t}+\dot{a}y_{x})+\ddot{a}=y_{x}(y_{tt}+2\dot{a}y_{tx}+\dot{a}^{2}y_{xx})+\ddot{a}(1+y_{x}^{2})=0$$

Let's divide everything by $\sqrt{1+y_{x}^{2}}$to make things pretty
(trust me on this)

$$\frac{y_{x}(y_{tt}+2\dot{a}y_{tx}+\dot{a}^{2}y_{xx})}{\sqrt{1+y_{x}^{2}}}+\ddot{a}\sqrt{1+y_{x}^{2}}=0$$

What a bunch of gobbledy-gook! Turns out that each part of this equation
has a fairly simple interpretation. Check out this triangle

![image](arclengthtriangle.png)

From this we get some trigonometric identities

$$\frac{y_{x}}{\sqrt{1+y_{x}^{2}}}=\sin(\theta)$$

$$\sqrt{1+y_{x}^{2}}=\sec(\theta)$$

Where $\theta$is the angle the curve makes with the horizontal x-axis.
This means we can write the component of velocity along the curve as

$$\frac{ds}{dt}=\dot{s}=\dot{a}\sqrt{1+y_{x}^{2}}=\frac{\dot{a}}{\cos(\theta)}$$

Likewise, the acceleration along the curve can be written

$$\frac{d^{2}s}{dt^{2}}=\ddot{s}=\ddot{a}\sqrt{1+y_{x}^{2}}=\frac{\ddot{a}}{\cos(\theta)}$$

First suppose that the time derivative $\dot{a}$is zero. The only terms
remaining in the equation are

$$\frac{y_{x}y_{tt}}{\sqrt{1+y_{x}^{2}}}+\ddot{a}\sqrt{1+y_{x}^{2}}=0$$

Replacing the ugliness with our new trigonometric quantities

$$\ddot{s}=-\sin(\theta)y_{tt}$$

We've seen this one! That is the inclined plane equation, with g
replaced by $y_{tt}$. Since the effects of gravity are equivalent to
those of an accelerating reference frame, this makes sense. If the
string is accelerating, the bead moving with it experiences an incline
plane type force.

What about those $\dot{a}$ terms. Consider a string that is stationary,
like a wire. Then all time derivative of $y(a)$ drop out.

$$\frac{y_{x}\dot{a}^{2}y_{xx}}{\sqrt{1+y_{x}^{2}}}+\ddot{a}\sqrt{1+y_{x}^{2}}=0$$

Now let's pull a trick and multiply the first term by 1

$$\frac{y_{x}(\dot{a}\sqrt{1+y_{x}^{2}})^{2}y_{xx}}{(\sqrt{1+y_{x}^{2}})^{3}}+\ddot{a}\sqrt{1+y_{x}^{2}}=0$$

Oh, but here's an interesting formula for the radius of curvature that I
pull from thin air

$$\frac{y_{xx}}{(\sqrt{1+y_{x}^{2}})^{3}}=\frac{1}{R}$$

What this means is that locally, the curve y looks like a circle of
radius R. Making all these substitutions

$$\sin(\theta)\frac{\dot{s}^{2}}{R}+\ddot{a}=0$$

We've seen this one too! For an unmoving wire, the spatial curvature
creates centripetal force. and this is just the x-component of that
force!

The last term that we haven't discussed is

$$\frac{y_{x}2\dot{a}y_{tx}}{\sqrt{1+y_{x}^{2}}}$$

I do not believe this term reduces down to anything extremely familiar,
but we can examine it by imaging a curve $y(x,t)$ that is a line with
constantly increasing slope

$$y(x,t)=cxt+d$$

The second derivatives $y_{xx}$and $y_{tt}$both vanish for this curve,
removing the other force terms from the equations of motion, isolating
the effects of this term. It is similar in nature to the other two. The
changing slope combined with the bead's velocity gives rise to an
effective curvature as far as the bead is concerned.

We have examined how the motion of the mass is affected by the changing
string, but there is also the effect of the mass upon the motion of the
string to be considered. We return to our action

$$S=\int\left[\int\left[\frac{1}{2}\sigma(\frac{dy}{dt})^{2}-\frac{1}{2}\tau(\frac{dy}{dx})^{2}\right]dx+\frac{1}{2}m\dot{y}(a)^{2}+\frac{1}{2}m\dot{a}^{2}\right]dt$$

Let's make use of an delta function

$$\dot{y}(a)^{2}=\int\delta(x-a)(\frac{\partial y}{\partial t}+\dot{a}\frac{\partial y}{\partial x})^{2}dx$$

All this delta function does is pluck out the value at $a$, where we're
interested in it. To collect all our partial derivative together we can
redefine our mass density$\sigma$and tension $\tau$.

$$\sigma=\sigma_{0}+m\delta(x-a)$$

$$\tau=\tau_{0}-m\dot{a}^{2}\delta(x-a)$$

This is a very sensible change. The string has its regular old mass
density expect where the particle is, where it shoots through the roof
in a manner such that

$$\intop_{a-\epsilon}^{a+\epsilon}\sigma dx=m$$

I do not believe that the addition to torque

$$S=\int\left[\int\left[\frac{1}{2}\sigma(\frac{dy}{dt})^{2}-\frac{1}{2}\tau(\frac{dy}{dx})^{2}+\delta(x-a)m\dot{a}\frac{dy}{dx}\frac{dy}{dt}\right]dx+\frac{1}{2}m\dot{a}^{2}\right]dt$$

The energy flux P

$$P=\frac{\partial L}{\partial\frac{\partial y}{\partial x}}\frac{\partial y}{\partial t}=(m\dot{a}^{2}\delta(x-a)-\tau_{0})\frac{\partial y}{\partial x}\frac{\partial y}{\partial t}+\delta(x-a)m\dot{a}(\frac{\partial y}{\partial t})^{2}$$

$$\frac{\partial}{\partial x}\frac{\partial L}{\partial(\partial y\backslash\partial x)}+\frac{\partial}{\partial t}\frac{\partial L}{\partial(\partial y\backslash\partial t)}-\frac{\partial L}{\partial y}=0$$

$$$$

Membranes
=========

Appendix: Code {#appendix-code .unnumbered}
==============

To be cleaned up

1 Richard Haberman, Elementary Partial Differential Equations.
Prentice-Hall (1987)

A. Fetter and D Walecka "Theoretical Mechanics of articles and
Continua." Dover

Philip Morse and Herman Feshbach "Methods of Theoretical Physics"
Mcgraw-Hill 1953.

G. Arfken "Mathematical Methods for Physicists" Academic Press. 1985

R. Courant and D. Hilbert "Methods of Mathematical Physics Vol I."
Interscience Publishers. 1961

T. Pang "An Introduction to Computational Physiscs" University Press.
2006

U.H. Gerlach "LINEAR MATHEMATICS IN INFINITE DIMENSIONS Signals Boundary
Value Problems and Special Functions"
http://www.math.osu.edu/\~gerlach/math/BVtypset/node77.html
