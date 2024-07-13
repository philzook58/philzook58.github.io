Is it possible for something to surprise us forever? There can be hiden
time bombs awaiting us, changing a systems behavior, but is it possible
for a systems past behavior to never being indicative of its future
behavior? Is this related to some bizarro anayltical notion? a sequence.
Is there no n such that given all the data before it, we cannot predict
something about the data after it? a perfect learner, predictor, oracle.

Probability
===========

Probability is an attempt to quantify the ideas of known and unknown and
the shades in between.

Why should it be a real number? I do not believe that people actually
think in real numbers. They'll give you a ratio.

Balls
-----

Probability starts at the idea of counting and fractions. We see a pie
with 3 slices cut out and 2 left. We say it is 3/5 eaten. A box with 4
red balls and 20 blue balls. We say that 4/24 of the balls are red.
Somehow, this notion is ingrained in us as children. Props to the
elementary teachers. This is a tough one.

We close our eyes and grab a ball. It makes sense that if we count up
how many of each type of ball we grab, we'll get roughly the same
propotion as what is there.

So that's the idea of probability. Count the balls in the box. Then you
have a guess for the count you'll grab.

That's the prototype of probability. Then we get all mathy with
continuums and such (1 infinite number of possibilities is much simpler
to grok than 20 possibilities. Very odd.).

Random Variables
----------------

Random variables are the pairing of the possiblities (red or blue balls)
with their associated proportion (4/24, 20/24). While the regular
variable color can take on red or blue, the random variable of color can
take on the values (red, 4/24) or (blue, 20/24). This is not a huge
redefinition, it's a subtle one. Random variables are a nice way of
putting together the probabilities and the qualitites that those
probabilities refer to. It makes us pay attention to how probabilties
change when we manipulate expressions.

Conditional probability
-----------------------

Back to counting balls.

Bayesian vs. Frequentist
------------------------

Statistics
==========

Statistics is the inverse problem to probability. Count the balls we
grab, and from that determine the count of the balls in the box. To what
degree can we be certain? After grabbing one red ball, do we know there
are all red balls in the box? No\... that seems kind of harsh. How about
2? What if we grabbed 20,000,000 red balls from the box?

We assume that there is a box with balls in it. Some proportion is red
and some blue

$$p(red)=a$$

$$p(blue)=1-a$$

At this point, we've already made some pretty strong assumptions. We
didn't include yellow balls. We didn't allow for shades of red and blue.
We assumed that there is some kind of consistancy for where these balls
are coming from. We assumed that every new ball we picked wasn't
affected by the previous pick.

Anyhow. we run the probem forward via the logic of probability. What was
the probilitiy that we got the ball picking that we got? Let's say we
picked 3 red and 1 blue

$$p(3red,1blue|prob(red),prob(blue))=a^{3}(1-a)$$

or for more general picks

$$p(xred,yblue|prob(red),prob(blue))=a^{x}(1-a)^{y}$$

This is known as the likelihood function. There is a commonly used
principle (the maximum likelihood principle) that we should pick the
value of a such that our data set was as likely to happen as possible.

$$\ln l=x\ln(a)+y\ln(1-a)$$

$$\frac{x}{a}+\frac{y}{1-a}=0$$

$$a=\frac{x}{x+y}$$

This is a very understandable estimate, one that you woudl've picked
without going through all this bullshit.

Hypothesis testing
------------------

Curve Fitting (Regression)
--------------------------

Curve fitting can be viewed from the experimental perspective or the
purely mathemtical perspective. From the mathematical perspective, we
pick some criteria to say when two curves are close to each other, like
integrating the difference between them squared, or the maximum distance
that they get apart. In this way we can write one given function, like
sin(x), approximately in terms of a parametized family of some other
function, like the polynomials. This is how we get Taylor series or
Fourier series or Pade Approximants, or what have you. We expect some
amount of error because of the inlfexibility of the family we're working
with. There is no such thing as overfitting.

In Between the two persepctives is considering fitting our family to
only sampled values of a known function. Now we do have a problem of
over fitting perhaps. If our family of functions has to do some weird
shit in between the sampled points that the original function did not do
in order to meet it at our samples, we're not happy. Our family very
poorly interpolates between the sample, which is almost certainly what
we cared about.

The statistical perspective thinks about how do we do this given that
the original function is unknown and even worse may have had error from
unknown sources piled on top of it. Over fitting can definitly be bad
here, since we might fit the mish mosh of error and lose the main gist
of the original function completely.

Bounds
------

Probability bounds are a curious idea. Ordinary inequlaities have their
uses in analysis. They represent looser guarantees about quantities,
when the exact specification corresponding to an equlity cannot be
guaranteed. Inequalities are a weakening of equality. Probability bounds
are a weakening of probability. They represent

Conjecture: Bounds are related to convergence conditions in Fourier
series (first differentiable go as 1/k second 1/k\^2, completely smooth
exponetially decay) They just seem kind of evocative

### Indicator Random Variables

Inidicator random variables are the statisticians version of Delta and
Heaviside functions. They are 1 when the value of the random variable
meets some condition and zero otherwise. They can be used to pull
properties of probability distribution into expectation value
expressions.

$$E[I(Condition)]=P(Condition)$$

$$\int\delta(x)f(x)dx=f(0)$$

### Markov Bound

If all you know is your random variable has mean $E[X]$and is positive,
the best you can do is the Markov bound

$$P(X\ge a)\le\frac{E[X]}{a}$$

Another phrasing is, how much of the distribution can be shoved away
from the expectation value and still keep the expectation value constant

$$P(X\ge kE[X])\le\frac{1}{k}$$

To meet the worst case scenario, what would we have to do? Well, we'd
want to place all the prbability p we could just in front of our value
a. Placing it way in front of a won't help us. We'll have to decrease
the probability at this outlier spike to maintain the expectation value.
Then we'd want to place all the rest of the probability at zero to
counterbalance as much as we can.

$$E[X]=pa+(1-a)0$$

$$P(X\ge a)=p=\frac{pa}{a}$$

Its very much like a playground teeter totter. You want to know how fat
is the kid at one end, given that they balance at the fulcrum $E[X]$ and
the total weight of all kids is 1. Well, we place a thin kid as far back
as we can, giving him a nice lever arm. Then we can gurantee that the
other kids are only so fat if they are past a certain point on the
teeter totter.

Source:

![image](Statistics_Pics/markov1.png)

![image](Statistics_Pics/markov2.png)

![image](Statistics_Pics/markov3.png)

### Chebyshev Inequality

This bad boy follows immediately from Markov. We look at the Random
variable $Y=(X-E[X])^{2}$
$$P(|X-E[X]|\ge k)=P(Y\ge k^{2})\le\frac{E[Y]}{k^{2}}=\frac{\sigma^{2}}{k^{2}}$$

The maximal distribution for him is one where its square maximizes
Markov. We get a little wiggle room whether to put our probability at k
or -k. This wiggle room gets taken out by the extra constraint of
$\sigma^{2}$

![image](Statistics_Pics/chebyshev1.png)

Distributions of functions
--------------------------

This is what we're really getting at with parameter estimation. We have
a function space (perhaps parametized). We do not know which function is
there. We take sampled values of the function in some sense. What is the
most probable function (or parameter set) now given that it evaluates to
our sample?

The perspective of "Learning From Data" is that the function has a
distribution, the data does not. We only want to know the connection
between a functions performance in our sample compared to the entire
space of possible data.

The Ouroboros: Applying probability to probability. Wheels within wheels
------------------------------------------------------------------------

What is the probability of a probability? What does it mean to say that
we are probably pulling from one distribution versus another. Two bags
of balls. We get a certain number of red and green. Which bag did we
pull from?

Regression and Classification
-----------------------------

From a relation on the data set, we try to estimatn on larger spaces.

We can go from continuous to discrete, this is classification

Continous to continous is regression

and the other two combos?

We need an error measure to say what is good and what is bad.
