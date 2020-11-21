---
author: philzook58
comments: true
date: 2018-05-13 20:26:03+00:00
layout: post
link: https://www.philipzucker.com/cartpole-maths/
slug: cartpole-maths
title: CartPole Maths
wordpress_id: 1071
---

Our approach to the Cartpole is not black box. A Cartpole is a pretty simple system all things considered.

The first thing to do is derive the equations of motion. Originally I was using the Lagrangian for the system and deriving the equations of motion that way, which includes the back reaction of the pole back on the acceleration of the cart for example.

But the motor complicates things. I have a tough time in general modeling motors. What physical thing does a command to our motor driver correspond to? Velocity? Power? Torque? I have guesses. The easiest thing to do is just build and measure. It turns out for us that the commands are basically velocity control.

So in our case the back reaction is basically irrelevant. We have direct control over the cart velocity. In that case, one can use some easy enough hand waving to get the equations of motion.

Let's set the angle $ \theta = 0$ at pole down with positive angle going counter clockwise. We can assume that gravity acts at the center of mass of the pole, which is at the midpoint. This gives a torque $ \tau = -mg \frac{L}{2} \sin(\theta)$. One way to see the negative sign is that a slight positive angle should give a negative torque returning it back to the down position. The moment of inertia of the pole is $ mL^2/3$. You can look this up as a pole around one of it's ends or derive it from $ I =\int dm r^2$. The $ \frac{1}{3}$ comes from the integration of the $ r^2$. Putting these together we get $ mL^2/3 \ddot{\theta} = -mg  \frac{L}{2} \sin(\theta) $ .

Now we need to actually put in the cart stuff. The cart puts the pole in an accelerating frame, where basically you have a new component of gravity that points horizontally. This adds a torque $ -ma  \frac{L}{2} \cos(\theta) $. As far as all of the signs go, honestly we just fiddled with them until it worked.

Now that we have all that in hand, we can talk about the Linear Quadratic Regulator (LQR) control.

[https://en.wikipedia.org/wiki/Linear%E2%80%93quadratic_regulator](https://en.wikipedia.org/wiki/Linear%E2%80%93quadratic_regulator)

The model that LQR uses is that the equations of motion are linear and the cost function that you want to minimize are quadratic in the controls $ u$ and state $ x$. This is plausibly tractable because Quadratic and linear stuff is usually ok. I'm serious.

These letter choices for the various bits are pretty standard.

$ cost = \int x^TQx + u^TRu dt $

$ \dot{x}=Ax+Bu$

If you just look at the wikipedia page, you can already just plug and chug to the solution.

$ u = -Kx$

$ K= R^{-1} B^T P$

$ A^TP + PA - PBR^{-1}B^TP + Q = 0  $

Jesus that equation looks like shit.

which is QUITE CONVENIENTLY solved by the following scipy function [https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.linalg.solve_continuous_are.html](https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.linalg.solve_continuous_are.html)

HOW SUSPICIOUS.



Now given this shit, we need to approximate our nonlinear equations of motion with linear equations in order to use the LQR framework.

$ mL^2/3 \ddot{\theta} = -m \frac{L}{2}( g\sin(\theta) + a \cos(\theta)) $

Near the top where we are linearizing

$ \delta\theta = \theta - \pi$

$ \sin(\theta)\approx-\delta\theta$

and

$ \cos(\theta)\approx-1$

$ mL^2/3 \ddot{\delta\theta} \approx m \frac{L}{2}(g\delta\theta+a)$

We can move some of those constants to the other side to get $ \ddot{\delta\theta}$ by itself.

$ \ddot{\delta\theta} \approx \frac{3}{2L}( g\delta\theta + a) $

Another thing you have to do is massage these second order equations into first order form. You do this by introducing a new state variable $ \omega $

$ \dot{\delta\theta} = \omega$

$ \dot{\omega} \approx \frac{3}{2L}( g\delta\theta + a) $

In matrix form this is

$ \begin{bmatrix}\dot{\delta\theta} \\ \dot{\omega}  \end{bmatrix} = \begin{bmatrix} 0 & 1 \\ \frac{3}{2L} g & 0 \end{bmatrix} \begin{bmatrix}\delta\theta \\ \omega \end{bmatrix} + \begin{bmatrix} 0 \\ \frac{3}{2L} \end{bmatrix} \begin{bmatrix} a \end{bmatrix}  $

In addition to this, it is nice to add the cart dynamics, even though they are pretty trivial. This is because we can then add some weighting terms to discourage the cart from trying to go off the track or go faster than the motors support. There are ways to make it so that the cartpole never tries to go out of bounds, but they are a bit more complicated. I've got some blog posts about them.

$$ \begin{bmatrix}\dot{\delta\theta} \\ \dot{\omega} \\ \dot{x} \\ \dot{v}  \end{bmatrix} = \begin{bmatrix} 0 & 1 & 0 & 0 \\ \frac{3}{2L} g & 0 & 0 & 0 \\ 0 & 0 & 0 & 1\\ 0 & 0 & 0 & 0 \\ \end{bmatrix} \begin{bmatrix}\delta\theta \\ \omega \\ x \\ v \end{bmatrix} + \begin{bmatrix} 0 \\ \frac{3}{2L} \\ 0 \\ 1 \end{bmatrix} \begin{bmatrix} a \end{bmatrix}  $$

So we can read off our needed matrices A and B from here.

$$ A = \begin{bmatrix} 0 & 1 & 0 & 0 \\
 \frac{3}{2L} g & 0 & 0 & 0 \\ 0 & 0 & 0 & 1\\ 0 & 0 & 0 & 0 \\ \end{bmatrix} $$

$$ B = \begin{bmatrix} 0 \\ \frac{3}{2L} \\ 0 \\ 1 \end{bmatrix}$$

Now in regards to the weighting matrices Q and R, this is a bit tougher to say what we want. We sort of want all the state variables to be small but the relative important isn't a priori clear to me. So we picked diagonal matrices and tried out some different values. One thing to note though is that the states variables could possibly have very different scales, since their units are different. The characteristic time of the system is $ T=\sqrt{\frac{L}{g}}$. The characteristic length is the size of our track $ 1000mm$ and the rough angle scale is $ \pi/8 $-ish.

Now that we have our matrices we can plug it all into scipy and use it!

One thing to be careful about is that the pole can have swung around multiple times leading to the angle being some multiple of $ 2\pi$. Our hack around this is to just take the $ \sin$ of the angle.








