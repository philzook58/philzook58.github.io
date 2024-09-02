---
title: "Oscillator Etudes: Frequency Sweeping"
date: 2024-08-26
---

We have a concept of a "frequency response" of a system we learn about. This is the "steady state" response of an input to a sinusoidal input.

It is interesting that this is not really what happens in an experimental or even numerical setting.

We need to excite the system in a repeatable way. We might

- Start the system in a consistent state (at rest probably) and apply a single frequency for a bunch of time
- Slowly "turn on" the nonlinear term to a steady state linear system. This is not typically experimentally feasible, so kind of a goofy thing to say.
- Sweep the frequencies in a slow controlled manner

The second is probably a lot more common because it's easy to set up and the plots coming out of oscilloscopes and things directly correspond to some experimental curve. It is also not uncommon for the time scale of the system to be much much faster than a reasonable sweep rate.

However, these notions do not necessarily reduce to the same thing. Linear systems are very forgiving, but nonlinear systems can change the respond depending on how you excite them. In particular, there is hysteresis in the respond curve of an upsweep vs a down sweep of frequencies.

Here I set up a little damped harmonic oscllator and a sweeping function. One thing to keep in mind is that the "frequency" of a sweep is the _derivative_ of phase. If we want a linear sweep of frequencies, there will be that $\frac{dx^2}{dx} = 2x$ factor of two difference between $\omega(t)*t$ and $\phi$. I'm a little embarassed (although c'mon, I shouldn't be) that I didn't realize this until I was debugging my curves. That's why experiments / numerics are good though. The theory is not the ground truth.

```python
import matplotlib.pyplot as plt
import scipy as sp
import numpy as np

def sweep(omega0, omega1, F, T=10000):
    def phase(t):
        return omega0 * t + (omega1 - omega0) * t* t /T / 2
    def omega(t): # omega = d phase / dt 
        return omega0 + (omega1 - omega0) * t/T
    def df(t, y):
        x, v = y
        # sweep frequencies. spring force + external drive + damping 
        a = -x + np.sin(phase(t)) - 0.05 * v + F(x) # + non linear term
        return [v, a]

    y0 = [0, 0]
    # https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html#scipy.integrate.solve_ivp
    sol = sp.integrate.solve_ivp(df, [0, T], y0)
    return omega(sol.t), sol.y

w, y = sweep(0,2,lambda x: 0)
plt.plot(w, y[0], label="sweep")
plt.plot(w, 1/np.sqrt((1 - w**2)**2 + 0.05**2), label="ideal freq response")
plt.legend()
```

![png](/pynb/2024-09-2-oscillate_files/2024-09-2-oscillate_1_1.png)

It matches pretty well. However if we add a small nonlinear term, there is a hysteresis between the up sweet curve and down sweep curve.

```python
w, y = sweep(0,2, lambda x: -0.001* x**3)
plt.plot(w, y[0], label="up sweep")
w, y = sweep(2,0, lambda x: -0.001* x**3)
plt.plot(w, y[0], label="down sweep")
plt.legend()
```

![png](/pynb/2024-09-2-oscillate_files/2024-09-2-oscillate_3_1.png)

# Bits and Bobbles

This one was tougher than I expected.

I wanted to use sympy to derive this hysteresis but I didn't get there. Maybe next time.

The general idea is to do perturbation theory in both the solution as cosines and sines and the frequency as powers of the parameter controlling the nonlinearity. It's cute. The "The Poincare-Lindstedt Method". Its very reminiscent / identical to in some sense the "dressed" parameter shell game you'll find in fancier perturbation of quantum field theory things.

Analytic signal. <https://en.wikipedia.org/wiki/Analytic_signal>

<https://en.wikipedia.org/wiki/Instantaneous_phase_and_frequency>

Instantaneous frequency is an odd concept. It's very intuitive, but if you try to nail it down it is hard. You end up with various not quite equvialenty ersatz definitions. A pure frequency lasts forever. Instantaneous frequency is

<https://en.wikipedia.org/wiki/Uncertainty_principle#Signal_processing>
<https://en.wikipedia.org/wiki/Time%E2%80%93frequency_analysis>
<https://en.wikipedia.org/wiki/Short-time_Fourier_transform>
<https://en.wikipedia.org/wiki/Spectrogram>

- <https://www.youtube.com/watch?v=eRnM5zVQsMc> Frequency Response Curves for Linear & Nonlinear Oscillators | Lecture 19 - Shane Ross
- Averaging Theory for Weakly Nonlinear Oscillators  <https://www.youtube.com/watch?v=UzQU1nyM-No>
- <https://www.youtube.com/watch?v=kkN13nEn2WA&list=PL5EH0ZJ7V0jV7kMYvPcZ7F9oaf_YAlfbI&index=22> Lecture 22: Introduction to the method of multiple scales - Strogatz

Good notes

- <https://web.physics.ucsb.edu/~fratus/phys103/LN/NLO.pdf>
- <https://www.reed.edu/physics/faculty/wheeler/documents/Sophmore%20Class%20Notes%202007/Chapter%205.pdf>
- <https://core.ac.uk/download/pdf/160739545.pdf> An introduction to nonlinear oscillators : a pedagogical review

- Landau Liftshitz mechanics
- Strogatz
- Pippard

maybe look at those asymptotic series books

<https://github.com/arkabokshi/asymptotics-perturbation-methods>

I like the compare numerics and theory thing. It's a good one to harp on.

- Classical scttaering theory numerics

Superharmonics subharmonics
spontaneuous synchronization

```python
from sympy import *
from sympy.abc import t, A
w0, eps, W, W0, W1 = symbols('\omega_0 \epsilon \Omega \Omega_0 \Omega_1', real=True, positive=True)
y0 = Function("y0")
y1 = Function("y1")

y = y0(t) + eps * y1(t)
y
```

$\displaystyle \epsilon y_{1}{\left(t \right)} + y_{0}{\left(t \right)}$

```python
def diffeq(y):
    return y.diff(t, 2) + w0**2 * y + eps * y**3

deq = diffeq(y).expand().collect(eps)
deq
```

$\displaystyle \epsilon^{4} y_{1}^{3}{\left(t \right)} + 3 \epsilon^{3} y_{0}{\left(t \right)} y_{1}^{2}{\left(t \right)} + 3 \epsilon^{2} y_{0}^{2}{\left(t \right)} y_{1}{\left(t \right)} + \epsilon \left(\omega_{0}^{2} y_{1}{\left(t \right)} + y_{0}^{3}{\left(t \right)} + \frac{d^{2}}{d t^{2}} y_{1}{\left(t \right)}\right) + \omega_{0}^{2} y_{0}{\left(t \right)} + \frac{d^{2}}{d t^{2}} y_{0}{\left(t \right)}$

```python
deq0 = deq.coeff(eps, 0)
deq0
```

$\displaystyle \omega_{0}^{2} y_{0}{\left(t \right)} + \frac{d^{2}}{d t^{2}} y_{0}{\left(t \right)}$

```python
sol0 = dsolve(deq0)
```

```python
deq1 = deq.coeff(eps, 1)
deq1
```

$\displaystyle \omega_{0}^{2} y_{1}{\left(t \right)} + y_{0}^{3}{\left(t \right)} + \frac{d^{2}}{d t^{2}} y_{1}{\left(t \right)}$

```python
deq1.subs(y0(t), sol0.rhs)
```

$\displaystyle \omega_{0}^{2} y_{1}{\left(t \right)} + \left(C_{1} \sin{\left(\omega_{0} t \right)} + C_{2} \cos{\left(\omega_{0} t \right)}\right)^{3} + \frac{d^{2}}{d t^{2}} y_{1}{\left(t \right)}$

Has Secular term that is linear in `t`

```python
dsolve(deq1.subs(y0(t), sol0.rhs))
```

$\displaystyle y_{1}{\left(t \right)} = \frac{C_{1} \left(C_{1}^{2} - 3 C_{2}^{2}\right) \sin^{3}{\left(\omega_{0} t \right)}}{8 \omega_{0}^{2}} + \left(- \frac{3 C_{1}^{3}}{8 \omega_{0}^{2}} - \frac{3 C_{1}^{2} C_{2} t}{8 \omega_{0}} + \frac{3 C_{1} C_{2}^{2}}{8 \omega_{0}^{2}} - \frac{3 C_{2}^{3} t}{8 \omega_{0}} + C_{3}\right) \sin{\left(\omega_{0} t \right)} + \left(\frac{3 C_{1}^{3} t}{8 \omega_{0}} + \frac{3 C_{1} C_{2}^{2} t}{8 \omega_{0}} - \frac{C_{2}^{3}}{4 \omega_{0}^{2}} + \frac{C_{2} \left(3 C_{1}^{2} - C_{2}^{2}\right) \sin^{2}{\left(\omega_{0} t \right)}}{8 \omega_{0}^{2}} + C_{4}\right) \cos{\left(\omega_{0} t \right)}$

```python
W = w0 + eps * W1
_1 = sol0.subs(w0, W)
_1
```

$\displaystyle y_{0}{\left(t \right)} = C_{1} \sin{\left(t \left(\Omega_{1} \epsilon + \omega_{0}\right) \right)} + C_{2} \cos{\left(t \left(\Omega_{1} \epsilon + \omega_{0}\right) \right)}$

```python
_2 = series(deq1.subs(y0(t), _1.rhs), eps, n=2).simplify().expand()
from sympy.simplify.fu import TR8
TR8(_2).collect(sin(w0*t))
```

$\displaystyle \frac{d^{2}}{d t^{2}} y_{1}{\left(t \right)} + \omega_{0}^{2} y_{1}{\left(t \right)} + C_{2}^{3} \left(\frac{3 \cos{\left(\omega_{0} t \right)}}{4} + \frac{\cos{\left(3 \omega_{0} t \right)}}{4}\right) + \frac{3 C_{2}^{3} \Omega_{1} \epsilon t \left(- \sin{\left(\omega_{0} t \right)} - \sin{\left(3 \omega_{0} t \right)}\right)}{4} + \frac{3 C_{1} C_{2}^{2} \left(\sin{\left(\omega_{0} t \right)} + \sin{\left(3 \omega_{0} t \right)}\right)}{4} + 3 C_{1} C_{2}^{2} \Omega_{1} \epsilon t \left(\frac{3 \cos{\left(\omega_{0} t \right)}}{4} + \frac{\cos{\left(3 \omega_{0} t \right)}}{4}\right) + \frac{3 C_{1} C_{2}^{2} \Omega_{1} \epsilon t \left(- \cos{\left(\omega_{0} t \right)} + \cos{\left(3 \omega_{0} t \right)}\right)}{2} + \frac{3 C_{1}^{2} C_{2} \left(\cos{\left(\omega_{0} t \right)} - \cos{\left(3 \omega_{0} t \right)}\right)}{4} + \frac{3 C_{1}^{2} C_{2} \Omega_{1} \epsilon t \left(\sin{\left(\omega_{0} t \right)} + \sin{\left(3 \omega_{0} t \right)}\right)}{2} - 3 C_{1}^{2} C_{2} \Omega_{1} \epsilon t \left(\frac{3 \sin{\left(\omega_{0} t \right)}}{4} - \frac{\sin{\left(3 \omega_{0} t \right)}}{4}\right) + C_{1}^{3} \left(\frac{3 \sin{\left(\omega_{0} t \right)}}{4} - \frac{\sin{\left(3 \omega_{0} t \right)}}{4}\right) + \frac{3 C_{1}^{3} \Omega_{1} \epsilon t \left(\cos{\left(\omega_{0} t \right)} - \cos{\left(3 \omega_{0} t \right)}\right)}{4} + O\left(\epsilon^{2}\right)$

```python
y = A*cos(W * t) + B * 
```

```python
eps = symbols('\epsilon', real=True, positive=True)
A,B,C = symbols('A B C', real=True)
e = A*cos((w + eps*B)*t) + C * cos(3*(w + eps*B)*t)
def diffeq(x):
    return x.diff(t, 2) + w**2 * x + eps * x**3
e = diffeq(e).expand().simplify().collect(eps)
e.coeff(eps,0)

e.series(eps, 0, 3)
```

windows

reminscent of group velocity vs phase velocity. What is really the "velocity" of a wave system
<https://en.wikipedia.org/wiki/Heisenberg%27s_microscope>

Oscillators are fun and useful.
Many physical systems are oscillatory in nature.

Our understanding of the physical world is based in complete mastery of simple models which we extend outward to apply to more somplex situations.

The basic oscillatory motion is a sine wave $A\cos(\omega t + \phi)$.

A broader model of oscillatory/periodic motion is $f(\omega t)$ with $f(t + T) = f(t)$

This can be decomposed into a power series.

A different starting point is the simple harmonic oscillator equation $m\ddot{x} + kx = 0$.

We can solve by guessing the solution and plugging in.

A different systematic approach is that of fourier analysis, which is kind of similar really. We can turn linear differential equations into algebraic equations.

It's a funny thing, but while some aixomatic approach probably might start with Newton's equations or classical mechanics, and derive the laws of motion, it isn't wrong to just guess the form of the solution. That is also a theory in a way. Landau theory kind of looks like that where you just guess the rough rough of the free energy based on symmettry considerations.

There are couple different comon perturbations we might apply to a simple harmonic oscillator.

- Damping $m\ddot{x} + \gamma \dot{x} + kx = 0$
- Forcing $m\ddot{x} + \gamma \dot{x} + kx = F(t)$

These stay closed form solvable.

We can also consider

- Pendulum $m\ell^2 \ddot{\theta} + m\ell g \sin(\theta) = 0$ This changes the global structure to have solutions where the pendulum swings all the way around
- Anharmonic oscillator $m\ddot{x} + kx + \lambda x^3 = 0$ . This is possibly the extension I tend to thin k of the most often because in leads to pertburation theory

We could treat the perturbation on short time scales

The anharmonic oscillator may change the frequency of the oscillation.

- adiabatic perturbation $\ddot{x} + \omega(t)^2 x = 0$ for omega changing slow. Parametric resonance if $\omega(t)$ is periodic.
-

- Van der-pol adds a velocity non-damping term with a maximum

It is common to just make the solution go complex $e^{i \omega t}$ and then take the real part. Complex exponentials are easier to remember the algerbaic rules for than sines and cosines.

The frequency response of a system is a physical experiment you can perform. Sometimes one gets so used to just writing it down based on really kind of ad hoc principles trhat one can forget this.

Numerics is a nice stand in for experiments for the lazy. It is a good way to never really be surprised by nature though.

```python


```

$\displaystyle A \cos{\left(\omega t + \phi \right)}$

```python
deq = Eq(x(t).diff(t, 2) + w**2 * x(t), 0)
deq
```

$\displaystyle \omega^{2} x{\left(t \right)} + \frac{d^{2}}{d t^{2}} x{\left(t \right)} = 0$

```python
dsolve(deq)
```

$\displaystyle x{\left(t \right)} = C_{1} \sin{\left(\omega t \right)} + C_{2} \cos{\left(\omega t \right)}$

```python
sol = dsolve(x(t).diff(t, 2) + w**2 * x(t), ics={x(0): 1, x(t).diff(t).subs(t, 0): 0})
sol.rhs

```

$\displaystyle \cos{\left(\omega t \right)}$

```python
t1 = deq.subs(x(t), e)
t1

```

$\displaystyle A \omega^{2} \cos{\left(\omega t + \phi \right)} + \frac{\partial^{2}}{\partial t^{2}} A \cos{\left(\omega t + \phi \right)} = 0$

```python
t1.simplify() # yes it is a solution
```

$\displaystyle \text{True}$

```python
w1 = symbols("\omega_1", real=True, positive=True)
f = cos(w1*t)
sol = dsolve(Eq(x(t).diff(t, 2) + gam*x(t).diff() + w**2 * x(t), f), ics={x(0): 0, x(t).diff(t).subs(t, 0): 0})
sol.rhs.
```

$\displaystyle x{\left(t \right)} = \frac{\gamma \omega_{1} \sin{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} + \frac{\omega^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} - \frac{\omega_{1}^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} + \left(- \frac{\gamma \omega^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\gamma \omega_{1}^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\omega^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}\right) e^{\frac{t \left(- \gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} + \left(\frac{\gamma \omega^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\gamma \omega_{1}^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\omega^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}\right) e^{- \frac{t \left(\gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}}$

```python
t = sol.rhs.args[2] + sol.rhs.args[3]
t
```

$\displaystyle \frac{\omega^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} - \frac{\omega_{1}^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}}$

```python
trans = lambdify([w,w1,gam], (t / cos(w1 * symbols("t"))).simplify())
```

```python
from sympy import *
w = symbols('\omega', real=True, positive=True)
w1 = symbols("\omega_1", real=True, positive=True)
gam = symbols("\gamma", real=True, positive=True)
f = cos(w1*t)
sol = dsolve(Eq(x(t).diff(t, 2),  - gam * x(t).diff(t) - w**2 * x(t) + f), ics={x(0): 0, x(t).diff(t).subs(t, 0): 0})
sol
```

$\displaystyle x{\left(t \right)} = \frac{\gamma \omega_{1} \sin{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} + \frac{\omega^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} - \frac{\omega_{1}^{2} \cos{\left(\omega_{1} t \right)}}{\gamma^{2} \omega_{1}^{2} + \omega^{4} - 2 \omega^{2} \omega_{1}^{2} + \omega_{1}^{4}} + \left(- \frac{\gamma \omega^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\gamma \omega_{1}^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\omega^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}\right) e^{\frac{t \left(- \gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} + \left(\frac{\gamma \omega^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\gamma \omega_{1}^{2}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} - \frac{\omega^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}} + \frac{\omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2 \gamma^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} - 4 \omega^{2} \omega_{1}^{2} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega} + 2 \omega_{1}^{4} \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}\right) e^{- \frac{t \left(\gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}}$

```python
sol = dsolve([Eq(x(t).diff(t, 2) + w**2 * x(t), f(t)), Eq(x(0), 0)])
sol
```

    ---------------------------------------------------------------------------

    ValueError                                Traceback (most recent call last)

    Cell In[37], line 1
    ----> 1 sol = dsolve([Eq(x(t).diff(t, 2) + w**2 * x(t), f(t)), Eq(x(0), 0)])
          2 sol


    File ~/.local/lib/python3.10/site-packages/sympy/solvers/ode/ode.py:559, in dsolve(eq, func, hint, simplify, ics, xi, eta, x0, n, **kwargs)
        553 # This may have to be changed in future
        554 # when we have weakly and strongly
        555 # connected components. This have to
        556 # changed to show the systems that haven't
        557 # been solved.
        558 try:
    --> 559     sol = dsolve_system(eq, funcs=func, ics=ics, doit=True)
        560     return sol[0] if len(sol) == 1 else sol
        561 except NotImplementedError:


    File ~/.local/lib/python3.10/site-packages/sympy/solvers/ode/systems.py:2087, in dsolve_system(eqs, funcs, t, ics, doit, simplify)
       2081     raise ValueError(filldedent('''
       2082         dsolve_system can solve a system of ODEs with only one independent
       2083         variable.
       2084     '''))
       2086 if len(eqs) != len(funcs):
    -> 2087     raise ValueError(filldedent('''
       2088         Number of equations and number of functions do not match
       2089     '''))
       2091 if t is not None and not isinstance(t, Symbol):
       2092     raise ValueError(filldedent('''
       2093         The independent variable must be of type Symbol
       2094     '''))


    ValueError: 
    Number of equations and number of functions do not match

```python
str(sol.rhs)
```

    '(C1 - Integral(f(t)*sin(\\omega*t), t)/\\omega)*cos(\\omega*t) + (C2 + Integral(f(t)*cos(\\omega*t), t)/\\omega)*sin(\\omega*t)'

```python
fourier_transform(x(t).diff(), t, w).simplify()
```

$\displaystyle \mathcal{F}_{t}\left[\frac{d}{d t} x{\left(t \right)}\right]\left(\omega\right)$

```python
inverse_fourier_transform( 1/(I * w * gam + w1**2 - w**2 ) )
```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[193], line 1
    ----> 1 inverse_fourier_transform( 1/(I * w * gam + w1**2 - w**2 ) )


    TypeError: inverse_fourier_transform() missing 2 required positional arguments: 'k' and 'x'

```python
gam = symbols('\gamma', real=True, positive=True)
dsolve(Eq(x(t).diff(t, 2), - w**2 * x(t) - gam * x(t).diff(t) +  f(t)))
```

$\displaystyle x{\left(t \right)} = C_{1} e^{\frac{t \left(- \gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} + C_{2} e^{- \frac{t \left(\gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} + \frac{e^{\frac{t \left(- \gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} \int f{\left(t \right)} e^{\frac{\gamma t}{2}} e^{- \frac{t \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2}}\, dt}{\sqrt{\gamma^{2} - 4 \omega^{2}}} - \frac{e^{- \frac{t \left(\gamma + \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}\right)}{2}} \int f{\left(t \right)} e^{\frac{\gamma t}{2}} e^{\frac{t \sqrt{\gamma - 2 \omega} \sqrt{\gamma + 2 \omega}}{2}}\, dt}{\sqrt{\gamma^{2} - 4 \omega^{2}}}$

```python
eps = symbols('\epsilon', real=True, positive=True)
A,B,C = symbols('A B C', real=True)
#e =  A * cos(w*t) + eps * (B * cos(2*w*t) + C * cos(3*w*t))


e = A*cos((w + eps*B)*t) + C * cos(3*(w + eps*B)*t)
def diffeq(x):
    return x.diff(t, 2) + w**2 * x + eps * x**3
e = diffeq(e).expand().simplify().collect(eps)
e.coeff(eps,0)

e.series(eps, 0, 3)
```

$\displaystyle \epsilon \left(A^{3} \cos^{3}{\left(\omega t \right)} + 3 A^{2} C \cos^{2}{\left(\omega t \right)} \cos{\left(3 \omega t \right)} - 2 A B \omega \cos{\left(\omega t \right)} + 3 A C^{2} \cos{\left(\omega t \right)} \cos^{2}{\left(3 \omega t \right)} + 24 B C \omega^{2} t \sin{\left(3 \omega t \right)} - 18 B C \omega \cos{\left(3 \omega t \right)} + C^{3} \cos^{3}{\left(3 \omega t \right)}\right) + \epsilon^{2} \left(- 3 A^{3} B t \sin{\left(\omega t \right)} \cos^{2}{\left(\omega t \right)} - 6 A^{2} B C t \sin{\left(\omega t \right)} \cos{\left(\omega t \right)} \cos{\left(3 \omega t \right)} - 9 A^{2} B C t \sin{\left(3 \omega t \right)} \cos^{2}{\left(\omega t \right)} + 2 A B^{2} \omega t \sin{\left(\omega t \right)} - A B^{2} \cos{\left(\omega t \right)} - 3 A B C^{2} t \sin{\left(\omega t \right)} \cos^{2}{\left(3 \omega t \right)} - 18 A B C^{2} t \sin{\left(3 \omega t \right)} \cos{\left(\omega t \right)} \cos{\left(3 \omega t \right)} + 36 B^{2} C \omega^{2} t^{2} \cos{\left(3 \omega t \right)} + 54 B^{2} C \omega t \sin{\left(3 \omega t \right)} - 9 B^{2} C \cos{\left(3 \omega t \right)} - 9 B C^{3} t \sin{\left(3 \omega t \right)} \cos^{2}{\left(3 \omega t \right)}\right) - 8 C \omega^{2} \cos{\left(3 \omega t \right)} + O\left(\epsilon^{3}\right)$

```python
#solve([e.coeff(eps,0), e.coeff(eps,1)], [C,B,A])
solve()
```

    [(C,
      -8*C*cos(3*\omega*t)/(3*cos(2*\omega*t)),
      5*C*cos(3*\omega*t)/(3*cos(\omega*t)))]

Lagrangians legendre hamiltonians

```python
v = Function("v")
m,k = symbols('m k', real=True, positive=True)
T = 1/2*m*v(t)**2
V = 1/2*k*x(t)**2
L = T - V # lagrangian

p = Function("p")
H1 : "tuple(RFun,RFun,RFun) >> RFun" = p(t)*v(t) - L

#def lgendre(L)
#    solve(, x.diff(t))[0]
v1 = solve(H1.diff(v(t)), v(t))[0]
H : "tuple(RFun, RFun) >> RFun" = H1.subs(v(t), v1).simplify()




```

$\displaystyle 0.5 k x^{2}{\left(t \right)} + \frac{0.5 p^{2}{\left(t \right)}}{m}$

```python
from sympy import *

t = symbols('t', real=True)
w0 = symbols('\omega_0', real=True, positive=True)
w1 = symbols('\omega_1', real=True, positive=True)
A = symbols('A')
x = A * exp(I * w1 * t)
solve(x.diff(t,2) + w0**2 * x + gam * x.diff(t) - exp(I* w1 * t), A)[0]


```

$\displaystyle \frac{1}{i \gamma \omega_{1} + \omega_{0}^{2} - \omega_{1}^{2}}$

```python
from sympy import *

t = symbols('t', real=True)
w0 = symbols('\omega_0', real=True, positive=True)
w = symbols('\omega', real=True, positive=True)
A, F = symbols('A F')
x = re(A * exp(I * w * t))
x.diff(t,2) + w0**2 * x + gam * x.diff(t) - re(F*exp(I* w * t))
```

$\displaystyle - \gamma \omega \operatorname{im}{\left(A e^{i \omega t}\right)} - \omega^{2} \operatorname{re}{\left(A e^{i \omega t}\right)} + \omega_{0}^{2} \operatorname{re}{\left(A e^{i \omega t}\right)} - \operatorname{re}{\left(F e^{i \omega t}\right)}$

Multiple time scales and ordinals...?

Pippard nonlinear oscillators sweeps. Sections in Landau
Folding over of resonance diagram
  
Parametric oscillators kapitsa
Probablaistic ensemble of oscillators

Frequency sepctrum shifting, becomes assymmetirc
folding over into catastrsophe
higher resoancnes appearing
synahcronization spontaenous

self consistent approximations
"mean field"
adiabatic approximations
effective parameters
Picard Lindelhof  x_n+1 = x0 +  integ  G(<x>, t) * x(t)

Adiabatic turning on and off of potentials. <https://en.wikipedia.org/wiki/Adiabatic_invariant>
action angle coords <https://en.wikipedia.org/wiki/Action-angle_coordinates>. What is the numerical notion of this anyway. Uhh...

Things that aren't robust to inaccuraices of the solver are suspect physical phenonomenon anyway
classical Berry phase <https://en.wikipedia.org/wiki/Geometric_phase>
foucault pendulum

```python
import scipy as sp
import numpy as np


T = 100000
omega0 = 0
omega1 = 2
def omega(t): # omega = d phase / dt 
    return omega0 + (omega1 - omega0) * t/T

def phase(t):
    return omega0 * t + (omega1 - omega0) * t* t /T / 2

def df(t, y):
    x, v = y
    # sweep frequencies. spring force + external drive + damping 
    a = -x + np.sin(phase(t)) - 0.01 * v # + non linear term
    return [v, a]

y0 = [0, 0]
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html#scipy.integrate.solve_ivp
sol = sp.integrate.solve_ivp(df, [0, T], y0)
sol

import matplotlib.pyplot as plt
w = omega(sol.t)
plt.plot(w, sol.y[0])
plt.plot(w, 1/np.sqrt((1 - w**2)**2 + 0.01**2))
#plt.plot(w, 0.01/((w - 1)**2 + 0.01))
#plt.plot(w, trans(1, w, 0.01))
#plt.plot(sol.t[1:], np.diff(omega(sol.t)*sol.t) )
# this picture surpises me by a facor of two. oooh the derviative of omega(t) ... hmm.

```

    [<matplotlib.lines.Line2D at 0x7b910f907b20>]

![png](2024-09-2-oscillate_files/2024-09-2-oscillate_42_1.png)

```python
omega(T)
```

    1.0

<https://dsp.stackexchange.com/questions/13514/how-to-estimate-the-frequency-at-certain-time-of-linear-sine-sweep>
<http://en.wikipedia.org/wiki/Chirp>

```python
import sympy
from sympy.abc import x,t,omega

x = sympy.Function("x")
v = sympy.Derivative(x(t), t)
a = sympy.Derivative(v, t)

result = sympy.dsolve(sympy.Eq(a, -x(t) + sympy.sin(t * t)), x(t)) #  - 0.01 * v
result
```

$\displaystyle x{\left(t \right)} = C_{1} \sin{\left(t \right)} + C_{2} \cos{\left(t \right)} - \frac{\sin{\left(\omega t \right)}}{\omega^{2} - 1}$

# Scattering

```python
def df(t, z):
    x = z[:,0]
    v = z[:,1]
    a = -x / np.norm(x)**3
    return np.hstack([v, a]).flatten()

T = 1000
v = [1,0] # forward moving
x = [-T*v[0]/2,1] # far tho the left and a little up

y0 = np.hstack(x,v).flatten() 
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html#scipy.integrate.solve_ivp
sol = sp.integrate.solve_ivp(df, [0, T], y0)
sol
```

Internal degrees of freedom in the scattering center.

We could just stop it, or use a closed form approximate extrapolation to infinity, like a born/picard thing.
This is the analog of just truncating the domain or coupling to infinite wave solutions.

Closed form solutions
The hard sphere potential

<https://williamsgj.people.charleston.edu/Scattering%20Theory.pdf>

Doing the hard sphere computationally becomes geometrical reasoning.
collision point equations
x = x0 + tvx
y = y0 + tvy
x*2 + y **2 = 1
mirror equations

Amenable to polynomial methods.

power laws
lennard jones

geometrical optical scattering. Interesting to think about. Differential snell's law.
A hard refractive sphere. Can snell be expressed algerbrically?
vx1 = vx2
n1 v1 = n2 v2
vy1^2 + vx1^1 = v1^2
That seems to work.

Can we determine the lens by looking at some known thing is the analog of a scattering experiment.

# balls and springs

```python
T = 10
N = 10
def df(t, x):
    x = x.reshape((N,2))
    v = x[:,1]
    a = -x[:,0] # + focring functions
    return np.stack([v,a],axis=1).flatten()

y0 = np.zeros((N, 2))
y0[0,0] = 1
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html#scipy.integrate.solve_ivp
sol = sp.integrate.solve_ivp(df, [0, T], y0.flatten())
sol
y = sol.y.reshape((N,2,len(sol.t)))
plt.plot(sol.t, y[0,0,:])
plt.plot(sol.t, y[0,1,:])
plt.plot(sol.t, y[1,0,:])
```

    [<matplotlib.lines.Line2D at 0x71979fbc9000>]

![png](2024-09-2-oscillate_files/2024-09-2-oscillate_50_1.png)

# Misc

Scattering experiments might be fun.
Coulomb rutherford style. I did that once
"Effective" charge of some cluster of charged points

Out of the box wave equation solver?
<https://scipython.com/blog/the-two-dimensional-wave-equation/>
<https://scipython.com/blog/the-electric-field-of-a-capacitor/>

<https://scipython.com/chem/articles/balancing-a-chemical-reaction/> integer diophantine eqs for chemical balance

dedalus fenics

bogolibov methods in nonlinear oscialltors. That op amp course.

Electrical oscillators. Armstrong and other. Really confused me.
Bender Orszag

<https://www.reddit.com/r/Python/comments/1ca4bwy/what_is_currently_the_fasteststateoftheart_ode/>
<https://docs.kidger.site/diffrax/>
<https://github.com/Nicholaswogan/numbalsoda>
<https://github.com/SciML/DifferentialEquations.jl> <https://github.com/SciML/diffeqpy>
<https://pydstool.github.io/PyDSTool/FrontPage.html>
<https://github.com/esa/torchquad>
<https://github.com/rtqichen/torchdiffeq>
<https://github.com/Zymrael/awesome-neural-ode>

It's not crazy to trty juli

```python
#https://juliapy.github.io/PythonCall.jl/stable/compat/#IPython
import juliacall
```

    [juliapkg] Found dependencies: /home/philip/.local/lib/python3.10/site-packages/juliacall/juliapkg.json
    [juliapkg] Found dependencies: /home/philip/.local/lib/python3.10/site-packages/juliapkg/juliapkg.json
    [juliapkg] Locating Julia ~1.6.1, ~1.7, ~1.8, ~1.9, =1.10.0, ^1.10.3
    [juliapkg] Installing Julia 1.10.4 using JuliaUp
    [juliapkg] Using Julia 1.10.4 at /home/philip/.julia/juliaup/julia-1.10.4+0.x64.linux.gnu/bin/julia
    [juliapkg] Using Julia project at /home/philip/.julia/environments/pyjuliapkg
    [juliapkg] Installing packages:
               julia> import Pkg
               julia> Pkg.Registry.update()
               julia> Pkg.add([Pkg.PackageSpec(name="PythonCall", uuid="6099a3de-0909-46bc-b1f4-468b9a2dfc0d")])
               julia> Pkg.resolve()
               julia> Pkg.precompile()


        Updating registry at `~/.julia/registries/General.toml`
       Resolving package versions...
       Installed UnsafePointers ─ v1.0.0
       Installed micromamba_jll ─ v1.5.8+0
       Installed CondaPkg ─────── v0.2.22
       Installed MicroMamba ───── v0.1.14
       Installed Pidfile ──────── v1.3.0
       Installed PythonCall ───── v0.9.20
        Updating `~/.julia/environments/pyjuliapkg/Project.toml`
      [6099a3de] + PythonCall v0.9.20
        Updating `~/.julia/environments/pyjuliapkg/Manifest.toml`
      [992eb4ea] + CondaPkg v0.2.22
      [9a962f9c] + DataAPI v1.16.0
      [e2d170a0] + DataValueInterfaces v1.0.0
      [82899510] + IteratorInterfaceExtensions v1.0.0
      [692b3bcd] + JLLWrappers v1.5.0
      [0f8b85d8] + JSON3 v1.14.0
      [1914dd2f] + MacroTools v0.5.13
      [0b3b1443] + MicroMamba v0.1.14
      [bac558e1] + OrderedCollections v1.6.3
      [69de0a69] + Parsers v2.8.1
      [fa939f87] + Pidfile v1.3.0
      [aea7be01] + PrecompileTools v1.2.1
      [21216c6a] + Preferences v1.4.3
      [6099a3de] + PythonCall v0.9.20
      [ae029012] + Requires v1.3.0
      [6c6a2e73] + Scratch v1.2.1
      [856f2bd8] + StructTypes v1.10.0
      [3783bdb8] + TableTraits v1.0.1
      [bd369af6] + Tables v1.11.1
      [e17b2a0c] + UnsafePointers v1.0.0
      [f8abcde7] + micromamba_jll v1.5.8+0
      [0dad84c5] + ArgTools v1.1.1
      [56f22d72] + Artifacts
      [2a0f44e3] + Base64
      [ade2ca70] + Dates
      [f43a241f] + Downloads v1.6.0
      [7b1f6079] + FileWatching
      [b77e0a4c] + InteractiveUtils
      [4af54fe1] + LazyArtifacts
      [b27032c2] + LibCURL v0.6.4
      [76f85450] + LibGit2
      [8f399da3] + Libdl
      [37e2e46d] + LinearAlgebra
      [56ddb016] + Logging
      [d6f4376e] + Markdown
      [a63ad114] + Mmap
      [ca575930] + NetworkOptions v1.2.0
      [44cfe95a] + Pkg v1.10.0
      [de0858da] + Printf
      [3fa0cd96] + REPL
      [9a3f8284] + Random
      [ea8e919c] + SHA v0.7.0
      [9e88b42a] + Serialization
      [6462fe0b] + Sockets
      [fa267f1f] + TOML v1.0.3
      [a4e569a6] + Tar v1.10.0
      [8dfed614] + Test
      [cf7118a7] + UUIDs
      [4ec0a83e] + Unicode
      [e66e0078] + CompilerSupportLibraries_jll v1.1.1+0
      [deac9b47] + LibCURL_jll v8.4.0+0
      [e37daf67] + LibGit2_jll v1.6.4+0
      [29816b5a] + LibSSH2_jll v1.11.0+1
      [c8ffd9c3] + MbedTLS_jll v2.28.2+1
      [14a3606d] + MozillaCACerts_jll v2023.1.10
      [4536629a] + OpenBLAS_jll v0.3.23+4
      [83775a58] + Zlib_jll v1.2.13+1
      [8e850b90] + libblastrampoline_jll v5.8.0+1
      [8e850ede] + nghttp2_jll v1.52.0+1
      [3f19e933] + p7zip_jll v17.4.0+2
    Precompiling project...
      ✓ DataValueInterfaces
      ✓ IteratorInterfaceExtensions
      ✓ UnsafePointers
      ✓ Requires
      ✓ Scratch
      ✓ DataAPI
      ✓ CompilerSupportLibraries_jll
      ✓ Pidfile
      ✓ OrderedCollections
      ✓ Preferences
      ✓ StructTypes
      ✓ TableTraits
      ✓ PrecompileTools
      ✓ JLLWrappers
      ✓ Tables
      ✓ MacroTools
    micromamba_jll Waiting for background task / IO / timer.
    [pid 2195110] waiting for IO to finish:
     Handle type        uv_handle_t->data
     timer              0x2493810->0x7c2143798e80
    This means that a package has started a background task or event source that has not finished running. For precompilation to complete successfully, the event source needs to be closed explicitly. See the developer documentation on fixing precompilation hangs for more help.
      ✓ Parsers
      ✓ JSON3
    
    [pid 2195110] waiting for IO to finish:
     Handle type        uv_handle_t->data
     timer              0x2493810->0x7c2143798e80
    This means that a package has started a background task or event source that has not finished running. For precompilation to complete successfully, the event source needs to be closed explicitly. See the developer documentation on fixing precompilation hangs for more help.
      ✓ micromamba_jll
      ✓ MicroMamba
      ✓ CondaPkg
      ✓ PythonCall
      22 dependencies successfully precompiled in 41 seconds. 3 already precompiled.
      1 dependency had output during precompilation:
    ┌ micromamba_jll
    │  Downloading artifact: micromamba
    │  
    │  [pid 2195110] waiting for IO to finish:
    │   Handle type        uv_handle_t->data
    │   timer              0x2493810->0x7c2143798e80
    │  This means that a package has started a background task or event source that has not finished running. For precompilation to complete successfully, the event source needs to be closed explicitly. See the developer documentation on fixing precompilation hangs for more help.
    │  
    │  [pid 2195110] waiting for IO to finish:
    │   Handle type        uv_handle_t->data
    │   timer              0x2493810->0x7c2143798e80
    │  This means that a package has started a background task or event source that has not finished running. For precompilation to complete successfully, the event source needs to be closed explicitly. See the developer documentation on fixing precompilation hangs for more help.
    └  
      No Changes to `~/.julia/environments/pyjuliapkg/Project.toml`
      No Changes to `~/.julia/environments/pyjuliapkg/Manifest.toml`


    Detected IPython. Loading juliacall extension. See https://juliapy.github.io/PythonCall.jl/stable/compat/#IPython

```julia
%%julia
typeof(1 + 1)
```

    Int64
