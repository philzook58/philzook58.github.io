---
layout: post
title: Differential Equations
---

- [Closed Form Solutions](#closed-form-solutions)
  - [Integrals](#integrals)
  - [Decay](#decay)
  - [Forced Decay](#forced-decay)
  - [Simple Harmonic Motion](#simple-harmonic-motion)
  - [Forced Simple Harmonic Motion](#forced-simple-harmonic-motion)
  - [Simple Harmonic Motion with Drag](#simple-harmonic-motion-with-drag)
- [Non closed Form Problems](#non-closed-form-problems)
  - [Iterative Methods](#iterative-methods)
  - [Perturbation Methods](#perturbation-methods)
    - [Fixed Points](#fixed-points)
  - [Chaos](#chaos)
    - [Lie Method](#lie-method)
- [Extensions](#extensions)
  - [Matrix "Decay"](#matrix-decay)
  - [Control Problems](#control-problems)
    - [LQR](#lqr)
    - [Inverse Problems?](#inverse-problems)
- [DFT, Fourier Series, Fourier Transform](#dft-fourier-series-fourier-transform)
  - [Dirac Delta](#dirac-delta)
  - [Laplace](#laplace)
  - [Related transforms](#related-transforms)
- [Finite Difference](#finite-difference)
  - [Summations](#summations)
  - [Growth Equation](#growth-equation)
- [Computers](#computers)
  - [Symbolic](#symbolic)
    - [State Machine Analogs](#state-machine-analogs)
    - [Symbolic Solution of Diff Eqs](#symbolic-solution-of-diff-eqs)
      - [Pattern matching](#pattern-matching)
      - [Lie Algebra methods](#lie-algebra-methods)
  - [Numeric](#numeric)
    - [Numbers](#numbers)
    - [Finite Difference](#finite-difference-1)
    - [Validated Numerics](#validated-numerics)
  - [1-D Laplace](#1-d-laplace)
  - [Particle in a Box](#particle-in-a-box)
  - [Periodic Systems and Bands](#periodic-systems-and-bands)
  - [Method of Matching coefficients](#method-of-matching-coefficients)
- [Higher PDE Dimensions](#higher-pde-dimensions)
  - [Poisson Free Space (Coulomb's Law)](#poisson-free-space-coulombs-law)
  - [Separation of Variables](#separation-of-variables)
  - [Laplace Box](#laplace-box)
  - [Analytic Functions](#analytic-functions)
  - [Circle](#circle)
  - [Algebraic multigrid](#algebraic-multigrid)
  - [Fast Multi pole method](#fast-multi-pole-method)
  - [FFT](#fft)
  - [Domain Decomposition](#domain-decomposition)
  - [Finite Elements / Galerkin](#finite-elements--galerkin)
  - [Boundary Element Method](#boundary-element-method)
- [Functional Analysis](#functional-analysis)
- [Misc](#misc)


See also:
- Linear Algebra


<script src="https://cdn.jsdelivr.net/pyodide/v0.18.1/full/pyodide.js"></script>
<script type="text/javascript">
    async function main(){
        let pyodide = await loadPyodide({
            indexURL : "https://cdn.jsdelivr.net/pyodide/v0.18.1/full/"
        });
        await pyodide.loadPackage("numpy");

        var codedivs = document.getElementsByClassName("python");
        for (var i = 0; i < codedivs.length; i++) {
            let codediv = codedivs[i];
            let code = codediv.innerHTML;
            codediv.innerHTML = "";

            let t = document.createElement("textarea");
            t.innerHTML = code;
            codediv.appendChild(t);

            let b = document.createElement("Button");
            b.innerHTML = "Run";
            b.onclick = function(){
                console.log(t.value);
                pyodide.runPython(t.value);
            }
            codediv.appendChild(b);

        /* ideas
        Extract this into a javascript file?
        Get plotting code working
        get z3 working via pysmt and external smtlib
        */
        }
    }
    main();
</script>

# Closed Form Solutions

Differential Equations are neat. They are the mathematical underpinning of a lot of physics.

Newtonian Mechanics is to canonical instance of differential equations. This may be the mechanics of point particles, or of rigid bodies.

There is a certain set of closed form solutions which are the bones we hang our intuition around

By differential equation, I tend to mean 1-d, and initial value problem.

## Integrals

$\frac{dy}{dx} = f(x)$ is indeed a differential equation, one so "trivial" in some sense that we tend to not view it as such.

The solution is $y(x) = \int_0^x f(x) + C$.

## Decay

$\frac{dy}{dx} = -ky$

The solution to the equations is $y(x) = Ce^{-kx}$. You can confirm this works by differentiating the right hand side.

We may choose to think of exponential explosion, for which the sign of $k$ is different as a different problem or not. Conceptually, it can be very different.

Where can this show up?
- RC circuits. If you attach a resistor to a charged capaictor, the charge will leak through the resistor.
- Particle Decay
- Cooling & Heating.

<div class="python">
import numpy as np
print(np.array([1,2,3]))
</div>


## Forced Decay

The method of "integrations factors"

Primeval Green's Functions / Impulse Function

## Simple Harmonic Motion



There's a lot here. This is really the bread and butter.


Coupled form
$\frac{dp}{dt} = -kx $
$\frac{dx}{dt} =  p/m$


Pippard Book
Waves Book

## Forced Simple Harmonic Motion
## Simple Harmonic Motion with Drag




# Non closed Form Problems

Many methods can be built on the assumption that the result can be approximated by a power series




## Iterative Methods
For "short times" $t$ is a small parameter and it is reasonable to expect you can approximate the solution well

## Perturbation Methods
[Numerical parameter continuation](https://github.com/nschloe/pacopy)



### Fixed Points

Finding fixed points is a question that is much easier than solving a differential equation. It takes out the differential stuff and now you just need to solve a possibly nonlinear set of equations. Linearization around a fixed point can be useful. Tells you about stability.

## Chaos
Attractors

[Koopman Operators](https://twitter.com/IgorMezic/status/1492326556433195009?s=20&t=Fyek6pLGPQrxADkntoVadg)


### Lie Method


# Extensions

## Matrix "Decay"

$\frac{}$

## Control Problems

### LQR

### Inverse Problems?

# DFT, Fourier Series, Fourier Transform
Bracewell book
Course

Schwarz distributions
## Dirac Delta
https://en.wikipedia.org/wiki/Dirac_delta_function

The identity operator as an integral transform
$\int \delta(x-y) f(x) dx = f(y) $

$\delta(x) = \int_{-\inf}^{\inf} e^{ikx}dx $

Can consider limit of gausian or square function

$ \delta(x) = e^{-\frac{x^2}{\alpha}} $

```python
from sympy import *
init_printing(use_unicode=False, wrap_line=False)
x, a = symbols('x a')
print(integrate(exp(-x**2/a), (x, -oo, oo), conds='none'))


```

## Laplace 
More appropriate for initial value problems / transients.
Fourier is kind of goofy and yet it feels more sensible to consider a superposition of sine and cosine. There is also more symmettry between the forward and inverse trasnform


## Related transforms

Radon
Mellin
Hankel


# Finite Difference

For many of the closed form problems in the continuum differential equation case, there are analagous closed forms for the finite difference case. It is not altogether apparent to me why the continuum case is so much more emphasized, but there is a sense that the results are cleaner or simpler is some sense, while confusingly finite difference really is much more mundane foundationally speaking.

## Summations

## Growth Equation


# Computers
## Symbolic
### State Machine Analogs
### Symbolic Solution of Diff Eqs
See sympy docs 
#### Pattern matching
#### Lie Algebra methods

## Numeric

### Numbers
### Finite Difference
### Validated Numerics

One can consider blobs (sets) of functions in function space. If you work with only a constrained class of blobs, these blobs can be finitely representable in a computer.
It's similar to how we can work in finite subsets or intervals of the reals. You can't describe every possible set of reals in these terms.
You can also over approximate sets, and perform approximations of union, intersection, complement in principled ways.
This is really interesting.




Partial differential equations often come from the combination of a constitutive relation with a conservation law.

Conservations Laws:
- Conservation of mass
- conservation of energy
- conservation of momentum
- Force Balance (for statics)
- Conservation of charge
- Conservation of number (similar to Mass)

Constitutive Relations
- Ohm's Law $V = IR$
- Hooke's Law $F = kx$
- Fick's Law
- Viscous Drag
- Capicitance $Q = CV$
- Inductance $\Phi = LI$
- Fourier's Law. Heat flow is proportional to temperature difference $J = k \Delta T$

The constitutive relations are most familiar or intuitive to us in kind of bulk form. We can imagine connecting together lots of little resistors for example to have a continuous conductive medium.


## 1-D Laplace

$frac{d^2 \phi }{dx^2} = 0$
$ \phi(0) = a$
$ \phi(1) = b$

## Particle in a Box

## Periodic Systems and Bands
A periodic system is separable into it's periodic and cell parts.
$H = I \otimes H_1 - C \otimes H_2 - C^{-1} \otimes H_3 $


Crystal momentum.



## Method of Matching coefficients

# Higher PDE Dimensions


## Poisson Free Space (Coulomb's Law)
## Separation of Variables
## Laplace Box
## Analytic Functions
## Circle


Morse and Feshbach

## Algebraic multigrid
https://github.com/pyamg/pyamg 
## Fast Multi pole method
## FFT
## Domain Decomposition
## Finite Elements / Galerkin
## Boundary Element Method

# Functional Analysis


# Misc

[json bramburger ode course](https://www.youtube.com/watch?v=UDUH58w4-5w&ab_channel=JasonBramburger)