---
layout: post
title: Differential Equations
---

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

# Iterative Methods
For "short times" $t$ is a small parameter and it is reasonable to expect you can approximate the solution well

# Perturbation Methods




### Solving For Fixed Points

Finding fixed points is a question that is much easier than solving a differential equation. It only involves 

### Lie Method


# Extensions

## Matrix "Decay"

$\frac{}

## Control Problems

### LQR

### Inverse Problems?



# Finite Difference

For many of the closed form problems in the continuum differential equation case, there are analagous closed forms for the finite difference case. It is not altogether apparent to me why the continuum case is so much more emphasized, but there is a sense that the results are cleaner or simpler is some sense, while confusingly finite difference really is much more mundane foundationally speaking.

## Summations

## Growth Equation


# Computers
## Symbolic
### State Machines

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

## Method of Matching coefficients

# Higher PDE Dimensions


## Poisson Free Space (Coulomb's Law)
## Separation of Variables
## Laplace Box
## Analytic Functions
## Circle


Morse and Feshbach
