---
layout: post
title: Mechanics
---
- [High School](#high-school)
  - [Vectors](#vectors)
  - [Kinematics](#kinematics)
  - [Free Body Diagrams and Force Balance](#free-body-diagrams-and-force-balance)
  - [F = ma](#f--ma)
  - [Virial](#virial)
  - [Simple Harmonic Motion](#simple-harmonic-motion)
- [Planetary Motion](#planetary-motion)
- [Collisions](#collisions)
- [Rigid Bodies](#rigid-bodies)
  - [State](#state)
    - [angular velocity](#angular-velocity)
- [Accelerating Frames](#accelerating-frames)
- [Conservation Laws](#conservation-laws)
  - [Momentum](#momentum)
  - [Energy](#energy)
  - [Angular Momentum](#angular-momentum)
  - [Center of Mass](#center-of-mass)
- [Lagrangian Mechanics](#lagrangian-mechanics)
  - [Noether's theorem](#noethers-theorem)
- [Hamiltonian Mechanics](#hamiltonian-mechanics)
  - [Legendre Transformations](#legendre-transformations)
  - [Phase Space](#phase-space)
  - [Hamilton Jacobi Equations](#hamilton-jacobi-equations)
  - [Action angle coordinats](#action-angle-coordinats)
    - [Liouville's theorem](#liouvilles-theorem)
- [Celestial Mechanics](#celestial-mechanics)
- [Chaos](#chaos)
- [Waves](#waves)
- [Normal Modes](#normal-modes)
- [Fluids](#fluids)
- [Acoustics](#acoustics)
- [Continuous Media](#continuous-media)
- [Stress Strain / Continuous Media / Strength of Materials](#stress-strain--continuous-media--strength-of-materials)
- [Resources](#resources)

# High School

## Vectors

## Kinematics

The Big 4

Velocity is the change of position with respect to time

## Free Body Diagrams and Force Balance

## F = ma

Friction
Atwood machines

The force is the change of momentum wth respect to time
$$ F = \frac{p}{dt} $$

Force is a function of position and velocity.

Conservation of energy and momentum

Center of Mass. Conservation of total momentum.
In center of mass frame, the center of mass itself is preserved.

## Virial

A truly odd duck. Most useful as a kinetic theory kind of thing.

## Simple Harmonic Motion

$$ F = -k x $$

# Planetary Motion

# Collisions

# Rigid Bodies

Angular momentum is $$ L = r \times p $$. It's value is dependent on your choice of coordinate system, which feels rather odd.

Torque is $$ r \times F $$

## State

[David's blog post tennis racket theorem](https://davidtersegno.wordpress.com/2022/01/30/the-tennis-racket-theorem/)

How do you describe the kinematics of a rigid object.
Three (non collinear) points in it are enbough.
That is more than necessary number of coordinates though. If you pick particular points in the object, they will alays be the same distance from each other. That's 3 $$R^2 = d^2 $$ constraints a-b, b-c, a-c.
More coordinates is not really a sin persay, despire an impulse for it to feel that way. It will mean you have to write more things, but perhaps the mathematics may be easier.
If you were measuring points on on object, perhaps it is not so bad to take redundant measurements/points to reduce error.

Something more common is take take the position of some point and orientation information.

Euler angles: We pick some reference orientation and a canonical sequence of transformations to transform into this configuation.

We could describe the rotation matrix. The rotation matrix can be thought of as very similar to the first method. Each column of the matrix is what the x-y-z axis is transformed to

Quaternions - Funky fellows.

Conversions:
We can create a rotation matrix from euler angles as a composition of 3 rotation matrices.
Converting from euler angles to points is straightforward.

Points to rotation matrix can be done as a matrix problem.
$$ X'= UX $$
$$ X' X^T = U X X^T $$  Here I somewhat randomly pick X to right multiply. I could've picked any matrix
$$ X' X^T (X X^T)^{-1} = U $$ is one solution. Is it optimal in any

A natural optimization formulation is (although it is no a priori clear what the distance function d could be.
$$ \min_{U} d(X', UX) $$
$$ U^T U = 1 $$

Straightforward enough. Is this problem solvable? Well, a choice of d might be $ d(X,X') = |X - X'|^2 $ . Combined with a lagrange multiplier for the constraint this is a multivariate polynomial system of equations. There are methods for this, not really fast ones though.

Alternatively we could just for a matrix decomposition.
General nonlinear optimization using gradient descent or other.

cos^2 + sin^2 = 1 is a useful trick to turn angles to systems of polynomial equations.

### angular velocity

Strangly, angular velocity seems more straightforward than describing rotation itself. This is because globally, rotation has some peculiar mathemtical properties. Locally, as in small orientation displacements, it isn't so bad.

$ v = \omega \cross r $$

# Accelerating Frames

# Conservation Laws

Symettry and conservation laws

## Momentum

## Energy

## Angular Momentum

## Center of Mass

# Lagrangian Mechanics

L = T - V
Basic form is kinetic energy minus potential energy.

The action is the time integral of the lagrangian
$$ S = \int L dt $$
What does this equation mean? Does it have any content?

## Noether's theorem

# Hamiltonian Mechanics

## Legendre Transformations

## Phase Space

## Hamilton Jacobi Equations

Caonical transformations

## Action angle coordinats

### Liouville's theorem

# Celestial Mechanics

# Chaos

<https://en.wikipedia.org/wiki/Chaos_theory>

Chaos book
Logisistic model
feigenbaum
poincare sections
Attractors lorenz and rossler
chua's circuit
quantum chaos

# Waves

# Normal Modes

# Fluids

<https://www.youtube.com/watch?v=iKAVRgIrUOU&t=648&ab_channel=TenMinutePhysics> 17 - How to write an Eulerian fluid simulator with 200 lines of code.

# Acoustics

# Continuous Media

# Stress Strain / Continuous Media / Strength of Materials

Beam equation
Young's modulus

# Resources

Landau Lectures
Gold something
SICM structure and interpretation of classical mechanics
Fetter and Walecka
Physics 1 textbooks. WHat do the kinds do these days?
Feynman
