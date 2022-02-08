---
layout: post
title: Mechanics
---

# High School
## Vectors
## Kinematics

The Big 4

## Free Body Diagrams and Force Balance

## F = ma

## Simple Harmonic Motion

$$ F = -k x $$

# Planetary Motion
# Collisions
# Rigid Bodies

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

# Langrangian Mechanics
L = T - V
Basic form is kinetic energy minus potential energy.
## Noether's theorem

# Hamiltonian Mechanics
## Legendre Transformations
## Phase Space
### Liouville's theorem



# Resources
Landau Lectures
Gold something
SICM structure and interpretation of classical mechanics