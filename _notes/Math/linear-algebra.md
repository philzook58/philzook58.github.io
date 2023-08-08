---
layout: post
title: Linear Algebra
---
- [Applications](#applications)
  - [Linear Dynamical Systems](#linear-dynamical-systems)
  - [LQR Control](#lqr-control)
  - [Kalman Filters](#kalman-filters)
  - [Probability](#probability)
  - [Quantum Mechanics](#quantum-mechanics)
  - [Least Squares Optimization](#least-squares-optimization)
  - [Boundary Value Problems](#boundary-value-problems)
  - [Filtering](#filtering)
- [Matrices](#matrices)
  - [Kronecker products](#kronecker-products)
- [Numerical](#numerical)
- [Decompositions](#decompositions)
    - [LU](#lu)
    - [SVD](#svd)
    - [Jordan](#jordan)
    - [QR](#qr)
    - [Eigenvector](#eigenvector)
      - [Power method](#power-method)
      - [Krylov](#krylov)
      - [Conjugate Gradient](#conjugate-gradient)
      - [](#)
- [Eigenvalues](#eigenvalues)
  - [Resolvent](#resolvent)
  - [Characteristic polynomial](#characteristic-polynomial)
- [Special Matrices](#special-matrices)
- [Determinants](#determinants)
- [Schur Complements](#schur-complements)
  - [Domain Decomposition](#domain-decomposition)
  - [H-Matrices](#h-matrices)
  - [Infinite domains](#infinite-domains)
  - [Circuit equivalents](#circuit-equivalents)
- [Resources](#resources)


# Applications
## Linear Dynamical Systems
## LQR Control
## Kalman Filters
## Probability
Forbenius Perrod theorem - there is a steady sta probability distribution

## Quantum Mechanics
## Least Squares Optimization
## Boundary Value Problems
## Filtering
Fourier transforms
Wavelet decompositions
PCA


Not sure how to arrange this hierarchy
# Matrices
## Kronecker products


# Numerical

# Decompositions
### LU
### SVD
https://peterbloem.nl/blog/pca-4
### Jordan
### QR
### Eigenvector
#### Power method
#### Krylov
#### Conjugate Gradient
#### 


# Eigenvalues
## Resolvent
## Characteristic polynomial

# Special Matrices
[List of named matrices](https://en.wikipedia.org/wiki/List_of_named_matrices)


```python
import numpy as np
import scipy.linalg as linalg
from scipy.linalg import toeplitz
K = toeplitz([2,-1,0,0])
print(K)
print(linalg.inv(K))
from sympy import *
init_printing(use_unicode=True)
Ksym = Matrix(K)
print(Ksym.inv())

```


# Determinants
Funny funny fellows indeed.
Geometrically is the "volume" spanned by the columns.
If the matrix represents a transformation, if is the factor of volume shrinkage of the transformation

A definition is an antisymetric recursive one. Why is this formula right? https://en.wikipedia.org/wiki/Laplace_expansion

det([a b; c d]) = ad-bc

Cramer's rule gives a direct solution to the inverse of a matrix. https://en.wikipedia.org/wiki/Cramer%27s_rule Mainly useful in the 2x2 case

Facts:
1. det(A) = prod of eigvals. 
2. det(AB) = det(A)det(B)
3. det(A) = product of pivots in LU form. A more useful way of calulating than brute force

Charactersitic Polynomial = det(A - lam). The roots of this polynomial are eigenvalues.

# Schur Complements
## Domain Decomposition
## H-Matrices
## Infinite domains
## Circuit equivalents

# Resources
- Horn, Roger A.; Charles R. Johnson (1985). Matrix Analysis. 
- COmputational Science and Engineering