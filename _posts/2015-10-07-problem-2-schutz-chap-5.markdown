---
author: philzook58
comments: true
date: 2015-10-07 14:38:05+00:00
layout: post
link: https://www.philipzucker.com/problem-2-schutz-chap-5/
slug: problem-2-schutz-chap-5
title: 'Problem 2: Schutz chap 5'
wordpress_id: 194
---

1.

Redshift from gravity. Fire a photon up. Convert into mass and let mass drop. If energy conserved then you gain mgh of energy where $ m = \hbar \omega'$, the freqeuncy at the top. Hence you have $ \hbar \omega = m+mgh=\hbar \omega (1+gh)$.

The frequency at the top is reduced by (1+gh), i.e. it is redder.

2. Uniform gravity raises no tides? That's odd. naively I would think that the water would flow towards the lowest energy configuration, which would be at the bottom of the external potential. On the total gravitational potential (+ centrifugal force) constant surface. Which does get distorted by an external field.

Oh. I see. Looking at the text, the earth would be freely falling as well.  Wow. That's an important point. The earth is falling towards the moon at exactly the rate of free fall. It's the differences of force that cause the tides. A little stronger on the front, a little weaker on the back. This is sort of the same thing as a draping cloth in a falling elevator.

7.

Can't raise an lower $ \Lambda$ using the metric. They are coordinate transformations. I believe upper indices are components of vectors and lower indices are components of 1-forms. $ dx^\mu \partial_\mu $ and $ \partial_\mu \phi$

$ x = r\cos(\theta)$

$ y = r\sin(\theta)$

This matrix will convert the gradient into new coordinates

$ \begin{bmatrix} \cos{\theta} & -r\sin(\theta) \\ \sin(\theta) & r\cos(\theta) \end{bmatrix}$

$ \theta = \arctan(\frac{y}{x})$

$ r = \sqrt{x^2+y^2}$

This one will convert vectors into new coordinates

$ \begin{bmatrix} x/r& y/r\\ -y/r^2 &x/r^2\end{bmatrix}$

Multiplying the two should give an identity matrix, since inner product should stay invariant under coordinate change. Quite miraculously they do. Try multiplying the two matrices. Nice.


