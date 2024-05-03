---
author: philzook58
comments: true
date: 2020-06-09 16:00:27+00:00
layout: post
link: https://www.philipzucker.com/?p=2834
published: false
slug: Notes of Notions of Computation as Monoids
title: Notes of Notions of Computation as Monoids
wordpress_id: 2834
---




Adjunctions: What is their deal?







A big example is currying







Galois Connections are an important example. Under approximation and over approximation.













Lattices are approximate sets. Intervals are a good example. The join of two intervals is not the set union, but the smallest interval that contains them both.







A Heyting algebra has some "set difference" operation that might not actually be set difference.  This set difference is usually defined in a manner as describing it as adjoint to meet. A slight sublte exmaple would be the domain of open intervals. In this case the set difference of two intervals is not an open interval in general. So you need to take the interior of the set difference. What about two intervals that contain each other? A \ B would be two disconnected intervals, which we are not allowing ourselvest o express. 







Approximating functions with polynomials puts an ordering relation on the polynomials. They are ordered by how well they fit sin(x) for example. If you give the polynomials a higher degree they can do better. Higher degree polynomials can be mapped to lower degree polynomials. One way to do so is to just drop the higher coefficients. Or one can do Lanczos economization. Injecting polynomials into the higher order ones is easy. We just add new 0 coefficients.







Objectives put an ordering relation on points in a domain for optimization problems.







Inequalities over the reals and over integers. Round up and round down are two natural mappings between the real to the integers.  We can merely inject the naturals into the reals.







Reasoning over inequalities







Some operations don't have inverses in the naturals, but they do have best inverses.







[https://forum.azimuthproject.org/discussion/1828/lecture-4-chapter-1-galois-connections](https://forum.azimuthproject.org/discussion/1828/lecture-4-chapter-1-galois-connections)







[https://forum.azimuthproject.org/discussion/1901/lecture-6-chapter-1-computing-adjoints](https://forum.azimuthproject.org/discussion/1901/lecture-6-chapter-1-computing-adjoints)







$latex (a \le b)  -> up(a) \le up(b)$ but not vice versa. Floor and ceiling are functors from real<= to  nat<= . Inclusion is a functor from nat<= to real<=.







Galios connections name comes from a relationship between groups and field extensions that is the subject of Galois theory







The point of category theory is to make things algebraic that weren't so clearly algerbaic. Point free programming makes lambda terms wtih all sorts of weird binders into something that can just be manipulated. Matrix algebra is the gold standard









