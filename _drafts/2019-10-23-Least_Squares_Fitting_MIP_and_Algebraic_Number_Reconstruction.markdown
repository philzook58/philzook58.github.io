---
author: philzook58
comments: true
date: 2019-10-23 00:29:56+00:00
layout: post
link: https://www.philipzucker.com/?p=2441
published: false
slug: Least Squares Fitting, MIP, and Algebraic Number Reconstruction
title: Least Squares Fitting, MIP, and Algebraic Number Reconstruction
wordpress_id: 2441
---




Least squares fitting is designed to result in a linear system of equations. 







Least squares fittings is taking a function parametrized like so $latex f(x)=\sum_i a_i f_i(x)$ This expression, while nonlinear in x, is linear in the coefficients $latex a_i$.







From a bunch of samples $latex (x_s,y_s)$ we can form a loss function 







$latex \sum_s( \sum_i a _i f(x_i) - y_i)^2$ This is quadratic in the coefficients.







Algebraic numbers are part of a hierarchy of exact numbers that you can express on a computer.







Integers are easy enough to see that they are exact (or can be made to be exact if you're careful about overflow). 







The next step is rationals. Rational can be stored as a tuple of numerator and denominator. You then find that you can implement +, *, -, inv, == for these numbers. (n1,d1) * (n2,d2) = (n1 * n2, d1 * d2). These results are exact because the integers are exact







The next level in the hierarchy is algebraic numbers, the implicit roots of polynomials with integer coefficients (rational coefficients adds nothing since you can always multiply out the denominator and still have the same roots). 







If we think some number we computed







Best rational approximations are easy. They can be found by continued fraction expansion. 







There is a method using the LLL algorithm that works







[https://en.wikipedia.org/wiki/Lenstra%E2%80%93Lenstra%E2%80%93Lov%C3%A1sz_lattice_basis_reduction_algorithm](https://en.wikipedia.org/wiki/Lenstra%E2%80%93Lenstra%E2%80%93Lov%C3%A1sz_lattice_basis_reduction_algorithm)







[https://en.wikipedia.org/wiki/Integer_relation_algorithm](https://en.wikipedia.org/wiki/Integer_relation_algorithm)






    
    <code>import cvxpy as cvx
    import numpy as np
    a = cvx.Variable(10, integer=True)
    x = np.sqrt(2) ** np.arange(10)
    
    obj = cvx.abs(a * xn)
    prob = cvx.Problem(obj,[])
    prob.solve()
    </code>



