---
author: philzook58
comments: true
date: 2019-12-12 03:58:31+00:00
layout: post
link: https://www.philipzucker.com/sum-of-squares-optimization-for-minimax-optimal-differential-eq-residuals/
slug: sum-of-squares-optimization-for-minimax-optimal-differential-eq-residuals
title: Sum of Squares optimization for Minimax Optimal Differential Eq Residuals
wordpress_id: 2553
categories:
- Physics
tags:
- Julia
- sumofsquares
---



### Minimax optimization of the residual of a differential equation. 

We can't solve differential equations $Ly = 0$ exactly usually. We need to work in some finite subspace of the full function space $ y(t) = \sum_i a_i f_i(t)$. A common criteria is to find a solution that is closest to obeying the differential equation in a least squares sense, say $ \min (Ly)^2 $. This is nice because it leads to linear system of equations. However, a minimax objective $\min \max \|Ly\| $ is also feasible using the sum of squares method. See here for more [http://www.philipzucker.com/deriving-the-chebyshev-polynomials-using-sum-of-squares-optimization-with-sympy-and-cvxpy/](http://www.philipzucker.com/deriving-the-chebyshev-polynomials-using-sum-of-squares-optimization-with-sympy-and-cvxpy/)

We can write down the optimization problem using a finite polynomial parametrization of our solution. We relax the condition of being some of squares everywhere to instead just a region of interest by adding a term that makes the inequality stricter in the domain and looser outside the domain. The domain is described by a polynomial expression $t (1 - t) $ which is positive when $ 0 \leq t \leq 1$ and negative otherwise. Here is an example for

$$ \frac{d^2 y}{dt^2}=-y$$


$$y(0)=1$$


$$y'(0) = 0$$

with exact solution $ \cos(t) $

```julia

using JuMP
using SumOfSquares
using DynamicPolynomials
using SCS

@polyvar t
T = monomials(t, 0:4)
model = SOSModel(with_optimizer(SCS.Optimizer))
@variable(model, y, Poly(T))
@variable(model, α)
dy = differentiate(y, t)
ddy = differentiate(dy, t)
domain = t*(π/2-t)
@variable(model, λ_1 , SOSPoly(T))
@variable(model, λ_2 , SOSPoly(T))
@constraint(model, y(t => 0) == 1)
@constraint(model, dy(t => 0) == 0)
@constraint(model, ddy + y - λ_1*domain >= -α)
@constraint(model, α >= ddy + y + λ_2*domain)

@objective(model, Min, α)

optimize!(model)
value(y)

# $$ 0.027642031145745472t^{4} + 0.021799794207213376t^{3} - 0.5066442977156951t^{2} + 3.506190174561713e-8t + 1.0000000041335204 $$

using Plots
xs = 0:0.01:π/2; exact_y = cos.(xs); approx_y = map(x -> value(y)(t => x), xs)# These are the plotting data
plot(xs,[exact_y,approx_y])

```


![](/assets/sos_diff_eq.svg)


original link: [https://gist.github.com/philzook58/2a42558f6f5bc417c0b68f930f0ef27c#file-sos-diff-eq-ipynb](https://gist.github.com/philzook58/2a42558f6f5bc417c0b68f930f0ef27c#file-sos-diff-eq-ipynb)

Huh. This doesn't embed very well. Maybe you're better off just clicking into the thing. It's nice not to let things rot too long though. *shrug*







Other ideas: Can I not come up with some scheme to use Sum of Squares for rigorous upper and lower bound regions like in [https://github.com/JuliaIntervals/TaylorModels.jl](https://github.com/JuliaIntervals/TaylorModels.jl) ? Maybe a next post.



