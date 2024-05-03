---
author: philzook58
comments: true
date: 2020-03-21 23:46:45+00:00
layout: post
link: https://www.philipzucker.com/?p=2710
published: false
slug: Gauss-Seidel is Kind of Like a Lens
title: Gauss-Seidel is Kind of Like a Lens
wordpress_id: 2710
---




Functions in functional programming feel one directional. They don't go backwards. However the lens type `type Lens a b = a -> (b, b -> a)` gives a simple composable thing that naturally packs together a forward and backward pass, where the backward pass needs to save some information from the forward pass. The forward pass is regular usage is the getter function, and the backward pass is the setter function. An interesting example is reverse mode differentiation, which needs to remember the original values calculated in order to produce a gradient.







From this perspective, Lens (and Iso) are the simplest and purest members of a family of things such as coroutines, iteratees, streams transformers, and pipes. These are all ways of organizing and composing possibly bidirectional computation. The Lens type is a version of a coroutine that is basically type constrained to only do a single backward forward pass. This is rather nice from the perspective of using the most intent expressing, tightest fitting type one can.







However, I think Lens is shoehorned a bit into this purpose. Some things that I or others call lenses may be better fit by other members of the coroutine family. 







Here's an example.







Gauss-Seidel iteration is an iterative method for solving linear equations $latex Ax=b$. One splits a matrix into its lower and upper triangular part $latex A = L + U$. Triangular matrices can be inverted quickly and easily. One iterates like so $latex Lx_{n+1}= b - Ux_{n}$.  [https://en.wikipedia.org/wiki/Gauss%E2%80%93Seidel_method](https://en.wikipedia.org/wiki/Gauss%E2%80%93Seidel_method)







Gauss Seidel can be made compositional by considering block Gauss-Seidel. $latex Ax + By = f$. Given $latex x_n$ we can produce $latex 







Hmmm. Does this not make sense at all?













It's been very freeing to try to do the category theory patterns I've learned from Haskell in python. First off, I can do all kinds of grungy things with state that I'd have to be explicit about in Haskell. Python let's me be a dishonest man. Secondly, the python ecosystem is nuts and I can slap a little catgegorical layer on top of some library and call it a post.







One thing that one could easily accuse me of is taking powerful, easy to use pointful libraries and shitting them up with am inefficient translation to a very difficult to read categorical point free interface. Guilty as charged.







Sometimes I am filled with self hate about what I'm doing. Like why do this? What is gained? What is the _point _of category theory besides trendiness?







[https://en.wikipedia.org/wiki/Gauss%E2%80%93Seidel_method](https://en.wikipedia.org/wiki/Gauss%E2%80%93Seidel_method)







ADMM (Alternating Direction Method of Multipliers) is a method for combining convex optimization solvers which is pretty easy to implement, parallelize and has pretty goo numerical properties. The canonical notes are here [https://stanford.edu/~boyd/papers/pdf/admm_distr_stats.pdf](https://stanford.edu/~boyd/papers/pdf/admm_distr_stats.pdf)







ADMM is called sort of a generalization of Gauss-Seidel, but this connection isn't made very explicit. It can be made so by considered a quadratic optimization problem $latex \min x^TQx + c^T x$. There are a couple slight adjustments that make ADMM not quite vanilla Gauss-Seidel.







Gauss-Seidel is a iterative matrix solution method







A large class of simple iterative matrix solvers come from maniuplating  
$latex Ax=b$ into $latex Px = (P-A)x + b$. Then we take the equation and make it an iterative recipe $latex x_{i+1} = P^{-1}(P-A)x_i + b$..  One picks the matrix P such that it 







  1. is easy to invert
  2. approximates A






Jacobi iteration, Gauss Seidel iteration fit into the schema. Jacobi iteration takes as the matrix P the diagonal of A. Gauss-Seidel takes the lower or upper triagnular part of A (triangular matrices are fast to invert).  

As slight extensions of these, we can consider Block Jacobi or Block Gauss-Seidel. In this case, we use a block diagonal and a block lower triangular piece. This blocks might be easily solvable for some reason in their own right, or at least we've started to divide and conquer.







I don't think conjugate gradient and GMRES fit into this scheme.







ADMM is a fairly general method for gluing convex optimization solvers together. It is sometimes described as a Gauss-Seidel iteration, but I rarely (if ever) see this made explicit. 







A quadratic optimization problem with positive semi definite matrix Q is a convex problem. We can glue together two Quadratic optimization problems  

using ADMM and see what we get.  

$latex x^TQx + z^tRz $  

$latex Ax + Bz = 0$







Via lagrange multiplier gets turned into  

$latex x^TQx + z^tRz + \lambda(Ax + Bz)$







We can also add a quadratic term, which is standard for ADMM  

$latex x^TQx + z^tRz + 2\lambda(Ax + Bz) + \rho(Ax + Bz)^2$







We differentiate this to get this matrix







$latex  

\begin{bmatrix}  

Q + A^TA &  A^TB  & A^T \  

B^TA &  R + B^TB  & B^T  \  

A    &  B         & 0  

 \end{bmatrix}  

$







Ok, but you can't just take the lower trinagular pieceo of this. It isn't invertible.  

So here's the little trick that brings us into ADMM.







$latex  

\begin{bmatrix}  

Q + \rho A^TA &  \rho A^TB  & A^T \  

\rho B^TA &  R + \rho B^TB  & B^T  \  

A    &  B         & \rho(I-I)  

 \end{bmatrix}  

$







Adding the quadratic penalty to the constraint vilation was also an imaginary term. It can't ever be anything other than 0 in the true solution.







It kind of makes sense to add the constraints as a piece of the penalty. I think that is a very natural way to try and bullshit your way into have constraints. You make them slightly soft and then fiddle with parameters until they are exactly satisfied.







Successive Over Relaxation is another variation on Guass Seidel that plays a similar game.







Check out Boyd et al's notes   

Dual Ascent vs the method of multipliers.







Taking the lower triangular piece of this 







Or in scaled form.







Rearranging the order of x z and lambda. $latex \lambda$ is natrually associated with x and z. It is the thing that maintains their constraint.







There is an implicit equality constraint at every composition







There is an internal lagrange multiplier in some combinators







Lagrange multipliers = cost of constraints.  

So they are a form of the value function. A linearized value function







ADMM / the Adjoint method gives a way to make the shooting method a collocation method



