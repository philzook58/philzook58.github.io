---
author: philzook58
comments: true
date: 2020-03-10 02:35:44+00:00
layout: post
link: https://www.philipzucker.com/categorical-combinators-for-convex-optimization-and-model-predictive-control-using-cvxpy/
slug: categorical-combinators-for-convex-optimization-and-model-predictive-control-using-cvxpy
title: Categorical Combinators for Convex Optimization and Model Predictive Control
  using Cvxpy
wordpress_id: 2692
categories:
- Formal Methods
- Optimization
tags:
- categorytheory
- convex
- cvxpy
- mpc
---




We're gonna pump this well until someone MAKES me stop.







This particular example is something that I've been trying to figure out for a long time, and I am pleasantly surprised at how simple it all seems to be. The key difference with my previous abortive attempts is that I'm not attempting the heavy computational lifting myself. 







We can take pointful DSLs and convert them into point-free category theory inspired interface. In this case a very excellent pointful dsl for convex optimization: cvxpy. Some similar and related posts converting dsls to categorical form







  * [http://www.philipzucker.com/categorical-lqr-control-with-linear-relations/](http://www.philipzucker.com/categorical-lqr-control-with-linear-relations/)
  * [http://www.philipzucker.com/categorical-combinators-for-graphviz-in-python/](http://www.philipzucker.com/categorical-combinators-for-graphviz-in-python/)
  * [http://www.philipzucker.com/rough-ideas-on-categorical-combinators-for-model-checking-petri-nets-using-cvxpy/](http://www.philipzucker.com/rough-ideas-on-categorical-combinators-for-model-checking-petri-nets-using-cvxpy/)
  * [http://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/](http://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/)






A [convex optimization problem ](https://web.stanford.edu/class/ee364a/)optimizes a convex objective function with constraints that define a convex set like polytopes or balls. They are polynomial time tractable and shockingly useful. We can make a category out of convex optimization problems. We consider some variables to be "input" and some to be "output".  This choice is somewhat arbitrary as is the case for many "relation" feeling things that aren't really so rigidly oriented.







Convex programming problems do have a natural notion of composition.  Check out the last chapter of [Rockafeller](https://www.amazon.com/Analysis-Princeton-Landmarks-Mathematics-Physics/dp/0691015864), where he talks about the convex algebra of bifunctions. Instead of summing over the inner composition variable like in Vect $latex \sum_j A_{ij}B_{jk}$, or existentializing like in Rel $latex \{ (a,c) |\exists b. (a,b)\in A, (b,c) \in B \}$, we instead minimize over the inner composition variable $latex min_y A(x,y) + B(y,z)$. These are similar operations in that they all produce bound variables. 







The identity morphism is just the simple constraint that the input variables equal to output variables with an objective function of 0. This is an affine constraint, hence convex.







In general, if we ignore the objective part entirely by just setting it to zero, we're actually working in a very computationally useful subcategory of Rel, ConvexRel, the category of relations which are convex sets. Composition corresponds to an existential operation, which is quickly solvable by convex optimization techniques. In operations research terms, these are feasibility problems rather than optimization problems. Many of the combinators do nothing to the objective.







The monoidal product just stacks variables side by side and adds the objectives and combines the constraints. They really are still independent problems. Writing things in this way opens up a possibility for parallelism. More on that some other day.







We can code this all up in python with little combinators that return the `input, output, objective, constraintlist`. We need to hide these in inner lambdas for appropriate fresh generation of variables.





[gist https://gist.github.com/philzook58/5544f04b2e08318dc623ff037e0a10a5#file-convexcat-py]











Now for a somewhat more concrete example: Model Predictive control of an unstable (linearized) pendulum.







Model predictive control is where you solve an optimization problem of the finite time rollout of a control system online. In other words, you take measurement of the current state, update the constraint in an optimization problem, ask the solver to solve it, and then apply the force or controls that the solver says is the best.







This gives the advantage over the [LQR controller](http://www.philipzucker.com/categorical-lqr-control-with-linear-relations/) in that you can set hard inequality bounds on total force available, or positions where you wish to allow the thing to go. You don't want your system crashing into some wall or falling over some cliff for example. These really are useful constraints in practice. You can also include possibly time dependent aspects of the dynamics of your system, possibly helping you model nonlinear dynamics of your system.







I have more posts on model predictive control here [http://www.philipzucker.com/model-predictive-control-of-cartpole-in-openai-gym-using-osqp/](http://www.philipzucker.com/model-predictive-control-of-cartpole-in-openai-gym-using-osqp/) [http://www.philipzucker.com/flappy-bird-as-a-mixed-integer-program/](http://www.philipzucker.com/flappy-bird-as-a-mixed-integer-program/)







Here we model the unstable point of a pendulum and ask the controller to find forces to balance the pendulum.





[gist https://gist.github.com/philzook58/5544f04b2e08318dc623ff037e0a10a5#file-controller-py]





We can interpret the controller in GraphCat in order to produce a diagram of the 10 step lookahead controller. This is an advantage of the categorical style a la [compiling to categories](http://conal.net/papers/compiling-to-categories/)





[gist https://gist.github.com/philzook58/5544f04b2e08318dc623ff037e0a10a5#file-diagram-py]



![](http://philzucker2.nfshost.com/wp-content/uploads/2020/03/controller-174x1024.png)





We can also actually run it in model predictive control configuration in simulation. 





[gist https://gist.github.com/philzook58/5544f04b2e08318dc623ff037e0a10a5#file-mpc-py]



![](https://www.philipzucker.com/wp-content/uploads/2020/03/controllerplot.png)And some curves. How bout that.





### Bits and Bobbles







LazySets [https://github.com/JuliaReach/LazySets.jl](https://github.com/JuliaReach/LazySets.jl)







ADMM - It's a "lens". I'm pretty sure I know how to do it pointfree. Let's do it next time.







The minimization can be bubbled out to the top is we are always minimizing. If we mix in maximization, then we can't and we're working on a more difficult problem. This is similar to what happens in Rel when you have relational division, which is a kind of  universal quantification $latex \forall$ . Mixed quantifier problems in general are very tough. These kinds of problems include games, synthesis, and robustness. More on this some other day.







Convex-Concave programming minimax [https://web.stanford.edu/~boyd/papers/pdf/dccp_cdc.pdf](https://web.stanford.edu/~boyd/papers/pdf/dccp_cdc.pdf)  [https://web.stanford.edu/class/ee364b/lectures/cvxccv.pdf](https://web.stanford.edu/class/ee364b/lectures/cvxccv.pdf)







The minimization operation can be related to the summation operation by the method of steepest descent in some cases. The method of steepest descent approximates a sum or integral by evaluating it at it's most dominant position and expanding out from there, hence converts a linear algebra thing into an optimization problem. Examples include the connection between statistical mechanics and thermodynamics and classical mechanics and quantum mechanics.







Legendre Transformation ~ Laplace Transformation via  steepest descent [https://en.wikipedia.org/wiki/Convex_conjugate](https://en.wikipedia.org/wiki/Convex_conjugate) yada yada, all kinds of good stuff.







Intersection is easy. Join/union is harder. Does MIP help?






    
    <code>def meet(f,g):
       def res():
          x,y,o,c = f()
          x1,y1,o1,c1 = g()
          return x,y,o+o1, c+ c1 + [x ==  x1, y == y1]
       return res</code>







Quantifier elimination







MIP via adjunction



