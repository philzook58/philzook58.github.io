---
author: philzook58
comments: true
date: 2019-10-13 21:00:25+00:00
layout: post
link: https://www.philipzucker.com/?p=1543
published: false
slug: Verifying a Neural Policy Controller with Mixed Integer Programming
title: Verifying a Neural Policy Controller with Mixed Integer Programming
wordpress_id: 1543
---




We're thinking of starting this back up with flappy bird.







[https://github.com/sisl/NeuralVerification.jl](https://github.com/sisl/NeuralVerification.jl)







To start, we should just literally use z3. That is the obvious dumb thing to do. But, then we could talk about 







### 12/2018 






Neural networks constructed out of Relu and Linear layers and max pooling layers are in totalitity piecewise linear functions.




Piecewise linear functions can be maniuplated in interesting ways using Mixed Integer Linear Programming.




https://github.com/joehuchette/PiecewiseLinearOpt.jl




Perhaps I should be doing this all in Julia.




There is an interesting paper scaling this technique to work on convolutional neural networks and using it to verify MNIST against adversarial attack.




https://arxiv.org/abs/1711.07356




 




We can encode an optimal model predictive controller as a MILP. Ideally, we would find a way to tune the solver such that we could just use this model in real time. This is not always viable at the moment.




A neural network is built in such a way that it is very easy to evaluate.




 




$latex \max r^T x* - r^T x_\pi$




If we had built a Value function controller




 




This controller can be mixed and matched in some interesting ways. For example, we might choose to use the MPC methodology for the first couple time steps, but then use the neural policy for the rest. We might choose to mix and match the neural polciy controller, perhaps using one for large scale choices and the other for local choices, pruning the search space signifcantly. Or we might attempt to something much more custom like Alpha Zero. We can seed the MILP solver with the solution returned by the pure policy. We could seed in the BB tree. Then it really looks like Alpha Go.




BB solve via Monte Carlo Tree Search.




Save space at bottom of A matrix. All zero rows. One by one put in 1s. Could build OSQP? Warm Start. replace entries of lower vs upper bounds. 0 1 for binary. 11 for 1 coice, 00 for 0 choice. only changing l and u vectors.




Combine with neural network. Train on dual solution and primal solution as input.




How does alpha go only inspect valid moves?




cvxpy.




 




 




 




 
