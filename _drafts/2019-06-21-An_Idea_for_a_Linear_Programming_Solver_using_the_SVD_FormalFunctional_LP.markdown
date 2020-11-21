---
author: philzook58
comments: true
date: 2019-06-21 15:25:58+00:00
layout: post
link: https://www.philipzucker.com/?p=2059
published: false
slug: An Idea for a Linear Programming Solver using the SVD. Formal/Functional LP
title: An Idea for a Linear Programming Solver using the SVD. Formal/Functional LP
wordpress_id: 2059
---




I've been tinkering around with solver ideas and thought of one that sounds cute. Maybe it's been done or very possibly it is wrong or slow.







Place the linear program into homogenous and feasible only form. $latex A x \ge 0$. 







You make the feasible form by taking the self dual embedding. $latex \min c^T x s.t. Ax \ge 0$ has the dual problem $latex A^T y = c, y \ge 0$. Hmm. By going homogenous first, the primal LP is either unbounded, 0, or infeasible.







Linear programming as a spec is to select from all possible d choices of constraints (which specifies a vertex by linear algebra) the choice that maximizes the objective function. N= number of constraints and d is number of variables = N choose d possibilities. We may be able to write this in relational point free form.







Greedy grabbing.







The homogenous form feels like transforming minimization problems into feasibility problems, but maybe this makes it harder. Or leaves too much power on the table?









