---
author: philzook58
comments: true
date: 2019-12-23 14:37:27+00:00
layout: post
link: https://www.philipzucker.com/?p=2590
published: false
slug: Complementarity Problems
title: Complementarity Problems
wordpress_id: 2590
---




Complementarity problems







I have a newfound appreciation for complementarity problems.







Complemnetarity problems are a class of mathemtical programming problems that allow constraints of the form xy == 0, x>=0 , y>=0. In other words, only one of x or y may be nonzero. This is a natural constraint to consider for mechanical contact problems. The normal force keeping you out of the floor can only be nonzero when the distance of your feet to the floor is exactly 0.  

More abstractly speaking, this condition is also very natural from the context of the KKT conditions, a generalization of minimizing by setting the derivatvie to 0 in the presence of inequality constraints







The magic of complementarity is that they convert optimization problems into feasibility problems. Why does this matter? Well, the solvers for feasibility problems are different than those for optimization problems. Intuitively, it feels like feasiblity is a bit easier to prove than optimization as well. To prove something is feasible, give me a solution. I check all the conditions. Great, you did it. To prove minimality, how do I do it? That is a global condition. How do I know another solution that is better isn't out there? In the context of convex optimization, there is an answer and it involves the duals. The value of the duals at the global minimum is a numerical proof term that demonstrates the minimality of your solution. This is quite remarkable.  

Another reason this is interesting is for multi-stage problems. Converting minimization conditions to feasibility conditions is a form of quantifier elimination. Mixing min and max makes a problem hard. Mixing forall and exists also makes a problem extra hard. In particular, it appears to be traversing up a complexity hierarchy.







The condition to minimize a quadratic objective with linear constraints can be found my differentiating the appropriate lagrangified objective. This results in linear equations, which is a feasibility problem.  

For things with inequality constraints however, the KKT conditions are the requirements for optimization. They are a combination of setting a derivative to 0 and the requirement that dual variables and slack variables must obey complementarity conditions.







We can encode complementarity into a mixed integer solver using the Big-M technique. Geometrically this is relaxing the complementarity condition (which is restircting the solution to be literally on the x-y axes) to a triangle. The MIP solution procedure will branch and bound on the diffrent axes choices.







MILP can encode LP. Linear programs have a formulation with very strong combinatorial flavor. An obvious but remarkable fact about LPs is that the solution can always be a corner of the polytope. You can find corners by selecting d inequalities, making them equalitities and solving that linear system. The trick is to find the right d inequalities of which there are c choose d possibilities, often quite large. It turns out for various reasons that you can exclude many possibilities and greedy search more or less works.







Selection of parameters is often solved by 







I have a suspicion that using a MIP relaxation for a mixed quantifier problem is probably the worst case scenario for branch and bound. 







MILP can encode quadratic programs. 













[https://epubs.siam.org/doi/abs/10.1137/1.9780898719000](https://epubs.siam.org/doi/abs/10.1137/1.9780898719000) book on LCP. LCP seems to be pretty tough







[https://support.gurobi.com/hc/en-us/community/posts/360043212072-Can-I-solve-bilevel-optimization-problems-in-Gurobi-](https://support.gurobi.com/hc/en-us/community/posts/360043212072-Can-I-solve-bilevel-optimization-problems-in-Gurobi-)







going from KKT conditions back to the optimization problem is a kind ofintegration procedure. Not all vector fields are solvable in this way. "convexifying" a problem. Could such a thing be made automatic? 







https://web.stanford.edu/class/ee392o/cvxccv.pdf







Non-zero sum bimatrix games are not LPs.







Bilevel optimization - [https://arxiv.org/pdf/1705.06270.pdf](https://arxiv.org/pdf/1705.06270.pdf) review. Interesting.







Robust optimization - Boyd's website. Convex Concave optimization - Guarantees a single saddle point basically. So it probably is just convex optimization in disguise [https://web.stanford.edu/class/ee364b/lectures/robust_slides.pdf](https://web.stanford.edu/class/ee364b/lectures/robust_slides.pdf)  [https://web.stanford.edu/class/ee392o/cvxccv.pdf](https://web.stanford.edu/class/ee392o/cvxccv.pdf)   



