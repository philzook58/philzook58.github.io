---
author: philzook58
comments: true
date: 2019-10-28 18:49:15+00:00
layout: post
link: https://www.philipzucker.com/?p=2019
published: false
slug: Abstract domains, Dynamical Systems and Program Proving
title: Abstract domains, Dynamical Systems and Program Proving
wordpress_id: 2019
---




### Keymaera







Zach was talking about grobner bases as a useful thing for "darboux" something







xdot = f(x) wihere f(x) is polynomial. Then similar to sum of squares lyapunov, we can derive polynomial invariants







[https://www.cs.colorado.edu/~srirams/papers/acc14-lyapunov.pdf](https://www.cs.colorado.edu/~srirams/papers/acc14-lyapunov.pdf)







darboux polynomials







first and second integrals







[https://www.springer.com/gp/book/9783319716541](https://www.springer.com/gp/book/9783319716541)







Symbolic differentiable







REDUCE  computer system. PSODE1 PSODE2. CDIFF. CDE [https://reduce-algebra.sourceforge.io/documentation.php](https://reduce-algebra.sourceforge.io/documentation.php)







sigfig













### Older







Dynamical systems ands Imperative programs







There is a great deal of similarity between dynamical systems and programs, in their analysis and structure.







check out the work of Andre Platzer.







In a certain sense this is unsurprising? Comuting systems live in the physical world. The operations of an abstract machine are exactly that, abstractions of the movement of electrons in transistor circuits, a chunky discretization of their movement.







In a somewhat generic framework, we can treat them similairly. Transition relations might be a good framework.







There is a notion of time. There may be a somewhat flexible notion of time if we extend ourselves to the relativistic or the asynchronous case. It's interesting that I believe I have heard Einstein's work as a patent clerk reviwing mechanisms for the synchronization of telegraph equipment may have had some influence on his ideas.  

Analogies like this are explicit in Lamport's work on vector clocks.  

Time can be continuous or discrete, partially or totally ordered.







There is a notion of state. In physics, one is inclined to think about continuous state of momentum and position of all degrees of freedom. In a program, once considers all the.   

We are often highly desirous of limitting the size of our state space for the purpose of analysis. In principle, perhaps very physical system has the state space consisting of the entire universe. Likewise a programs' state space is the entirety of of the computer memeory and register content. Or again perhaps the netire universe.







There are equations of motion. The transition relations







Clean physics systems do not have dissipation and have hamiltonian structure and time independence. But in the more general context of dynamical systems, all these things occur.







time independent equations of motion. Programs are usually not best thought of in this way. If we include a clock or an insturction pointer register, we can recover time independence in a cheating kind of way.







backwards and forward sets.







Of fundamental importance to both is the notion of invariants. Simple invaraints, onece hypothesized, can be checked by seeing if they rae conserved by a single step of the transition relation / checking if their time derivative is 0.  

Energy, momentum, spin.  

tree balancing, sortedness, positivity







Time can be chunked into periodicity for ocnitnous systems. Sometimes we want to talk about invariant of the cycle.







Symmettry and conservation laws. It is one of the rather spooky principles of modern physics that symmettry and conservation laws are intrinsically linked. The connection of this point to programs is unclear. Programs tend to not be hyper symmetrical? Parallel processing models. I've heard weirdo rumblings connecting polymorphism to noether's theorem I think. What if I could annotate polymorphic variables with group annotations?  

(a,a,a) -> a -- full permutation available  

(a,b,c) -> g  -- Z3 only?  

Or what about my V2 code. I want it to be invariant under SO(2).  

Does noether's theorem require a lagrangian formulation? incompressible dynamics?  

It's interesting. Symmettry is a good principle. Abstract interpetation via symmettries. Symmettrical sets. Maybe this is a good technique for nuermical programs. Symmettry is one of the standard tests by which we determine something is fucked.







Incompressibility. Linear Types? Reversible computing. non reversible processes as projections of reversible ones.







Lyapunov functions and termination metrics. It is not clear if a system will eventually go to some region or position. Once methodology for proving this is to cook up a lyapunov function, a function that is always decreasing sufficiently and bounded below. Ibce we have this function, we know that the execution must always be.  Similarly, recursion and iteration may not terminate. We need a bounded function that is always decreasing and then this is sufficient to show that they do.







Physics is strongly interested in geometrical space. Programs seem to be much  less so. Perhaps seperation logic and "regions" of memory. Perhaps artificially imposing low dimensional spatial notions upon memory might have benefits? Pure speculation. adress space is 1 dimensions usually.  

matrices. For matrices and parallelism, the circle is closed because we are often using those in application to physical problems. Computers are built in phsycial reality, and then they can simulate it. kind of fucky huh?  

Multiple variable values or multiple adresses can be  

embedded as an n-d space. HOwever, the usually geometrical symmettries seem to not matter so much. Maybe translational symmettry?







Topology in code. ? Topology in physics is a weird subject anyhow. Classical topological invaraints of dislocations. Topological band theory. Homotopy type theory. Topological considerations of types escardo. "Continuity" gets intepretted in different ways.







Consider the code of an ode solver.  

From this consideration, the universal program analysis must inlcude as a sepcial case the analysis of physics. Yikes.   

consider the code of a parallel pde solver







hybrid systems and the bouncing ball







finite state machines







induction













## Abstract domains







[http://polly.llvm.org/](http://polly.llvm.org/)







[https://www.bugseng.com/parma-polyhedra-library](https://www.bugseng.com/parma-polyhedra-library)







[http://apron.cri.ensmp.fr/library/](http://apron.cri.ensmp.fr/library/)







[https://github.com/topics/abstract-interpretation](https://github.com/topics/abstract-interpretation)







[http://elina.ethz.ch/](http://elina.ethz.ch/) elina







Relaxation Operations Reaearshc - Abstraction Abstract Intepretation







There are obviously connected ideas across many fields.  








  * Abstract Interpetation
  * Control - Reachability. Robustness analysis. Julia project on these. Hybrid Systems
  * Games. The quantified linear program work.
  * Model Checking. Timed Automata. Temporal logic
  * Quantifier problems. Polynomial hierarchy. Complex queries. Beyond NP






CEGAR and CEGIS. abstraction refinement)







Control. http://www-ljk.imag.fr/membres/Antoine.Girard/Publications/hscc2005.pdf zonotope for reachability. tedrake's postdoc and polyhedral inclusion. http://groups.csail.mit.edu/robotics-center/public_papers/Marcucci18.pdf  https://github.com/sadraddini/pypolycontain







lrs and CDD. Polyhedra.jl. parametric MPC. Expicit mpc. Multiparametric mpc. There are toolboxes available. It is a qeustionable approach when online solving is so fast. 







Kmett and Guanxi. 







Beyond NP http://beyondnp.org/  








There are equivalant methods in the binary and conitnuoous domain.







Interval domains. In a bit vector is is 0,1, and don't care are the only domains







BDD seem closest to decision trees, which are variable ordered kD trees using variable oriented cutting planes. Can we do reduction? Can we be applicative on the result? Yes. Cutting planes are unlikely to coincide in many methods of making them though. 







Octagon and 2-Sat. Binary relations means resolution procedure only produces more binary terms rather than higher order terms. There are only n^2 such terms and it is easy to see when one dominates the other. There are ways of formulating both as graph problems. 2-SAT can be though of as an implication graph. We can generate 2 variables per vairable and think of one as the negative variable. Then add the constraints xbar or not x.   Both allow us to express at least equaltiy of variables and sort of conujgation of variables. 2-Sat is a kind of connectivity problem and octagon is some kind of shortest path.







Difference bounded matrices. This double inclusion property and requiring a certain symettry of the matrices is evocative of bogoliubov/ majorana stuff.  The paper mentioons constraint logic programming over binary constraints.  Difference bounded matrices are used in the context of timed automata. You know that a trasnition will happen within twelve seconds of an arrival into a state. That is natural expressed as a time difference.







Matrix analogies. Min + algerba can use matrices to find hsortest paths. The and/or analogy can find relational connections / connected components (this is 2-sat). regular matrices can find quantum or stochastic walks. What is left and right division for min,+? relational and min-+ converge in finite time. Probability converges but eigenvalue algo necessary to get true fixed point. Square versus rectangular matrices bring in different questions. pointwise inequality of matrices for the relational inlcusion. meet and join are pointwise max/min. Projection...? removing variables.







A rectangular difference bounded matrix does make sense. And it makes sense to compose them as well (via a resolution procedure, with simplification). You can dup and merge. There is an id. I was already playing with a linear relation thing in ConvexCat. If i want a trans untrans, I need to be able to include difference constraints purely among the input or output also. i don't HAVE to allow this. Yeah. It seems like relational algebra is a better fit for Quantified LP problems rather than LP problems. The octagon domain is pretty cool. I can probably make a simple quasi simplex algorithm for a linear cost function by traversing the DBM graph.







Python : networkxX or cvxpy. Can I encode octagon in fairly easily? I can encode shortest path in either. But I'm not sure I can encode  







Mixing domains. i was thinking of mixing octagon and polyhedral. Like relaxing as we go. But what about relaxing octagon to interval. Or having an interface between 2sat and octagon. We could try and replace big pieces of inequyalities with approximate octagonal equivalents. A careful kind of rounding to zero.







I do think the core of it is a resolution / linear derivation procedure. It isn't clear that you derive everything possible or that the procedure will reach a fixed point, except by the graph analogy.







Question: Given SAT problem, can we relax to a 2-SAT? In a way that is sound. Every satisfiable assignemnt is satisfiable in 2-sat problem. This is sort of trivially true. Question is if we can give a pretty tight version?  Selecting all pairs from within a clause makes it a tighter formula. Harder to satisfy only. Dropping variables from within clause is likewise harder to satisfy. Ok. Just dropping entire clauses is an obvious relxation. We can introduce new variables for chunks of clauses (especially ones that appear in many spots).  







Horn clauses. There is possibly a fourier motzkin equivalent. If you rewrite an inequality such that only positive coefficients appear, then a clause is in Horn form if only 1 variable appears on the left hand side. Then unit propagation? If a variable appears by itself you have a bound on that variable. You may be able to remove it's appearance in other terms via an LP probe? Certainly as a relaxation. You may want to maintain it's implicit dependence on the variable in case that bound gets updated. 







Fourier Motzkin - You need to combine all inequalities available to remove a variable. Redundant contraints are somewhat difficult to detect. One can try to not fully expand all foureir motzkin options, or reduce the equations linearly as one procedes.







Double description. Convex polytopes are both the convex hull of point sets and regions of inequality contraints. You could lazily convert between the two forms. Then use counterexample refinement to figure out good planes or points to convert back over. Points make it easy to remove variables existentially. Also Union = union of points. Planes make intersection easy.







Relaxation. You can perform non-negative sums of constraints to make new valid constraints. You can linearly reduce a set to a smaller set. Inequalities can be added together







Intersection of D planes gives a point, probably. This can be found by turning inequalities to equalities and doing a matrix solve. Polytope is smallest bounded shape. I guess a priori we don't know we need bounded shapes.







Linear programming as subroutine. LP are solvable and useful. 







Internal abstraction and domain transference. We can 







Brute force enumeration is king. For finite domains that can resolve anything. Then we can consider convex zones in finite domains and the adjunction to the polyhedra domain. The galois connection is pumped by branch and bound algorithms







There is a galois connection between the difference matrix representation and the 







You want to perform set-y operations. But given some data type for some kind of set, union and interesection don't always work. You could just freeze out all your unions and intersections into a union/interesction tree. That basically does nothing and puts off the decisions for later. Maybe a good call. However, you sometimes (always?) can find the best interesction and union in the ones you have available. These are the meet and join. Now you are in the realm of inequality reasoning rather than equality reasoning which is very similar but a bit subtler and richer.\ Convex hull of union is best union of convex sets.







Parma libary uses exacts fraciotns. Slower but exact. CDD based stuff uses floating point. Parma library appears to have at least 2 projects for its python bindings?







  * [https://scaron.info/teaching/polyhedra-and-polytopes.html](https://scaron.info/teaching/polyhedra-and-polytopes.html)
  * [https://github.com/stephane-caron/pypoman](https://github.com/stephane-caron/pypoman)
  * [https://github.com/haudren/pyparma](https://github.com/haudren/pyparma)
  * [https://pypi.org/project/pplpy/](https://pypi.org/project/pplpy/)
  * [https://pycddlib.readthedocs.io/en/latest/](https://pycddlib.readthedocs.io/en/latest/)
  * [https://github.com/JuliaPolyhedra/Polyhedra.jl](https://github.com/JuliaPolyhedra/Polyhedra.jl)
  * [https://github.com/JuliaReach/Reachability.jl](https://github.com/JuliaReach/Reachability.jl)






The tensor sets are integer sets. The integer set library may have something to say about that.







For general convex sets, you can lazily sample points. If you get extremal points, those are partilarly good. Convex hull of points gets you an inner apporximation. The conjunction of the extremal half planes gives you a good over approximation. Perhaps general convex sets should be thought of as a tower of n-point or n-half plane or (n,m) point halfplane domains. You push your way through them as you think you need. Bounding box is gotten by probing 2n directions. kamenev algorithm. Take direction with worst difference between inner and out approximaion. Add that into your set. This LazySet julia package has interesting docs







Affine Map + Interval input. This is a roatetd rectangle output. Can we combine interval and affine map usefully? Zonotopes. Minkowski sum of lines. Seems like it is powerful enogu hto describe full polyhedra. The cartesian decomposition seems like a relative of relational division. Can make cartesian over and under representations







[https://en.wikipedia.org/wiki/Hybrid_system](https://en.wikipedia.org/wiki/Hybrid_system)







Cyber physical system appears to be a keyword.







PowerSet construction can be sprinkled in. PowerSet of unique integers.







[http://www.people.ku.edu/~melhodiri/Convex-Cone-Sets-and-Functions.pdf](http://www.people.ku.edu/~melhodiri/Convex-Cone-Sets-and-Functions.pdf) interesting book by fenchel. I had the idea to compactify but just putting us in a box of 1e10. Much better compactification is given by going "projective" / Cone rather than convex set. If we consider points to by rays in one higher dimension. A plane at z=1 can be seen as regular euclidean space. Slightly different from projective because negative coefficients are not acceptable. Now points at infinity are fine, as are half planes that cover the entire space. Duality becomes cleaner. Minkowski sum is literal sum. Homoegnous linear ineqaulities. We have 1 degree of freedom to introudce regularization. Or we can use the angle metric. Or the chord metric. 0 represents an impossible to satisfy set. Cone inequalities are relations.







Application of these polyhedral techniques to alternating quantieifer problems. It isn't that the techniques are addressing the issue. Polyhedra techniques allow you to talk about "infinite" spaces using finite means. Finite problems are fundamentally not an issue. All problems can be solved on them by brute force. QBF is not fundamentally unsolvable. Enumeration is king. However, the ability to talk about inifnite spaces also is the ability to talk about large but finite spaces. And the mechanism by which they do this is over and under approximation, which can be precisely stated. The hope is to approximate a big problem using smaller finite means in such a way as that the enumeration method on the small problem is tractable. 







https://arxiv.org/pdf/cs/0703084.pdf The octagon domain







[http://inst.cs.berkeley.edu/~ee291e/sp09/handouts/book.pdf](http://inst.cs.berkeley.edu/~ee291e/sp09/handouts/book.pdf) analysis of hybrid systems bookl







http://www.uppaal.org/ time automata model checker







http://www.effective-modeling.org/ cyber physical systems







https://www.seas.upenn.edu/~lee/10cis541/lectures.html







SpaceEx, dreach, Flow, keymera, dreal  








Hybrid automata, hybrid systems, cyber physical systems.







http://i-cav.org/2016/wp-content/uploads/2016/03/cpsCAVMW.pdf useful overview slides







[https://ptolemy.berkeley.edu/books/leeseshia/](https://ptolemy.berkeley.edu/books/leeseshia/)







[https://mitpress.mit.edu/books/principles-cyber-physical-systems](https://mitpress.mit.edu/books/principles-cyber-physical-systems) https://ieeexplore.ieee.org/book/7109352







Andre Platzer, Logical Analysis of Hybrid Systems







[https://ptolemy.berkeley.edu/](https://ptolemy.berkeley.edu/)







CAV 







http://underactuated.csail.mit.edu/Spring2019/guest_lecture/poly_underactuated.pdf lecture 20 of 2019 underactuated robotics has poltyope stuff. Apparently polytope containment is a very different problem based on whether you have V or H reps. I guess that makes sense. Checking V rep in Hrep is super easy. Check each point. H in H is pretty easy. See if you can break each inequality in one in the other -> N LPs. Sadradinni has some tricks to pack this up as a single lp? My mixed quantifier model of the diffculty of problems is not matching up well. Hm,m He actually mentions mied quantifiers. Polytopic Laypunov functions. Minokwoski sum plays nice with zonotopes? Robust control invariant set. He mentions oxford work from 2007 and something from the 70s that is principled but untractable? So it is a mixed quantifier problem, but somehow we're making them tractable? Is invaraint question Like the single step polyotopic relation T\C mod the control possiblities? exists control for a







https://link.springer.com/content/pdf/10.1007%2F978-1-4613-8431-1.pdf Ziegler book on polytopes is amusing







https://spiral.imperial.ac.uk/bitstream/10044/1/4346/1/cued_control_155.pdf Kerrigan thesis. Interesting. It feels very clear to me that we could make relational algerba formulations of the things they are talking about. Minkowski difference is take the minkowski sum relation and doing a shrink r division of some kind. Bemporad. Boyd Morari?   








i feel like something clicked regarding relational algerba and polytopes and control. That thesis talks abot minkowski difference. It clearly has the feel of relational division. Dynamic programming. The one step relation x_t R x_{t+1}. The cost relation. Using an L1 or Linfinity cost makes it polytopal. Minkwoski sum relation. We have meet. and join, although join is much harder. trans and untrans cost nothing. Projection is also a thing. It seems like a galois connection possibly with injection x -> (x,0). injection is easy. projection is hard. Containment is expressible as a single big lp or by exmaining n lps. chains of containement 







Girard. Tube MPC. Funnel vs Tube? Minkowski sum is useful for pertubative analysis by error. We are summing in the error polytope. Zonoetopes are another subclass of polytopes that have useful properties. It's easy to minkwoski sum for example. 







  








  




