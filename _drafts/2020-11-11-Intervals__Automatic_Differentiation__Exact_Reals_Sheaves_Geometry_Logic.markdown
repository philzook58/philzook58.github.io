---
author: philzook58
comments: true
date: 2020-11-11 00:52:53+00:00
layout: post
link: https://www.philipzucker.com/?p=2729
published: false
slug: Intervals + Automatic Differentiation ~ Exact Reals, Sheaves, Geometry Logic,
title: Intervals + Automatic Differentiation ~ Exact Reals, Sheaves, Geometry Logic,
wordpress_id: 2729
---




There exists the peano form and the man value form of the remainder of a taylor expansion. These formula are precise, but non constructive. They posit the existence of a point with such and such a property, but do not tell you how to find it.







The mean value theorem is a consequence of continuity. A function must take on the mean value of two endpoints of a region somewhere. This is also nonconstructive.







If we take use the mean value theorem on the derivative, we get $latex f'(x) = f'(y) 







$latex \exists y.  x_0 <= y <= x  f(x) = f(x_0) + f'(y)(x - x_o)$ The existential form of the approximation law. This is a rearrangement of the mean value theorem. 







A common tact to take is to turn this into a maximal form $latex f(x) <= f(x_0) \max_y  f(y) (x - x_0)$  $latex f(x) >= f(x_0)  + \min_y f(y) (x - x_0)$. These are less precise statement. It is also possible usually to give overestimates and underestimates for f'. One compositional method by which systematically to do so is Interval Arithmetic.







If we consider a floating point value x to represent an exact number, a numerical computer function will compute only some approximate answer $latex f*(x)$ to the ideal one. We could model this as an additive error $latex f*(x) = f(x) + \epsilon(x)$ or as a multiplicative error $latex (1 + \epsilon(x) ) f(x)$. The multiplicative error is more appropriate for modelling floating point.  https://en.wikipedia.org/wiki/Machine_epsilon







This function $latex \epsilon$ should hopefully be small if in any sense f* is a good approximation. It is unlikely that $\epsilon$ is continuous. To know $epsilon$ precisely would be the same as to know f precsiely, which is exactly the thing that is difficult. So we are in a conundrum. 







We can cut the know by determining bounds on $epsilon$. Good computer libraries computer individual primitive functions such that they are accurate to around the last bit  https://en.wikipedia.org/wiki/Unit_in_the_last_place 













[http://fredrikj.net/calcium/](http://fredrikj.net/calcium/) [https://news.ycombinator.com/item?id=24700705](https://news.ycombinator.com/item?id=24700705)







[https://news.ycombinator.com/item?id=23797302](https://news.ycombinator.com/item?id=23797302) Seemingly impossible functional programs discussion







Cantor space (N -> Bool) is compact.Compact is every open cover has a finite subcover yes? And they 







Ulrich Burger article







Simpson exact integration







[http://math.andrej.com/2011/12/06/how-to-make-the-impossible-functionals-run-even-faster/](http://math.andrej.com/2011/12/06/how-to-make-the-impossible-functionals-run-even-faster/)













The difference between exact reals and interval arithmetic is about control of thec accuracy of the output rather than input.







One way of doing this is Thinking of a real number as 






    
    <code>data Real = Approx -> Approx
    
    type Approx = Rational -- a reasonable choice
    
    But another reasonable choice is
    
    data Real   Z  -> Z
    where the first Z is the accurady 2^n  and the second number is the real in fixed point using 2^n
    
    -- The sierpinksi object. Should return control to you for the purposes of interleaving
    -- since haskell is lazy, we don't necessarily need the explicit thunk
    data SemiDecide = Thunk (() -> SemiDecide) | Yes
    
    </code>







Arbitrary precision floats are available as a library in most languages. Julia actually has them by default which impressed me very much.







The difference between arbitrary precision and exact real computation is a bit subtle. In my mind there is a hierarchy







  * Arbitrary precision floats allow you to set a precision  to do a calculation, but does not track the propagated error under multiple calculations
  * Interval arithmetic let's you set an accuracy on the input and propagate the error forward.
  * Exact Reals allow you to request the error of a _result_ of many calculations to arbitrary precision. It then figures out how much error to request of the input.






There is an implication that exact reals are going to be used on continous functions. Why? Because otherwise if you request too small an asccuracy there may be no input accuracy that gurantees it. Consider a step function evaluated at the step. What accuracy of x will guarantee an accuracy < 1 on y? De nada.  In fact the ability to request an accuracy of the output matches the rough structure of the mathematical $latex\epsilon\delta$ definition of continuity.  













We could avoid this restriction by allowing the accuracy function $latex \epsilon_y -> \delta_x $ to be partial $latex \epsilon_y -> Maybe \delta_x $ if that us what we desire.







Interval arithemtic does not have the implication. The only thing that happens if interval arithemtic is applied to a discontuous function is that we may lose the ethereal property that the size of the result interval goes to 0 when the input interval does.







A point of this post is that we can take arbitrary precision and interval calculations along with a sufficiently generic implementation of automatic differentiation and fairly easily boost them into a form of exact reals with some desirable seeming properties.







A Lens is an interesting and useful example of a forward-backward pass algorithm. It may be related to the "There and Back Again" notion of Danvy. 







It is a relative of the coroutine or the stream processor. Whereas stream processors and coroutines allow dynamic choice of control flow, the lens has the static assumption built into it's type sugnature and structure that There will be a single forward and backward pass, in which the backward pass may use information saved from the forward pass. 







We can extend this to multiple passes, or dynamic control flow structure. 







This control flow can be obfuscated somewhat usefully into a continuation passing style. Continuations are well known as being a technique to gain first class access to control flow.







In a previous post, I was noting how similar interval arithmetic is to automatic differentiation. Simple dual number forward mode automatic differentiation carries along an extra number representing the derivative through a calculation. 







This number characterizes the properties of the function in an infinitesimal neighborhood around the evaluation point.







In interval artihmetic, you can carry an $latex \epsilon$ along with a number. This gives a bound on how 







These bounds and the value of the derivatives are directly related by [Taylor's theorem](https://en.wikipedia.org/wiki/Taylor%27s_theorem), something you probably rightfully ignored the first time they taught you it in calculus class.













There is a hierarchy of conditions about the smoothness and well behavedness of functions. [https://en.wikipedia.org/wiki/Lipschitz_continuity](https://en.wikipedia.org/wiki/Lipschitz_continuity) Requiring something be differentiable is stronger than requiring it to be continuous.













I think it often makes sense to consider the accuracy desired from a computation as a statically known (compile time) quantity. Or at least very slowly changing, in which case it makes sense to JIT a fast version. The interval and automatic differentiation passes can be considered a straightforward form of static analysis done in order to produce fast calculation code that is correct to spec.







It may make sense to use raw floats when it is statically known that these are sufficient. This will probably be faster although there will be cost associated with moving in and out of the arbitrary precision library













Belnap Booleans. There is somne funny business associated with the exact reals. Because they are so heavily entrenched in approximation, this infects other data types too. If I want to know if 0 <x < 1, but have only calculated x to precision 7, what is the appropriate boolean answer? The truth is at that precision we don't have enough information to know. In addition, some decisions may not effect the final result sufficiently to be important. if I test if x > 42.8 and then add 0.0000001 to the result if so, 







Higher order exact structures. There has been some interest and work lately in higher order (in the sense of first class fucntions) automatic differentiation. One wants to consider sequences N -> R and functions R -> R also (and beyond).







Heyting algebra and open sets.  The simplicial model of open sets. Points aren't open in the common model. Let's consider a triangulzation of some shape where we have faces, lines, and vertices. A face does not include it's edges, and a line does not include it's vertcies. We have a simple discrete model then of the topology of this shape. The open sets are arbitrary unions of faces, plus we're allowed sets with lines if all the faces that touch those lines are in the set, and vertices if all the lines are in the set. We can consider mappings the powersets of these things to the other powersets. If all the open sets in the codomain come from open sets in the domain, then this is a continuous map. The













[https://dl.acm.org/doi/abs/10.1145/3385412.3386037](https://dl.acm.org/doi/abs/10.1145/3385412.3386037) Toward an API for real numbers







MarshallB used for CAD [https://dl.acm.org/doi/pdf/10.1145/3341703](https://dl.acm.org/doi/pdf/10.1145/3341703)  [https://www.youtube.com/watch?v=h7g4SxKIE7U](https://www.youtube.com/watch?v=h7g4SxKIE7U) - Ben Sherman giving a talk on this [https://www.ben-sherman.net/publications.html](https://www.ben-sherman.net/publications.html)  some other related publications and thesis







  [https://www.youtube.com/watch?v=f8fivVYdGlg](https://www.youtube.com/watch?v=f8fivVYdGlg) - Norbert Muller 







  







Sierpinski space - semidecidable propositions. You can't have a (non trivial) continuous map into the booleans with the discrete topology. Is this a way to force a computation to a certain precision. Sierpinski feels somewhere between unit and bool. It is something like unit with lazy semantics. We only need to force the computation that returns unit when we inspect it













Semidecidable sets and Heyting Algebra. Semidecidable sets have the curious property that the complement may not also be a semidecidable set







Decidable sets and finite sets. 







What is a set?







What questions do we desire to ask of sets. How do we use them? [http://math.andrej.com/2008/02/06/representations-of-uncomputable-and-uncountable-sets/](http://math.andrej.com/2008/02/06/representations-of-uncomputable-and-uncountable-sets/)







  * union
  * intersection
  * complement
  * difference
  * subset inclusion?
  * element of?
  * select arbitrary
  * empty?
  * full?
  * minimum/maximum
  * equality?
  * power set
  * size?
  * comprehension  - a fundamental reflection principle






What are the canonical examples of constructions or questions about sdpecific sets. Uses?







For finite sets we can form a finite list of the objects in it. We can use fast data structures that use the ability of elements to be compared.







One functional formulation of set is (A -> Bool). This is `elem S`. We can reconstruct S given a complete set [  x | x <- enumAll, f x ]







Another functional set is `all S :: (A -> Bool) -> Bool`, `any S :: (A -> Bool) -> Bool`







Instead of directly using a functional representation, we can use an AST that is interpretable into the functional representation. Every data structure is a program with a stretched definition of program. AST v data structure is not a meaningful distinction







For countably infinite sets we can use lazy lists to represent them [ ]







Sets as ASTs of their operations `data SetN = LTE n | union SetN SetN | InterSect Setn Setn | Not SetN.`

























Mac Lane and Moredijk







Stone Spaces, Categories Allegories







Topos Logos







CPOs. Partially ordered sets that always 







Lattice, semilattice.







Ed Kmett and his propagators.







Barendregt book







Heyting Algebra - Intuitionisitic logic. => isn't just not A \/ B. Why? Intepreting the => operation into 0, .5,  1. You can calculate a value. Pretty funny. => is interior complement. You miss the boundary.







Boolean algebra







Filters, nets, directed sets, ideals, sieves







directed set any two elements have another element that is an upper bound (not necessaruly least, which distinguishes from filter I think)







Regular Logic and Geometrical logic. Weakened forms of logic. Infinitary disjunction. Not supers sure what that means. Regular has forall x. phi(x) -. psi(x). phi an psi include /\ and exists only. Geometrical logic has inifintary disjunction, which has the flavor of topology







What does a categorical limit have to do with a ordinary notion of limit







Exact Reals. Marshall. My other blog post. Belnap bools. Sierpinski space. Functions to () can be interesting if you consider bottom







Abstract Stone Duality. [http://www.paultaylor.eu/ASD/intawi/intawi.pdf](http://www.paultaylor.eu/ASD/intawi/intawi.pdf) [http://www.paultaylor.eu/](http://www.paultaylor.eu/)







Open subsets are semidecidable







Theory of Approximation. Belnap [http://www.pitt.edu/~belnap/howacomputershouldthink.pdf](http://www.pitt.edu/~belnap/howacomputershouldthink.pdf)







Domain theory. Denotation as computable functions. [http://www.cs.nott.ac.uk/~pszgmh/domains.html](http://www.cs.nott.ac.uk/~pszgmh/domains.html) phenomenol.







[https://en.wikibooks.org/wiki/Haskell/Denotational_semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics)







[http://comonad.com/reader/2015/free-monoids-in-haskell/](http://comonad.com/reader/2015/free-monoids-in-haskell/)







Lisp in Small Pieces. Schmidt denotiational semantics







Monotonic and continous







Dana Scott papers - Data types as lattices, 







[https://en.wikipedia.org/wiki/Domain_theory](https://en.wikipedia.org/wiki/Domain_theory)







[https://en.wikipedia.org/wiki/Scott_continuity](https://en.wikipedia.org/wiki/Scott_continuity)







[https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space](https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space)







[http://math.andrej.com/2014/05/08/seemingly-impossible-proofs/](http://math.andrej.com/2014/05/08/seemingly-impossible-proofs/)







Baire Space.  Cantor Space.







[https://link.springer.com/chapter/10.1007/BFb0055795](https://link.springer.com/chapter/10.1007/BFb0055795) exact real functionals







What about Jules Hedges thesis? Did he say something like the Intermeidate value theorem is a functionaL?















