---
author: philzook58
comments: true
date: 2020-03-29 17:34:27+00:00
layout: post
link: https://www.philipzucker.com/uniform-continuity-is-kind-of-like-a-lens/
slug: uniform-continuity-is-kind-of-like-a-lens
title: Uniform Continuity is Kind of  Like a Lens
wordpress_id: 2723
categories:
- Formal Methods
- Haskell
tags:
- analysis
- categorytheory
- lens
---




A really interesting topic is exact real arithmetic. It turns out, there are systematic ways of calculating numerical results with arbitrarily fine accuracy.







In practice this is not used much as it is complicated and slow.







There are deep waters here. 







  * [https://github.com/andrejbauer/marshall](https://github.com/andrejbauer/marshall)
  * [https://github.com/dpsanders/ExactReals.jl](https://github.com/dpsanders/ExactReals.jl)
  * [https://dl.acm.org/doi/10.1016/j.tcs.2005.09.058](https://dl.acm.org/doi/10.1016/j.tcs.2005.09.058)  Implementing exact real arithmetic in python, C++ and C
  * [https://dl.acm.org/doi/10.1145/3341703](https://dl.acm.org/doi/10.1145/3341703)  Sound and robust solid modeling via exact real arithmetic and continuity [https://www.youtube.com/watch?v=h7g4SxKIE7U](https://www.youtube.com/watch?v=h7g4SxKIE7U)
  * [https://en.wikipedia.org/wiki/Computable_analysis](https://en.wikipedia.org/wiki/Computable_analysis)  [https://eccc.weizmann.ac.il/resources/pdf/ica.pdf](https://eccc.weizmann.ac.il/resources/pdf/ica.pdf) [https://www.springer.com/gp/book/9783540668176](https://www.springer.com/gp/book/9783540668176)
  * [http://www.dcs.ed.ac.uk/home/mhe/plume/](http://www.dcs.ed.ac.uk/home/mhe/plume/)
  * [https://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs](https://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs)
  * [https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf](https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf) Geometric Logic in Computer Science by Vickers. Is this connected? It seems so. I have not absorbed much of this.
  * [https://en.wikipedia.org/wiki/Constructive_analysis](https://en.wikipedia.org/wiki/Constructive_analysis)  [https://www.maa.org/press/maa-reviews/real-analysis-a-constructive-approach](https://www.maa.org/press/maa-reviews/real-analysis-a-constructive-approach) Also Bishop.






The problem is made rather difficult by the fact that you can't compute real numbers strictly, you have to in some sense compute better and better finite approximations.







One way of doing this is to compute a stream of arbitrarily good approximations. If someone needs a better approximation than you've already given, they pop the next one off.







Streams give you some inverted control flow. They allow the results to pull on the input, going against the grain of the ordinary direction of computation. If you are interested in a final result of a certain accuracy, they seem somewhat inefficient. You have to search for the right amount to pull the incoming streams, and the intermediate computations may not be helpful.







Haskell chews infinite lists up for breakfast, so it's a convenient place for such things [https://wiki.haskell.org/Exact_real_arithmetic](https://wiki.haskell.org/Exact_real_arithmetic) [https://hackage.haskell.org/package/exact-real](https://hackage.haskell.org/package/exact-real)







A related but slightly different set of methods comes in the form of interval arithmetic. Interval arithmetic also gives precise statements of accuracy, maintain bounds of the accuracy as a number is carried along







Interval arithmetic is very much like forward mode differentiation. In forward mode differentiation, you compute on dual numbers (x,dx) and carry along the derivatives as you go. 






    
    <code>type ForwardMode x dx y dy = (x,dx) -> (y,dy)
    type IntervalFun x delx y dely = (x,delx) -> (y, dely)</code>







Conceptually, differentiation and these validated bounds are connected as well. They are both telling you something about how the function is behaving nearby. The derivative is mostly meaningful at exactly the point it is evaluated. It is extremely local. The verified bounds being carried along are sort of a very principled finite difference approximation.







But reverse mode differentiation is often where it is at. This is the algorithm that drives deep learning. Reverse mode differentiation can be modeled functionally as a kind of lens. [http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) . The thing that makes reverse mode confusing is the backward pass. This is also inverted control flow, where the output pushes information to the input. The Lens structure does this too






    
    <code>type Lens s t a b = s -> (a, b -> t)</code>







It carrier a function that goes in the reverse direction which are being composed in the opposite direction of ordinary control flow. These functions are the "setters" in the ordinary usage of the Lens, but they are the backproppers for differentiation.







By analogy one might try






    
    <code>type RealF x delta y epsilon = Lens x delta y epsilon = x -> (y, epsilon -> delta)</code>







There is something pleasing here compared to interval arithmetic in that the output epsilon drives the input delta.  The second function is kind of a Skolemized $latex \delta(\epsilon)$ from the definition of continuity.







Although it kind of makes sense, there is something unsatisfying about this. How do you compute the x -> y? You already need to know the accuracy before you can make this function?







So it seems to me that actually a better definition is 






    
    <code>type RealF x delta y epsilon = Lens epsilon y delta x  = epsilon -> (delta, x -> y)</code>







This type surprised me and is rather nice in many respects. It let's you actually calculate x -> y, has that lazy pull based feel without infinite streams, and has delta as a function of epsilon.







I have heard, although don't understand, that uniform continuity is the more constructive definition (see constructive analysis by Bridger) [https://en.wikipedia.org/wiki/Uniform_continuity](https://en.wikipedia.org/wiki/Uniform_continuity) This definition seems to match that.







In addition we are able to use approximations of the actual function if we know the accuracy it needs to be computed to. For example, given we know we need 0.01 accuracy of the output, we know we only need 0.009 accuracy in the input and we only need the x term of a Taylor series of sine (the total inaccuracy of the input and the inaccuracy of our approximation of sine combine to give total inaccuracy of output). If we know the needed accuracy allows it, we can work with fast floating point operations. If we need better we can switch over to mpfr, etc. 







This seems nice for MetaOcaml staging or other compile time macro techniques. If the epsilon required is known at compile time, it makes sense to me that one could use MetaOcaml to produce fast unrolled code. In addition, if you know the needed accuracy you can switch between methods and avoid the runtime overhead. The stream based approach seems to have a lot of context switching and perhaps unnecessary intermediate computations. It isn't as bad as it seems, since these intermediate computations are usually necessary to compute anyhow, but still.







We can play the same monoidal category games with these lenses as ever. We can use `dup`, `par`, `add`, `mul`, `sin`, `cos` etc. and wire things up in diagrams and what have you.







This might be a nice type for use in a theorem prover. The Lens type combined with the appropriate properties that the intervals go to zero and stay consistent for arbitrary epsilon seems like enough? { Realf |  something something something}







Relation to Backwards error analysis?







Does this have nice properties like backprop when on high dimensional inputs? That's where backprop really shines, high to low dimensional functions



