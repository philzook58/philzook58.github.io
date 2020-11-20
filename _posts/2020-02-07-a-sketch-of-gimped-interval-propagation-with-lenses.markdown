---
author: philzook58
comments: true
date: 2020-02-07 15:52:53+00:00
layout: post
link: https://www.philipzucker.com/a-sketch-of-gimped-interval-propagation-with-lenses/
slug: a-sketch-of-gimped-interval-propagation-with-lenses
title: A Sketch of Gimped Interval Propagation with Lenses
wordpress_id: 2645
categories:
- Formal Methods
- Haskell
tags:
- interval
- lens
---




David Sanders (who lives in Julia land [https://github.com/JuliaIntervals](https://github.com/JuliaIntervals) ) explained a bit of how interval constraint propagation library worked to me last night. He described it as being very similar to backpropagation, which sets off alarm bells for me. 







Backpropagation can be implemented in a point-free functional style using the lens pattern. [http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) Lenses are generally speaking a natural way to express in a functional style forward-backward pass algorithm that shares information between the two passes .







I also note Conal Elliot explicitly mentions interval computation in his compiling to categories work [http://conal.net/papers/compiling-to-categories/](http://conal.net/papers/compiling-to-categories/)  [https://github.com/conal/concat](https://github.com/conal/concat) and he does have something working there.







Interval arithmetic itself has already been implemented in Haskell in Ed Kmett's interval package. [https://hackage.haskell.org/package/intervals-0.9.1/docs/Numeric-Interval.html](https://hackage.haskell.org/package/intervals-0.9.1/docs/Numeric-Interval.html) so we can just use that.







The interesting thing the backward pass gives you is that everything feels a bit more relational rather than functional. The backward pass allows you to infer new information using constraints given down the line. For example, `fuse :: Lens (a,a) a`  let's you enforce that two variables we actually equal. The lens pattern lets you store the forward pass intervals in a closure, so that you can intersect it with the backwards pass intervals.







I make no guarantees what I have here is right. It's a very rough first pass. It compiles, so that is cool I guess.





[gist https://gist.github.com/philzook58/4920b29ac9bd90954ee6d35b95c2b5c7]





Here's my repo in case I fix more things up and you wanna check it out [https://github.com/philzook58/ad-lens/blob/master/src/Numeric/ADLens/Interval.hs](https://github.com/philzook58/ad-lens/blob/master/src/Numeric/ADLens/Interval.hs)







Now having said that, to my knowledge Propagators are a more appropriate technique for this domain. [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ) [https://www.youtube.com/watch?v=nY1BCv3xn24](https://www.youtube.com/watch?v=nY1BCv3xn24) I don't really know propagators though. It's on my to do list.







Lens has a couple problems. It is probably doing way more work than it should, and we aren't iterating to a fixed point. 







Maybe an iterated lens would get us closer?






    
    <code>data Lens s t a b = Lens (a -> (b , (b -> (a, Lens s t a b))))</code>







This is one way to go about the iterative process of updating a neural network in a functional way by evaluating it over and over and backpropagating. The updated weights will be stored in those closures. It seems kind of nice. It is clearly some relative of Iteratees and streaming libraries like pipes and conduit (which are also a compositional bidirectional programming pattern), the main difference being that it enforces a particular ordering of passes (for better or worse). Also I haven't put in any monadic effects, which is to some degree the point of those libraries, but also extremely conceptually clouding to what is going on.  








Another interesting possiblity is the type 







type Lens s t a b = s -> (a, b -> t)







Lens s (Interval s) a (Interval a)







This has pieces that might be helpful for talking about continuous functions in a constructive way. It has the forward definition of the function, and then the inverse image of intervals. The inverse image function depends on the original evaluation point? Does this actually make sense?  The definition of continuity is that this inverse image function must make arbitrarily small image intervals as you give it smaller and smaller range intervals. Continuity is compositional and plays nice with many arithmetic and structural combinators. So maybe something like this might be a nice abstraction for proof carrying continuous functions in Coq or Agda? Pure conjecture. 



