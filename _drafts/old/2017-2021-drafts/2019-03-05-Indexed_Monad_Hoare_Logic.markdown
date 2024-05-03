---
author: philzook58
comments: true
date: 2019-03-05 18:22:02+00:00
layout: post
link: https://www.philipzucker.com/?p=1866
published: false
slug: Indexed Monad, Hoare Logic,
title: Indexed Monad, Hoare Logic,
wordpress_id: 1866
---




[https://kseo.github.io/posts/2017-01-12-indexed-monads.html](https://kseo.github.io/posts/2017-01-12-indexed-monads.html)







There are a couple different styles of indexed monad. 







In one version there are two extra type parameters that have to match up into order to compose stuff. This is sometimes described as a changing state type.







The indexed monad is so close to just a category, that I'm not entirely sure what the benefit is. We have split our category into two pieces, the index pieces and the contained pieces and monadized the contained pieces.







In a sense, if known properties of the state are expressed in the type of the state, this corresponds to a Hoare logic style proof







The rebindablesyntax extension let's us get at do notation







[https://ocharles.org.uk/guest-posts/2014-12-06-rebindable-syntax.html](https://ocharles.org.uk/guest-posts/2014-12-06-rebindable-syntax.html)







[https://ocharles.org.uk/blog/posts/2013-11-24-using-indexed-free-monads-to-quickcheck-json.html](https://ocharles.org.uk/blog/posts/2013-11-24-using-indexed-free-monads-to-quickcheck-json.html)







[http://hackage.haskell.org/package/do-notation](http://hackage.haskell.org/package/do-notation)







So what is the simplest hoarse logic proof?







Ryan G.L. Scott has a cool repo where he is replicating some of Software Foundations (a prominent Coq textbook) in dependent Haskell












    
    <code>
    
    data State i j a
    
    makeRef :: State s (Int  , s)  
    
    -- introduce a new variable. It has 
    makeRef :: SInt n -> State s (SInt n, s) (Ref Int)
    
    
    organizing our theorems is sucky
    
    
    set :: Ref -> SInt n -> State s (Ref == n)
    get
    
    return :: a -> State s s a
    
    
    compile :: State s s' a -> TExpQ (IO a)
    
    compile :: State s s' a -> TExpQ (ST s a)
    
    While :: Proxy cond -> State p p a -> State p (p, Not cond) a</code>









