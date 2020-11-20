---
author: philzook58
comments: true
date: 2017-03-30 19:59:17+00:00
layout: post
link: https://www.philipzucker.com/simple-st-monad-examples/
slug: simple-st-monad-examples
title: Some simple ST Monad examples
wordpress_id: 687
tags:
- haskell
---

The ST monad is what you use to do real mutable state in Haskell basically.

The State monad is a more pure guy that just automatically threads the state through pure functions for you.

The ST monad, and structures in it, to my understanding is actually backed by computer memory that is changing. Some things that should be fast and easy become actually fast and easy. Like changing a single element in an array without rebuilding the whole damn thing (or a lot of it).

The ST monad is probably bad style. You're supposed to bend over backward to avoid mutability. It's a gun. Don't shoot yourself. Maybe better style is to use the C FFI (foreign function interface) if you really really need mutability.

Edit (2/4/19): Woah, I really don't agree with the above anymore. You should turn to the ST monad WAY before the C FFI (and odds are you need neither). To suggest otherwise is insane. Although inline-c is an easy package to sprinkle in a little c.

Unlike the IO monad the ST monad can be escaped. Sometimes this is called thawing and freezing, the process of going into and out of the monad.

Here's a couple snippets that demo how it works.

I recommend not thinking about the actual monad laws of this thing. The type signature of ST is messed up. It uses some kind of weird type argument to guarantee in the typechecker that the ST monad reference can't leak outside the monad. In terms of just pretending the do notation is imperative like, it makes sense though.

makeSTRef puts that value you give it into the variable n.

readSTRef pulls out. Modify Let's you modify.

runST ubiquitously has to be used to rip off the ST monad layer. You don't want it if you want to combine a bunch of little ST functions. makeArray' doesn't have it so if you look at it in ghci you don't see 10, you see <<ST Action>>. If you haven't read the reference or frozen the vector, you can't use runST. You'll get an error because that would leak the mutable thing out of the monad.

Vectors are how Haskell has actual c style arrays. It's kind of like numpy if you're familiar with that. Unboxed means you're using raw ints and floats and stuff.

M.replicate builds a size 3 vector filled with doubles of value 1.2. Then I modify the second element and freeze it into an immutable vector to escape the monad.

Storable vectors might be the better default. They are the same really, except they can be passed through the C FFI. I believe hmatrix uses them (and other c interfacing libraries) for passing arrays into Haskell.

    
    import Control.Monad.ST
    import Data.STRef
    import Control.Monad
    import Data.Vector.Unboxed.Mutable as M
    import Data.Vector.Unboxed as V
     
     
    sumST :: Num a => [a] -> a
    sumST xs = runST $ do           -- runST takes out stateful code and makes it pure again.
     
        n <- newSTRef 0             -- Create an STRef (place in memory to store values)
     
        Control.Monad.forM_ xs $ \x -> do         -- For each element of xs ..
            modifySTRef n (+x)      -- add it to what we have in n.
     
        readSTRef n                 -- read the value of n, and return it.
    
    
    
    
    makeArray = runST $ do
        n <- newSTRef [1,2,3]
        readSTRef n
    
    makeArray' = newSTRef 10 >>= readSTRef
    
    makeArray'' = do 
    	a <- newSTRef 10 
    	b <- newSTRef 11
    	return (a,b) 
    
    
    
    makeVec = runST $ do
    	v <- M.replicate 3 (1.2::Double)
    	write v 1 3.1
    	V.freeze v 
    
