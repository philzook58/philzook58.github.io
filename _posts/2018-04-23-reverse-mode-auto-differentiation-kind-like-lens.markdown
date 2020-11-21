---
author: philzook58
comments: true
date: 2018-04-23 16:36:24+00:00
layout: post
link: https://www.philipzucker.com/reverse-mode-auto-differentiation-kind-like-lens/
slug: reverse-mode-auto-differentiation-kind-like-lens
title: Reverse Mode Auto Differentiation is Kind of Like a Lens
wordpress_id: 1045
tags:
- automatic differentiation
- haskell
---

Edit: More cogent version here [http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/)

Warning: I'm using sketchy uncompiled Haskell pseudocode.

Auto-differentiation is writing a function that also computes the derivative alongside calculating its value. Function composition is done alongside applying the chain rule to the derivative part.

One way to do this is to use a "dual number". Functions now take a tuple of values and derivatives.

The Jacobean of a function from $ R^n \rightarrow R^m$ is a m by n matrix. The chain rule basically says that you need to compose the matrices via multiplication when you compose the value functions.  This is the composition of the linear maps.

Conceptually, you initialize the process with a NxN identity matrix corresponding to the fact that $ \partial x_i/\partial x_j=\delta_{ij}$

    
    type DFun = (Vector Double, Matrix Double) -> (Vector Double, Matrix Double)
    
    sin' :: DFun
    sin' (x, j) = (sin x, dot (diag $ cos x) j )


Vectorized versions of scalar functions (maps) will often use diag

A couple points:



 	
  1.  Since the Jacobean j is always going to be multiplied in composition, it makes sense to factor this out into a Monad structure (Applicative maybe? Not sure we need full Monad power).

 	
  2. There is an alternative to using explicit Matrix data types for linear maps. We could instead represent the jacobeans using (Vector Double) -> Vector Double. The downside of this is that you can't inspect elements. You need explicit matrices as far as I know to do Gaussian elimination and QR decomposition. You can sample the function to reconstitute the matrix if need be, but this is somewhat roundabout. On the other hand, if your only objective is to multiply matrices, one can use very efficient versions. Instead of an explicit dense NxN identity matrix, you can use the function id :: a -> a, which only does some minimal pointer manipulation or is optimized away. I think that since we are largely multiplying Jacobeans, this is fine.



    
    newtype DMonad a = (a , a -> a)
    
    instance Monad (DMonad) where
       return a = (a, id)
       (x, j) >>= f =  let (y, j') = f x in (y, j' . j)




What we've shown so far is Forward Mode.

When you multiply matrices you are free to associate them in any direction you like. (D(C(BA))) is the association we're using right now. But you are free to left associate them. ((DC)B)A). You can write this is right associated form using the transpose $ ((DC)B)A)^T = (A^T(B^T(C^TD^T))) $

This form is reverse mode auto differentiation. Its advantage is the number of computations you have to do and the intermediate values you have to hold. If one is going from many variables to a small result, this is preferable.

It is actually exactly the same in implementation except you reverse the order of composition of the derivatives. We forward compose value functions and reverse compose derivative functions (matrices).

[![drawing-2](/assets/Drawing-2.png)](/assets/Drawing-2.png)

    
    newtype RDMonad a = (a , a -> a)
    
    instance Monad (RDMonad) where
       return a = (a, id)
       (x, j) >>= f =  let (y, j') = f x in (y, j . j')


We have CPSed our derivative matrices.

Really a better typed version would not unify all the objects into `a`. While we've chosen to use Vector Double as our type, if we could tell the difference between R^n and R^m at the type level the following would make more sense.

    
    newtype FD a b = (a , b -> a)



    
    newtype RD a b = (a , a -> b)


However, this will no longer be a monad. Instead you'll have to specify a Category instance. The way I got down to this stuff is via reading Conal Elliott's new Automatic Differentiation paper which heavily uses the category interface.  I was trying to remove the need to use constrained categories (it is possible, but I was bogged down in type errors) and make it mesh nice with hmatrix. Let me also mention that using the Arrow style operators *** and dup and &&& and fst, and clever currying that he mentions also seems quite nice here. The Tuple structure is nice for expressing direct sum spaces in matrices. (Vector a, Vector b) is the direct sum of those vector spaces.

Anyway, the arrows for RD are

    
    type DFun' = a -> RD a b = a -> (b, b -> a)


This is a form I've seen before though. It is a lens. Lens' have a getter (a -> b) that extracts b from a and a setter (a -> b -> a) that given an a and a new b returns the replaced a.

Is an automatic derivative function in some sense extracting an implicit calculable value from the original vector and returning in a sense how to change the original function? It is unclear whether one should take the lens analogy far or not.

The type of Lens'  (forall f. [Functor](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Functor.html#t:Functor) f => (b -> f b) -> a -> f a) means that it is isomorphic to a type like DFun'. The type itself does imply the lens laws of setters and getters, so these functions are definitely not proper lawful lenses. It is just curious that conceptually they are not that far off.

The lens trick of replacing this function with a quantified rank 1 type (forall f. ) or quantified rank-2 (forall p.) profunctor trick seems applicable here. We can then compose reverse mode functions using the ordinary (.) operator and abuse convenience functions from the lens library.

Neat if true.




