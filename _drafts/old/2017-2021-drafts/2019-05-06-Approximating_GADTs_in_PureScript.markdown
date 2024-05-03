---
author: philzook58
comments: true
date: 2019-05-06 19:52:41+00:00
layout: post
link: https://www.philipzucker.com/?p=2011
published: false
slug: Approximating GADTs in PureScript
title: Approximating GADTs in PureScript
wordpress_id: 2011
---




[https://medium.com/@hgiasac/purescript-gadts-alternatives-recap-7960daf4acd8](https://medium.com/@hgiasac/purescript-gadts-alternatives-recap-7960daf4acd8)







While I was trying to figure out how to approximate GADTs in Rust, I came across a design that I think is pretty ok. The lack of higher kinded types in Rust really hurts.







Here's the idea. We're going to rely on smart constructors and deconstructors.







Existentials should be taken care of via the Exists type.







Make a data type per constructor of the original gadt. Export these constructors







Make a Sum wrapper type over all of these. Do not export this constructor.







Use Exists to destroy any existential variables.







make smart constructors that build the appropriate piece of the Sum type.







Make a smart destructor typeclass. It cases off of the type variables available in the outer type. Maybe we don't need a typeclass? Just a match function? No we need it.







What if some cases are polymorphic and some are specific. We'll have overlap.







A general Match typeclass might be possible parametrized on the Wrapper type and the inner variables. 







When you use this destructor 






    
    <code>data Eq a b = ReflInternal (Refl a a)
    data Refl a b = Refl
    refl :: Eq a a
    refl = ReflInternal Refl
    
    caseEq :: Eq a b -> ((Refl a a) -> f a a)) -> f a b
    caseEq (ReflInternal r) f = unsafeCoerce (f r)
    
    
    class Case case a' b' | case -> a' b' where
        innermatch :: (case -> f a' b') ->
    instance Case (ReflInternal a b) a a where
        innermatch = 
    
    data S a
    data Z
    
    -- Use newtype if only holds a single thing, but generally will -- sometimes need to be data
    data SNat s = SSInternal (Exists (SS (S a))) | SZInternal (SZ Z)
    newtype SZ a = SZ
    newtype SS b = SS (SNat b) 
    ss :: SNat b -> SNat (S b)
    ss x = SSInternal (Exists (SS x)) 
    sz :: SNat Z
    sz = SZInternal SZ
    
    -- this exists is gnarly. Wait... I don't need it. We have rankntypes
    caseSNat :: forall f s. SNat s -> (SZ -> f Z) -> (forall a. (SS a -> f a)) -> f s
    caseSNat (SZInternal z) f g = unsafeCoerce (f z)
    caseSNat (SSInternal ss) f g = unsafeCoerce (g (unsafeCoerce runExists ss))
    
    class Plus s s' s'' | s s' -> s''
    instance Plus Z s s
    instance Plus x s s' => Plus (S x) s (S s')
    
    plus :: (Plus s s' s'') => SNat s -> SNat s' -> SNat s''
    plus x y = caseSNat x (\SZ      -> y)
                          (\(SS x') -> ss (plus x' y))
    -- can make a consistent match variable arity function
    class Match s [] where
       match :: s -> </code>







Correctly implementing these GADTs is a challenge in and of itself though







The unavoidable match on the inner constructors makes the syntax not all that different from a regular case statement.



