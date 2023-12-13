---
author: philzook58
comments: true
date: 2020-08-09 01:48:39+00:00
layout: post
link: https://www.philipzucker.com/?p=2787
published: false
slug: Finally Tagless Differentiation is Automatic
title: Finally Tagless Differentiation is Automatic
wordpress_id: 2787
---




Defunctionalization to a Wengert list.













I find it a bit puzzling the dichotomy that is claimed between automatic and symbolic differentiation. Symbolic differentiation is things like mathematica and sympy. Automatic is things like tensorflow. Symbolic operates on syntax trees whereas automatic .







But on deeper inspection are they really so different? A computer program is a symbolic thing. Inside any compiler it is going to be represented symbolically as a tree just like sin(x) is stored in Mathematica. The main difference is performance and the degree to which you are abusing the built in capabilities of the compiler. Perhaps this is the entire funky programming technique game. Figuring out ways to abuse compiler capabilities. Transforming between shallow and deeply embedded DSLs.







The most basic differentiator can be built like so.







Finally Tagless style  is one way to take a tree like data type and have the compiler interpret it.







For any data type , we can build a typeclass that is the same thing basically.







It is even clearer to see in the GADT syntax.













Finally Tagless is kind of a pain in the ass because you have to write everything ass end out. I don't know what it is. Why are some styles "natural" and some aren't. Do you get better and more comfortable with practice?







The intepretation function is very straightforward.







However, the differentiation function is less so.







Things than need to be carried down the interpretation become negative parameters in the finally tagless data type. Things that need to be carried up become products. 












    
    <code>data Expr = X | Lit Double | Times Expr Expr | Plus Expr Expr
    
    interp X x = x
    interp (Times a b) x = (interp a x) * (interp b x)
    interp (Plus a b) x = (interp a x) + (interp b x) 
    interp (Lit a) x = a
    
    
    diff X = Lit 1
    diff (Times a b) = Plus (Times (diff a) b)) (Times a (diff b))
    diff (Plus a b) = Plus (diff a) (diff b)
    diff (Lit _) = Lit 0
    
    -- interp . diff -- look at this thing inlined.
    
    class Expr a where
       x :: a
       times :: a -> a -> a
       plus :: a -> a -> a
       lit :: Double -> a
    
    instance Expr (Double -> Double) where
       x y = y
       times f g x = (f x) * (g x) 
       plus f g x = (f x) + (g x)
       lit a _ = a
    
    newtype Diff = Diff (Double -> Double)
    
    instance Expr Diff where
      x _ = 1
      plus (Diff f) (Diff g) = Diff (\x -> f x + g x)
      times (Diff f) (Diff g) = 
    
    
    </code>



