---
author: philzook58
comments: true
date: 2016-09-20 23:56:11+00:00
layout: post
link: https://www.philipzucker.com/extra-simple-simply-typed-lambda-calculus-haskell/
slug: extra-simple-simply-typed-lambda-calculus-haskell
title: Extra Simple Simply Typed Lambda Calculus in Haskell
wordpress_id: 517
---

There is something magical about in some sense having a proof in the computer.

You can't really tell if one function equals another in general or two really big things are the same or if some property will hold for all objects via brute force  enumerating and checking. There could always be some counterexample down the line. So that is what intrigues me about Coq and dependent types and propositions as types.

In part of my journey of type theory, I made a really small simply typed Lambda calculus thing in Haskell. I've seen other examples but they have more bells and whistles.

It is so simple that it is worthless. The only type I have are TUnit, which has one value Unit:TUnit.  I also have function types.

Next I'll add on Sum (Eithers) and Product (Pairs) types. With those, then you can start to do something that feels like computation. Either gets us some if statement like constructs. Then I'll add Natural Numbers, then polymorphism, then ultimately dependent types (Maybe not in that order). Also I should poke into the untyped lambda calculus.

Functions only take one variable. Multivariable functions can be defined using currying. I used de Bruijn indices, which as I understand them just put bound variables on a stack, which I implement as a list carried around in both the type checker and evaluator. I could have used a dictionary to hold named variables, but that would've been more complicated.

Any global variables/ function definitions should be put into the initial environment.

Note that the typechecker and the evaluator are pretty dang similar

the typecheck function is self explanatory.

My evaluator is suspicious. I'm not sure it is right. If anyone ever reads this and sees something wrong, please let me know.

I do not particularly understand the sequent calculus notation and how to translate it to the type checker. I mostly did what feels right rather than consult any source.

    
    
    -- simply typed lambda
    
    {-
    data MyTypes = Unit | Func MyTypes MyTypes
    
    data Expr = Var Int MyTypes | Ap Expr Expr | Lam Expr MyTypes | Name String MyTypes
    
    -}
    
    
    data MyTypes = TUnit | TFunc MyTypes MyTypes | TErr deriving (Show, Eq)
    -- That I used Eq deserves some pause perhaps.
    
     -- Lambda x:T body
     -- var derives its type from its lambda binding
     -- The type in Lam is the type of it's incoming variable
    data Term = Unit MyTypes | Lam MyTypes Term | Var Int | Ap Term Term deriving Show
    
     
    -- gamma is environment
    -- implement gamma as a stack. gamma is only storing the typing of bound variables
    -- by the books, gamma should be storing more.
    type Gamma = [MyTypes]
    
    infunctype (TFunc a b) = a
    outfunctype (TFunc a b) = b
    
    
    typecheck :: Gamma -> Term -> MyTypes
    typecheck gamma (Unit TUnit) = TUnit
    typecheck gamma (Lam vartype term) = TFunc vartype (typecheck gamma' term) where gamma' = (vartype : gamma)
    typecheck gamma (Ap term1 term2) = if intype == vartype then outtype else TErr where intype = infunctype (typecheck gamma term1)
                                                                                         outtype = outfunctype (typecheck gamma term1)
                                                                                         vartype = typecheck gamma term2 
    
    typecheck (a:gamma) (Var 0) = a
    typecheck (a:gamma) (Var n) = typecheck gamma (Var (n-1)) 
    typecheck _ _ = TErr
     
    -- I could also enforce type annotation on variables but then I'd have to check that matches the var type given in the lambdaexpr
    --
    
    n = Unit TUnit
    
    myexpr = (Lam TUnit (Var 0))
    myexpr2 = Ap myexpr (Unit TUnit)
    myexpr3 = Ap myexpr4 (Lam TUnit (Unit TUnit)) -- higher order function. Takes
    -- func and gives it Unit
    myexpr4 =  (Lam (TFunc TUnit TUnit) (Ap (Var 0) (Unit TUnit)))
    nestedexpr = (Lam TUnit (Lam TUnit (Var 1))) -- With no unique stuff, pretty hard to check.
    myexpr5 = Ap nestedexpr (Unit TUnit)
    myexpr6 = (Lam TUnit (Ap (Lam TUnit (Var 1)) (Unit TUnit)))
    myexpr7 =  Ap myexpr6 (Unit TUnit)
    failexpr = Ap (Lam TUnit (Var 0)) (Lam TUnit (Unit TUnit))
    nullgamma = []
    -- type this to give it a try
    -- typecheck nullgamma myexpr
    
    
    eval :: [Term] -> Term -> Term
    eval env (Unit _) = Unit TUnit
    eval env (Ap (Lam _ body) term2) = eval ((eval env term2):env) body
    eval env (Ap (Var n) term2) = eval env (Ap func term2) where func = eval env (Var n) 
    eval (a:env) (Var 0) = a
    eval (a:env) (Var n) = eval env (Var (n-1))
    eval env (Lam x y) = Lam x y -- I want to eval y but 
    eval _ x = x
    
    
    run expr = eval [] expr
    -- can bind global stuff by lambda lifting? 
    -- Ap (Lam global (body)) (what it refers to)
    
    
    -- Can I rewrite the program with logic naming?
    {-
    data Prop = PTruth | PImpl Prop Prop deriving (Show, Eq)
    data Evidence = Truth PTruth | TurnStile 
    -}
    
    
    
    
    



