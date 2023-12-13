---
author: philzook58
comments: true
date: 2019-09-25 18:28:10+00:00
layout: post
link: https://www.philipzucker.com/?p=1856
published: false
slug: Writing An Interpeter. Point Free DSLs and Tensor Compiling Expressions
title: Writing An Interpeter. Point Free DSLs and Tensor Compiling Expressions
wordpress_id: 1856
---




Updooooot







I really like the algebra example, but I should just pump out a post on the point free lambda GADT. That is simple and interesting







The simplest lambda calculus syntax DSL looks like this













Running this lambda calculus requires somehow dealing with the variables.







In addition, named variable style DSLs require you to buy in whole hog . They aren't very naturally correct. When you interpret or manipulate them you need to think a bit about scoping, alpha renaming, and other issues. You can't refer to variables outside it's scope. Perhaps you are interested in making a fancy lambda calculus with like linear lambda calculus where you have to use a variable exactly once. In order to ,make these things happen, you have to check them. You need to get the cat back in the bag.







Categorical/Point Free DSLs let you more easily buy into power when you want it, piecemeal. They don't have any binding forms and are more easily manipulated.







Conal Elliott has been pushing categorical DSLs in his Compiling to Categories work. He has been focused on final encodings of these DSLs using .a standard set of categorical typeclasses. Final encodings have phenomenal properties, but are not the easiest to use or understand for some reason. It is more familiar to use a data type to represent a DSL.







I think point-free programming is not always that much worse than pointful programming from an ergonomics perspective. But I do think it is less readable and very foreign for some. And the pipework required is painfully explicit, when a named variable let's you implicilty teleport variables around. Perhaps a good approach would be to give a pointful surface syntax for users and immediately transform it into an internal point-free form. Performing manipulations on point-free representations is SO much better.







It is well known that Simply Typed Lambda Calculus is roughly or exactly a Cartesian Closed Category. 







I give hesitation on adding the Closed property to the DSL. This adds closures to your language, which are useful but again you've perhaps added too much power.







Recursion schemes to my knowledge are basically a necessity for point-free programming.







Many DSLs require named variables, for example a DSL with a summation form.






    
    <code>-- The most basic expression
    data Expr = Add Expr Expr | Mul Expr Expr | Lit Int
    
    runExpr (Add a b) = (runExpr a) + (runExpr b)
    
    -- rewrite rules
    dist (Mul (Add x y) z) = rule $ (Mul x z) `Add` (Mul y z)
    
    -- either let the rule match or return same result?
    -- convert io exception to EitherT?
    rule f x = unsafePerformIO $ catches (Just $ f x) [Handle \PatternMatchFail _ -> Nothing]
    -- or use a template haskell quasiquoter section
    [$rule
    dist
    yada yada
    ]
     
    
    
    data ExprF a = Add a a | Mul a a | Lit Int
    type Expr = Fix ExprF
    alg (Add x y) = x + y
    interp = cata alg
    
    --  The simplest boy
    data Expr  = Add Expr Expr | Var String | Mull Expr Expr | Lit Int
    interp env (Var x) = lookup x env 
    data ExprHOAS = Add Expr Expr | Lam (Expr -> Expr) | Mul Expr Expr | Lit Int
    data ExprPHOAS v = Add (Expr v) (Expr v) | Lam (v -> Expr v) | Var v | Lit Int -- Why lam? It's not particularly right to add functions together
    
    data ExprHOAS = Add Expr Expr | Sum (Expr -> Expr) | Mul Expr Expr | Lit Int
    data ExprPHOAS v = Add (Expr v) (Expr v) | Sum (v -> Expr v) | Var v | Lit Int
    data ExprBruijn = 
    
    -- uncurry all contrusctors. Suppose you had to build data types in a point free style. replace (->) with CatExpr. Make type correct wtih GADT.
    -- free variables appear in the input. We pick them by position via Fst/Snd. 
    data Expr
    data ExprCat where
      Add :: ExprCat (Expr,Expr) Expr -- make each constructor a gadt of same type --
      Lit :: ExprCat Int Expr 
      LitInt :: Int -> ExprCat a Int -- inject any literals that may appear (anywhere)
      Compose :: ExprCat b c -> ExprCat a b -> ExprCat a c
      Id :: 
    
      Fan ::
      Fst ::
      Snd ::
      Sum :: CatExpr (a,b) (a,b) -> CatExpr b (Expr, b)
      Sum :: CatExpr (a,b) c -> CatExpr b c 
      Var? -- no var. we're point free
    -- a refacotring kind of like Fix. But not in the sense that we're allow recursive data scruture
    FreeCat f a b where
      Compose
      Id 
      Lift :: f a b -> FreeCat f a b
    Add (Lit 1) (Lit 2) -> Compose Add (Fan (Lit 1) (Lit 2)) :: ExprCat a Expr
    Add (Var "a") (Var "b") ~~ Add :: (Expr,Expr) Expr
    Add (Var "a") (Var "a") ~~ Add . dup -- dup = Fan Id Id
    Sum \x -> x ~ Fst . Sum Id
    add ~ Compose Add Dup
    What does an expression with no free variables look like?
    ExprCat a Expr   
    
    Hadamard -- Meet
    Add -- Join
    MatMul -- Compose
    Div -- Inverse.
    Id -- identity matrix
    KRProd -- partial kron, partial  == Fan
    Kron -- Par = Fst Snd KRProd . What are Fst Snd? A partial trace? While these may be identities in the bool version, they aren't linearly. Maybe if considered homogenously? Or if working with probability, trace = 1.
    Transpose -- Converse
    Trans --
    UnTrans -- moving things between input and output
    Trace -- ? == Compose (Trans Id)
    Scalar Double -> Tensor () ()
    vec :: Tensor a b -> Tensor () (a,b)</code>







[https://www.schoolofhaskell.com/user/edwardk/bound](https://www.schoolofhaskell.com/user/edwardk/bound)







Ed Kmett on bound, his library







First Order Syntax.







HOAS







de Bruijn







PHOAS







Whatever locally nameless is







"Tutorials " on writing depdnetly typed languages







Simply Easy by McBride and co







Mini-TT







Andrej Bauer - http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/







[https://github.com/sweirich/pi-forall](https://github.com/sweirich/pi-forall)







Point-Free Languages  










