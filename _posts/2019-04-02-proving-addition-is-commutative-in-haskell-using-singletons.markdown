---
author: philzook58
comments: true
date: 2019-04-02 16:41:15+00:00
layout: post
link: https://www.philipzucker.com/proving-addition-is-commutative-in-haskell-using-singletons/
slug: proving-addition-is-commutative-in-haskell-using-singletons
title: Proving Addition is Commutative in Haskell using Singletons
wordpress_id: 1909
categories:
- Haskell
tags:
- haskell
- proofs
- singletons
---




Yesterday morning, I was struck with awe at how amazingly cool the dependently typed approach (Agda, Idris, Coq) to proving programs is. It is great that I can still feel that after tinkering around with it for a couple years. It could feel old hat.







In celebration of that emotion, I decided to write a little introductory blog post about how to do some proving like that in Haskell. Haskell can replicate this ability to prove with varying amounts of pain. For the record, there isn't anything novel in what follows.







One methodology for replicating the feel of dependent types is to use the singletons pattern. The singleton pattern is a way of building a data type so that there is an exact copy of the value of a variable in its type.







For future reference, I have on the following extensions, some of which I'll mention when they come up.






    
    
```

{-# LANGUAGE GADTs, DataKinds, TypeFamilies, RankNTypes, UndecidableInstances, PolyKinds #-}
```








Here's how the pattern goes. 







Step 1: define your ordinary data type. `Bool` is already defined in the Prelude, but here is what it looks like






    
    
```

data Bool = True | False
```








Step 2: turn on the DataKinds extension. This automatically promotes any data type constructor like `True` or `False` or `Just` into types that have apostrophes in front of them `'True`, `'False`, `'Just`. This is mostly a convenience. You could have manually defined something similar like so






    
    
```

data True
data False
data Just a
```








Step 3: Define your singleton datatype. The singleton datatype is a GADT (generalized abstract data type). GADT declarations take on a new syntax. It helps to realize that ordinary type constructors like `Just` are just functions. You can use them anywhere you can use functions.  `Just` has the type `a -> Maybe a`. It might help to show that you can define a lower case synonym.






    
    
```

just :: a -> Maybe a
just = Just
```








`just` is clearly just a regular function. What makes constructors a special thing (not quite "just functions") is that you can also pattern match on them. Data constructors are functions that "do nothing". They hold the data until eventually you get it back again via pattern matching.







So why don't you write the type signature of the constructors when you define them? Why does using a data statement look so different than a function definition? The GADT syntax brings the two concepts visually closer.







Letting you define the type signature for the constructor let's you define a constrained type signature, rather than the inferred most general one. It's similar to the following situation. If you define an identity function `id`, it has the polymorphic type `a -> a`. However, you can explicitly constrain the function with an identical implementation. If you try to use `boolid` on an `Int` it is a type error.






    
    
```

id x = x

boolid :: Bool -> Bool
boolid x = x
```








The GADT syntax let's you constrain what the type signature of the constructor is, but also very interestingly, let's the type checker infer information when you pattern match into the GADT.







With all that spiel, here is the singleton type for `Bool` as a  GADT.






    
    
```

data SBool s where
   STrue :: SBool 'True
   SFalse :: SBool 'False
```








You have made an exact copy of the value at the type level. When you pattern match into a variable `x` of type `SBool s` in the `STrue` branch, it knows that `s ~ 'True` and in the `SFalse` branch it knows that `s ~ 'False`. 







Here's the analogous construction for a Peano natural number






    
    
```

data Nat = Zero | Succ Nat

data SNat s where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)
```








Now let's talk about programming. 







Addition is straightforward to define for our `Nat`.






    
    
```

nplus :: Nat -> Nat -> Nat
nplus Zero x = x
nplus (Succ x) y = Succ (nplus x y)
```








Let's replicate this definition at the type level. The extension we'll want is `TypeFamilies`. Type families enables a syntax and feature for defining functions on types very similarly to how you define regular functions.






    
    
```

type family NPlus x y where
    NPlus 'Zero x = x
    NPlus ('Succ x) y = 'Succ (NPlus x y)
```








Now finally, we can exactly mirror this definition on singletons






    
    
```

snplus :: SNat n -> SNat n' -> SNat (NPlus n n')
snplus SZero x = x
snplus (SSucc x) y = SSucc (snplus x y) 
```








In the type signature `SNat` is kind of like a weirdo `forall`. It is a binding form that generates a new type variable you need to express the typelevel connections you want. The type variable `n` is a typelevel thing that represents the value.







Now let's talk about proving. Basically, if you're intent is proving things, I think it is simplest if you forget that the original data type ever existed. It is just a vestigial appendix that makes the DataKinds you need. Only work with singletons. You will then need to make a safe layer translating into and out of the singletons if you want to interface with non-singleton code.







We're going to want to prove something about equality. The standard definition of equality is






    
    
```

data Eq1 a b where
    Refl :: Eq1 a a
```








I put the 1 there just so I wouldn't clash with the Eq typeclass. It's  ugly, sorry. You can find an identical definition in base [http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Type-Equality.html](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Type-Equality.html) that uses the extension TypeOperators for a much cleaner syntax.







Why is this a reasonable equality?  You can construct using `Refl` only when you are just showing that `a` equals itself. When you pattern match on `Refl`, the type checker is learning that `a ~ b`. It's confusing. Let's just try using it.







We can prove a couple facts about equality. First off that it is a symmetric relation. If $ a = b$ then $ b = a$.






    
    
```

symm :: Eq1 a b -> Eq1 b a
symm Refl = _
```








When we pattern match and expose the incoming `Refl`, the type checker learns that `a ~ b` in this branch of the pattern match. Now we need to return an `Eq1 b a`. But we know that `a ~ b` so this is the same as an `Eq1 a a`. Well, we can easily do that with a `Refl`.






    
    
```

symm :: Eq1 a b -> Eq1 b a
symm Refl = Refl
```








Similarly we can prove the transitivity of equality.






    
    
```

trans :: Eq1 a b -> Eq1 b c -> Eq1 a c 
trans Refl Refl = Refl
```








Pattern matching on the first equality tells the type checker that `a ~ b`, the second that `b ~ c`. Now we need to return a `Eq1 a c` but this is the same as `Eq1 a a` because of the `~` we have, so `Refl` suffices.







It's all damn clever. I wouldn't have come up with it.  








Now let's start proving things about our addition operator. Can we prove that 






    
    
```

proof1 :: Eq1 'Zero 'Zero
proof1 = Refl
```








This one is straightforward since obviously `'Zero` is `'Zero`. How about something slightly more complicated $ 1 + 0 = 1$.






    
    
```

proof1' :: Eq1 (NPlus ('Succ 'Zero) 'Zero) ('Succ 'Zero)
proof1' = Refl
```








The typechecker can evaluate addition on concrete numbers to confirm this all works out.







Here's a much more interesting property $ \forall x. 0 + x = x$  







    
    
```

proof2 :: SNat x -> Eq1 (NPlus 'Zero x) x
proof2 x = Refl
```








This one is also straightforward to prove. Looking at the definition of `NPlus` knowing that the first argument is `'Zero` is enough to evaluate forward. 







Here's our first toughy. $ \forall x. x + 0 = x$ This may seem silly, but our definition of `NPlus` did not treat the two arguments symmetrically. it only pattern match on the first. Until we know more about x, we can't continue. So how do we learn more? By pattern matching and looking at the possible cases of `x`.






    
    
```

proof3 :: SNat x -> (Eq1 (NPlus x 'Zero) x)
proof3 SZero = Refl
proof3 (SSucc x) | Refl <- proof3 x = Refl
```








The first case is very concrete and easy to prove. The second case is more subtle. We learn that `x ~ 'Succ x1` for some `x1` when we exposed the `SSucc` constructor. Hence we now need to prove `Eq1 (NPlus ('Succ x1) 'Zero) ('Succ x1)`. The system now has enough information to evaluate `NPlus` a bit, so actually we need `Eq1 ('Succ (NPlus x1 'Zero)) ('Succ x1)`. The term `(NPlus x1 'Zero)` looks very similar to what we were trying to prove in the first case. We can use a recursive call to get an equality proof that we pattern match to a `Refl` to learn that`(NPlus x1 'Zero) ~ x1` which will then make the required result `Eq1 ('Succ x1) ('Succ x1)` which is obviously true via `Refl`. I learned a neat-o syntax for this second pattern match, called pattern guards. Another way of writing the same thing is






    
    
```

proof3 (SSucc x) = case (proof3 x) of Refl -> Refl
```








Follow all that? Haskell is not as friendly a place to do this as Idris or Agda is.







Now finally, the piece de resistance, the commutativity of addition, which works in a similar but more complicated way.






    
    
```

natcomm :: SNat x -> SNat y -> Eq1 (NPlus x y) (NPlus y x)
natcomm SZero y | Refl <- proof3 y = Refl 
natcomm x@(SSucc x') SZero | Refl <- proof3 x = Refl
natcomm (SSucc x) (SSucc y) | Refl <- natcomm x (SSucc y), Refl <- natcomm (SSucc x) y, Refl <- natcomm x y = Refl
```








  








A question: to what degree does this prove that `nplus` or `snplus` are commutative? The linkage is not perfect. `snplus` is type constrained to return the same result as `NPlus` which feels ok. `nplus` is syntactically identical to the implementation of the other two, but that is the only link, there is nothing compiler enforced.







The existence of non-termination in Haskell also makes everything done here much less fool-proof. It wouldn't be all that hard to accidentally make a recursive call in one of our proofs that is non terminating and the compiler would accept it and say nothing.







I recommend you check out the links below for more.







Source available here [https://github.com/philzook58/singleberg](https://github.com/philzook58/singleberg)  














Resources:







[https://github.com/RyanGlScott/ghc-software-foundations](https://github.com/RyanGlScott/ghc-software-foundations)







[http://hackage.haskell.org/package/singletons](http://hackage.haskell.org/package/singletons)







[https://blog.jle.im/entry/introduction-to-singletons-1.html](https://blog.jle.im/entry/introduction-to-singletons-1.html)







[http://hackage.haskell.org/package/singleton-nats](http://hackage.haskell.org/package/singleton-nats)



