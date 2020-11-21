---
author: philzook58
comments: true
date: 2020-03-04 05:35:17+00:00
layout: post
link: https://www.philipzucker.com/notes-on-finally-tagless/
slug: notes-on-finally-tagless
title: Notes on Finally Tagless
wordpress_id: 2686
categories:
- Haskell
tags:
- haskell
---




For reading group this week we read finally tagless partially evaluated [http://okmij.org/ftp/tagless-final/JFP.pdf](http://okmij.org/ftp/tagless-final/JFP.pdf). It took me a couple minutes to regain my footing on my preferred explanation of what tagless is. This is why we write blog posts, to remember that kind of thing.







One thing that is very confusing about finally tagless as presented is that people tend to be talking about dsls with binding forms, like embedded lambda calculi, or tensor summation and things. This is complicated and I think to some degree orthogonal to the core of the the idea. Instead I'll use Bool as my running example, which is so simple that it perhaps obscures the idea in the opposite direction.







When you define a data type, you define constructors. Constructors are just functions. This is more readily apparent using GADT syntax. 







What makes constructor feel like more than just ordinary functions is that you can pattern match out of them too. Applying constructors and pattern matching out of them is a completely lossless process. The two processes are dual in some sense. In some sense, it seems like programming is one big shuffling game. In some sense. In some sense. In some sense.







In some sense. iN SoME SeNSe







Anyway, pattern matching is it's own thing that doesn't feel like other piece of the language. But pattern matching can be captured as a first class object with the notion of an eliminator / recursor function. If you think about it, what pattern matching is is a thing that takes that data type and then gives you the stuff inside the data type. So pattern matching is the same as  function that takes in a functions that tell me what to do with that stuff for each case. 







The bohm-berarducci encoding of data types makes the pattern matching function the data type itself.






    
    
```

data BoolI where
  TrueI  :: BoolI
  FalseI :: BoolI

type BoolC = forall s. s -> s -> s
truec :: BoolC
truec = \x y -> x
falsec :: BoolC 
falsec = \x y -> y

to :: BoolI -> BoolC
to TrueI = truec
to FalseI = falsec

from :: BoolC -> BoolI
from f = f TrueI FalseI

```








In the final encoding of the datatype, we replace the `data` keyword with the `class` keyword. We can witness the isomorphism with an instance for BoolI and an intepretation function from BoolI to BoolF






    
    
```

class BoolF a where
   truef :: a
   falsef :: a

instance BoolF BoolI where
   truef = TrueI
   falsef = FalseI

interpf :: BoolF a => BoolI -> a
interpf TrueI = truef
interpf FalseI = falsef
```








However, there are some very nice features of this encoding. Typeclass resolution happens completely at compile time. This means that you can write something once and have it run many ways, with no runtime overhead. This is useful for dsls, especially ones you intend to just immediately interpret out of. 







Once way you can have something run many ways is by having a syntax tree for the thing you want to do. Then you can write different intepreters. But then you have the runtime cost of interpretation.






    
    
```

interpi :: BoolI -> Int
interpi TrueI = 40
interpi FalseF = 27

interps :: BoolI -> String
interps TrueI = "hi"
interps FalseF = "fred"

instance BoolF Int where
   truef = 40
   falsef = 27

instance BoolF String where
  truef = "hi"
  falsef = "fred" 
```








A second feature is the openness of typeclasses compared to data types. Suppose you wanted to add another field to BoolI. Now you need to correct all your functions. However, you can make the new field a new typeclass and all your old functions still work. You can require the power you need.







A third thing is that finally tagless does get you some of the type restriction available with GADTs in a language without them. GADTs are IN SOME SENSE just constructors without the most general inferred type. But they also let you recover the type information you hid away upon pattern matching.







We can see the correspondence in a different way. A typeclass constraint corresponds to the implicit supplying of a dictionary with fields correspond to the typeclass.






    
    
```

s -> s -> s ~ (s,s) -> s ~ {truef :: s, falsef :: s} -> s ~ BoolF s => s
```








What is finally tagless not so good for? Brains mostly. It is quite a mind bending style to use. If you want to do deep pattern matching in some simplifier, it is possible, yet rather difficult to achieve. I've seen this done in some Oleg papers somewhere (on SQL query optimization I think?)







Here's another example on list






    
    
```

class ListF f where
  cons :: a -> f a -> f a
  nil :: f a

instance ListF [] where
  cons = (:)
  nil = []

interpl :: LiftF f => [a] -> f a
interpl (x : xs) = cons x (interpl xs)
interpl [] = nil


type ListC a = forall s. (a -> s -> s) -> s -> s
```








Going the other direction from finally tagless is interesting as well. If you take a typeclass and replace the keyword `class` with `data`, you get something like the "free" version of that class. Two cases in mind are that of the free monoid and free monad. The usual presentation of these looks different though. That is because they are canonized. These data types need to be thought of as "modulo" the laws of the typeclass, which probably shows up in a custom Eq instance. I'm a little hazy on exactly how to explain the Pure constructors, but you do need them I think. 






    
    
```

data FreeMonoid a where
   Mappend :: FreeMonoid a -> FreeMonoid a -> FreeMonoid a
   Mempty :: FreeMonoid a
   Pure :: a -> Freemonoid a
data FreeMonad f a where
   Bind :: FreeMond f a -> (a -> FreeMonad f b) -> FreeMonad f b
   Return :: a -> FreeMonad f a
   Pure' :: f a -> FreeMonad f a

```








[http://okmij.org/ftp/tagless-final/JFP.pdf](http://okmij.org/ftp/tagless-final/JFP.pdf) - tagless final paper. Also some very interesting things related to partial evaluation







[https://oleg.fi/gists/posts/2019-06-26-linear-church-encodings.html](https://oleg.fi/gists/posts/2019-06-26-linear-church-encodings.html) - interesting explanation of bohm-berarducci







[http://okmij.org/ftp/tagless-final/course/lecture.pdf](http://okmij.org/ftp/tagless-final/course/lecture.pdf) - oleg's course







I thought reflection without remorse had some related form of free monad  [http://okmij.org/ftp/Haskell/zseq.pdf](http://okmij.org/ftp/Haskell/zseq.pdf)



