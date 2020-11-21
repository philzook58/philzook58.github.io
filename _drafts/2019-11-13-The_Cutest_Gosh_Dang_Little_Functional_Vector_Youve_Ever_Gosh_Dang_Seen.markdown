---
author: philzook58
comments: true
date: 2019-11-13 20:59:47+00:00
layout: post
link: https://www.philipzucker.com/?p=2434
published: false
slug: The Cutest Gosh Dang Little Functional Vector You've Ever Gosh Dang Seen
title: The Cutest Gosh Dang Little Functional Vector You've Ever Gosh Dang Seen
wordpress_id: 2434
---




I've been thinking about functional programming and vectors for a while now. 





[gist https://gist.github.com/2314628 /]





While many vector packages use the Foreign Function Interface to use low-level arrays for speed, it makes me feel good to use the more normal functional programming facilities and data types to define my vectors.













I was caught by surprise by 







Here's a list of the vector types I'm aware of







Untyped Vectors   







  * Untyped Array 
    * [a]  - Naive lists. Pretty bad on every front except simplicity
    * Vector a   [http://hackage.haskell.org/package/vector](http://hackage.haskell.org/package/vector) [https://www.tweag.io/posts/2017-10-12-vector-package.html](https://www.tweag.io/posts/2017-10-12-vector-package.html)
    * HMatrix - Closest scipy equivalent   [http://hackage.haskell.org/package/hmatrix](http://hackage.haskell.org/package/hmatrix) [http://dis.um.es/~alberto/material/hmatrix.pdf](http://dis.um.es/~alberto/material/hmatrix.pdf)
    * Massiv   - [http://hackage.haskell.org/package/massiv](http://hackage.haskell.org/package/massiv)
    * Repa   
    * Accelerate - A DSL that compiles via LLVM to GPU or CPU [https://hackage.haskell.org/package/accelerate](https://hackage.haskell.org/package/accelerate)
    * [https://hackage.haskell.org/package/dense-linear-algebra](https://hackage.haskell.org/package/dense-linear-algebra)
    * [https://hackage.haskell.org/package/sparse-linear-algebra](https://hackage.haskell.org/package/sparse-linear-algebra)
    * [https://hackage.haskell.org/package/sparse](https://hackage.haskell.org/package/sparse)
    * [https://hackage.haskell.org/package/eigen](https://hackage.haskell.org/package/eigen)
  * Nat Typed
    * Vec 7 a   - Justin Le  [https://blog.jle.im/entry/fixed-length-vector-types-in-haskell.html](https://blog.jle.im/entry/fixed-length-vector-types-in-haskell.html)
    * [http://hackage.haskell.org/package/sized](http://hackage.haskell.org/package/sized)
  * Vector space shape described by type   
  * Index Typed
    * b -> r  
    * Map b r  
    * [(b,r)]  
    * Conal Elliott's thing  [http://hackage.haskell.org/package/vector-space](http://hackage.haskell.org/package/vector-space)
  * Nominal Container
    * Kmett's Linear  [http://hackage.haskell.org/package/linear](http://hackage.haskell.org/package/linear)
    * data V4 a = V4 a a a a
    * https://hackage.haskell.org/package/free-vector-spaces
    * [https://hackage.haskell.org/package/linearmap-category](https://hackage.haskell.org/package/linearmap-category)
  * Duals
    * type Dual f a = f a -> a






I recently realized that there is a more primitive functional vector than I had been considering. 







What does one require to make a vector? Well, you need numbers first. It doesn't make much sense to talk about something being a vector without at least a semiring (addition and multiplication).







If we're talking about functional programming, we also have functions. From these two ingredients we can make the simplest functional vector.












    
    <code>type V2 a = a -> a -> a
    type DV2 a = a -> a -> a 
    exV2 x y = 2*x + 3*y -- represents vector [2,3] 
    exV2' x y = dot (V2 2 3) (V2 x y) 
    convert :: V2 a -> DV2 a 
    convert v x y = dot v (V2 x y)
    m :: Num a => DV2 a -> DV2 a
    m v x y = v (2*x+4*y) (3*x + 7*y) 
    {-
    represents the matrix 
    [[2,4]
     [3,7]]
    or it's transpose?
    -}
    
    smul :: a -> DV2 a -> DV2 a
    smul s v x y = v (s * x) (s * y)
    v2plus :: DV2 a -> DV2 a -> DV2 a
    v2plus v w x y = (v x y) + (w x y)
    
    dot :: DV2 a -> DV2 a -> a
    dot v w = (v 1 0) * (w 1 0) + (v 0 1) * (w 0 1)
    
    type a + b = Either a b
    type a * b = (a,b)
    type Two = Bool
    type One = ()
    type Zero = Void
    type Three = Ordering 
    
    type TV2 = * -> * -> *      -- kind
    type ExTV2 x y =  Two * x + Three * y  
    type SMul2 s v x y = v (s * x) (s * y) 
    type V2Plus f g x y = (f x y) + (g x y)
    type Dot2 
    </code>







The types like V2, V3, V4 in the linear package are pretty primitive. All they require is data type facilities. And then you can define operations by pattern matching out of them.







Typelevel Haskell is a very poor functional programming environment. It doesn't allow higher order type families (yet), but does allow higher order type contructors. 













Dual vector are linear functions on vectors to scalars. You can take the dual of a dual and in some sense you are back where you came form (hence the word dual)







Contravariant and covariant. Meijer and Beckman's Jazz session. [https://channel9.msdn.com/Shows/Going+Deep/E2E-Brian-Beckman-and-Erik-Meijer-CoContravariance-in-Physics-and-Programming-1-of-2](https://channel9.msdn.com/Shows/Going+Deep/E2E-Brian-Beckman-and-Erik-Meijer-CoContravariance-in-Physics-and-Programming-1-of-2)







Phil Freeman explaining before going on to profunctors [https://www.youtube.com/watch?v=OJtGECfksds](https://www.youtube.com/watch?v=OJtGECfksds)







Every arrow you go under, you change from contravariant to covariant.







Duals to all the above.  
classic style stuff needs to be destructued, by the dual style doesn't. This can be seen. There is a rule of thumb that the dual space is easier to work with. It is evocative, related, identical perhaps in the right framework to the rule of thumb that CPS style is the most elegant. I do not understand this point clearly, but I can't help but feel it is correct if only I could find the right way of phrasing it.  
newtype Dual f a = Dual (f a -> a)newtype Dual v a = Dual (v -> a)  
A more primitive style. Using container types brings in excess waste. We need type definition facilities, and we need to pattern match out of the data type ultaimtely to do anything with it. Data types do nothing.Instead we can build a vector type out of functions and numerical operations. This type is very similar to the sgnature of the constructor V2 :: a -> a -> V2 a without the V2 in there.  
  








Levels 0 - 2Level 0 is the indexing function. You can convert any reprsentable functor to this form via the (!!) operator.a -> rLevel 1 is the dot product operator. Gien a vector in functor form, tae the do product with it. It's evocative of partially applied fmap.(a -> r) -> rLevel 2 is((a -> r) -> r) -> r  
Level 2 is forall f. (v a -> f a) -- impossible. Can only give 0.forall f. (Additive f) => (v a -> f a) -> f a -- kron and traceforall f. ((v a -> f a) -> f a) -> f aMixing levels with the parametric vector idea. Maybe we can actually do a yoneda lemma then? Double negation translation.







If you have another representation to add to this list above, I'd love to hear from you.  














WHat is a vector?  
It is a column of numbers. In other words an n-tuple of numbers  
It is components. It is a function from which component you want to a number  
type V = XYZ -> Double







Covectors are linear functionals of vectors. They take a vector and return a number  

type CoV = V -> Double  

s.t.   

f (v + w) = (f v) + (f w)  

This equality is not expressible in Haskell if we use functions to represent our vectors







CoV ~ V  

to f = \x -> f 







type CoCoV = CoV -> Double  

CoCoV ~ V







There is a very big difference between the push and pull







Level-0 vectors are things like Vector Double, [Double], V3 Double  

They can push numbers  

Level-1 is (a -> Double)   

They pull indices. These correspond to partially applied indexing functions  

from v = \a -> let i = fromEnum a in v !! i  

to f   = [f X, f Y, f Z]  

Level 2  

These correspond to partially applied dot product functions / iteration sweep reducing functions  

(a -> DOuble) -> Double  

to02 v = \f -> fold (\acc x -> acc + f x) v   

from02 f =   

Level-3 is "naturally" equivalent to Level-1 







Infinite Vectors  

[Double]  

Level-1  

Int ->  Double  

They are still interconvertible







vector equality  

f ~ g  is not generally possible







Level-2  

(Int -> Double) -> Double -- if this returns, it can actually only probe a finite prelude  

So in fact this HAS to be a (finitely) sparse vector.  

Now a natural thing to do might be to terminate probing based on what we see.  

This won't be linear anymore though. There could be a NUTS big coefficient later on  

even with some weirdo form of Double based equality







This has a form similar to impossible functionals







(Int -> Double) -> Double equality testing is probably possible







Type level haskell (And the type level of most languages) is a pretty raw functional programming environment. You run into walls all the time when you're trying to do things. You only kind of sort of have higher order functions. Mostly you don't. This may change (see Csongor Kiss's stuff)



