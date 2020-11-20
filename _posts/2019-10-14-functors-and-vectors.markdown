---
author: philzook58
comments: true
date: 2019-10-14 20:10:37+00:00
layout: post
link: https://www.philipzucker.com/functors-and-vectors/
slug: functors-and-vectors
title: Functors, Vectors, and Quantum Circuits
wordpress_id: 2405
categories:
- Haskell
tags:
- categorytheory
- haskell
- vectors
---




Vectors are dang useful things, and any energy you put into them seems to pay off massive dividends.







Vectors and Linear Algebra are useful for:







  * 2D, 3D, 4D geometry stuff. Computer graphics, physics etc. 
  * Least Squares Fitting
  * Solving discretized PDEs
  * Quantum Mechanics
  * Analysis of Linear Dynamical Systems
  * Probabilistic Transition Matrices






There are certain analogies between Haskell Functors and Vectors that corresponds to a style of computational vector mathematics that I think is pretty cool and don't see talked about much.







Due to the expressivity of its type system, Haskell has a first class notion of container that many other languages don't. In particular, I'm referring to the fact that Haskell has higher kinded types `* -> *` (types parametrized on other types) that you can refer to directly without filling them first. Examples in the standard library include `Maybe`, `[]`, `Identity`, `Const b`, and `Either b`. Much more vector-y feeling examples can be found in Kmett's linear package `V0`, `V1`, `V2`, `V3`, `V4`. For example, the 4 dimensional vector type `V4`






    
    <code>data V4 a = V4 a a a a</code>







This really isn't such a strange, esoteric thing as it may appear. You wouldn't blink an eye at the type






    
    <code>struct V4 {
       double x, y, z, w;
    }</code>







in some other language. What makes Haskell special is how compositional and generic it is.  We can build thousand element structs with ease via composition. What we have here is an alternative to the paradigm of computational vectors ~ arrays. Instead we have computational vectors ~ structs. In principle, I see no reason why this couldn't be as fast as arrays, although with current compiler expectations it probably isn't.







Monoidal categories are a mathematical structure that models this analogy well. It has been designed by mathematicians for aesthetic elegance, and it seems plausible that following its example leads us to interesting, useful, and pleasant vector combinators. And I personally find something that tickles me about category theory.







So to get started, let's talk a bit about functors.







## The Algebra of Functors 







Functors in Haskell are a typeclass for containers. They allow you to map functions over all the items in the container. They are related to the categorical notion of functor, which is a mapping between categories.






    
    <code>type Container = * -> * -- Note: This is actually a kind signature.
    -- Kinds and types are the same thing in Haskell.</code>







You can lift the [product and sum of types](http://www.philipzucker.com/linear-algebra-of-types) to the product and sum of Functors which you may find in [Data.Functor.Product](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Functor-Product.html) and [Data.Functor.Sum](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Functor-Sum.html).  This is analogous to the lifting of ordinary addition and multiplication to the addition and multiplication of polynomials, which are kind of like numbers with a "hole".






    
    <code>newtype Product f g a = Pair (f a , g a)
    newtype Sum f g a = Sum (Either (f a) (g a))</code>







Functors also compose. A container of containers of `a` is still a container of `a`. We can form composite containers by using the Compose newtype wrapper.






    
    <code>newtype Compose f g a = Compose (f (g a))</code>







When you use this Compose newtype, instead of having to address the individual elements by using `fmap` twice, a single application of `fmap` will teleport you through both layers of the container.







`Product`, `Sum`, and `Compose` are all binary operator on functors. The type constructor has kind 






    
    <code>{- Enter into ghci -}
    :kind Compose ==> (* -> *) -> (* -> *) -> (* -> *)
    :kind Product ==> (* -> *) -> (* -> *) -> (* -> *)
    :kind Sum ==> (* -> *) -> (* -> *) -> (* -> *)</code>







Some important other functors from the algebra of types perspective are  `Const Void a`, `Const () a`, and `Identity a`. These are identity elements for `Sum`, `Product`, and `Compose` respectively.







You can define mappings between containers that don't depend on the specifics of their contents. These mappings can only rearrange, copy and forget items of their contained type. This can be enforced at the type level by the polymorphic type signature






    
    <code>type f ~> g = forall a. f a -> g a</code>







These mappings correspond in categorical terminology to [natural transformations](https://bartoszmilewski.com/2015/04/07/natural-transformations/) between the functors `f` and `g`. There is a category where objects are Functors and morphisms are natural transformations. `Sum`, `Product`, and `Compose` all obeys the laws necessary to be a monoidal product on this category.







How the lifting of functions works for `Compose` is kind of neat.






    
    <code>mon_prod :: Functor f' => (f ~> f') -> (g ~> g') -> (Compose f g ~> Compose f' g')
    mon_prod ntf ntg (Compose fg) = Compose (fmap ntg (ntf fg))
    -- or equvalently Compose (ntf (fmap ntg fg)) with a (Functor f) typeclass requirement.</code>







Because the natural transformations require polymorphic types, when you apply `ntf` to `fg` the polymorphic variable `a` in the type of `ntf` restricts to `a ~ g a'`.







`Product` and `Sum` have a straight forward notion of commutativity ( `(a,b)` is isomorphic to `(b,a)`) . `Compose` is more subtle. `sequenceA` from the Traversable typeclass can swap the ordering of composition. `sequenceA . sequenceA` may or may not be the identity depending on the functors in question, so it has some flavor of a braiding operation. This is an interesting post on that topic [https://parametricity.com/posts/2015-07-18-braids.html](https://parametricity.com/posts/2015-07-18-braids.html)







Combinators of these sorts are used arise in at least the following contexts







  * [Data types a la carte](http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf) - A systematic way of building extensible data types
  * [GHC Generics ](https://www.stackbuilders.com/tutorials/haskell/generics/)- A system for building generic functions that operate on data types that can be described with sums, products, recursion, and holes.
  * In and around the Lens ecosystem 






Also see the interesting post by Russell O'Connor and functor oriented programming [http://r6.ca/blog/20171010T001746Z.html](http://r6.ca/blog/20171010T001746Z.html). I think the above is part of that to which he is referring.







### Vector Spaces as Shape







Vector spaces are made of two parts, the shape (dimension) of the vector space and the scalar.







Just as a type of kind `* -> *` can be thought of as a container modulo it's held type, it can also be a vector modulo its held scalar type. The higher kinded type for vector gives an explicit slot to place the scalar type.






    
    <code>type Vect = * -> *</code>







The standard Haskell typeclass hierarchy gives you some of the natural operations on vectors if you so choose to abuse it in that way.







  * Functor ~> Scalar Multiplication: `smul s = fmap (* s)`
  * Applicative ~> Vector Addition:  vadd x y = (+) <$> x  <*> y 
  * Traversable ~> Tranposition. `sequenceA` has the type of transposition and works correctly for the linear style containers like V4.






The[ linear library](http://hackage.haskell.org/package/linear-1.20.9/docs/Linear-Vector.html) does use `Functor` for scalar multiplication, but defines a special typeclass for addition, `Additive`. I think this is largely for the purposes for bringing `Map` like vectors into the fold, but I'm not sure.







Once we've got the basics down of addition and scalar multiplication, the next thing I want is operations for combining vector spaces. Two important ones are the Kronecker product and direct sum. In terms of indices, the Kronecker product is a space that is indexed by the cartesian product `(,)` of its input space indices and the direct sum is a space indexed by the `Either` of its input space indices. Both are very useful constructs. I use the Kronecker product all the time when I want to work on 2D or 3D grids for example. If you'll excuse my python, here is a toy 2-D finite difference Laplace equation example. We can lift the 1D second derivative matrix $latex K = \partial_x^2 $ using the kronecker product $latex K2 = K \otimes I + I \otimes K$. The direct sum is useful as a notion of stacking matrices.






    
    <code>import numpy as np
    N = 10 # We're making a 10x10 grid
    row = np.zeros(N)
    row[0] = -2
    row[1] = 1
    K = np.toeplitz(row,row) #toeplitz makes constant diagonal matrices
    I = np.eye(N) #identity matrix
    K2 = np.kron(K,I) + np.kron(I,K)</code>







The following is perhaps the most important point of the entire post.






    
    <code>type Kron = Compose
    type DSum = Product</code>







`Compose` of vector functors gives the Kronecker product, and `Product` gives the direct sum (this can be confusing but its right. Remember, the sum in direct sum refers to the _indices_).







We can form the Kronecker product of vectors given a Functor constraint. 






    
    <code>kron :: (Num a, Functor f, Functor g) => f a -> g a -> Kron f g a
    kron f g = Compose $ fmap (\s1 -> fmap (\s2 -> s1 * s2) g) f
    
    dsum :: f a -> g a -> DSum f g a
    dsum f g = Pair f g</code>







Notice we have two distinct but related things called kron: `Kron` and `kron`. One operates on vectors _spaces_ and the other operates on vector _values_.







Building vector spaces out of small combinators like V2, V4, DSum, Kron is interesting for a number of reasons.







  * It is well typed. Similar to Nat indexed vectors, the types specify the size of the vector space. We can easily describe vector spaced as powers of 2 as `V16 =  Kron V2 (Kron V2 (Kron V2 (Kron V2 V1)))`, similarly in terms of its prime factors, or we can do a binary expansion (least significant bit first) `V5 = DSum V1 (Kron V2 (DSum V0 (Kron V2 V1)))` or other things. We do it without going into quasi-dependently typed land or GADTs.
  * It often has better semantic meaning. It is nice to say Measurements, or XPosition or something rather than just denote the size of a vector space in terms of a nat. It is better to say a vector space is the Kron of two meaningful vector spaces than to just say it is a space of size m*n. I find it pleasant to think of the naturals as a free Semiring rather than as the Peano Naturals and I like the size of my vector space defined similarly.
  * Interesting opportunities for parallelism. See Conal Elliott's paper on scans and FFT: [http://conal.net/papers/generic-parallel-functional/](http://conal.net/papers/generic-parallel-functional/)






#### What do linear operators look like?







In the Vectors as shape methodology, Vectors look very much like Functors.







I have been tempted to lift the natural transformation type above to the following for linear operators.






    
    <code>type LinOp f g = forall a. (Num a) => f a -> g a</code>







In a sense this works, we could implement `kron` because many of the container type (`V1`, `V2`, `V3`, etc) in the linear package implement Num. However, choosing Num is a problem. Why not Fractional? Why not Floating? Sometimes we want those. Why not just specifically Double?







We don't really want to lock away the scalar in a higher rank polymorphic type. We want to ensure that everyone is working in the same scalar type before allowing things to proceed.






    
    <code>type LinOp f g a = f a -> g a</code>







Note also that this type does not constrain us to linearity. Can we form the Kronecker product of linear operators? Yes, but I'm not in love with it. This is not nearly so beautiful as the little natural transformation dance.






    
    <code>kron''' :: (Applicative f', Applicative g', Traversable f, Traversable g') =>
        (f a -> f' a) -> (g a -> g' a) -> (Kron f g a -> Kron f' g' a)
    kron'' lf lg (Compose fga) = Compose $ sequenceA $ (fmap lf) $ sequenceA $ (fmap lg fga)</code>







This was a nice little head scratcher for me. Follow the types, my friend! I find this particularly true for uses of `sequenceA`. I find that if I want the containers swapped in ordering. In that situation sequenceA is usually the right call. It could be called `transpose`.







Giving the vector direct access to the scalar feels a bit off to me. I feel like it doesn't leave enough "room" for compositionally. However, there is another possibility for a definition of morphisms could be that I think is rather elegant.






    
    <code>type LinOp1 f g a = forall k. Additive k => Kron f k a -> Kron g k a</code>







Does this form actually enforce linearity? You may still rearrange objects. Great. You can also now add and scalar multiply them with the `Additive k` constraint. We also expose the scalar, so it can be enforced to be consistent. 







One other interesting thing to note is that these forms allow nonlinear operations. `fmap`, `liftU2` and `liftI2` are powerful operations, but I think if we restricted `Additive` to just a correctly implemented scalar multiply and vector addition operation, and zero, we'd be good. 






    
    <code>class Additive' f where
      smul :: Num a => a -> f a -> f a
      vadd :: Num a => f a -> f a -> f a
      zero :: Num a => f a</code>







We can recover the previous form by instantiation `k` to `V1`. `V1`, the 1-d vector space, is almost a scalar and can play the scalars role in many situations. `V1` is the unit object with respect to the monoidal product `Kron`.







There seems to be a missing instance to Additive that is useful. There is probably a good reason it isn't there, but I need it.






    
    <code>instance (Additive g, Additive f) => Additive (Compose f g) where
        (Compose v) ^+^ (Compose w) = Compose (liftU2 (^+^) v w)
        zero = zero
        liftU2 f (Compose x) (Compose y) = Compose $ liftU2 (liftU2 f) x y
        liftI2 f (Compose x) (Compose y) = Compose $ liftI2 (liftI2 f) x y</code>







## Monoidal Categories







The above analogy can be put into mathematical terms by noting that both vectors and functor are monoidal categories. I talked a quite a bit about monoidal categories in a previous post [http://www.philipzucker.com/a-touch-of-topological-computation-3-categorical-interlude/](http://www.philipzucker.com/a-touch-of-topological-computation-3-categorical-interlude/) .







Categories are the combo of a collection of objects and arrows between the objects. The arrows can compose as long as the head of one is on the same object as the tail of the other. On every object, there is always an identity arrow, which when composed will do nothing.







We need a little extra spice to turn categories into monoidal categories. One way of thinking about it is that monoidal categories have ordinary category composition and some kind of horizontal composition, putting things side to side. Ordinary composition is often doing something kind of sequentially, applying a sequence of functions, or a sequence of matrices. The horizontal composition is often something parallel feeling, somehow applying the two arrows separately to separate pieces of the system.







### **Why are they called Monoidal?**







There is funny game category people play where they want to lift ideas from other fields and replace the bits and pieces in such a way that the entire thing is defined in terms of categorical terminology. This is one such example.







A monoid is a binary operations that is associative and has an identity.







Sometimes people are more familiar with the concept of a group. If not, ignore the next sentence. Monoids are like groups without requiring an inverse.







Numbers are seperately monoids under both addition, multiplication and minimization (and more), all of which are associative operations with identity (0, 1, and infinity respectively).







Exponentiation is a binary operation that is not a monoid, as it isn't associative. 







The Monoid typeclass in Haskell demonstrates this [http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Monoid.html](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Monoid.html)






    
    <code>class Semigroup a => Monoid a where
            mempty  :: a
            mappend :: a -> a -> a</code>







A common example of a monoid is list, where `mempty` is the empty list and `mappend` appends the lists.







There are different set-like intuitions for categories. One is that the objects in the category are big opaque sets. This is the case for Hask, Rel and Vect. 







A different intuitiion is that the category itself is like a set, and the objects are the elements of that set. There just so happens to be some extra structure knocking around in there: the morphisms. This is the often more the feel for the examples of preorders or graphs. The word "monoidal" means that they we a binary operation on the objects. But in the category theory aesthetic, you also need that binary operation to "play nice" with the morphisms that are hanging around too. 







Functors are the first thing that has something like this. It has other properties that come along for the ride. A Functor is a map that takes objects to objects and arrows to arrows in a nice way. A binary functor takes two objects to and object, and two arrows to one arrow in a way that plays nice (commutes) with arrow composition.







### **String diagrams**







[String diagrams](https://en.wikipedia.org/wiki/String_diagram) are a graphical notation for monoidal categories. Agin I discussed this more [here](http://www.philipzucker.com/a-touch-of-topological-computation-3-categorical-interlude/).







Morphisms are denoted by boxes. Regular composition is shown by plugging arrows together vertically. Monoidal product is denoted by putting the arrows side to side.







When I was even trying to describe what a monoidal category was, I was already using language evocative of string diagrams.







You can see string diagrams in the [documentation](https://en.wikibooks.org/wiki/Haskell/Understanding_arrows) for the Arrow library. Many diagrams that people use in various fields can be formalized as the string diagrams for some monoidal category. This is big chunk of Applied Category Theory.







This is the connection to quantum circuits, which are after all a graphical notation for very Kroneckery linear operations.






    
    <code>type Qubit = V2
    type C = Complex Double
    
    assoc :: Functor f => (Kron (Kron f g) h) ~> (Kron f (Kron g h))
    assoc = Compose . (fmap Compose) . getCompose . getCompose
    
    assoc' :: Functor f =>  (Kron f (Kron g h)) ~> (Kron (Kron f g) h)
    assoc' (Compose x)  = Compose $ Compose $ (fmap getCompose x) 
    
    kron'' :: (Additive f, Additive g, Additive k, Additive f', Additive g') => 
      LinOp1 f f' a -> LinOp1 g g' a -> Kron (Kron f g) k a -> Kron (Kron f' g') k a
    kron'' lf lg fgk = let v = (assoc fgk) in assoc' (Compose $ fmap lg $ getCompose (lf v))
    
    sigx' :: LinOp1 Qubit Qubit C 
    sigx' (Compose (V2 up down)) = Compose $ V2 down up  
    
    sigz' :: LinOp1 Qubit Qubit C 
    sigz' (Compose (V2 up down)) = Compose  $ V2 up ((-1) *^ down) 
    
    sigy' :: LinOp1 Qubit Qubit C 
    sigy' (Compose (V2 up down)) = Compose $ V2 ((-i) *^ down) (i *^ up) where i = 0 :+ 1
    
    swap' :: (Traversable f, Applicative g) => LinOp1 (Kron f g) (Kron g f) a 
    swap' (Compose (Compose fgk)) = Compose $ Compose $ sequenceA fgk 
    
    cnot :: LinOp1 (Kron Qubit Qubit) (Kron Qubit Qubit) a 
    cnot (Compose (Compose (V2 (V2 up1 down1) v))) = Compose $ Compose $ V2 (V2 down1 up1) v
    
    phase :: Double -> LinOp1 Qubit Qubit C
    phase phi (Compose (V2 up down)) = Compose $ V2 up ((cis phi) *^ down)
    
    lefting :: (Additive f, Additive k, Additive g) => LinOp1 f g a -> LinOp1 (Kron f k) (Kron g k) a
    lefting l = kron'' l id -- Qubit.assoc' . l . Qubit.assoc 
    
    righting :: (Additive k, Additive f, Additive g) => LinOp1 f g a -> LinOp1 (Kron k f) (Kron k g) a
    righting l = kron'' id l -- (Compose (Compose fkk)) = Compose $ Compose $ (fmap (getCompose . l . Compose) fkk)
    
    example :: LinOp1 (Kron Qubit Qubit) (Kron Qubit Qubit) C 
    example = (lefting sigx') . (lefting sigy') . (righting sigz') . swap'
    </code>





![](http://philzucker2.nfshost.com/wp-content/uploads/2019/10/My-Drawing.sketchpad-546x1024.png)example circuit





There is an annoying amount of stupid repetitive book keeping with the associative structure of Kron. This can largely be avoided hopefully with `coerce`, but I'm not sure. I was having trouble with roles when doing it generically.







### Bit and Bobbles







  * Woof. This post was more draining to write than I expected. I think there is still a lot left to say. Sorry about the editing everyone! Bits and pieces of this post are scattered in this [repo](https://github.com/philzook58/fib-anyon)
  * How would you go about this in other languages? C, Rust, OCaml, C++, Agda
  * The discussion of Vect = * -> * is useful for discussion of 2-Vect, coming up next. What if we make vectors of Vect? Wacky shit.
  * Metrics and Duals vectors. `type Dual f a = f a -> a`. `type Dual1 f a = forall k. Additive k => Kron f k a -> k a`
  * Adjunction diagrams have cups and caps. Since we have been using representable functors, they actually have a right adjunction that is tupling with the vector space index type. This gives us something that almost feels like a metric but a weirdly constrained metric.
  * LinOp1 form is yoneda? CPS? Universally quantified k is evocative of `forall c. (a -> c) -> (b -> c)`






### References







  * I got the LinOp1 construction from Kitaev [https://arxiv.org/abs/cond-mat/0506438](https://arxiv.org/abs/cond-mat/0506438) Presumably there are better references as this is not the thrust of this massive article.
  * Jeremy Gibbons Naperian Functor - Very interesting and related to this post. [https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf)
  * Bartosz Milewski - String Diagrams  [https://www.youtube.com/watch?v=eOdBTqY3-Og](https://www.youtube.com/watch?v=eOdBTqY3-Og)
  * Huenen and Vicary - [http://www.cs.ox.ac.uk/people/jamie.vicary/IntroductionToCategoricalQuantumMechanics.pdf](http://www.cs.ox.ac.uk/people/jamie.vicary/IntroductionToCategoricalQuantumMechanics.pdf) Intro to categorical quantum mechanics.
  * [http://hackage.haskell.org/package/linear](http://hackage.haskell.org/package/linear) Kmett's linear package
  * [https://graphicallinearalgebra.net/](https://graphicallinearalgebra.net/) - Graphical Linear Algebra
  * [http://www.philipzucker.com/resources-string-diagrams-adjunctions-kan-extensions/](http://www.philipzucker.com/resources-string-diagrams-adjunctions-kan-extensions/)
  * [http://www.philipzucker.com/functor-vector-part-2-function-vectors/](http://www.philipzucker.com/functor-vector-part-2-function-vectors/)
  * [http://www.philipzucker.com/functor-vector-part-1-functors-basis/](http://www.philipzucker.com/functor-vector-part-1-functors-basis/)
  * Baez and Stay. Rosetta Stone. A classic [http://math.ucr.edu/home/baez/rosetta.pdf](http://math.ucr.edu/home/baez/rosetta.pdf)






## Appendix







### Representable/Naperian Functors







Containers that are basically big product types are also known as representable, Naperian, or logarithmic. Representable places emphasis on the isomorphism between such a container type and the type `(->) i` which by the algebra of types correspond is isomorphic to $latex a^i$ (i copies of a). They are called Naperian/Logarithmic because there is a relationship similar to exponentiation between the index type `a` and the container type `f`. If you take the `Product f g`, this container is indexed by (a + b) = `Either a b`.  `Compose f g` is indexed by the product `(a,b)`. `(f r) ~ r^a` The arrow type is written as an exponential `b^a` because if you have finite enumerable types `a` and `b`, that is the number of possible tabulations available for `f`. The Sum of two representable functors is no longer representable. Regular logarithms of sums Log(f + g) do not have good identities associated with them.







See Gibbons article. There is a good argument to be made that representable functors are a good match for vectors/well typed tensor programming.







But note that there is a reasonable interpretation for container types with sum types in them. These can be thought of as subspaces, different bases, or as choices of sparsity patterns. When you define addition, you'll need to say how these subspaces reconcile with each other.  
-- two bases at 45 degrees to each other.






    
    <code>data V2_45 a = XY a a | XY' a a
    data Maybe a = Just a | Notinhg -- a 1-d vectro space with a special marker for the zero vector.
    data Maybe2 a = Just2 a a | Nothing2 -- a 2d vector space with special zero marker</code>








https://bartoszmilewski.com/2015/07/29/representable-functors/














### **Monoidal Products on Hask**







Hask is a name for the category that has objects as Haskell types and morphisms as Haskell functions. 







Note that it's a curious mixing of type/value layers of Haskell.  The objects are types whereas the function morphisms are Haskell values. Composition is given by `(.)` and the identity morphisms are given by `id`. 







For Haskell, you can compose functions, but you can also smash functions together side by side. These combinators are held in [Control.Arrow](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Arrow.html). 







You can smash together types with tuple `(,)` or with `Either`. Both of these are binary operators on types. The corresponding mapping on morphisms are given by






    
    <code>(***) :: a b c -> a b' c' -> a (b, b') (c, c') 
    (+++) :: a b c -> a b' c' -> a (Either b b') (Either c c') </code>







These are binary operators on morphisms that play nice with the composition structure of Haskell.







### Monoidal Combinators of Functors







A monoidal category also has unit objects. This is given by the Identity functor






    
    <code>rightUnitor :: Functor f => Compose f Identity a -> f a
    rightUnitor (Compose f) = fmap runIdentity f
    
    rightUnitor' :: f ~> Compose f Identity
    rightUnitor' = Compose . fmap Identity
    
    leftUnitor' :: f ~> Compose Identity f
    leftUnitor' = Compose . Identity
    
    leftUnitor :: Identity *** f ~> f
    leftUnitor = runIdentity . getCompose</code>







There is also a sense of associativity. It is just newtype rearrangement, so it can also be achieved with a `coerce` (although not polymorphically?).






    
    <code>assoc :: Functor f => ((f *** g) *** h) ~> (f *** (g *** h))
    assoc = Compose . (fmap Compose) . getCompose . getCompose
    
    assoc' :: Functor f => (f *** (g *** h)) ~> ((f *** g) *** h)
    assoc' (Compose x) = Compose $ Compose $ (fmap getCompose x)</code>







Similarly, we can define a monoidal category structure using Product or Sum instead of Compose. 







These are all actually just newtype rearrangement, so they should all just be instances of `coerce`, but I couldn't get the roles to go through generically?



