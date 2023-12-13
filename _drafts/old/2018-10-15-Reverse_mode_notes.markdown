---
author: philzook58
comments: true
date: 2018-10-15 00:24:23+00:00
layout: post
link: https://www.philipzucker.com/?p=1356
published: false
slug: Reverse mode notes
title: Reverse mode notes
wordpress_id: 1356
---

Even then not quite though. The units don't work out. The vector dx has units of meters let's say and some function f has units of Celsius, then $latex \frac{\partial f}{\partial x}$ has units of Celsius/meters. This is an actual problem in less clearcut situtations. It is really a CoVector.

I had the following gorgeous post by Christoper Olah  [http://colah.github.io/posts/2015-09-NN-Types-FP/](http://colah.github.io/posts/2015-09-NN-Types-FP/) as inspiration .

One may also want to destroy sharing intentionally. Checkpointing is a technique that you use when you don't want to store all the intermediate calculations in memory. It is not clear that an optimizing compiler might find common subexpressions and ruin any checkpointing structure we build.

https://www.twanvl.nl/blog/haskell/cps-functional-references

Polymorphism is a powerful for correctness. Because of the opacity of these pointers, you are highly restricted in what you can do in a function (in a good way). There is a mechanical way to derive theorems from the polymorphic type. This method is known as Free Theorems, but more informally I think of it as the "Principle of What the Fuck Else Could You Do" (PWTFECYD).





The simplest versions of this are the identity function (id :: forall a. a -> a) or simple tuple functions like swap :: (a,b) -> (b,a)

A more advanced example is (forall b. Functor f => (a -> b) -> f b). This function HAS to be partially applied fmap. So there is secretly some object (x :: f a) being held inside that function. You can get it out by handing the function id.

The lens trick is a similar deal although at the next level of craziness. Polymorphism . f is a container type that you can reach under with fmap, but you can't do anything else. (a -> f b) -> (s -> f t).



Isos are already good AD differentiators. They are basically some kind of permutation function.

Do Prisms have an interpretation in automatic differentiation? I do not know of one.



Idea 2. Polymorphic Types are opaque pointers

Pointers in C give you the ability to perform arithmetic on them. You can also dereference them. A polymorphic type does not allow dereferencing or pointer arithmetic. So the only thing you can do is shuffle, copy, and drop the pointers.

Idea 3. Functions are closures. They hold data. There is a notion of  holding data in a Wengert Tape in the literature. You need to store what you did so you can back traverse through it somehow

Idea 4. Sharing

Haskell is a high level language and does not always make it the easiest to have a good understanding of what memory will do what and when. One _can_ know such things, it just isn't front and center and is an intermediate or advanced topic.

I by no means am an expert



Comment 6. Sum is the Dual of Split

I got this from Conal Elliott's paper. And he references PearlMutter and ...

In typical languages you may freely make use of an object multiple times. This is extremely useful most of the time. There are applications where it is actually better to have to explicitly get new references. This is not even necessarily a copy operation.

The functional representation

We could embed splitting as an explicit Jacobian matrix.

Comment 7. Actually using this point free form is abysmal.

Maybe with more work it could be better. See Conal Elliott's compiling to categories. Even lightweight compiling to categories like my previous post may help.

Check out my example here. It is inscrutable. It is only a three layer neural network (I hope).

Another option is to use the monad? It's not quite a monad. Too many type parameters. Too many restictions on application. I am cloudy on this point.





Questions:

Contravaraince and Covariance.

Pushing things into callbacks. CPS transforming.

Prisms

Higher Order Reverse Mode? The Hessian at least. The Hessian is SO useful.





Using the stock lens library:

Combinators of lens will probably be okay

Iso are good to go as is.

Lens are usually projective, so they can be lifted into a Differentiation Lens by supplying the setter function with zero rather than the original value.

It is bad that regular lens and AD lens intermingle, however a newtype wrapper would be some noise that I'm not sure I'd appreciate.



Prisms and Traversals are not obviously useful to me as AD. (Forward mode? No obviously. Inverse function? Not obviously. )

A common erroris to forget that AD Lens compose backwards, just like regular lens. There is an imperative feel. Take the sine, then square, yada yada

The pointfree arrow style that you need is kind of fun but also a nightmare. Hence the usefulness of Conal Elliott's compiling to categories.

One thing I'd love is to get explicit Hessians. Or invertible Hessians. You can kind of get that via a conjugate gradient method

Some Examples of AD lens:

Using accelerate. A Pain in the butt to install


brew install llvm@5 --with-shared-libs




export PATH="/usr/local/opt/llvm@5/bin:$PATH




I also ln -s a dylib so that it had a 5 in it




    
    {-# LANGUAGE RankNTypes, LambdaCase #-}
    
    -- import Data.Functor.Identity
    -- import Data.Functor.Const.Compat
    import Control.Lens
    
    data V2 a = V2 a a
    
    type RD a b = a -> (b, b -> a)
    {-
    type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
    type Lens' s a = Lens s s a a
    -}
    -- id is a Lens
    id' :: Lens' a a
    id' = id
    {-
    fst' :: Lens' (a,b) a
    fst' = _1
    
    snd' :: Lens' (a,b) b
    snd' = _2
    
    _2 and _1 are linear functions
    
    -}
    {-
    set :: Lens' s a -> a -> s -> s
    set l b = runIdentity . (l (\_ -> Identity b))
     
    
    view :: Lens' s a -> s -> a
    view l = getConst (l Const)
    -}  
    
    --mul :: Number a => Lens' (a,a) a
    --mul = 
    
    -- add :: Number a => Lens' (a,a) a
    -- add f (x,y) = fmap  
    
    add' :: Num a => Lens' (a,a) a 
    add' = lens (\(x,y) -> x + y) (\case (x,y) -> \d -> (d,d))
    
    sub' :: Num a => Lens' (a,a) a 
    sub' = lens (\(x,y) -> x - y) (\case (x,y) -> \d -> (d,-d))
    
    
    mul :: Num a => Lens' (a,a) a 
    mul = lens (\(x,y) -> x * y) (\case (x,y) -> \d -> (d*y,d*x))
    
    recip' :: Fractional a => Lens' a a 
    recip' = lens recip (\x -> \dx -> -dx / (x*x) )
    
    div' :: Fractional a => Lens' (a,a) a 
    div' = lens (\(x,y) -> x / y) (\(x,y) -> \d -> (d/y,-x*d/(y * y)))
    
    
    {-
    mul' :: Num a => Lens' (V2 a) a 
    mul' = lens (\(V2 x y) -> x * y) (\case (V2 x y) -> \d -> (V2 y x))
    -}
    
    dup :: Num a => Lens' a (a,a)
    dup = lens (\x -> (x,x)) (\_ -> (\case (y,z) -> y + z))
    {-
    dup' :: Num a => Lens' a (V2 a)
    dup' = lens (\x -> V2 x x) (\_ -> (\case (V2 y z) -> y + z))
    
    add'' :: Num a => Lens' (V2 a) a 
    add'' = lens (\ (V2 x y) -> x + y) (\case (V2 x y) -> \_ -> V2 1 1)
    -}
    square :: Num a => Lens' a a
    square = dup . mul
    
    --square' :: Num a => Lens' a a
    --square' = dup' . mul'
    
    par :: Lens' a b -> Lens' c d -> Lens' (a,c) (b,d)
    par l1 l2 =  lens (\(x,y) -> (g1 x, g2 y)) (\(x,y)-> \(a,b) -> (s1 a x, s2 b y)) where
                    g1 = view l1
                    g2 = view l2
                    s1 = set l1
                    s2 = set l2 
    
    fourve :: Num a => Lens' a a
    fourve = square . square -- Isn't working... 
    -- evaluation is working
    -- Is the whole idea wrong?
    -- Yes. Setter composition does not work like derivatives
    -- you do sequential getting from the intermiedate types... that is right
    -- Then you 
    -- Wait isn't this right?
    --f s b =  
    
    
    threeve :: Num a => Lens' a a
    threeve = dup . ((par square id) :: Num a => Lens' (a,a) (a,a)) . mul
    
    -- Sort of the nondestructive version of mult. Like a quantum circuit or something
    onemore :: Num a => Lens' (a,a) (a,a)
    onemore = lens (\(x,xn) -> (x, x*xn)) (\(x,xn)  -> \(d1,d2) -> (d1 + d2*xn, d2*x) )
    
    -- These are probably already in lens (more specifically Isos)
    -- The rule of thumb may be actual lens cannot be used since we need to zero pad
    -- projections rather that maintain data
    -- But Isos are fine
    assoc :: Lens' ((a,b),c) (a,(b,c))
    assoc = lens (\((a,b),c) -> (a,(b,c))) (\((a,b),c) -> \(da,(db,dc)) -> ((da,db),dc))
    
    -- swapped from Lens should work
    swap ::  Lens' (a,b) (b,a)
    swap = lens (\(a,b) -> (b,a)) (\(a,b) -> \(db,da) -> (da, db))
    -- can also be done using assoc
    -- onemore' = (fst' . dup) . assoc . mul
    snd' :: Num a => Lens' (a,a) a
    snd' = lens (\(x,y) -> y) (\(x,y) -> \dy -> (0,dy) )
    
    fst' :: Num a => Lens' (a,a) a
    fst' = lens (\(x,y) -> x) (\(x,y) -> \dx -> (dx,0) )
    
    
    pow :: Num a => Int -> Lens' a a
    pow n = dup . (foldr (.) id (replicate (n-1) onemore)) . snd'
    
    sin' :: Floating a => Lens' a a
    sin' = lens sin (\x -> \dx -> dx * (cos x))
    
    cos' :: Floating a => Lens' a a
    cos' = lens cos (\x -> \dx -> -dx * (sin x))
    
    cmul :: Num a => a -> Lens' a a
    cmul c = lens (* c) (\x -> \dx -> c * dx)
    
    exp' :: Floating a => Lens' a a
    exp' = lens exp (\x -> \dx -> dx * (exp x))
    
    
    
    -- Can do less well typed version using lists
    {-
    headdup :: Num a => Lens' [a] [a]
    headdup = lens (\x -> (head x) : x) (\_ ->(a:b:xs) -> (a + b) : xs)
    -}
    {-
    listsum :: Num a => Lens' [a] [a]
    listsum = lens (\x -> sum x) (\x -> \_ -> fmap (const 1) x)
    -}
    grad :: Num a => Lens' b a -> b -> b 
    grad f = set f 1  
    
    {-
    -- Vectorized Operations
    sum :: Number a => Lens' (Vector a) a
    fill :: Number a => Int -> Lens' a (Vector a)
    add :: Lens (Vector a, Vector a) (Vector a)
    kron :: Lens (Vector a, Vector a) (Vector a)
    elemmul :: Lens (Vector a, Vector a) (Vector a)
    det :: Lens (Matrix a) (Matrix a)
    dot :: Lens (Matrix a, Matrix a) (Matrix a)
    -- with det and dot, we could make a differentiable Hartree Fock
    
    
    -- It might make sense to use a traversal?
    -- Or is traversal for use in a monadic/applicative context?
    -- like reinfrocement learning
    
    -- functional differentiation.
    
    -}
    
    
    {-
    -- according to the usual scehem
    We'll need a  (grad -> Lens a b)
    
    RecursiveLens a b = Lens a (b, RecursiveLens a b) 
    
    -}
    
    --val = view
    --deriv = set
    
    
    
    




Some more thoughts: I could get higher order reverse derivatives. Super cool. I think I lose the lens trick. It does seem like there is a lens' function that wouldn't destroy sharing. There is no reason to think the standard lens library is careful about this.

(a -> (b, b -> Powser a))

One sticking point is how do I define the structure of higher order derivatives?

Maybe the Free Comonad trick is applicable here. Powser really has to be Fock

Does lens-accelerate let me lift autodif lens straight up into accelerate? That'd be cool

    
    type FreeVec a f = [(a,f)]
    newtype D2 a b = D2 a -> (b, Either (b,b) b -> Either (a,a) a)
    newtype D2 a b = D2 a -> (b, b -> a, b -> [(a,a)])
    
    compose :: D2 a b -> D2 b c -> D2 a c
    compose (D2 f) (D2 g) = D2 $ \x -> (z,  y' . z', \b -> map y' (z'' b) ++ y'' (z' b) )  where
    																	                   (y, y', y'') = g x
    																	                   (z, z', z'') = f y
    
    sq x = (x*x, \dy -> 2 * x * dy, \d2y -> [(2,d2y)])
    
    fourth = compose (D2 sq) (D2 sq)
    
    add (x,y) = (x + y, \dz -> (dz,dz), \d2z -> [((0,0),(0,0))] )
    
    -- Less abstract
    
    
    newtype D2 a b c = D2 a -> (b, b -> a, b -> c)
    
    
    
    type Typical = D2 (Vec Double) (Vec Double) (Mat Double)
    
    -- instead of trying to be clever
    
    
    -- An ISO
    data InvertibleMat a b = Invertible (a -> b) (b -> a)
    
    defaultinvmat f = Invertible (\x -> dot f x) (\y -> solve f y) 
    
    
    lens'' :: Functor f => (a -> (b, b -> a)) -> (b -> f b) -> a -> f a
    lens'' h g x = fmap j fb where
    	(b, j) = h x
    	fb = g b




replicate the shared weights

Then zip them in with the inputs list zip' :: Lens ([a], [b]) [(a,b)]

and then groupby n :: Int -> Lens [a]  [[a]]

or tupled group3 :: Lens [a] [(a,a,a)]

and fmap over with a max

mmult :: Lens (a,x) y -- Ax=y for multiply the weight matrices

Can also map Relu





A Google summer of Code project that does basically the same thing except he is attacking accelerate, which apparently was very difficult (I believe it).

https://ajknapp.github.io/2018/08/14/notomatic-differentiation.html



We are holding the reverse mode tape in closures is basically what we're doing.
