---
author: philzook58
comments: true
date: 2019-03-11 01:25:37+00:00
layout: post
link: https://www.philipzucker.com/?p=1688
published: false
slug: Functional Differentiation, QFT, Haskell
title: Functional Differentiation, QFT, Haskell
wordpress_id: 1688
---




What were my favorite physics textbooks? Ziman, Sidney Coleman, Mattuck, Wen,  nanohub guy This is all hard quantum stuff. Of course I like griffiths. Misner thorne wheeler. Sommerfeld. Feynman lectures. Feynman stat mech.  Shankar







Classical mechanics - Goldstein, landau lifshitz.







I have some work in the archive of trying to do a more straightforward path integral of spins using regular auto differentiation tech. The idea was to do a perturbative calculation on 2 spins interacting







Antisymmettric product. The most basic form is the free vector space of a single guy. The only place where it comes up is in issues of either equality or dot product. I don't think you'd want equality really in the context of vectors. Equality is if dot product between two things is roughly product of their norms.  Completely expanded out (a,a) is two particle space. v x y = 1 / (x - y).







Why is there always a competition between finding immediate computational meaning to constructions. A DSL makes so much more sense, because sometimes you want to do more. Like any operations you perform are lossy. YOu kind of always want the ability to work in the lossless dsl represetnation. Finally tagless does give you a balance. You can write both an immediate intepretration and a reflection 







data Fermion i = Annihilate i | Create i | Sum (i -> Fermion i) | Scalar Complex Double | Vector String i |   | Times (Fermion i) (Fermion i) | G i i |







Vector (HVector Complex DOuble) . Vector maybe can just be a lookup. Or a symbolically known vector. G, the propgagotr is important.







ISum \(i -> Expr ) | Prod Expr Expr | Sum Expr Expr |  V [i] ([i]-> Double) | V2 i i ((i,i) -> Double) | V0 Double | V1 i (i -> Double) | Let cute? (cute -> Expr)







snüsh -> yes







interp ISum f = interp (f basis)







Finding par is kind of like finding factorization 







Sum Domain (\i -> . Domain may be understood or not







What do fermion expressions look like?







Multiindex functions/tensors. Plus operators. Multiplied







Particles in a box = 121 matrix. Particles on a ring.







lattice theories







Lattices of funky shapes. Can give a boolean predicate for the lattice sites in it. And bounds to search in. just filter the sites in the bounds based on the predicate. Edges can also be given. Edge if both sites are there.







circle r = \(i,j) -> i*i + j*j <= r*r







box w h = [(i,j) | i <- 1.. w , j <- 1 .. h ]







filter (circle 10) box 



















Might be cool to try and do a kitaev chain, levin-wen using my fib guys. toric code.







conversion between particle and field representation.







lazy expansion of tensor products.







perturbation theory







sharing wavefunctions/ hierarchical













Functional Differentiation is a way of talking about Feynman diagrams







ChebFun is a methodology to manipulate arbitrary functions via sampling.







Samples a







Fourier a is a representable functor to







Num a => Circle -> a







newtype Circle = Circle Double







Fourier is also traversable. It is just a big list of fourier coefficients. Which is sufficient.







This + Ed Kmett's ad package.







integrate :: Num a => Fourier a -> Fourier a







differentiate ::  similar













We can't do the actual functional integral.







But we can use the gaussian formula = e^JGJ. This sum is an ordinary integral.







How can we also put out diagrams?







class Projective a b where







  








Fermions and Bosons







Ordinary vector spaces are 







A Quotient construction. Free Tensor product mod F F.







Algebra = Ring + Vector space.







determinant can be fast and better. should we even worry about that?







Canonical forms. QR, etc.







Canonical ordering. Monomial ordering?







Embedding into full tensor, use alternating sum N!.







Part and parcel of the leave stuff unfactored movement.







Q [Box] would have tuples of box coordinates. algebra of labelled particles.







Q [Box] has Num? mulitplication that is tensor, sum that is vector sum







Rational Q [Box] 







Quotient by the ideal xx. ideal is done via grobner basis. Grobner picks ordering.







Free vect Form of the free comonad guy. 







not very elegant



















One approach is to take the factored form as standard. In order to lift a linear operator requires svd it. https://ro-che.info/articles/2015-12-04-fft







This is s a pretty good fft.







A couple of approaches. 1. Do the chebfun style cutoff. 2. do a lazy stream of better approximations.







samples :: (Double -> Double) -> [[Double]]







data Samples = Samples {samples :: [Double]  interpolate :: Samples}







Samples {samples :: Double, f :: Double -> Double, length :: Double}







dx = length / length (samples s)







[Double -> Double] a stream of inteprolating functions







Double -> [Double] a stream of interpolating values that can share computation.







Hmm if we included derivatvie info, and estimates of next value update, computational cost of next value update?, we could selectively choose whichever pieces matter the most.







Category of function sequences. a -> [(b,db)], db -> da. On compose, we either choose to increase the. Nah, I think we need forward mode basically. Stream of dual numbers. May be a little silly unless we have a lot of moving parts.







interleave [  db -> da]  








 e^JGJ







Samples a b -- a category of samples. = [(a,b)]







compose Samples -- use interpolation. sample at union of points? sampel at original a points?







If sorted on a, not so hard to search and then linearly interpolate.







Or even simpler is find closest pouitn and just use that value. Could require a to be a vector space? Num? Have a metric?







sampleapply :: Samples a b -> a -> b (Functor, that uses some kind of inteprolation)  








sample :: (a -> b) -> Sample a b -- a different functor. in the reverse direction. Typically lossy, but repeated sample sampleapply sample reduces. Adjunection?







lossysample :: Sample a b -> Sample' a b -- we can do this. usually via (a -> b) interpolation = sample' . sampleapply







smoothedsample :: Sample' a -b -> Sample a b = sample . sampleapply'







sampling and interpolation are functors only if composition in Sample and in -> commute. But they won't unless we sample exactly at the right positions. Invertible functions? epsilon-Functors? Like they commute within a factor epsilon?







For random positions, I would do a fitting procedure. (interpolation = fit)







fit :: Samples a b -> Coefficients b/Parameters 







applyceoffs :: Coefificients -> a -> b







This is back to the reprsentable paradigm. assuming b is a vectro space R^n, 







Vector b => Circ -> b -> Fourier b













I've been fascinated fora while about inspectable functions.







One of the introductory mantras to functional programming ins that "functions ARE data". This is true







  1. In some languages, you can directly inspect the source of functions. Very dynamic languages might let you do this. Python for example. This is not true in runtime haskell to my knowledge.
  2. A large class of inspectable functions are those that corresopnd to represetnable functos. This is a condiution onm the domain opf the funciton. An important subclass is functions from a finite domain. These functions can be probed a finite number of times to build a table.
  3. Linear Functions (i.e Matrix application). See conal elliott's linear spaces package. Haskell does not super provide the ability to promise that a function is linear. If you encode linearity using a Linear monad, this actually falls under the previous case.
  4. Highly Polymorphic functions. Some functions are so constrained by their polymoirphic type signature that there is very little they can do. In some cases they are unique. In some cases they have only a couple possible implementations that you can determine by probing one or more times. Tuple rearrangements, Yoneda-theorem/CPS functions, forall a. (a->a)->(a -> a) can only apply the incoming function n times. These functions are connected to Free Theorems.  












Functions from R^n to R^m are interesting. They are the bread and butter of physics and engineering.







Take a generic and return a tuple list.







class Productify a b | a -> b







  to







 from  








In order to take an FFT, it has to have Circ as the implicit domain  








ChebFun a = {pow2 :: Int,  coefficients :: [a] }







Could consider anything that comes after [] is 0.







Treat as a number by the coefficients







Num b => Num (ChebFun a b) where







   (+)  








validChebFun :: ChebFun -> Bool - check if there is any point in expanding







envelope =  fmap abs coefficients







running maximum from the back







envelope xa@(x : xs) = max xa : envelope xs   -- quadratic time which is ridicuslous







envelope' accmax (x:xs) = (max accmax x) : xs







envelope = scanleft (\acc x -> max acc x)  







envelope = reverse . envelope' 0 . reverse













Representable Circ Chebfun (With constraint that a is Num)







ChebFun a where







  ChebFun :: Num a =>







But (Circ -> a) isn't going to havbe a Num a avaialbe.







Specialized functions







chebtabulate







chebindex  




