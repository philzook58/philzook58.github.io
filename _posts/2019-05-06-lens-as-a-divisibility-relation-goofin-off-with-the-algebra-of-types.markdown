---
author: philzook58
comments: true
date: 2019-05-06 02:36:05+00:00
layout: post
link: https://www.philipzucker.com/lens-as-a-divisibility-relation-goofin-off-with-the-algebra-of-types/
slug: lens-as-a-divisibility-relation-goofin-off-with-the-algebra-of-types
title: 'Lens as a Divisibility Relation: Goofin'' Off With the Algebra of Types'
wordpress_id: 1960
categories:
- Haskell
tags:
- algebra
- formal methods
- haskell
- proof
---




Types have an algebra very analogous to the [algebra of ordinary numbers](https://gist.github.com/gregberns/5e9da0c95a9a8d2b6338afe69310b945) ([video](https://www.youtube.com/watch?v=YScIPA8RbVE)). This is the basic table of correspondences. Code with all the extensions available [here](https://github.com/philzook58/lens-algebra).






    
    
```haskell

type a * b = (a,b)
type a + b = Either a b
type b ^ a = a -> b
type O = Void
type I = ()

-- check out typelits implementation
-- http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.TypeNats.html#%2A

infixl 6 + -- ((a + b) + c) associates to the left
infixl 7 *
infixr 8 ^


-- derived definitions
type Succ a = I + a
type Two = Succ I
type Three = Succ Two
type Four = Succ Three
```








One way to see that this makes sense is by counting the cardinality of types built out of these combinators. Unit is the type with 1 inhabitant. Void has 0 inhabitants. If `a` has $ n$ and `b` has $ m$ possible values, then `Either a b` has $ n + m$ inhabitants, `(a,b)` has $ n*m$ and there are $ n^m$ possible tabulations of a->b. We're gonna stick to just polynomials for the rest of this, ignoring a->b.







Another way of looking at this is if two finitely inhabited types have the same number of inhabitants, then the types can be put into an isomorphism with each other. In other words, types modulo isomorphisms can be thought as representing the natural numbers. Because of this, we can build a curious proof system for the natural numbers using ordinary type manipulation.







In addition, we also get a natural way of expressing and manipulating polynomials.Polymorphic types can be seen as being very similar to polynomial expressions with natural coefficients `N[x]`. The polymorphic type variables have the ability to be instantiated to any value, corresponding to evaluating the polynomial for some number.






    
    
```haskell

type ExamplePoly a = I + a + a * a * Three 
```








The [Lens](https://github.com/ekmett/lens) ecosystem gives some interesting combinators for manipulating this algebra. The type `Iso' a b` contains [isomorphisms](http://hackage.haskell.org/package/lens-4.17.1/docs/Control-Lens-Iso.html). Since we're only considering types up to isomorphism, this `Iso'` represents equality. We can give identity isomorphisms, compose isomorphisms and reverse isomorphisms.






    
    
```haskell

type a ~~ b = Iso' a b

refl ::  a ~~ a
refl = id

compose :: (a ~~ b) -> (b ~~ c) -> (a ~~ c)
compose = (.)

rev :: a ~~ b -> b ~~ a
rev = from
```








We can already form a very simple proof.






    
    
```haskell

-- a very simple proof. Holds by definition
oneonetwo :: (I + I) ~~ Two
oneonetwo = id
```








Now we'll add some more combinators, basically the axioms that the types mod isos are a commutative [semiring](https://en.wikipedia.org/wiki/Semiring). Semirings have an addition and multiplication operator that distribute over each other. It is interesting to note that I believe all of these `Iso'` actually are guaranteed to be isomorphisms ( `to . from = id` and `from . to = id` ) because of [parametricity](https://www.well-typed.com/blog/2015/05/parametricity/). `from` and `to` are unique ignoring any issues with bottoms because the polymorphic type signature is so constraining. This is not usually guaranteed to be true in Haskell just from saying it is an `Iso'`. If I give you an `Iso' Bool Bool` it might actually be the `iso (const True) (const True)` for example, which is not an isomorphism.






    
    
```haskell

-- now we start to state our axioms
-- interestingly, I believe the Iso and Lens laws to follow actually follow via parametricity.

-- associativity + a identity object make mul and plus a monoid
plus_assoc :: Iso' (a + (b + c)) ((a + b) + c)
plus_assoc =  iso assoc unassoc  where
                   assoc (Left a) = Left (Left a)
                   assoc (Right (Left b)) = Left (Right b)
                   assoc (Right (Right c)) = Right c
                   unassoc (Left (Left a)) = Left a
                   unassoc (Left (Right b)) = Right (Left b)
                   unassoc (Right c) = (Right (Right c))

mul_assoc :: Iso' (a * (b * c)) ((a * b) * c)
mul_assoc =  iso (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))


-- use `absurd` from Data.Void for empty case.
id_plus :: Iso' (a + O) a
id_plus = iso (\case Left x -> x
                     Right x -> absurd x) Left

id_mul :: Iso' (a * I) a
id_mul = iso (\(x,_) -> x) (\x -> (x,()))


-- they are also commutative
-- specialized version of swapped from Control.Lens.Iso for future clarity
comm_plus :: Iso' (a + b) (b + a)
comm_plus = swapped
comm_mul :: Iso' (a * b) (b * a)
comm_mul = swapped


-- I don't see this one in Lens. Maybe it is there though?
-- distributive property
rdist :: Iso' (a * (b + c)) (a * b + a * c)
rdist = iso (\(a,bc) -> (a,) +++ (a,) $ bc) (\case Left (a,b) -> (a, Left b)
                                                  Right (a,c) -> (a, Right c))   

mul_zero :: Iso' (a,O) O
mul_zero = iso (\(_,y) -> absurd y) absurd

```








There are also combinators for [lifting isomorphisms into bifunctors](http://hackage.haskell.org/package/lens-4.17.1/docs/Control-Lens-Iso.html#v:bimapping): `firsting`, `seconding`, and `bimapping`. These are important for indexing into subexpressions of our types in a point-free style.






    
    
```haskell

-- a specialized version of firsting and seconding for clarity
-- firsting and seconding feel to me more like words for tuples
lefting :: (a ~~ b) -> (a + c) ~~ (b + c)
lefting = firsting

righting :: (a ~~ b) -> (c + a) ~~ (c + b)
righting = seconding
```








Here is a slightly more complicated proof now  available to us.






    
    
```haskell

-- a more complicated proof
twotwofour :: Iso' (Two + Two) Four
twotwofour = rev plus_assoc
```








We can attempt a more interesting and difficult proof. I developed this iteratively using `. _` hole expressions so that GHC would tell me what I had manipulated my type to at that point in my proof.






    
    
```haskell

ldist ::   ((b + c) * a) ~~ (b * a + c * a)
ldist = comm_mul . rdist . (lefting comm_mul) . (righting comm_mul)


-- very painful. Using holes _ and error messages absolutely essential
factorexample ::  ((a + I) * (a + I)) ~~ (a * a + Two * a + I)
factorexample = rdist .  -- distribute out the right side 
               (lefting (comm_mul . rdist)) . -- in the left sum term distribute out
               (righting (comm_mul . rdist)) . -- in the right sum term distribute out
                plus_assoc . -- reassociate plus to the left
               (lefting (lefting (righting comm_mul))) . -- turn a * I term to I * a
                (lefting (rev plus_assoc)) . -- associate the two a*I terms together into an (a * I + a * I) term 
                 (lefting (righting (rev ldist))) . -- factor together that subterm into Two * a
                  (righting id_mul) -- convert last I * I term into I


```






![](/assets/haskell.gif)Artwork Courtesy of David. Sorry for any motion sickness.





The proof here is actually pretty trivial and can be completely automated away. We'll get to that later.







If `Iso'` is equality, what about the other members of the Lens family?  [Justin Le](https://blog.jle.im/entry/lenses-products-prisms-sums.html) says that `Lens s a` are witness to the isomorphism of a type `s` to the tuple of something and `a`. `Prism` witness a similar thing for sums. Once we are only considering types mod isos, if you think about it, these are expressions of two familiar relations on the natural numbers: the inequality relation and the divisibility relation






    
    
```haskell

type a >= b = Prism' a b
type a .| b = Lens' a b
```








Mathematically, these relations can be composed with equalities, just like in the lens hierarchy `Lens` and `Prism` can be composed with `Iso`. Both form a category, since they both have `id` and `(.)`.






    
    
```haskell

{-

the core combinators from the lens library for manipulating these are

_1 :: (a * b) .| a
_2 :: (a * b) .| b

_Left :: (a + b) >= a
_Right :: (a + b) >= b

For example:
-}
twodiv4 :: (Two * Two) .| Two
twodiv4 = _1

onelesstwo :: Two >= I
onelesstwo = _Left

threedivthree :: Three .| Three
threedivthree = id

```








<del>Here are a couple identities that we can't derive from these basic combinators. There are probably others.</del> Woah-ho, my bad. These are totally derivable using id_mul, id_plus, mul_zero, _1, _2, _Left, _Right.






    
    
```haskell

-- once again, these are true via parametricity, more or less
one_div :: a .| I 
-- one_div = lens (const ()) const
one_div = (rev id_mul) . _2

zero_lte :: a >= O
-- zero_lte = prism' absurd (const Nothing)
zero_lte = (rev id_plus) . _Right

zero_div :: O .| a
-- zero_div = lens absurd const
zero_div = (rev mul_zero) . _1
```








Pretty neat! Random thoughts and questions before we get into the slog of automation:







  * Traversal is the "is polynomial in" relation, which seems a rather weak statement on it's own.
  * Implementing automatic polynomial division is totally possible and interesting
  * What is the deal with infinite types like `[a]`? `Fix`. I suppose this is a theory of [formal power series](https://en.wikipedia.org/wiki/Formal_power_series) / combinatorial species. Fun combinatorics, generatingfunctionology. [Brent Yorgey](https://byorgey.wordpress.com/2012/11/20/combinatorial-species-definition/) did his [dissertation](https://www.cis.upenn.edu/~sweirich/papers/yorgey-thesis.pdf) on this stuff. Wow. I've never really read this. It is way more relevant than I realized.
  * Multivariate polynomial algorithms would also be interesting to explore (Grobner basis, multivariate division)
  * Derivatives of types and zippers - [Conor McBride](http://strictlypositive.org/calculus/)
  * Negative Numbers and Fractions?
  * Lifting to rank-1 types. Define Negative and Fractions via [Galois connection?](https://www.sciencedirect.com/science/article/pii/S1567832612000525)





    
    
```haskell

-- partially applied +
type P n = (Either n) 
-- partially applied *
type M n = (,) n
```








Edit: /u/carette (wonder who that is ;) ) writes:







> "You should dig into J Carette, A Sabry [Computing with semirings and weak rig groupoids](http://www.cas.mcmaster.ca/%7Ecarette/publications/esop2.pdf), in Proceedings of ESOP 2016, p. 123-148. Agda code in [https://github.com/JacquesCarette/pi-dual/tree/master/Univalence](https://github.com/JacquesCarette/pi-dual/tree/master/Univalence). A lot of the algebra you develop is there too."







If you hunt around in my repos, you'll also find things about lenses, exploring some of the same things you mention here."







Similar ideas taken further and with more sophistication. Very interesting. Check it out.







## Automation







Our factor example above was quite painful, yet the theorem was exceedingly obvious by expansion of the left and right sides. Can we automate that? Yes we can!  







Here's the battle plan: 







  * Distribute out all expressions like $ a*(b+c)$ so that all multiplication nodes appear at the bottom of the tree.
  * Reduce the expression by absorbing all stupid $ a*1$, $ a*0$, $ a+0$ terms.
  * Reassociate everything to the right, giving a list like format
  * Sort the multiplicative terms by power of the variable






Once we have these operations, we'll combine them into a `canonical` operation. From there, most equality proofs can be performed using the `rewrite` operation, which merely puts both sides into canonical form






    
    
```haskell

-- | The main combinator to expand out any polynomial into canonical form with terms sorted

canonical :: (Dist a b, Absorb b c, RightAssoc c d, SortTerm d e) => a ~~ e
canonical = dist . absorb . rightAssoc . sortTerm

rewrite :: forall a' a b c d e e' d' c' b'. (Dist a b, Absorb b c, RightAssoc c d,
                 SortTerm d e, e ~ e', Dist a' b',
                Absorb b' c', RightAssoc c' d', SortTerm d' e') => a ~~ a'
rewrite = canonical . (rev canonical)
```








Once we have those, the painful theorem above and harder ones becomes trivial.






    
    
```haskell

ex9 :: (a ~ V a') => ((a + I) * (I + a)) ~~ (a * a + Two * a + I)
ex9 = rewrite 

ex10 :: (a ~ V a') => ((a + I) * (I + a) * (Two + a)) ~~  (a * a * a + a * a * Four + Two + Four * a + a)
ex10 = rewrite 
```








Now we'll build the Typeclasses necessary to achieve each of these aims in order. The Typeclass system is perfect for what we want to do, as it builds terms by inspecting types. It isn't perfect in the sense that typeclass pattern matching needs to be tricked into doing what we need. I have traded in cleverness and elegance with verbosity.







In order to make our lives easier, we'll need to tag every variable name with a newtype wrapper. Otherwise we won't know when we've hit a leaf node that is a variable. I've used this trick before [here](http://www.philipzucker.com/shit-compiling-categories-using-type-level-programming-haskell/) in an early version of my faking Compiling to Categories series. These wrappers are easily automatically stripped.






    
    
```haskell

-- For working with Variables

-- a newtype to mark variable position
newtype V a = V a

-- Suggested usage, bind the V in a unification predicate to keep expression looking clean
-- (V a' ~ a) => (a + I) * a 

-- multinomials. to be implemented some other day
-- a phantom l labelled newtype for variable ordering. 
newtype VL l a = VL a
```








A common pattern I exploit is to use a type family to drive complicated recursion. Closed type families allow more overlap and default patterns which is very useful for programming. However, type families do not carry values, so we need to flip flop between the typeclass and type family system to achieve our ends.







Here is the implementation of the distributor `Dist`. We make `RDist` and `LDist` typeclasses that make a sweep of the entire tree, using `ldist` and `rdist` as makes sense. It was convenient to separate these into two classes for my mental sanity. I am not convinced even now that I have every case. Then the master control class `Dist` runs these classes until any node that has a `(*)` in it has no nodes with `(+)` underneath, as checked by the `HasPlus` type family.






    
    
```haskell


class RDist a b | a -> b where
    rdist' :: Iso' a b

instance RDist a a' => RDist (a * I) (a' * I) where
    rdist' = firsting rdist'
instance RDist a a' => RDist (a * O) (a' * O) where
    rdist' = firsting rdist'
instance RDist a a' => RDist (a * (V b)) (a' * (V b)) where
    rdist' = firsting rdist'

instance (RDist (a * b) ab, RDist (a * c) ac) => RDist (a * (b + c)) (ab + ac) where
    rdist' = rdist . (bimapping rdist' rdist')
instance (RDist a a', RDist (b * c) bc) => RDist (a * (b * c)) (a' * bc) where
    rdist' = (bimapping rdist' rdist')
instance (RDist a a', RDist b b') => RDist (a + b) (a' + b') where
    rdist' = bimapping rdist' rdist'

instance RDist O O where
    rdist' = id
instance RDist I I where
    rdist' = id
instance RDist (V a) (V a) where
    rdist' = id

-- can derive ldist from swapped . rdist' . swapped?

class LDist a b | a -> b where
    ldist' :: Iso' a b
instance (LDist (b * a) ab, LDist (c * a) ac) => LDist ((b + c) * a) (ab + ac) where
    ldist' = ldist . (bimapping ldist' ldist')
instance (LDist (b * c) bc, LDist a a') => LDist ((b * c) * a) (bc * a') where
    ldist' = bimapping ldist' ldist'
instance LDist a a' => LDist (I * a) (I * a') where
    ldist' = seconding ldist'
instance LDist a a' => LDist (O * a) (O * a') where
    ldist' = seconding ldist'
instance LDist a a' => LDist ((V b) * a) ((V b) * a') where
    ldist' = seconding ldist'

instance (LDist a a', LDist b b') => LDist (a + b) (a' + b') where
    ldist' = bimapping ldist' ldist'

instance LDist O O where
    ldist' = id
instance LDist I I where
    ldist' = id
instance LDist (V a) (V a) where
    ldist' = id

type family HasPlus a where
    HasPlus (a + b) = 'True
    HasPlus (a * b) = (HasPlus a) || (HasPlus b)
    HasPlus I = 'False
    HasPlus O = 'False
    HasPlus (V _) = 'False

class Dist' f a b | f a -> b where
    dist' :: a ~~ b
instance (f ~ HasPlus ab', LDist (a * b) ab, 
          RDist ab ab', Dist' f ab' ab'') => Dist' 'True (a * b) ab'' where
    dist' = ldist' . rdist' . (dist' @f)
instance Dist' 'False (a * b) (a * b) where
    dist' = id
instance (HasPlus a ~ fa, HasPlus b ~ fb, 
          Dist' fa a a', Dist' fb b b') => Dist' x (a + b) (a' + b') where
    dist' = bimapping (dist' @fa) (dist' @fb)
    -- is that enough though? only dist if 
instance Dist' x I I where
    dist' = id
instance Dist' x O O where
    dist' = id
instance Dist' x (V a) (V a) where
    dist' = id

class Dist a b | a -> b where
    dist :: a ~~ b
-- dist' should distributed out all multiplications
instance (f ~ HasPlus a, Dist' f a b) => Dist a b where
    dist = dist' @f

```








Next is the `Absorb` type class. It is arranged somewhat similarly to the above. Greedily absorb, and keep doing it until no absorptions are left. I think that works.






    
    
```haskell


-- RAbsorb matches only on the right hand side of binary operators
-- matching on both sides is ungainly to write
class RAbsorb a b | a -> b where
    rabsorb :: a ~~ b
-- obvious absorptions
instance RAbsorb x x' => RAbsorb (x + O) x' where
    rabsorb = id_plus . rabsorb
instance RAbsorb x x' => RAbsorb (x + I) (x' + I) where
    rabsorb = firsting rabsorb
instance RAbsorb x x' => RAbsorb (x * I) x' where
    rabsorb = id_mul . rabsorb
instance RAbsorb (x * O) O where
    rabsorb = mul_zero
instance RAbsorb x x' => RAbsorb (x * (V a)) (x' * (V a)) where
    rabsorb = firsting rabsorb
instance RAbsorb x x' => RAbsorb (x + (V a)) (x' + (V a)) where
    rabsorb = lefting rabsorb
-- recursion steps
instance (RAbsorb (y * z) yz, RAbsorb x x') => RAbsorb (x * (y * z)) (x' * yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y + z) yz, RAbsorb x x') => RAbsorb (x * (y + z)) (x' * yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y + z) yz, RAbsorb x x') => RAbsorb (x + (y + z)) (x' + yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y * z) yz, RAbsorb x x') => RAbsorb (x + (y * z)) (x' + yz) where
    rabsorb = bimapping rabsorb rabsorb
-- base cases
instance RAbsorb O O where
    rabsorb = id
instance RAbsorb I I where
    rabsorb = id
instance RAbsorb (V a) (V a) where
    rabsorb = id


-- mirror of RAbsorb    
class LAbsorb a b | a -> b where
    labsorb :: a ~~ b
instance LAbsorb x x' => LAbsorb (O + x) x' where
    labsorb = comm_plus . id_plus . labsorb
instance LAbsorb x x' => LAbsorb (I + x) (I + x') where
    labsorb = righting labsorb
instance LAbsorb x x' => LAbsorb (I * x) x' where
    labsorb = comm_mul . id_mul . labsorb
instance LAbsorb (O * x) O where
    labsorb = comm_mul . mul_zero
instance LAbsorb x x' => LAbsorb ((V a) + x) ((V a) + x') where
    labsorb = righting labsorb
instance LAbsorb x x' => LAbsorb ((V a) * x) ((V a) * x') where
    labsorb = seconding labsorb

instance (LAbsorb (y * z) yz, LAbsorb x x') => LAbsorb ((y * z) * x) (yz * x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y + z) yz, LAbsorb x x') => LAbsorb ((y + z) * x) (yz * x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y + z) yz, LAbsorb x x') => LAbsorb ((y + z) + x) (yz + x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y * z) yz, LAbsorb x x') => LAbsorb ((y * z) + x) (yz + x') where
    labsorb = bimapping labsorb labsorb

instance LAbsorb O O where
    labsorb = id
instance LAbsorb I I where
    labsorb = id
instance LAbsorb (V a) (V a) where
    labsorb = id

-- labsorb :: (Swapped p, RAbsorb (p b a) (p b' a')) => (p a b) ~~ (p a' b')
-- labsorb = swapped . rabsorb . swapped   

-- a test function to see if an expression is properly absorbed
type family Absorbed a where
    Absorbed (O + a) = 'False
    Absorbed (a + O) = 'False
    Absorbed (a * I) = 'False
    Absorbed (I * a) = 'False
    Absorbed (a * O) = 'False
    Absorbed (O * a) = 'False
    Absorbed (a + b) = (Absorbed a) && (Absorbed b)
    Absorbed (a * b) = (Absorbed a) && (Absorbed b)
    Absorbed I = 'True
    Absorbed O = 'True
    Absorbed (V a) = 'True

-- iteratively rabsorbs and leftabsorbs until tree is properly absorbed.
class Absorb' f a b | f a -> b where
    absorb' :: a ~~ b
instance Absorb' 'True a a where
    absorb' = id
instance (LAbsorb a a', RAbsorb a' a'',
          f ~ Absorbed a'', Absorb' f a'' a''') => Absorb' 'False a a''' where
    absorb' = labsorb . rabsorb . (absorb' @f)

-- wrapper class to avoid the flag.
class Absorb a b | a -> b where
    absorb :: a ~~ b
instance (f ~ Absorbed a, Absorb' f a b) => Absorb a b where
    absorb = absorb' @f

```








The Associators are a little simpler. You basically just look for the wrong association pattern and call `plus_assoc` or `mul_assoc` until they don't occur anymore, then recurse. We can be assured we're always making progress if we either switch some association structure or recurse into subparts.






    
    
```haskell


class LeftAssoc a b | a -> b where
    leftAssoc :: Iso' a b

instance LeftAssoc a a' => LeftAssoc (a + I) (a' + I) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a + O) (a' + O) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * I) (a' * I) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * O) (a' * O) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * (V b)) (a' * (V b)) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a + (V b)) (a' + (V b)) where
    leftAssoc = firsting leftAssoc 

instance (LeftAssoc ((a + b) + c) abc') => LeftAssoc (a + (b + c)) abc' where
    leftAssoc = plus_assoc . leftAssoc 
instance (LeftAssoc ((a * b) * c) abc') => LeftAssoc (a * (b * c)) abc' where
    leftAssoc = mul_assoc . leftAssoc 


instance (LeftAssoc (b * c) bc, LeftAssoc a a') => LeftAssoc (a + (b * c)) (a' + bc) where
    leftAssoc = bimapping leftAssoc leftAssoc
-- a * (b + c) ->  a * b + a * c 
-- This case won't happen if we've already distribute out.
instance (LeftAssoc (b + c) bc, LeftAssoc a a') => LeftAssoc (a * (b + c)) (a' * bc) where
    leftAssoc = bimapping leftAssoc leftAssoc

instance LeftAssoc O O where
    leftAssoc = id
instance LeftAssoc I I where
    leftAssoc = id
instance LeftAssoc (V a) (V a) where
    leftAssoc = id




-- right assoc will completely associate strings of + or -. Mixed terms are not associated.
-- cases  on left hand side of binary expression
-- always makes progress by either reassociating or recursing
class RightAssoc a b | a -> b where
    rightAssoc :: Iso' a b
instance (RightAssoc (a + (b + c)) abc') => RightAssoc ((a + b) + c) abc' where
    rightAssoc = (rev plus_assoc) . rightAssoc 
instance (RightAssoc (a * (b * c)) abc') => RightAssoc ((a * b) * c) abc' where
    rightAssoc = (rev mul_assoc) . rightAssoc 
instance RightAssoc a a' => RightAssoc (I + a) (I + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (O + a) (O + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (I * a) (I * a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (O * a) (O * a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc ((V b) + a) ((V b) + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc ((V b) * a) ((V b) * a') where
    rightAssoc = seconding rightAssoc 


instance (RightAssoc (b * c) bc, RightAssoc a a') => RightAssoc ((b * c) + a) (bc + a') where
    rightAssoc = bimapping rightAssoc rightAssoc
instance (RightAssoc (b + c) bc, RightAssoc a a') => RightAssoc ((b + c) * a) (bc * a') where
    rightAssoc = bimapping rightAssoc rightAssoc

instance RightAssoc O O where
    rightAssoc = id
instance RightAssoc I I where
    rightAssoc = id
instance RightAssoc (V a) (V a) where
    rightAssoc = id

```








Finally, the `SortTerm` routine. `SortTerm` is a bubble sort. The typeclass `Bubble` does a single sweep of swapping down the type level list-like structure we've built. The `SortTerm` uses the `Sorted` type family to check if it is finished. If it isn't, it call `Bubble` again.






    
    
```haskell


type family (a :: k) == (b :: k) :: Bool where
    f a == g b = f == g && a == b
    a == a = 'True
    _ == _ = 'False

type family SortedTerm a :: Bool where
    SortedTerm (a + (b + c)) = (((CmpTerm a b) == 'EQ) || ((CmpTerm a b) == 'GT)) && (SortedTerm (b + c))
    SortedTerm (a + b) = ((CmpTerm a b) == 'EQ) || ((CmpTerm a b) == 'GT)
    --SortedTerm a = 'True 
    SortedTerm I = 'True 
    SortedTerm O = 'True 
    SortedTerm (V a) = 'True 

-- higher powers of V are bigger.
-- CmpTerm compares TimesLists.    
type family CmpTerm a b where
    CmpTerm ((V a) * b) ((V a) * c) = CmpTerm b c
    CmpTerm ((V a) * b) (V a) = 'GT
    CmpTerm (V a) ((V a) * b)  = 'LT
    CmpTerm I ((V a) * b) = 'LT
    CmpTerm ((V a) * b) I = 'GT
    CmpTerm (V a) (V a) = 'EQ
    CmpTerm I (V a) = 'LT
    CmpTerm (V a) I = 'GT
    CmpTerm I I = 'EQ


-- Maybe this is all uneccessary since we'll expand out and abosrb to a*a + a*a + a + a + a + a


-- type a == b = TEq.(==) a b


-- Head and Tail of PlusLists
type family PlusHead a where
    PlusHead (x + y) = x
    PlusHead x = x
type family PlusTail a where
    PlusTail (x + y) = y



-- bubble assume a plusList of multiplicative terms. I.E. fully distributed, fully rightassociated , fully absorbed  
-- does one pass of a bubble sort
class Bubble f a b | f a -> b where
    bubble :: a ~~ b
-- more to go
instance (f ~ CmpTerm b (PlusHead c), Bubble f (b + c) bc) => Bubble 'EQ (a + (b + c)) (a + bc) where
    bubble = righting (bubble @f)
instance (f ~ CmpTerm b (PlusHead c), Bubble f (b + c) bc) => Bubble 'GT (a + (b + c)) (a + bc) where
    bubble = righting (bubble @f)
instance (f ~ CmpTerm a (PlusHead c), Bubble f (a + c) ac) => Bubble 'LT (a + (b + c)) (b + ac) where
    bubble = plus_assoc . (lefting comm_plus) . (rev plus_assoc) . righting (bubble @f)


-- The times, or constants shows that we're at the end of our + list.
instance Bubble 'EQ (a + (b * c)) (a + (b * c)) where
    bubble = id
instance Bubble 'GT (a + (b * c)) (a + (b * c)) where
    bubble = id
instance Bubble 'LT (a + (b * c)) ((b * c) + a) where
    bubble = comm_plus

instance Bubble 'EQ (a + I) (a + I) where
    bubble = id
instance Bubble 'GT (a + I) (a + I) where
    bubble = id
instance Bubble 'LT (a + I) (I + a) where
    bubble = comm_plus

instance Bubble 'EQ (a + O) (a + O) where
    bubble = id
instance Bubble 'GT (a + O) (a + O) where
    bubble = id
instance Bubble 'LT (a + O) (O + a) where -- shouldn't happen
    bubble = comm_plus

instance Bubble 'EQ (a + (V b)) (a + (V b)) where
    bubble = id
instance Bubble 'GT (a + (V b)) (a + (V b)) where
    bubble = id
instance Bubble 'LT (a + (V b)) ((V b) + a) where
    bubble = comm_plus
-- goofy base cases in case bubble gets called on a single element
instance Bubble x O O where
    bubble = id
instance Bubble x I I where
    bubble = id
instance Bubble x (V a) (V a) where
    bubble = id


-- sort term assumes rightassociated, fully distributed, fully I O absorbed expressions
class SortTerm' f a b | f a -> b where -- f is flag whether PlusList is sorted.
    sortTerm' :: a ~~ b
instance SortTerm' 'True a a where
    sortTerm' = id
-- a single term with no plus shouldn't get here. That is why PlusTail is ok.
instance (f ~ CmpTerm (PlusHead a) (PlusHead (PlusTail a)), Bubble f a a',
          f' ~ SortedTerm a', SortTerm' f' a' b) => SortTerm' 'False a b where
    sortTerm' = (bubble @f) . (sortTerm' @f')
class SortTerm a b | a -> b where -- f is flag whether PlusList is sorted.
    sortTerm :: a ~~ b
instance (f ~ SortedTerm a, SortTerm' f a a') => SortTerm a a' where
    sortTerm = sortTerm' @f

```








Hope you thought this was neat!



