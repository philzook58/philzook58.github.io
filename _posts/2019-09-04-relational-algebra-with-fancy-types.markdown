---
author: philzook58
comments: true
date: 2019-09-04 23:26:02+00:00
layout: post
link: https://www.philipzucker.com/relational-algebra-with-fancy-types/
slug: relational-algebra-with-fancy-types
title: Relational Algebra with Fancy Types
wordpress_id: 2271
categories:
- Formal Methods
- Haskell
tags:
- fancytypes
- gadts
- haskell
---




[Last time](http://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/ ),  I tried to give a primer of relations and relational algebra using the Haskell type `type Rel a b = [(a,b)]`. In this post we're going to look at these ideas from a slightly different angle. Instead of encoding relations using value level sets, we'll encode relations in the type system.  The [Algebra of Programming Agda repo](https://github.com/scmu/aopa) and the papers quoted therein are very relevant, so if you're comfortable wading into those waters, give them a look. You can find my repo for [fiddling here](https://github.com/philzook58/rel/blob/master/src/ProRel.hs)







At this point, depending on what you've seen before, you're either thinking "Yeah, sure. That's a thing." or you're thinking "How and why the hell would you do such a ridiculous thing."







Most of this post will be about how, so let's address why first:







  1. Examining relations in this style illuminates some constructions that appear around the Haskell ecosystem, particularly some peculiar fellows in the [profunctor package](http://hackage.haskell.org/package/profunctors-5.4). 
  2. More syntactic approach to relations allows discussion of larger/infinite domains. The finite enumerations of the previous post is nice for simplicity, but it seems you can't get far that way. 
  3. Mostly because we can - It's a fun game. Maybe a useful one? TBD.






With that out of the way, let's go on to how.







### Translating Functions to Relation GADTs







We will be using some Haskell extensions in this post, at the very least GADTs and DataKinds. For an introduction to GADTs and DataKinds, check out this [blog post](https://www.parsonsmatt.org/2017/04/26/basic_type_level_programming_in_haskell.html). DataKinds is an extension that reflects every data constructor of data types to a type constructor.  Because there are values `True` and `False` there are corresponding types created`'True` and `'False`. GADTs is an extension of the type definition mechanism of standard Haskell. They allow you to declare refined types for the constructors of your data and they infer those refined type when you pattern match out of the data as well, such that the whole process is kind of information preserving.







We will use the GADT extension to define relational datatypes with the kind 
    
    
```haskell

a -> b -> *
```


. That way it has a slot `a` for the "input" and `b` for the "output" of the relation.  What will goes in these type slots will be DataKind lifted types like `'True`, not ordinary Haskell types like `Int`. This is a divergence from from the uses of similar kinds you see in Category, Profunctor, or Arrow. We're doing a more typelevel flavored thing than you'll see in those libraries. What we're doing is clearly a close brother of the [singleton](http://hackage.haskell.org/package/singletons) approach to dependently typed programming in Haskell.







Some examples are in order for what I mean. Here are two simple boolean functions, `not` and `and` defined in ordinary Haskell functions, and their equivalent GADT relation data type.






    
    
```haskell

not True = False
not False = True

data Not a b where
    NotTF :: Not 'True 'False
    NotFT :: Not 'False 'True

and True True = True
and False _ = False
and _ False = False

data And a b where
    AndTT :: And '( 'True, 'True) 'True
    AndFU :: And '( 'False, a) 'False
    AndUF :: And '( a, 'False) 'False
```








You can already start to see how mechanical the correspondence between the ordinary function definition and our new fancy relation type. A function is often defined via cases. Each case corresponds to a new constructor of the relation and each pattern that occurs in that case is the pattern that appears in the GADT. Multiple arguments to the relations are encoded by uncurrying everything by default.







Any function calls that occur on the right hand side of a function definition becomes fields in the constructor of our relation. This includes recursive calls and external function calls. Here are some examples with a Peano style natural number data type.






    
    
```haskell

data Nat = S Nat | Z

plus Z x = x
plus (S x) y = S (plus x y)

data Plus a b where
    PZ :: Plus '( 'Z, a) a
    PS :: Plus '( a,b) c -> Plus '( 'S a, b) c 

```








We can also define things that aren't functions. Relations are a larger class of things than functions are, which is part of their utility. Here is a "less than equal"  relation `LTE`.






    
    
```haskell

data LTE a b where
    LTERefl :: LTE n n
    LTESucc :: LTE n m -> LTE n ('S m)
```








You can show that elements are in a particular relation by finding a value of that relational type. Is `([4,7], 11)` in the relation `Plus`? Yes, and I can show it with with the value `PS (PS (PS (PS PZ))) :: Plus (4,7) 11` .  This is very much the Curry-Howard correspondence. The type `R a b` corresponds to the proposition/question is $ (a,b) \in R$ .







### The Fun Stuff : Relational Combinators







While you need to build some primitive relations using new data type definitions, others can be built using relational combinators.   If you avoid defining too many primitive relations like the above and build them out of combinators, you expose a rich high level manipulation algebra. Otherwise you are stuck in the pattern matching dreck. We are traveling down the same road we did in the [previous post](http://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/), so look there for less confusing explanations of the relational underpinnings of these constructions, or better yet some of the references below.







Higher order relational operators take in a type parameters of kind 
    
    
```haskell

a -> b -> *
```


and produce new types of a similar kind. The types appearing in these combinators is the AST of our relational algebra language.







The first two combinators of interest is the composition operator and the identity relation.  An element $ (a,c) $ is in $ R \cdot Q $ if there exists a $ b$ such that $ (a,b) \in R$ and $ (b,c) \in Q$. The fairly direct translation of this into a type is






    
    
```haskell

{- rcompose :: Rel b c -> Rel a b -> Rel a c  -}

data RCompose k1 k2 a c where
   RCompose :: k1 b c -> k2 a b -> RCompose k1 k2 a c

type k <<< k' = RCompose k k' 
type k >>> k' = RCompose k' k
```








The type of the composition is the same as that of [Profunctor composition](https://hackage.haskell.org/package/profunctors-5.2.1/docs/Data-Profunctor-Composition.html) found in the profunctors package.






    
    
```haskell

type RCompose = Procompose
```








Alongside a composition operator, it is a knee jerk to look for an identity relation and we do have one 






    
    
```haskell

data Id a b where
   Refl :: Id a a


-- monomorphic identity. Leave this out?
data IdBool a b where
  ReflTrue :: IdBool 'True 'True
  ReflFalse :: IdBool 'False 'False
```








This is also a familiar friend. The identity relation in this language is the [Equality type.](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Type-Equality.html)






    
    
```haskell

-- identity function is the same as Equality
type Id a b = Id (a :~: b)
```








We can build an algebra for handling product and sum types by defining the appropriate relational combinators. These are very similar to the combinators in the Control.Arrow package. 






    
    
```haskell

-- Product types

data Fan k k' a b where
    Fan :: k a b -> k' a c -> Fan k k' a '(b,c)

type k &&& k' = Fan k k'

data Fst a b where
    Prj1 :: Fst '(a, b) a

data Snd a b where
    Prj2 :: Snd '(a, b) b

-- Sum type

data Split k k' a b where
    CaseLeft :: k a c -> Split k k' ('Left a) c
    CaseRight :: k' b c -> Split k k' ('Right b) c

type k ||| k' = Split k k'

data Inj1 a b where
    Inj1 :: Inj1 a ('Left a)
data Inj2 a b where
    Inj2 :: Inj2 a ('Right a)

-- some derived combinators
type Par f g = Fan (f <<< Fst) (g <<< Snd)
type Dup  = Fan Id Id
type Swap = Fan Snd Fst

```








The converse of relations is very interesting operation and is the point where relations really differ from functions. Inverting a function is tough. Conversing a relation always works. This data type has no analog in profunctor to my knowledge and probably shouldn't.






    
    
```haskell

data RConverse k a b where
    RConverse :: k a b -> RConverse k b a
-- Shorter synonym
type RCon = RConverse
```








Relations do not have a notion of currying. The closest thing they have is 






    
    
```haskell

data Trans k a b where
    Trans :: k '(a,b) c -> Trans k a '(b,c)
```








### Lattice Operators







For my purposes, lattices are descriptions of sets that trade away descriptive power for efficiency. So most operations you'd perform on sets have an analog in the lattice structure, but it isn't a perfect matching and you're forced into approximation. It is nice to have the way you perform these approximation be principled, so that you can know at the end of your analysis whether you've actually really shown anything or not about the actual sets in question.





![](/assets/lattice-1024x769.jpg)? No. No... Yes? Oh. OH! IT IS!





The top relation holds all values. This is represented by making no conditions on the type parameters. They are completely phantom. 






    
    
```haskell

newtype Top a b = Top ()
```








Bottom is a relation with no inhabitants.






    
    
```haskell

newtype Bottom a b = Bottom Void
```








The meet is basically the intersection of the relations, the join is basically the union.






    
    
```haskell

newtype RMeet k k' a b = RMeet (k a b, k' a b)
type k /\ k' = RMeet k k'  

newtype RJoin k k' a b = RJoin (Either (k a b) (k' a b))
type k \/ k' = RJoin k k' 
```








A Lattice has an order on it. This order is given by relational inclusion. This is the same as the  :-> combinator can be found in the [profunctors package](http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor.html#t::-45--62-).






    
    
```haskell

type (:->) p q = forall a b. p a b -> q a b
type RSub p q = p :-> q
```








Relational equality can be written as back and forth inclusion, a natural isomorphism between the relations. There is also an interesting indirect form.






    
    
```haskell

data REq k k' = REq {to' :: k :-> k', from' :: k' :-> k }
```








#### Relational Division







If we consider the equation `(r <<< p) :-> q` with `p` and `q` given, in what sense is there a solution for `r`? By analogy, this looks rather like `r*p = q`, so we're asking a kind of division question.  Well, unfortunately, this equation may not necessarily have a solution (neither do linear algebraic equations for that matter), but we can ask for the best under approximation instead. This is the operation of relational division. It also appears in the profunctor package as the [right Kan Extension](http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Ran.html). You'll also find the universal property of the right division under the name `curryRan` and `uncurryRan` in that module.






    
    
```haskell

newtype Ran p q a b = Ran { runRan :: forall x. p x a -> q x b }
type RDiv = Ran
```








One formulation of Galois connections can be found in the [adjunctions ](http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Adjunction.html) file. [Galois Connections are very slick](https://www.sciencedirect.com/science/article/pii/S1567832612000525), but I'm running out of steam, so let's leave that one for another day.







### Properties and Proofs







We can prove many properties about these relational operations. Here a a random smattering that we showed using quickcheck last time.






    
    
```haskell

prop_ridleft ::  (k <<< Id) :-> k
prop_ridleft (RCompose k IdRefl) = k

prop_ridright ::  (Id <<< k) :-> k
prop_ridright (RCompose IdRefl k) = k

prop_meet :: p /\ q :-> p
prop_meet (RMeet (p, q)) = p

prop_join :: p :-> p \/ q
prop_join p = RJoin (Left p)

meet_assoc :: RMeet k (RMeet k' k'') a b -> RMeet (RMeet k k') k'' a b
meet_assoc (RMeet (k, (RMeet (k',k'')))) = RMeet (RMeet (k,k'), k'')

prop_top :: k :-> Top
prop_top _ = top

prop_bottom :: Bottom :-> k
prop_bottom (Bottom x) = absurd x

bottom_compose :: REq (k <<< Bottom) Bottom
bottom_compose = REq (\(RCompose k (Bottom b)) -> absurd b) prop_bottom

data Iso a b = Iso {to :: a -> b, from :: b -> a}
type a <-> b = Iso a b

meet_universal :: (p ::-> RMeet k k') <-> (p ::-> k, p ::-> k')
meet_universal = Iso to from where
    to (RSub f) = (RSub $ \p -> case f p of RMeet (k,k') -> k  , RSub $ \p -> case f p of RMeet (k,k') -> k')
    from (RSub f,RSub g) = RSub $ \p -> RMeet (f p, g p) 

prop_con :: RCon (RCon k) :-> k
prop_con (RConverse (RConverse k)) = k
```








### Odds and Ends







  * Recursion Schemes - Recursion schemes are a methodology to talk about recursion in a point free style and where the rubber meets the road in the algebra of programming. [Here](https://blog.sumtypeofway.com/an-introduction-to-recursion-schemes/) is an excellent series of articles about them. Here is a sample of how I think they go:





    
    
```haskell

data MapMaybe k a b where
    MapJust :: k a b -> MapMaybe k ('Just a) ('Just b)
    MapNothing :: MapMaybe k 'Nothing 'Nothing

data Cata map k a b where
    Cata :: k fa a -> map (Cata map k) x fa  -> Cata map k ('Fix x) 
```








  * Higher Order Relations?
  * Examples of use. Check out the[ examples folder in the AoP Agda repo](https://github.com/scmu/aopa/tree/master/Examples). These are probably translatable into Haskell.
  * Interfacing with Singletons. Singletonized functions are a specialized case or relations. Something like?
 


    
     
```haskell

newtype SFun a b = SFun (Sing a -> Sing b)
```
 



  * A comment to help avoid confusion. What we've done here feels confusingly similar to profunctor, but it is in fact distinct I think. [Profunctors are described as a categorical generalization of relations](https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/) [,](https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/) but to be honest, I kind of don't get it. Despite many of our constructions appearing in the profunctor package, the profunctor typeclass itself appears to not play a role in our formulation. There just isn't a good way to dimap under our relations as written, unless you construct free profunctors. Converse at the least is a wrench in the works.
  * Star and graphs. Transition relations are a powerful methodology. A transition relation is in some respects the analog of a square matrix. We can iteratively compose it with itself. 





    
    
```haskell

-- Check out "term rewriting and all that"
-- This is also the reflection without remorse data type
-- TSequence http://okmij.org/ftp/Haskell/zseq.pdf
-- this is also a free instance of Category
data Star k a b where
    Done :: Star k a a
    Roll :: k b c -> Star k a b -> Star k a c

data KPlus k a b where
    PDone :: k a b -> KPlus k a b
    PRoll :: k b c -> KPlus k a b -> KPlus k a c

type SymClos k a b = RJoin k (RCon k) a b
type RefClos k a b = RJoin k Id a b
{- n-fold composition -}
-- similar to Fin.
-- This is also the Vec n is to list and this is to reflection without remorse. Kind of interesting
data NFold n k a b where
    One :: k a b -> NFold ('S n) k a b
    More :: k b c -> NFold n k a b -> NFold ('S n) k a b
```








### References







  * Program Design by Calculation - JN Oliveira
  * Bird and de Moor
  * Term Rewriting and all that
  * Software Abstractions
  * [https://softwarefoundations.cis.upenn.edu/lf-current/Rel.html](https://softwarefoundations.cis.upenn.edu/lf-current/Rel.html)
  * [https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html#lab335](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html#lab335)
  * [https://github.com/scmu/aopa](https://github.com/scmu/aopa)


