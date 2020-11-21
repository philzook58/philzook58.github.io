---
author: philzook58
comments: true
date: 2019-09-23 02:35:07+00:00
layout: post
link: https://www.philipzucker.com/linear-algebra-of-types/
slug: linear-algebra-of-types
title: Linear Algebra of Types
wordpress_id: 2313
categories:
- Haskell
tags:
- 2vect
- haskell
- types
- vector
---




It gives my brain a pleasant thrum to learn new mathematics which mimics the algebra I learned in middle school. Basically this means that the new system has operations with properties that match those of regular numbers as much as possible. Two pretty important operations are addition and multiplication with the properties of distributivity and associativity. Roughly this corresponds to the mathematical notion of a [Semiring](https://en.wikipedia.org/wiki/Semiring).







Some examples of semirings include







  * Regular multiplication and addition
  * And-Or
  * [Min-plus](https://en.wikipedia.org/wiki/Tropical_semiring  )
  * Matrices. 
  * Types






I have[ written before about how types also form a semiring](http://www.philipzucker.com/lens-as-a-divisibility-relation-goofin-off-with-the-algebra-of-types/), using `Either` for plus and `(,)` for times. These constructions don't obey distributivity or associativity "on the nose", but instead are isomorphic to the rearranged type, which when you squint is pretty similar to equality. 







Matrices are grids of numbers which multiply by "row times column". You can form matrices out of other semirings besides just numbers. One somewhat trivial but interesting example is[ block matrices](https://en.wikipedia.org/wiki/Block_matrix), where the elements of the matrix itself are also matrices. Another interesting example is that of [relation](http://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/)s, which can be thought of as matrices of boolean values. Matrix  multiplication using the And-Or semiring on the elements corresponds to relational composition.







What if we put our type peanut butter in our matrix chocolate and  consider matrices of types, using the `Either`-`(,`) semiring?







The simplest implementation to show how this could go can be made using the naive list based implementation of vectors and matrices. We can directly lift this representation to the typelevel and the appropriate value-level functions to type families.






    
    
```haskell

type a :*: b = (a,b)
type a :+: b = Either a b

type family Dot v v' where
    Dot '[x] '[y] = x :*: y 
    Dot (x : xs) (y : ys) = (x :*: y) :+: (Dot xs ys)

type family MVMult m v where
    MVMult '[r] v = '[Dot r v]
    MVMult (r : rs) v = (Dot r v) : (MVMult rs v)

type family VMMult m v where
    VMMult v '[c] = '[Dot v c]
    VMMult v (c : cs) = (Dot v c) : (VMMult v cs)

type family MMMult' m m' where
    MMMult' '[r] cs = '[VMMult r cs]
    MMMult' (r : rs) cs = (VMMult r cs) : (MMMult' rs cs)

type family MMMult m m' where
    MMMult m m' = MMMult' m (Transpose m')

type family Transpose m where
    Transpose ((r1 : rs') : rs) = (r1 : (Heads rs)) : (Conss rs' (Transpose (Tails rs)))
    Transpose '[] = '[]

-- some mapped helper functions
-- verrrrrry ugly. Eh. Get 'er dun
type family Heads v where
    Heads ((v : vs) : xs) = v : (Heads xs)
    Heads '[] = '[]
type family Tails v where
    Tails ((v : vs) : xs) = vs : (Tails xs)
    Tails '[] = '[]
type family Conss v vs where
    Conss (x : xs) (y : ys) = (x : y) : (Conss xs ys)
    Conss '[] '[] = '[]

type family Index v i where
    Index (x : xs) 0 = x
    Index (x : xs) n = Index xs (n-1)

```








This was just for demonstration purposes. It is not my favorite representation of vectors. You can lift a large fraction of possible ways to encode vector spaces at the value level up to the type level, such as the [linear package](http://hackage.haskell.org/package/linear), or using dual vectors `type V2 a = a -> a -> a`. Perhaps more on that another day.







### **What is the point**?







Ok. That's kind of neat, but why do it? Well, one way to seek an answer to that question is to ask "what are matrices useful for anyway?"







One thing they can do is describe transition systems. You can write down a matrix whose entire $ a_{ij}$ describes something about the transition from state $  i$ to state $ j$. For example the entry could be:







  * The cost of getting from $ i$ to $ j$ (min-plus gives shortest path),
  * The count of ways to get from $ i$ to $ j$ (combinatorics of paths)
  * The connectivity of the system from $ i$ to $ j$ using boolean values and the and-or semiring
  * The probability of transition from $ i$ to $ j$
  * The quantum amplitude of going from $ i$ to $ j$ if we're feeling saucy.






If we form a matrix describing a single time step, then multiplying this matrix by itself gives 2 time steps and so on.







Lifting this notion to types, we can build a type exactly representing all the possible paths from state $ i$ to $ j$.







Concretely, consider the following humorously bleak transition system: You are going between home and work. Every 1 hour period you can make a choice to do a home activity, commute, or work. There are different options of activities at each.  







    
    
```haskell

data Commute = Drive
data Home = Sleep | Eat
data Work = TPSReport | Bitch | Moan
```








  
This is described by the following transition diagram





![](/assets/My-Drawing-1-1024x674.png)Stapler.





The transitions are described by the following matrix.type:






    
    
```haskell

type T = '[ '[Home    ,  Commute ],  
            '[Commute ,  Work    ]]

```








What is the data type that describe all possible 4-hour day? You'll find the appropriate data types in the following matrix.






    
    
```haskell

type FourHour = MMMult T (MMMult T (MMMult T T))
```








Now, time to come clean. I don't think this is necessarily the best way to go about this problem. There are alternative ways of representing it.







Here are two data types that describe an indefinite numbers of transition steps.






    
    
```haskell

data HomeChoice = StayHome Home HomeChoice | GoWork Commute WorkChoice
data WorkChoice = StayWork Work WorkChoice | GoHome Commute HomeChoice
```








Another style would hold the current state as a type parameter in the type using a GADT.






    
    
```haskell

data Path state where   
   StayWork :: Work -> Path Work -> Path Work
   CommuteHome :: Commute -> Path Home ->  Path Work
   StayHome :: Home -> Path Home -> Path Home
   CommuteWork :: Commute -> Path Work ->  Path Home
```








We could construct types that are to the above types as `Vec n ` is to `[]` by including an explicit step size parameter.







Still, food for thought.







### Further Thoughts







The reason i was even thinking about this is because we can lift the above construction to perform a linear algebra of vectors spaces. And I mean the spaces, not the vectors themselves. This is a confusing point.







Vector spaces have also have two natural operations on them that act like addition and multiplication, the direct sum and kronecker product. These operations do form a semiring, although again not on the nose. 







This is connected to the above algebra of types picture by considering the index types of these vector spaces. The simplest way to denote this in Haskell is using the free vector space construction as shown in this [Dan Piponi post](http://blog.sigfpe.com/2007/03/monads-vector-spaces-and-quantum.html). The Kronecker product makes tuples of the indices and the direct sum has an index that is the Either of the original index types.






    
    
```haskell

type Vec b r = [(b, a)]
-- Example 2D vector space type
type V2D = Vec Bool Double
```








This is by far not the only way to go about it. We can also consider using the Compose-Product semiring on functors (Compose is Kron, Product is DSum) to get a more index-free kind of feel and work with dense vectors.







Going down this road (plus a couple layers of mathematical sophistication) leads to a set of concepts known as[ 2Vect](https://ncatlab.org/nlab/show/TwoVect). Dan Roberts and James Vicary produced a Mathematica package for 2Vect which is basically incomprehensible to me. It seems to me that typed functional programming is a more appropriate venue for something of this kind of pursuit, given how evocative/ well modeled by category theory it can be. These mathematical ideas are applicable to describing anyonic vector spaces. See my previous post below. It is not a coincidence that the `Path` data type above is so similar to `FibTree` data type. The `root` type variable takes the place of the work/home state, and the tuple structure take the place of a Vec-like size parameter `n` .








[http://www.philipzucker.com/a-touch-of-topological-quantum-computation-in-haskell-pt-i/](http://www.philipzucker.com/a-touch-of-topological-quantum-computation-in-haskell-pt-i/)








More to on this to come probably as I figure out how to explain it cleanly.







Edit: Wordpress, your weird formatting is _killing_ me.







Edit: Hoo Boy. This is why we write blog posts. Some relevant material was pointed out to me  that I was not aware of. Thanks @DrEigenbastard.







[https://link.springer.com/chapter/10.1007/978-3-319-19797-5_6](https://link.springer.com/chapter/10.1007/978-3-319-19797-5_6)







[http://blog.sigfpe.com/2010/08/constraining-types-with-regular.html](http://blog.sigfpe.com/2010/08/constraining-types-with-regular.html)







[http://blog.sigfpe.com/2010/08/divided-differences-and-tomography-of.html](http://blog.sigfpe.com/2010/08/divided-differences-and-tomography-of.html)



