---
author: philzook58
comments: true
date: 2020-09-12 20:56:20+00:00
layout: post
link: https://www.philipzucker.com/?p=2170
published: false
slug: Vector Spaces I Have Love & Category Vector Stuff, 2vect, functor vector. Two
  Vect with Kind Signatures
title: Vector Spaces I Have Love & Category Vector Stuff, 2vect, functor vector. Two
  Vect with Kind Signatures
wordpress_id: 2170
---










2 Vect is a very strange and abstract place. The analog with regular vector is like so







  * scalars ~ vector spaces
  * mul-plus matrices - kron-directsum matrices of spaces
  * One more thing: linear natural transformation






I know what a vector is. It is a list of numbers. We cna work with that, represdent it on paper, on a computer. But what the hell is a vector _space_? How can I even write such a thing down?







Well at the very least some data associated with a vector space is it's number of dimensions.







In Haskell, the appropriate language seems to be that a vector space is a type. We will use well typed vector representations for which the type tells us the dimensionality of the vector.







What is very similar to this post, so maybe you want to check that out.








https://www.philipzucker.com/linear-algebra-of-types/








type MyVector = '[(), Void, Bool] is an type level analog of [1,0,2]. This is a vector of types.







Linear operators can be represented as type level matrices. Instead of * and + appearing in the matrix multiplication definition, use the type operations (_, _) and Either _ _ (type multiplication and sum).







Very good. But in what sense has any of this been acting on vector spaces and not types? None so far. The 2-morphisms of two vect are where that shows up







One of the very simplest well typed representations of vector is `type Vect a = [ (a,Double) ]`. It's not the worst conceivable representation for sparse vectors and it plays pretty nice with Haskelly ways of doing things.







A linear operator takes the form  `type LinOp a b =` `a -> Vect b`. With this type we can see that there is some monad stuff at play. This is also a way of representing probabilistic programming in Haskell. See these posts for more: Piponi, Fib post.







A 2 morphism is thing whose domain and codomain are 1-morphisms (which are typelevel matrices in our case). 2-Morphisms also compose associatively and have an identity






    
    <code>kind TwoVectMorph = [[*]]
    type ExampleMorph :: TwoVectMorph = '['[],'[]]
    kind TwoVectObj = [*]
    type TwoVect2Morph = LinOp (MV a v) (MV b w)</code>







type TwoVectObj = [*]







type TwoMorph a b v w= LinOp (MMul a v) (MMul b w)







The standard model of category theory in Haskell is that types ~ objects and function _values_ ~ morphisms. Similarly here both objects were types, 1-morphisms were type operators, and 2-morphisms are functional values. 







An alternative representation is






    
    <code>type MyVector42 v = () :*: (v !! 0) :+: Void :*: (v !! 1) :+: Bool :*: (v !! 2)
    myvector42 v = 1 * (v !! 1) + 0 * (v !! 1) + 2 * (v !! 2)</code>







There is often a duality between vectors and linear functions on those vectors. Often the linear functions have nice properties and are better behaved. It's weird.







My personal favorite







It is interesting that one can do this directly at the higher kinded type level. Rather than using index types, we can use container types like V1 V2 V3. Instead of using tuple as multiplication and sum as multiplication, we can use the lifted forms of those for functors.













10/19







The standard typeclass hierarchy of Functor, Foldable, Traversable, Applicative, Monad of the Haskell standard library is one of its stand out points. It expresses various conceptual operations of containers in a mathematical way.







One thing that makes Haskell somewhat unusual in the landscape of commonly used programming languages is that you have well founded conceptual means to talk about containers and operations on containers without talking about the things inside the containers. You have higher kinded types, types that are parametrized on other types. 







I think the concrete things are necessary to be sure the abstract things mean anything at all.







The two core runnign examples of this post are Haskell Functors (think containers list list), and Vector spaces. These two interleave and even pun on each other, which is both confusing and explaining. Hopefully mostly the latter.







I personally find something that tickles me about category theory. I'm not necessarily convinced that it sufficiently useful and intuitive that it is morally correct for me to prosletiyze it though.







  
The going seems rather slow and it is not uncommon for mathematicians to have an asethetic that does not coincide with my own. I like things simple.  
Sometimes I am not ready to understand what they are saying. Sometimes they are just delusional, bad communicators, or full of shit. It is hard to tell what situation you're in.







My simple is insanely arcane to others though. It is all subjective.







Post structure  
Functor composition  
Kronecker product  
Vector as shapes / functors / structs  
Monoidal categories  
String diagrams







What is the central message: Well, that I'm smart of course  
What are monoidal categories







Compositional construction of vectors spaces







A type of kind * -> * can be thoguht of as a container. Familiar examples include Maybe, and []. Container have shape. A Vector space is also commonly thought of as a container of numbers of a certain shape. By abstractly using types of kind * -> *, we avoid using labelling vector spaces only by the dimension.   

You wouldn't want to mix semantically incompatibnle vector spaces just because thir dimension just so happened to be the same. Adding an RGB color space to and XYZ geometrical vector space should never happen. Therefore, it is inelegant and confusing ad error prone we shouldn't define them both as (V 3 Double).  

To name every vector space the same just because they have the same dimensionality is the same as saying every flag type should be a Bool. It makes sense, works, but it creates confusion and allows more programs than you actually want to type check  

There are the 3 sizes of vector spaces.  

Vector spaces can be contructed out of others by two combinators,  

the direct sum and the kronecker product.







Vector spaces can also be thought of as indexed containers. 







Vectors might be synonmous with Representable / Naperian / Logarithmic functors. These are the functors that are isomorphic to (a -> _) for some a.







They are called Naperain/Logrithmic because there is a relationship similar to exponentiaion between the index type `a` and the container type `f`.  

If you take the Product f g, this container is indexed by (a + b) = Either a b. In a sense Compose f g is indexed by the product (a,b). (f r) ~ r^a  

The arrow type is written as an expoential b^a because if you have finite enumerable types a and b, that is the number of possible tabulations avaiable for f.  

The Sum of two representable functors is no longer representable. Log(f + g) does not have very good identities associated with it.







The names direct sum and direct product are most easily seen the make sense by looking at the algebra of the indices rather than the containers.  

The direct product has a dimensionality that is the product of the idnvidiual dimensionality and the direct sum has 







String disagrams are first of just an intuitive notation. An attempt to formalize them comes up in the context of monoidal categories.  

String diagrams take the Poincare dual of a more ordinary categorical diagram. Usually we draw objects as points, arrows as arrows (pointing along the line) and 2-morphisms as bubbles.  

String diagrams represent arrows by lines (pointing perpendicular to the line), points as regions, and 2-morphisms as points. 







Sometimes it is nice to expand the points out into boxes, such that they are easier to label.







There are a number of cases where the natural progression goes 0,1,2, infinity.  

3 is often not that interesting, and 4 almost never is.  

Godel's incompleteness theorem.







Consider any cutting of the plane into regions. Draw a point at the center of each face corresponding to the face. Draw an edge between each face center if their regions touch. You will now find that the new edges encircle the original vertices, so that the vertcies are now faces of this new diagram. We have trasnformed faces to points, edges to perpendicular edges, and points to faces. Repeating the consturction will give you back your original drawing (at least topologically), so there is a two-ness to this correspondence, hence the term dual. These two systems are dual to each other. 







This construction has something to do with the topology of the plane. 







There are a couple other dualities that are related to these.







  * Circuit duality
  * Hodge duality
  * Poincare duality
  * Voronoi diagrams






Monoidal categories are categories first off. So they have arrows which compose, and there are always identity arrows. The monoidal prefix means that they have a binary operation on the objects. What does a binary operation look like in the categroical aesthetic? Well a binary operation is something that takes two things are returns another. Functors are the first thing that has something like this. It has other properties that come along for the ride. A Functor is a map that takes objects to objects and arrows to arrows in a nice way. A binary functor takes two objects to and object, and two arrows to one arrow in a way that plays nice (commutes) with arrow composition.







Monoidal categories have ordinary composition and some kind of Horizontal composition., putting things side to side







We said monoidal category though. WHat is a monoid? It is a structure with an associative binary operation and an identity object.







What the hell does is mean for a binary functor to be associative? 







What does it mean to be an identity object? Well whenever this object is placed into a slot of the functor, it must do nothing.







Actually I guess neither of these require the associator.   

It turns out to be prdocutive to not require these properties to hold on the nose. There may be some fairly trivial reshuffling necessary to make them work. This reshuffling is a natural isomophism.







One monoidal category dear to our heart is that of Haskell functors.







We can form a kind of pun on these two monoidal categories, Cat and 2-Vect.







2Cat.   

In our case the only object is Hask  

Functors take Hask to Hask  

and natural transformation are parametrically polymorphic   

Compose, Product, and Sum are all binary combinators on functors. And they all form monoidal categories.







Adjunctions can be described in a couple different ways. I don't know how adjunctions could make nearly any fucking sense if you haven't seen Galois Connections, which are basically the same thing but in the Lattice context.







There is an adjunction between   

In string diagrams, adjunctions can be represnted by cups and caps and a particular orientation. 







sequenceA as a tranpose operation / braid.   

sequenceA has the type f g a -> g f a. If I maniuplate this a little to   

Kron f g :-> Kron g f, what do you think this does?  

In terms of   

sequenceA . sequenceA in general does not equal the identity, but in this case it does. If this is the case, it is useful to draw this operation in your string diagram as a braid. Then you do not intuitively think that these two must be equal.







I have my talk to plum for stuff.







Different styles of vectors.







Vectors = Arrays.







Vectors are things that contain numbers. They are a big ole product type







  * (a -> r)
  * [(a,r)]
  * Map a r






Vectors considered as a container over their basis elements - The linear monad







Vectors are representable functors. If you sort of combine (a ->) and [(a,-)] into an opaque f.







Vectors are structs. A perfectly well typed vector, even in C. This vector is statically size. Now, it is perhaps unacceptable to build a 1000 element vector in this manner using anything except some sort of metaprogramming. (CPP?)







struct V3 {x y z}







V3 {V3, V3, V3}







Haskell has better facilities for this (uh huh, DOY). 







Compose V3 V3







Vectors spaces i have loved: v3, v4 (homogenosu, Function vectors (quantum mechanics, the stretched rope, take a picture of a stretched rubber band), quantum field theory.







Symmettric spaces







Occupation number







### Vectors as functions and the double negation translation







a -> Double  

(a -> Double) -> Double covector  

(a -> Double) 







type Dual x = x -> Double   

type T = Dual  

T (X) =   

T T (a -> Double) ~ a -> Double







a -> Double == \f -> f (\g -> )  

to v = \f -> f (\g -> g v)  

from w = w 







from (to v) =  from (\f -> f (\g -> g v)) = (\f -> f (\g -> g v)) $ const 1  

= const 1 (\g -> g v) = 







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







* * *







### 2Vect and the Linear Algebra of Types







The `[a]` type is defined as







[a]=1+b*[a].







If we iterate this we get







[a]=1+b+bb+bbb+bbbb+...







Which is right. A list is all possible sizes of tuples.







We could also solve the equation







$latex [a]=\frac{1}{1-b}$  
The interpretation of this is questionable. It is not entirely obvious what could be the meaning of either type division or type subtraction. This is similar to working with the non-negative integers. It isn't clear what 3 - 4 should mean or 5/3 unless you expand your domain. Or similarly $latex \sqrt(-1)$. There can be a reasonable answer, but there doesn't have to be.







Formal manipulations of expressions of these kinds can still be useful, if the end result that pops out is sensible. This was the historical perspective on the complex numbers. Yeah, they make no sense, but you can derive a real root and then verify it really is a root by going through the fictional intermediary of complex numbers. 







For integers, we're used to there not being division necessarily. We need to include a remainder. For the positive integers, subtraction has a similar answer. If we want to try to divide m by n, we can find divisor d and remainder r such that m = n*d+r, where r is less than n. If we want to subtract n from m, we can find m+r=n+d, where r is nonzero only if d is zero.







Because of the lack of an obvious subtraction operation, types form something akin to a semiring.







For finite types, if the types have the same number of inhabitants, then the types can be put into an isomorphism with each other.







For parameterized types built in this way correspond naturally to polynomials with integer coefficients. We can similarly ask questions like factoring of these types. Is it possible to break a big type into a product of smaller ones.







We should wrap all type variables in a V newtype. We can automatically extract out of it at the end if we like. Then we can typeclass automate canonical form with the appropriate Iso transformations. If we make this typeclass work for any distributive commutative category, then we can also reflect the proof into an initial value. Dagger also. We run it in reverse to get the other direction.







auto @(a+b*c)







rewrite @((x+1)*(y+2))  
You know what. I'm gonna take + and *. Let's do it.







Functor compose is polynomial composition. Kan is functor decomposition?. Consoider (n+) and (m*) functors. The Kan construction may define division and subtraction.













The basic isomorphisms are







Iso' 







Prisms represent inequalities and Lens represent divisibility. type Div = Lens'. type LTE = Prism







Traverse is the "is polynomial in" relation.







Systems of equations and grobner bases. Unification problems hold on the nose. You can have a set of type equalities (a ~ b) that the type checker figures out for you. But one could conceive of a different set of constraints (a ~~ b) that have to hold only up to isomorphism. Then what we have is a system of polynomial equations. The big hammer for solving such things is the technique of Grobner bases. If we had a pile of isomorphisms (corresponding to a set of equations), we can transform it into a better behaved pile.







[https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis](https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis)







What is the point? 1. Ideal membership 2. Quotient Ring constructions 3. Eliminating variables (solving polynomial systems)  








Polynomial division. We can similarly divide a type by another type with remainder. If types divide perfectly, we can have an intrinsic quotient type. The remainder represents the extra elements that we shouldn't be able to represent. 







[https://www.youtube.com/watch?v=YScIPA8RbVE](https://www.youtube.com/watch?v=YScIPA8RbVE)



















There are a couple different representations of vector spaces. My favorite for is simplicity is type Vec b a = [(b,a)] which is the free vector space over a type b with coefficients a. A very similar representation is type Vec b a = (Map b a) or (HashMap b a). The difference between them is some runtime characteristic and typeclass constraints. [(b,a)] needs Eq b, Map needs Ord b and HashMap need Hashable b.  Despite an intrinsic revulsion one might feel representing a vector space in anything except an array (fight it), these all are more or less reasonable sparse formats for vectors.







Another style is the sized Vector which carries along an index that corresponds to the size of your finite space. 







In a different style, as is seen in Kmett's linear library, is to use statically sized Functors. V0, V1, V2, V3, V4 which have very obvious implementations. Then these vector spaces can be combined polynomially/functorially using the kronecker product / direct sum which correspond to functor composition / functor product. This is a reasonable dense vector format. In principle, the compiler has a great deal of information available to it for laying out memory.







The first and third style are connected by the notion of a representable functor, functors that can be tabulated by a table indexed by some type. They represent the same thing if the type `b` is the index type of the functor `f`.







I wrote some blog posts a while back on some of this.







Because types behave roughly like slightly gimped numbers  (semiring) it is reasonable to ask if we can lift linear or tensor algebra to the type level. Yes, we can.







This may be a nice way to arrange building complicated spaces if they are built via a homogenous growth process. An example where this flies is anyon vector spaces. I've previously described using the first free style of vector space how to construct anyon vector spaces. I constrained myself to constructible anyon trees only using GADTs. I think this is the most straightforward approach to building such a thing in a Haskell aesthetic.







  







    
    <code>data VTTT a = VTTT a a - this is the only vector space with 2 ways to achieve it 
    newtype VTTT a = VTTT (V2 a) -- newtype deriving everything
    newtype VTTI a = VTTI a
    newtype VIII a = VIII a 
    newtype VIIT a = VIIT () -- impossible case.
    </code>







  








Stay and Vicary describe a 2-category of encyrpted communcation. Might a GF 2vect be useful here?







I think an argument can be made that this might be a good use of Idris and the like. It is quite painful to do this in Haskell.







https://arxiv.org/pdf/0908.2469.pdf







[https://ncatlab.org/nlab/show/2-vector+space](https://ncatlab.org/nlab/show/2-vector+space)







This is the formalism used in that mathematica anyon package







the tensor product adn direct sum have properties that are very similar to regular mutlpication and addition. distrbutivuty, commutativy, a natural 1 and 0. However these are actually slightly non trivial isomorphisms rather than equaltities.







a 2 dimensional 2Vect, 2Vect2, is a tuple of two vector spaces. 






    
    <code>type 2Vect2 f g a = (f a, g a)
    type 2Vect3 f g h a = (f a, g a, h a)
    -- we may want f and g to be a subset of all possible vector spaces. This is very similar to a direct sum, except we are non specific about f and g?
    -- or at the index level
    -- a transfromation from 2vect2 to 2vect3 is a linear functor
    type family LFunctorG 
       LFunctorG (2Vect2 f g a) = 2Vect3 (c1 f + c2 g) (c3 f + c4 g) (c5 f + c6 g) a
    where c are also vector spaces. functor composition = tensor product.
    -- 2vect2 and 2vect 3 are categires wtih morhpisms given by
    data Morph2 (2Vec2 f g) (2Vect2 h k) = Morph2 (LinOp f h) (LinOp g h)</code>







LFunctor does not have necessarily any particular data associated with it? You can instantiate different forms of the LFunctor. I think the implementations should probably involve a kron of a constant c1 with the given f. That is, the fixed c my depend on the TYPE of f but not it's values. The linearity of the implementation of LFunctorG gives it the commutative functor property with respect to linear operators inside of 2Vect3 and 2Vect2






    
    <code>instance LFunctorG (2Vect2 V2 V7 a) where
       type Out = 2Vect3 (yadaya)
       lfunctorg (2Vect2 x y) = 2Vect3 ((kron c x) `dsum` (kron c y)) yada yada</code>







Maybe LFunctor should be a typeclass?







Then an LNaturalTransformation has . Natural transformations are Morphisms in the target ctaegory (in this case linear operators. from 2Vect3 f g w a -> 2Vect3 h k z a   ) indexed by by objects in the source category. The f g w are the results of applying the coefficients of LFunctorG, and the h k z are the results of applying LFunctorH. The source categroies has vector spaces as objects. NatTrans f g






    
    <code>instance NatTransFG1 f where
       alpha :: 2Vect3
    instance NatTransFG2 g where</code>







  








This may also be related to Preskill's notes version where you can make a kron sum expansion of the given vector space.







We can build a basic version using type level Lists to store our vectors and matrices.







* * *







## String Diagrams and Vectors. Categorical examples in Haskell - 12/2018







Haskell is an interesting place to find examples for category theory concepts. It's also a large part of the reason that I even care about category theory.







String diagrams are a diagrammatic notation to describe monoidal categories.







A monoidal category is a category with some extra structure available. It has some kind of "product" Bifunctor $latex \circtimes : C \times C \rightarrow C$. Being a Biiunctor means that it has a way of mapping a pair of objects into a new object. It also maps a pair of morphisms to morphisms







The Haskell pair (,) is the most obvious but also somewhat confusing example. (a,b) is an object in Hask. (a,b) Is also a paper and pencil notation that one might have tendency to use for $latex Hask \times Hask$. $latex Hask \times Hask$ is not something that will be in a Haskell program because $latex Hask \times Hask$ is not Hask. We are decribing the really obvious transformation that takes an object in $latex Hask \times Hask$ to Hask. The notation is so similar for (a,b) that we can't tell just syntactically which category we are talking about.







String Diagrams are a way to represent Functorial manipulations. The category of Functors.







Bartosz Videos and Articles. My previous link dump.







A restriction of this is the Category of Haskell EndoFunctors (the things in Haskell with the typeclass Functor). We can compose them (Maybe [a]).







Compose f g.







Vectors are also decribed using the language of monoidal categories. The objects in Vect are vector _spaces_ not individual vectors, similar to how objects in Hask are types, not individual values. Morphisms are linear maps between spaces.







A natural tensor product is the tensor product aka Kronecker product. Funny that. In coordinates, the tensor product of two vbectors spaces has indices which are pairs of indices from the two original spaces. The Tensor product can also be described as .







In matrix form, the kronecker product $latex A \otimes B$ is a matrix like looks like space A, except every entry is a matrix from space B rather than a number







Penrose Diagrams are the system when this is applied to tensors.







Vectors are a great example of representable functors. These are functors that are equivalent to a function from some index type. Representable functors are usually some big ol' product type.







Link to Gibbons article.







This gives us an alternative methodology for fixed sized arrays. I find it is more aesthetic and clear to describe the vector space in terms of it's composition rather than in terms of it's size.







data OneDbox







type TwoDBox a = OneDBox (OneDBox a) -- Kron OneDBox OneDBox







type ThreeDBox a = OneDBox (TwoDBox a) -- Kron OneDBox TwoDBox







type Spin = V2







type Kron = Compose







type DSum = Product







You can also just build a integer sized vector this way by using some kind of number system. Using the Boolean expansion of the size, you can write a vector using direct sums and tensor products of 1 and 2 dimensional vector spaces. Or you may choose to use the prime number expansion of the integer to write the vector space as the tensor product of it's prime factors. This, for example, can give you a nice FFT implementation. (Conal Eilliot)







Adjunctions. The adjoint of a vector like functor is the functor that corresponds to its index







Taco compiler?







* * *







### Functor Vector Notes 2/2018







String Diagrams: 2 presetnations composition of functor or a monoidal category left right







BUT Functors form a monoidal category under composition. Also Summation and Product.







We can form some kind of mapping between the Functor_Hask category and the Vector-Kron Category that preserves the monoidal structure







Function Vectors. Vectors as representable functors of their basis.







type Vec a = a -> Float







type CoVec a = Vec a -> Float







The end of a pair of vectors is their dot product (Coend?)







type Dot w v = forall a. (CoVec a, Vec a)







exists a. (CoVec a, Vec a)







There is nothing you can do with such a type except plug them together.







This seems to make a good perpsective







[http://r6.ca/blog/20171010T001746Z.html](http://r6.ca/blog/20171010T001746Z.html)







Also some of the correpsonding comments. One notes that functors are richer because they have composition







Unfortunate? : Identity does go away, neither does Compose. Swap is another higher order Functorial manipulation.







Traverse gives a kind of braiding







Overloading Compose might be able to make Split







Profunctors? They also Compose. I would guess that profunctors are also a monoidal category.







[http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html)







Functor-Oriented Programming.







Ordinary ADT are constructed by custom sum and product data types.







Why though? We could use the Generic Either and Pair? It is nice to give them special more informative names. This can be achieved via ordinary naming like = Left.







Problems: Sometimes you DO want confusing structurally identical things to not typecheck as the same.







What you don't get is the automatic associativity that new data types give you. There is no Either or Pair that is automatically . There is not necessarily a good reason why this couldn't be the case.







If you just add an extra type paremter to make every constructor a functor, you can perform the same manipulations. It is however unfortunate that







You can use Sum and Product of Functors to replciated these ADTS







If you fill the functor parameter with (), there is clear isomorphism between these functor data types and .







The One functorial lifting is to just add a parameter b in a product type.







data Lift a b = Lift a b







So you can build an abstract syntax tree.







I sometimes feel like I would like to enforce that a certain term is exactly one kind of constructor from .







from a Haskell standpoint, explicit coordinate based iteration is very goofy. It smacks of a for loop, which is not idiomatic Haskell. From some theory persepctive, index manipulation of vectors is also somewhat inelgeant. Maybe. But I find indices rather useful.







forall a. (b -> a) -> a is a continuation passing transformation. It is equivlaent to the value b. We can extract b by passing in ```id```. But we don't have the forall a. We pick a fixed field to work in. We're trying to find an equivalence to (b->a) anyhow.







This doesn't work because (b->a)->a is not really a functor in a. Maybe it is a profunctor in a a. There may be some advantage to seperating out these type.







(basis -> field) -> kron







Ordinary vectors are Rerpesetnable functors. The numerical nature of the enclosed values does not matter







The Dual Dual is the same as no dual at all without using the metric. Used Djinn http://www.hedonisticlearning.com/djinn/. This actually has a more general type







\a b -> a (\ c -> c b) :: (((t2 -> t) -> t) -> t1) -> t2 -> t1






    
    f a b = a (\ c -> c b)







The Dual is isomorphic to Id using the metric.







The more restrained implementation is






    
    f a b = a (\ c -> a (\ _ -> c b))







I don't understand how this typechecks.







The opposite transformation is






    
    f a b = b a







which is just flip ($)







These are both natural transformations







(Enum b, Bounded b) => Representable (b ->a) -> a







tabulate = dot







index = codot







I have this backwards. Being dottable should be it's own class, because we want array backed vectors to use their fast dot methods.







instance Enum b Bounded b => Metric (->) b







dot :: (Number a, Monoid a?, Ring a?) => f a -> f a -> a







maybe I should put in the slight extra energy to use the HashMap vector. Is it even better? Well, it doesn't allow duplicates and fast lookup.







Optimization and Linear Algebra, the two big hammers. There is a big intersection in the venn diagram (gradient descent, backprop, conjugate gradient descent, newton's method, linear programming), although not. Maybe this is a silly dichotomy. Graphs is also a big hammer.







Dual is already a type for monoid. Christ.







Piponi on Profunctors







[http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html)







sequenceA + adjunction gives us both possible ways of bending the state.







```exists. a (v1 a, v1 a -> Float)``` This doesn't really force us to do anything.  
Profunctor Composition. Considering Linear Operators to be profunctors in the basis, profunctor composition does correspond to ordinary composition.  
```exists b. (LinOp a b , LinOp b c)```







The tuple  
(a -> i, Matrix_ij , j->b ) is a profunctor in the input and output basis.  
We can make this profunctor Strong and Choice to get direct sum and product.  
so is  
(a->i, Vector) is the analogous construction for vectors.  
(i -> a, Vector) is the dual vector.







Matrix is a profunctor in Vector also. But only in Vector.







(a->n)->(b->n) == Hom(a,b) in our weirdo catgorry. Lift to a new cetgoyr that always carries around unifying extra number info







Index structure of anyons -> Type Matrices. consider as Curried A :: (b -> *) -> (b -> *)






    
    A v 'True = Either(a,v 'True) (b,v 'False)
    A v 'False = Either (c,v 'True) (d, v' False)
    
    







One = Unit







Zero = Void







Two = Bool







EitherFib a b = Tau a | Id b







SumFib a b = Tau a | Id b -- appears in summation epxressions







Const (EitherFib One Zero) :: b -> * is a tau leaf







Polymorphic function on extra leaves for classical f-move.







Tree structure makes Tensor summation easier. Only need product of the form V()_a ()_b which happily bitrs it's tale oproducing another typelvel vector.







A completely imbalanced tree can be done with matrix product using external edge c as selector of matrix.







Can use FibProd that avoids the Voids maybe







Void actually is enumerable







Classical counting? Typelevel catamorphism taking type sum to typeNat sum and prod to prod. Or possibly an enumerate call at value level.







Select braiding via lowest common ancestor. a lens to this position. Gives unique index for braiding operation. The rest of path is known, all Left on left side all right on right side. Bring together, braid, then undo bring together for convenience. Need to use Free or recurive type if we want to automate this process I think.







\c -> [(float,Tau, Id, va, vb )]







cps







\c va vb -> [(float,va Tau, vb Id)]







va and vb are also of this form. The Tau and Id are implicitly being handed to the va and vb.







dense anyons? [(Tree, float) ]







sharing via lambda reference?







hughes list for functor vector. partially applied kron. The abounding functor composition plus attempted sharing smells like Kan. Could be because I know nothing though.







Dependent Types may make type matrix construction more natural. I seem to be attempting the equivalent of the well type Vector Nat sometimes and dumb Vectors other times.







enum :: Bounded a, Enum a => [a]







enum = enumFromTo minBound maxBound







probably error prone and bad. unifies too easily. May not be able to infer type.







maybe do







sum' ::







sum' (Proxy :: Proxy a) = sum fmap v enum







The proxy gives us a bit more type safety







data Space3 = X | Y | Z deriving Enum, Bounded







Huh. This doesn't work







instance (Representable f, Enum Rep f, Bounded Rep f, Num a) => Represetnable (f a) -> a where







tabulate = sum







Linear Functors. Maybe I do have to replicate the hierarchy. Or One could use a free consutrction, like a CoYoneda wrapper. One suspects that one could maniupuplate this coyoneda wrapper on the backend and massage the whole thing into a nicer form. Maybe that makes Dual more self contained also. The dual does contain an implicit summation, which i have claimed requires a exists.







Constrained typeclass problem







[https://stackoverflow.com/questions/12922187/how-does-one-statisfy-a-class-constraint-in-an-instance-of-a-class-that-requires](https://stackoverflow.com/questions/12922187/how-does-one-statisfy-a-class-constraint-in-an-instance-of-a-class-that-requires)







Could enriched category theory based programming language be good fit for quantum programming lang







pattern match = measurement?







enriching with vec gives each hom a vector space. composition is kronecker product? Types of final leaves are objects. Morphisms are vector spaces and 2-morphisms are linear maps between vector spaces.







anyons = types of in out leaves.







extend appending with a bunch of identity operations







associativity is 2-morphism







VecHom c (a,a,a,a,a) for example. Internal structure is not explicit, depends on constructive past. Or maybe it is explicit in (,) ordering? VecHom c (a,(a,a))







idMorph = forall c. Vec c c ~ Complex number (unit of monoidal structure of Vec)







2morph a b c d = Vec a b -> Vec c d







Vec seems like a profunctor. idmorph seems like an end. Also a control category. 2morph is lens like. If Vec is truly a profunctor any lens is a 2morph? Depends if Vec is strong or not. Probably not.







fmove :: Vec a (b,(c,d)) -> Vec a ((b,c)d)







opfmove ::Vec a ((b,c)d) -> Vec a (b,(c,d))







These really are universally quantified. c may unify with an entire subtree.







dual :: Vec a b -> Vec b a







lbraid :: Vec a (b,c) -> Vec a (c,b)







rbraid :: Vec a (b,c) -> Vec a (c,b)







composition is given by fusion.







compose :: Vec a b -> Vec b c -> Vec a c







primvec :: a -> b -> c -> Vec c (b,a)







idprim :: Vec b (Id, b)







idprim' :: Vec Id (b, Dual b)







I do I compose into one position? Can I make a compose that focuses on a leaf or can I give a way to add a bunch of identity operators on the side? Could make an identity tree







The [(tree, complex)] type seems acceptable. Where tree has internal nodes labeled.







maybe \tree -> [(tree, complex)] which looks like a linear operator. composition is given by linear operator composition making it closer to matrix product that kron product actually.







The connection between the type in Vec and the value held could be enforced by a type family.







type family internalStructure :: (()()()) -> internallylabelledtree







For each (,) -> (,label,)







for each final type ->







Utility functions : automatic fmoving based on lowest common ancestor.







Optimization: Interleave tree strcture and vector structure. Keeps simple products expanded.







Do not require internal structure to match external structure.







Be able to switch into array based structures.







g_ij :: (Enum a, Bounded a, Number n) => Vec a n -> Vec a n -> n







g_ij = sum $ map (\x -> directprod v1 v2 (x,x)) enumerate







Heat Equation as example







box x = if 0 < x < 1 then 1 else 0







diff :: Double -> LinOp Double Double Double







diff eps f x = (f (x + eps) - f (x-eps)) / 2 * eps







diff2 eps = (diff eps) . (diff eps)







diffn n eps = diff eps . (diffn n-1 eps)







diffn n eps = iterate (diff eps) !! n







heatprop dt dx f x = f x + dt * (diff2 dx f x)







sol = iterate heatprop box







Relaxation Method







domain :: (Double,Double) -> Bool







type BC2 = (Double, Double) -> Double







localaverage eps g = g (x+eps) + g (x - eps) + g (y - eps) + (g + y + eps) / 4







relax eps bc g x = if (domain x) then bc x else localaverage g x







A similairty transofrmation defines both







s1 LinOp a b c and s2 DualOp a b c







such that (s2 f) (s1 v) = f v (quasi inverses.







If the two spaces are of different size, then not invertible. The opposite way of composing them, should create a projection matrix.)







You can conjugate the metric with these.







You can also conjugate LinOps less obviously







Example of similarity transformation is conversion to finite domain for infinite problem. precomposition y = arctan(x) is in fact a linear operator since the actual field valuers have a linear dependence. The dual integrators get the 1/1+x^2 factor.







class Similarity a b where







s1 :: LinOp a b c







s2 :: DualOp a b c







Interpolation is a simiularity transformation.







s is a phantom type parameter for a Nat describing how many points we broke up the interval into.







data Interval s = Interval Double







data RealLine s = RealLine Double







This makes the analogy better between true finite types.







we can define an enumerarte instance for Interval N.







edot eddot







One way of stating what we want in regards to the infinite space, we don't want to reduce to dot products. We want to perform summation maintaining direct sum structure, which is possible, but using g as a LinOp from Kron space to single space.







g :: LinOp (a,a) () c







liftNum :: Number a => a -> Vec () a -- could make unit forall b, but I prefer ()







liftNum = const a







functional differentiation







Vector differentation







type D x = (x , Vec a -> x)







type D (D x) = (x, Vec a -> D x)







type DF x= (x, Vec a -> )







Gaussian = []







outer :: Dual a c -> Vec b c -> LinOp a b c







outer d v w = smult (d w) v







We need an ordering on the basis. LU and QR are dependent







orthognaliz [Vec a] -> [Vec a] is a reasonable operation







DirectSum is invertible for vectors







class SchurInvertible where







matinv ::







instance Invertible LinOp () () c where







matinv l = const const (1 / l (const 1) ())







perhaos other base cases







instance (SchurInvertible LinOp a c, Invertible LinOp b d) => Invertible LinOp (Either a b) (Either c d)







matinv f = let a,b,c,d = unblock f in







block () () () ()







So create an isomorphism to an Sum decomposition of the requisite type in order to access the invertible insatnce







Bool <-> Either () ()







OR, you can invert iteratively.  
instance arrowInv :: Invertible (LinOp a a), Invertible (LinOp c c) => Invertible (LinOp (Either a c) (Either a c)) where  
inv f = MBlock a b c d = deblock f







Phantom Type parameters on Array Backed Vector type. Nat is Dumb. Use Either Pair calculus to build stuff up







Sized typeclass can use type parameter to statically derive length







which in turn can be used to







Vec (BoxSize,BoxSize,BoxSize)







data BoxSize can be empty







newtype DSum a b = DSum a b







newtype LinOp a b = LinOp a -> b







newtype Kron a b c = Kron (Array (Tuple3 a b c))







SemiRing a SemiRing b, DivisibleRing LinOp a a, DivisibleRing LinOp b b => DivisibleRing LinOp (DSum a b) (DSum a b)







recip f = let a = fst \x -> f DSum x zero







slices are lens. They take out a Dsum







type Conjugate/POVM = LinOp -> LinOp







type Block a d = a d (a->d) (d->a)







The two functions perform conjugation by B C







mul :: a -> (a -> a) using multiplication







f <<< (mul x)







or f <<< (flip mul x) are ways to inject left and right multplication







Thus I think that we can implicitly perform ab dc products we need for multiplication. No maybe not







newb = a b' + b d'







newc = c a' + d c'







new b ... newc = a b' ... c a' +







Right. We need a way to conjugate one from each. That is subtle. shit







what about conjugation with b ... btranspose







Conjugate does possess a natural addition via fmap







but Conjugate does not have a mul instance unless conjugating the same space







Conjugate is also similarity transformation







Enriched Category of POVM? objects - denbsity matrices, Klaus Operators = morphisms and probablistic combination of operators is 2-morphism?







laziness afford us a kind of sparsity.







However using Lazy makes types not match if we pick and choose. Maybe there is no reason to not use lazy







This will have basically the same implentation as MBlock while avoiding the unfortunateness of the LinOp DSum DSum duplication problem







linop = LinOp <<< multvec







rectzero = LinOp const zero







data LinBlock a b = LinBlock (LinOp a a) (LinOp b a) (LinOp a b) (LinOp b b)







blockout :: DSum (LinOp a a) (LinOp b b) -> LinBlock a b







blockout (DSum f g)= LinBlock f rectzero rectzero g







Problem: Does not recurse well







One possibility store B BT C CT as functions







Block a d (a->d) (d->a) () Nope.







CoRoutine based vec







* * *







This making a functor level version of many typeclasses ditrubts me







I can't easily construct matrices or vectors.







Foldable and unfoldable as constructors to and from arrays







Lenses as slices







Function vectors just because they are easier?







AVecs







FreeSemRing







More isomorphisms?







M2 <-> V2 V2







Dual







CKron variants of composition







fillFromIndex f = tabulate (f <<< fromEnum) (\x -> x*x)







Pretty printing







What is the one varaint for? Composition, basically. Only define the one variant for .







Except for Semiring, which I don't have control of







wow. Is there a point to any one instance?







Time-Ordering as a semiring? Doesn't work.







timeorder :: Semiring a => [t->a] -> Free (t ->) a







or [t->a] -> [t]->a







newtype T







timeorder (T x) (T y)







time ordering as symmettrization.







Normal ordering.







Wick's theorem ~ Differentiation







Spin valued field :: space -> M2 Number







Memoization







common subterms identification, dependency graph







Geometric series identification (I think some series acceleration)







split semiring into two classes to avoid deifning mulpticative instances for vectors







Additive







Multiplicative







(Additive, Mutlpilication) => Semiring







Commutative (FreeSemiRing Spin)







commutator Sigmax Sigmay = Mul (Pures 2i) (Sigmaz)







data Spin = PureS Number | Sigx | Sigy | Sigz







--This is headed pure symbolic. I'm not sure that the sommuator could mean anything computationally in other contexts.







Operator algebra... where could this fit in all of this.







DOttable a b c , Dottable a' c d => Dottable (DotComp b d) b d







Dot composition.







DComp is a cetgory







DComp b c = exists a a' c. Dottable a b c => Dottable a' c d => (Tuple a a')







arrowfunctor :: DComp b d -> (->) b d







or







Dottable ((->) a b) a b where







dot = ($)







Dottable a b c => a -> (b -> c)







dot a is the functionizer







Dottable a b c <= Metric a b c







tod :: (b -> c) -> a







memo :: (b->c)->a, summarize, ddot







M2 M2 M2 has a dotr instance but no Metirc







M2 V2 V2 has a metric instance though.







yeah. The dot instance. It is very much something like Arrow or Category. I moved the type parameters out of the type name itself and into a multiparmaeter typeclass. I don't want to have to cast M2 to use with other M2 vs V2. Or do I?







I need an Index.purs?







Do I?







type Two = Boolean







type One = Unit







type Two' = Plus One One







type Zero = Void







type Times a b = Tuple a b







type Plus a b = Either a b







-- use higher product types







type I64 = T4 Two







and so on







Lens as a vector? nooooo... We can FreeSemiRing it, we can







max plus semiring and adjancy matrices.







softmax -> division ring?







{- Maybe want this for the tail recursive version  
go z 16 where  
go z 0 = Tuple (mod z 2) (mod (shr z 1) 2)  
go 0 n = Tuple 0 0  
go z n = Tuple x y where  
Tuple x' y' = go (shr z 2) (n-1)  
x = (mod z 2) + x' * 2  
y = (mod z 4) + y' * 2  
-}



