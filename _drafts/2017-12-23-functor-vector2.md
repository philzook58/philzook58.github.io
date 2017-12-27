---
layout: post
title:  "Functor Vector: Let's Do Some Linear Algebra in Haskell"
date:   2017-12-21 19:27:12 -0400
categories: haskell quantum linear
---



There is an interesting interplay between category theory, logic, computer science, topology, and physics. 

Woah. That's heavy, man.

The canonical thought provoker for this is the Rosetta Stone paper by Baez and Stay <sup>[1](#rosettastone)</sup>.
I suppose this entire article is in my meager way emulating the spirit of the Rosetta Stone, making the section on typed lambda calculus more concrete in Haskell.

Vectors are a ubiquitous notion in science and engineering and mastery of them pays off. Vectors are the mathemetical language necessary to describe quantum mechanics.

## Baby Bear, Momma Bear, and Papa Bear Vectors

The way I see it, there are three broad classes of numerical vectors, classified basically by their size. One can talk about the asymptotic size of vector spaces in terms of some natural parameter, similarly to how one classifies the complexity of algorithms. The baby vectors are , the medium are polynomial $O(n^c)$ in some sense of a natural parameter n, and the big vectors are .

There are baby vectors, the 2,3, and 4 dimensional vectors that are intensely useful for geometry and physics, vectors of a constant size $O(1)$. These are the vectors of displacement or rotations, forces and momentums. These kinds of vectors are pretty intuitive (they are little arrows we can draw), have great visualizations, and very interesting specialized techniques like Geometric Algebra or quaternions.

The next level up are the medium vectors, polynomial in size $O(n^d)$. The vectors represent fields in the physics sense of the word like displacement fields or the electromagnetc field. They have a couple numbers for every point in a discretized space, or they might be the vectors of some data you have collected and which you want to perform a least squares fit on. So $n$ is the number of lattice points in one direction and $d$ is the dimensionality for example. These are the vectors you use when you are doing finite element simulations for simulating the flexing of a plane wing or fluid flow around a dog and are the vectors for which the typical applications of numerical linear algebra lie.


The BIG vectors are the vectors that represent many-body quantum mechanics, quantum field theory or similarly the probability distributions of many correlated variables. These mondo vectors grow exponentially $O(2^n)$ in the problem size, where n may be the number of particles for example. The Kronecker product is of paramount importance here, giving you a method to docompose these vectors in terms of simpler pieces. These vectors 


The kinds of vectors that I leave out of my classification are truly infinitely sized vectors. Legit non-discretized infinite function spaces live here for example. These vectors basically have to be treated by discretization or symbolic means and are outside the domain of discussion here (although I would be ecstatic if we found a proper abstraction in Haskell that includes these as well).


Vectors are almost entirely synonymous with arrays for numerical purposes. This is unfortunate and mind closing, similar to saying that programming is only assembly language. It is indeed true that a vector expressed in an array form will be the fastest on actual computer hardware, but for a sophisticated application the inherent complication requires powerful abstractions in order for mere mortals to be able to grapple with the problem.

WARNING: This article is NOT about using high performance vectors of this type. For that I forward you to the libraries vector, hmatrix, accelerate, and repa.

The array based vector is the maximum performance (for dense vectors) with the least expressivity. You really have to twist your mind into their terms, always using integers as your basis.

For baby vectors, it often doesn't matter what you do. Computers are so goddamn fast.
For crunching millions of baby vectors, sure optimize the hell out of it. Go into assembly if you want.

For medium vectors, arrays are basically the best choice.

For BIG vectors though, living in Kron-land, you have the elbow room for elegance, in fact you NEED it. The vectors here can get so big that naive array based approaches will take the lifetime of the universe to compute a dot product.

There are a number of alternative representations of vectors on a computer.




Functors are a container-like pattern used often in Haskell. This article will examine three perspectives on how to encode vector-like structure in Haskell: As Functors on the basis, as functors on the scalars, and as functors on vectors themselves.

This article is a message in a bottle. I hope to receive feedback and suggestions on how to take the ideas enclosed further.

So let's go on a journey that touches almost every Haskell concept I know about. Wheee!!!!




## Vectors as Functors on the Basis Type and the Linear Monad

For simplistic purposes, a simple to use Haskell representation of a vector is a keyed list, which is often used when when doesn't want to deal with the extra mental overhead of a full HashMap dictionary.

``` haskell
newtype LVec number basis = LVec {runLVec :: [(basis,number)]}. 
```

I consistently feel a pull to abstract further from this type, but it is so convenient, and it is built in terms of some of the most basic Haskell constructs, pairs and lists. Let us use this type as our starting point.

We can easily define vector addition and scalar multiplication for this data type.
```haskell
vadd = ++
smult s v = fmap (\(b,n) -> (b, s * n)) v
```

There are two choices for what we want this type to be a functor in, and either are useful, however the choice we make at this time is a functor in the basis type. What we have then is the Free Vector space over the basis.

``` haskell
instance Functor (LVec n) where
	fmap f = LVec . fmap (\(b,n) -> (f b, n)) . runLVec 
```

The Functor instance allows us to fmap functions on the basis to linear extensions. These are basically permutation matrices.

### Shadows of the monoidal categories to come

It is cute to note that the direct product and direct sum vector are easy to express for this type. The new basis for the direct product is the product type of the old basis types and the basis for the direct sum is the sum type of the old basis types.

``` haskell
directProd :: forall a b. (LVec a f, LVec b f) -> LVec (a,b) f
directSum :: forall a b. (LVec a f, LVec b f) -> LVec (Either a b) f
```
 
There is also an encoding of the numbers themselves

``` haskell
vectifyNum :: f -> LVec () f
unVectify:: LVec () f -> f
```


### Linear Monad
One wants to enforce that vectors are to only be acted upon linearly. One can achieve this through a monad pattern, similar to how the monad pattern protects stateful code from leaking into pure code.

I do not know that Piponi invented this concept, in fact I think he did not, but his execellent blog articles certainly popularize it.

In order to do this, one has to consider the Vector to be a Functor over its basis.

The monad pattern basically redefines function composition `(.)` to `(=>=)` and function application `($)` to `(>>=)` to reduce repetitive pipework that occurs in some contexts. For possible error throwing code, it pipes the errors through and aborts if one gets thrown. For partial functions, the Maybe monad aborts if any of them fail. The Reader monad threads a static configuration that everyone needs throughout a computation. The State monad threads a changing state as an extra input and output in every function.

Another perspective is that the type signature `a -> m b` should be viewed as `a -m> b`, with the `m` associated more with the arrow itself than the result. What we want is weird arrows that act only linearly `-l>` rather than the ordinary Haskell arrows `->` that are more general.

``` haskell
type LinOp = basis -> LVec basis number
```


One way to define a linear map is to define it's action on the basis elements. The entire linear map is then defined uniquely by demanding linearity. $A(a \hat{e}_1 + b \hat{e}_2)=a A\hat{e}_1 + b A \hat{e}_2$ This is very common.
The repetitive pipework that this monad abstracts over is the breaking up of a vector into it's basis elements, using the definition of the linear operator on those, then multiplying by the component of that basis elements and summing the entire result.


``` haskell
instance (Num n) => Monad (Vec n) where
   pure e1 = Vec [(1, e1)]
   join = Vec . concatmap (\(b,n) -> fmap (smult n) b) . runVec
   v >>= a = 
```

An alternative specification of the monad involes defining ```join :: m (m a) -> m a``` which compresses two layers of the monad structure to one. In this case, that just distributes a scalar multiplication over a vector $c(a \hat{e}_1 + b \hat{e}_2)=ca \hat{e}_1 + cb \hat{e}_2$

## Function Vectors, Functors over the Numbers

What is a vector? One operational definition is that it is a thing that you give a basis element and it gives back the component of the vector in this element, in other words a function
``` haskell
type FunVec basis number = Num number => basis -> number
```
As functional programmers, this is great news. Vectors are basically functions. We have so many elegant combinators for functions.

To say that a vector is basically (->) basis is to say that vectors are Represetnable functors with the Representation type given by the basis.

### Dual Vectors

The Dual of vectors are linear valued functions of vectors. 

``` haskell
type Dual v number = v -> number  
```

This is an interesting higher-order function given that vectors are functions.
It converts the basis from contravariant to covaraint position. Check out this Phil Freeman talk for more. Every time you cross into the arguments of a higher order function, you flip between contravariant and covariant. Or more mechanically, every time you cross a ) and then an -> going from right to left you flip.
Contravariant functors consume their arguments while covariant functors in some sense produce them. In this case the dual vector will produce basis elements to hand to the vector and then manipulate the produced coefficients linearly.

It's interesting that the dual of the dual converts back to contravaraint position. 

We see here a tantalizing connection between the covariant and contravariant notion in Functors and the same words used in vector context.

There is a sensible manner in which the Dual Dual v is isomorphic to v itself.


The dualizing operator IS the metric.
The metric is an operator that takes two vectors and gives their dot product.
v -> v -> number
Currying this operation shows that it also can be viewed as an operation that takes a vector and produces a dual vector.
v -> (v -> number)

For finite enumerable types there is a straightforward natural metric
For quasi-infinite types like a float, we need to specify an integration routine. This is the metric. Dual vectors have the integration routine already built into them.


## Category Theory & Vectors

A Category is a set of objects and morphisms. One perspective is that Category theory is a simple formalized theory of functions. You get many of the important properties of functions without looking deeply into their implementation. Functions can be composed if one's codomain matches the other's domain. Certain ways of composing functions may be 

The resource that I learned basically everything I know about category theory is Bartosz Milewski's Category Theory for Programmer's, which I cannot reccomend enough. 
The category of Sets 

The category of Posets is an interesting one.
The category of inequalities. You can compose inequalities. Functors are inequality preserving maps, in other words mono

The category that one discusses the most in the context of haskell is the category where types are objects and functions are the morphisms. This is pretty dang similar to Set. The objects are these things with complicated sturcture but we avaoid looking at the internal structure. We usually can't and don't want to know at compile time if an Int is exactly 3. We want to be able to put in different Ints at runtime and have the thing still work.

I think there are a couple of obvious choices of how one might want to  

There is a Functor connecting the Category of bases to the Category of Vectors.

There is some convenience to being able to map functions between basis labels to functions changing vectors. For example, a simple renaming of the basis becomes simple, or in the context of quantum computing, a classical reversible computation can be mapped directly up to the quantum state.

There is a split brained perspective on most topics in Haskell. Ultimately, Haskell does compile into machine runnable code, so there is an imperative translation of everything it does. On the other hand, there are very abstract and mathematical perspective. The Haskell community by and large does not emphasize the machine aspect. This is not the aspect that makes Haskell unique, and it constrains your mind to thinking in the old ways, ways that are accidents of the engineering realities and compromises of real processor architectures.

Functors are types that are containers of other types. They may hold one or more different copies of their inner types. fmap is a generic function. By its type signature, it cannot reach into and see anything about the object being held, it can only apply the function given.

On the other hand, Functors are a mainfestation of the category theoretical functor. This functor is a mapping between categories, mapping objects to objects and morphisms to morphisms such that it plays nice with the composition of morphisms, i.e. it does not matter whether the composition occurs before or after the mapping.
parametric type variables are basically a systematic way of treating pointers. How is it possilbe that the function ```id :: forall a. a -> a``` could possibly work for every type a? It is because a is basically a pointer reference and pointers are a uniform description of all possible types. All pointers are 64-bit integers referring to some spot in memory. Later on in your Haskell learns, you find out about other Kinds than \*, like unboxed types. These are not compatible with the types of \* because they are not pointer references and can't be treated the same way.


Natural transformations are mappings between functors. 
Natural transformations are functions of the form 
```type Nat f g = forall a. f a -> g a```
From the container persepctive, these are functions that can only rearrange the container structure and not touch the contained objects. They can copy or discard objects.
Like smushing a ```Tree a``` into a ```List a``` for example.
If you ever see a bare type parameter not in a functor, mentally add an ```Identity``` to the front of it.

Limits are objects of type ```forall a. f a```. Since they need to work for any ```a```, they won't have one in there. For example ```Nothing``` is a value ```forall a. Maybe a``` and ```[]``` is a value of ```forall a. [a]```


## Representable Functors and Vectors. 

There is a pattern with a name in category theory. If a Functor ```f a``` is basically the same thing as the function functor ```b -> a``` (the Reader functor) for some type ```b```, it is called a representable functor. These are very special functors that inherit lots of properties.

A type family is an advanced Haskell topic, although if you're a brave strong dog, it isn't that scary. Type families are a syntax that let's you define type-level functions: functions that you give a type and they output a type. You could already do this with (List a) for example, but now you can pattern match on the type, letting you decide to do very different things if you're given an Int versus a String.

The Rep type family let's you 
There is an interesting idea that perhaps Rep should be called Ln (The natural logarithm, let's not use Log. There are already plenty of Log types for recording errors in a file and stuff). In Haskell, there are sum, product, and function types. There is funky algebra for these types. Let's suppose you had a couple finite enums which you took the sums and products of. How do you calculate the number of possible enum values now? It turns out, very aptly, that you translate Sum types into $+$ and Product types into $\times$. For function types, if you think about it ```(a -> b)``` gets counted as $b^a$. This is because you have b possible choices for every value of a that you give the function.
Product types have sum types as their representation type. Just like the log of a product is the sum of the logs of the factors. $\ln(abc) = \ln(a) + \ln(b) + \ln(c)$.  

Vectors are basically Product types holding many numbers.

## The Kronecker Product
From the perspective of the basis, this densification operation is actually a natural transformation. For any basis we can densify the product of two vectors into 
``` haskell
densify :: forall a b. (Vec a f, Vec b f) -> Vec (a,b) f
```
densification is something to be avoided. Every time you densify your space requirements explode.
What one can do is create a new vector ```Vec (Vec a f, Vec b f) f``` and pray to god.


This doesn't feel much like a functor in Haskell.


Implanting C as a 1-dimensional vector space. This is the unit object
``` haskell
unit :: Vec () f
```

vassoc is directly inherited from the associativty of the tuples
```
vassoc :: forall a b c. Vec ((a,b),c) f -> Vec (a,(b,c)) f 
vassoc = fmap assoc
```





### String Diagrams for the Kronecker Product

TODO: Graphics for all of these.

In multidimensional linear algebra, the indices can get out of control. In General relativity, there are a ton

There are also a ton of indices flying around in quantum field theory. A very mathematical perspective on Feynman Diagrams is that they are representating a very complicated multilinear expression with indices flying all over the place. To be perfectly honest, although I think it is clear that something like this is going on, I do not really know how to nail down satisfactorily what vector spaces we're talking about despite having tried for years. The identical particle statistics in partiuclar really fuck up the clarity of the situation.



It is the fact that in many situations there are corresponding input and output indices that makes Einstein summation convention work. If you ever seen two indices it is understood that you should sum over them.

It is conveneint to represent a matrix as a little box. A matrix has an input index and an output index. When you apply a matrix, you sum over the input index (summing columns)
Penrose Notation

We'll take the convention of going from the bottom to the top. Two baoxes stacked represents the matrix product of those two boxes.

Boxes can span multiple strings. The boxes are the ones that are going to screw up the Kronecker factorized nature of state. Potential energies are an example of these, or entangling quantum gates.

Boxes and lines put next to each other horizontally implies a krocker product between them. THe string notation reflects that the kronkecer product is associative. there is no way to tell from a diagram in which order you performed the products.

When lines are connected  between boxes. That implies a summation.
A straight line represents and identity matrix. The nature of the string notation makes it ambiguous whether you intended

You can encapsulate products of matrices into their own opaque box, or collect up a bunch of strings into a thick string. This is the power of abstraction, letting you box things up.

In some cases, there may be special boxes that you may wish to denote with special notation. Equations that you can use are reflected in manipulations you can perform on the string diagrams.

You can form cups and caps. The caps represent performing an inner product between those two vector lines. There are now less indices that before. Cups are a bit more peculiar. They correspond to kroneckering the metric into the state. This can be useful, for example for representing a maximally entangled pair of states in quantum information.


###Monoidal Categories

Monoidal categories are categories with some special structure. They possess a couple of associated functor and natural transformations that have to obey certain laws.
They are a generalization of the structure that appears in vector spaces under the kronecker product. They require a densify operator (which under the right perspective is a functor. This isvery confusing from the Haskell point of view) called the tensor product.

The associativity of the kronecker product translates to 

What is very interesting though is that if you look at the list of monoidal categories, The category of functors is on there, with morphisms given by natrual transformations. The tensor product is functor composition.


## String Diagrams for Functors and Natural Transformations.

<sup>[1](#stringhaskell)</sup>

Functors form a monoidal category with the tensor product given by composition.


### Kan Extensions
Maybe. If I ever understand these and if they are useful.

### Maybe Ends and CoEnds
If I every understand these and they actually help. There may, ideally, be a connection actual summation of indices.

## Functor Vector

So, here is the flash of insight. Can we unify the notion of String Diagrams for Functor and Strings diagrams for the Kroncker Product concretely in Haskell?

Yes, I think so.

We can do that by changing our earlier focus on the interplay etween the vector and it's basis and instead on focusing on the kroncker product.

The functor vector paradigm is that a vector is a functor 
data V a
where a is a type parameter where we intend to place the other functors.

Vectors are Functors.
Matrices are Natural Transformations. 
The Kronecker Product is Functor composition.
The Direct Sum is Functor Product.
Vector Summation is perhaps 

Because of the polymorphic nature of the type, you cannot affect vector deeper in the



A vector made of many kroncker products is represented by a functor made by the composition of many functors.

You decided how deep into the indices you want to go with  the number of fmaps you compose a la the Lens library or Semantic Editor Combinators.

```haskell
fmap . fmap . fmap
```



Swapping the order of lines is implemented by sequenceA :: t (s a) -> s (t a).

Swapping is pretty easy since all of them are implemented by product vectors.
Things get funky though when the are index by non sum types. i.e. trees. i.e. anyons.
How do you enumerate the number of indices? Nabc. Counting is non-trivial. Use default 

### Recovering Ordinary Vectors with Unit ()

### The Scalar Functor
Any monoid can be lifted to a monad.

This is already in base.

```Monoid a => Monad ((,) a)```

So

```haskell
type Scalar n a = (Product n , a)
```

Scalar is a Functor and Monad in ```a``` already with ```join``` given by the monoidal product ```mappend```.

### Adjunctions
The representable nature of vectors gets lifted into the notion that functor vectors are the right adjoint of their index functors.

One way of defining an adjunction is as an isomorphism between type

L a -> b
and 
a -> R b

wintessed by the implementation 


leftAdjunct :: (f a -> b) -> a -> u b
rightAdjunct :: (a -> u b) -> f a -> b

The implementation should obey these laws.
leftAdjunct . rightAdjunt = id
rightAdjunct . leftAdjunct = id 

An adjunctions

unit :: a -> u (f a)
counit :: f (u a) -> a

Ind Bool (Spin a) -> a
a -> Spin (Ind Bool a)

It is mentioned that the right adjoint has to be representable because in Haskell the adjunction laws make L () the representation type of R.

What we can do is lift our idea of a functor as representable to the new Functor Vector idea.
Instead of having a Rep type, instead we define a Left Adjunct, which is going to beasically be the same thing as the Rep type except with a type parameter avialble for functorial composition.


The index functor 
data ind_V a 
has a type parameter for the slot where the rest of the index structure will go.
```haskell
type Bit a = Either a a
data Bit a = Zero a | One a
data Bit = Zero | One
type Lift f a = (f, a) 
type Lift = (,)
type Ind = Lift
type IndB = Ind Bool -- This is the index functor to spin or qubit
type IndB' a = Ind Bool (Scalar Float a)  
```

### Lifting Piponi's LinOps

Ind a b -> Ind a (Scalar b)

### Functor Oriented Programming

I do not know if I am accurately reflecting the original authors intent.
<sup>[1](#functooriented)</sup>

In recursion schemes, it is an essential trick to put a type parameter where you would put the recursive call to yourself. <sup>[1](#recursionschemes)</sup>

### Fix & Free



Data Types a la Carte does something similar. you can split a DSL up into much smaller combinable pieces. Part of the essential trick there 

This is the type level version of the fix combinator. The fix combinator is very confusing. It does not calculate the fixed point in a numerical sense. It calculates the fixed point in a funky domain theoretic sense.

It does compute the fixed point of a function if you add in a termination condition.

fix let's you convert a function to a value. Very weird.

Free let's you have arbitrary qubits.


## Sharing and BDDs

With a let construction you can share all the pieces. This let's you build the kronkecker product very efificently. Unfortunately, even indexing in with fmap and applying an id will destroy this shared structure, making the thing explode.

``` haskell
fmap . fmap . fmap id
```

make Vacuum graphs. The heap thing

### Tying The Knot

### Explicit Sharing

Data.Reify


The Binary Decision Diagrams is a really super cool data structure. It is a way of representing arbitrary mutiple bit functions that if you are both smart and lucky can just shred through impossible seeming questions and computations.
if you have a small BDD of your question, you can answer SAT questions no prob. You can even easily count SAT
However, there are some functions for which no small BDD exists. bitwsie multiplication is evidently in this class, which makes sense because otherwise factorization would be easily sovlable via a BDD method.

## Further Work

I'd love to know what Thorsten Altenkirch was talking about Kan Extensions in this video

Can we make ends and coends correspond somehow to index contraction?


## Who am I

As a graduate student I studied the Fractional Quantum Hall Effect, states of matter that exist in very, very cold semiconductor samples which possess peculiar particles called anyons. Describing the quantum state of a collection of anyons is somewhat obscurely expressed in the language of category theory<sup>[1](#kitaev1)</sup>. This is really what let me to the start of my Haskell, functional programming, and logic journey.

I've spent some quality time with numpy, an array library for python. It really is a very powerful, very useful library with awesome abstractions. However, I think MONDO vectors fall outside of its domain of use.


## Footnotes

<a name="kitaev1">1</a>: https://arxiv.org/abs/cond-mat/0506438

<a name="recursionschemes">1</a>: http://blog.sumtypeofway.com/

<a name="functororiented">1</a>: http://r6.ca/blog/20171010T001746Z.html

<a name="rosettastone">1</a>: https://arxiv.org/abs/0903.0340

<a name="naperian">1</a>: https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf & https://www.youtube.com/watch?v=D1sT0xNrHIQ

<a name="stringhaskell">1</a>: https://parametricity.com/posts/2015-07-18-braids.html

