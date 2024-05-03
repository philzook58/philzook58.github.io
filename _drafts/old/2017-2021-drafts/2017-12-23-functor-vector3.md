---
layout: post
title:  "Functor Vector Part 1: Functors in the Basis"
date:   2017-12-31 19:27:12 -0400
categories: haskell quantum linear
---

There is an interesting interplay between category theory, logic, computer science, topology, and physics. 

Woah. That's heavy, man.

The canonical thought provoker for this is the Rosetta Stone paper by Baez and Stay <sup>[1](#rosettastone)</sup>.
I suppose this entire series is in my meager way emulating the spirit of the Rosetta Stone, making the section on typed lambda calculus more concrete in Haskell.

Vectors are a ubiquitous notion in science and engineering and mastery of them pays off. Vectors are the mathematical language necessary to describe quantum mechanics.

Vectors are almost entirely synonymous with arrays for numerical purposes. (At least they were for me. Maybe you're smarter than I was.)

This is unfortunate and mind closing, similar to saying that programming is synonymous with assembly language. It is indeed true that a vector expressed in an array form will be the fastest on actual computer hardware, but for a sophisticated application the inherent complication requires powerful abstractions in order for mere mortals to be able to grapple with the problem.

WARNING: This article is NOT about using high performance vectors of this type. For that I forward you to the libraries vector, hmatrix, accelerate, and repa.

I am giving myself the leeway to not worry about performance until much later in the series and frankly it is not my primary concern.

Given that I am explicitly ignoring performance, fully demonstrating that I am an out of touch functional programmer that doesn't work on anything real, why should you still give a shit what I have to say?

1. Vectors make for great examples for Haskell and category theory topics. It may be illuminating to read on.
2. For BIG vectors though, living in Kron-land, you have the elbow room for elegance, in fact you NEED it. The vectors here can get so big that naive array based approaches will take the lifetime of the universe to compute a dot product.
3. I think it's all kind of neat. Maybe you will too.

So that said, let's go on a journey that touches almost every Haskell concept I know about. Wheee!!!!

Please contact me with any suggestions. This article will forever be a work in progress.


## Baby Bear, Momma Bear, and Papa Bear Vectors

I'd like to sketch an important conceptual classification between different vector spaces.

The way I see it, there are three broad classes of numerical vectors, classified basically by their size. One can talk about the asymptotic size of vector spaces in terms of some natural parameter, similarly to how one classifies the complexity of algorithms. 

There are baby vectors, vectors of a constant size $O(1)$. These are the 2,3, and 4 dimensional vectors that are intensely useful for geometry and physics and the first ones you usually learn. These are the vectors of displacement or rotations, forces and momentums. These kinds of vectors are pretty intuitive (they are little arrows we can draw), have great visualizations, and very interesting specialized techniques like Geometric Algebra or quaternions.

The next level up are the medium vectors, polynomial in size $O(n^d)$. The vectors represent classical fields in the physics sense of the word, like displacement fields or the electromagnetc field. They have a couple numbers for every point in a discretized space. So $n$ is the number of lattice points in one direction and $d$ is the dimensionality for example. These are the vectors you use when you are doing finite element simulations for simulating the flexing of a plane wing or fluid flow around a dog and are the vectors for which the typical applications of numerical linear algebra lie. Another exmaple of vectors of this size is noisy collected data that you want to perform a least squares fit on. Basically, almost everything in commonplace engineering and science falls into this category that isn't a use of baby vectors.

The BIG vectors are the vectors that represent many-body quantum mechanics, quantum field theory or similarly the probability distributions of many correlated variables. These Mondo vectors grow exponentially $O(2^n)$ in the problem size, where n may be the number of particles or number of random variables. The Kronecker product is of paramount importance here, giving you a method to docompose these vectors in terms of simpler, smaller pieces. 

The ultimate goal of this series is to ascend a sequence of abstraction to get a good handle on these BIG vectors and a focus on the Kronecker product.


## Vectors as Functors on the Basis Type and the Linear Monad

Functors are a container-like pattern used often in Haskell. This series will examine three perspectives on how to encode vector-like structure in Haskell: As Functors on the basis, as functors on the scalars, and as functors on vectors themselves.

For simplistic purposes, a simple to use Haskell representation of a vector is a keyed list, which is often used when when doesn't want to deal with the extra mental overhead of a full HashMap dictionary.

``` haskell
newtype LVec number basis = LVec {runLVec :: [(basis,number)]}
```

I consistently feel a pull to abstract further from this type, but it is so convenient, and it is built in terms of some of the most basic Haskell constructs, pairs and lists. Let us use this type as our starting point.

We can easily define vector addition and scalar multiplication for this data type.
```haskell
vadd = (++)
smult s = LVec . fmap (\(n,b) -> (s * n, b)) . runLVec
```

It is a touch goofy that we don't collect terms of the same basis element under addition. This would happen automatically if we were to use HashMaps, which is a nice feature of them.

There are two choices for what we want this type to be a functor in, and either are useful, however the choice we make at this time is a functor in the basis type. What we have then is the Free Vector space over the basis.

``` haskell
instance Functor (LVec n) where
	fmap f = LVec . fmap (\(n,b) -> (n, f b)) . runLVec 
```

The Functor instance allows us to fmap functions on the basis to linear extensions. These are basically permutation matrices.

### Shadows of the Monoidal Categories to Come

It is cute to note that the direct product and direct sum vector are easy to express for this type and in fact for any type parametized on it's basis. The new basis for the direct product is the product type of the old basis types and the basis for the direct sum is the sum type of the old basis types.

``` haskell
directProd :: forall a b. (LVec a f, LVec b f) -> LVec (a,b) f
directSum :: forall a b. (LVec a f, LVec b f) -> LVec (Either a b) f
```


### Linear Monad
One wants to enforce that vectors are to only be acted upon linearly. One can achieve this through a monad pattern, similar to how the monad pattern protects stateful code from leaking into pure code.

I do not know that Piponi<sup>[2](#piponi1)</sup> invented this concept, in fact I think he did not, but his excellent blog articles certainly popularize it.

In order to do this, one has to consider the Vector to be a Functor over its basis.

The monad pattern basically redefines function composition `(.)` to `(=>=)` and function application `($)` to `(>>=)` to reduce repetitive pipework that occurs in some contexts. For possible error throwing code, it pipes the errors through and aborts if one gets thrown. For partial functions, the Maybe monad aborts if any of them fail. The Reader monad threads a static configuration that everyone needs throughout a computation. The State monad threads a changing state as an extra input and output in every function.

Another perspective is that the type signature `a -> m b` should be viewed as `a -m> b`, with the `m` associated more with the arrow itself than the result. What we want is weird arrows that act only linearly `-l>` rather than the ordinary Haskell arrows `->` that are more general.

With those preliminaries, Let us suggest that the type signature for a linear operator is:

``` haskell
type LinOp = basis -> LVec number basis
```


One way to define a linear map is to define it's action on the basis elements. The entire linear map is then defined uniquely by demanding linearity. $A(a \hat{e}_1 + b \hat{e}_2)=a A\hat{e}_1 + b A \hat{e}_2$ This is very common.
The repetitive pipework that this monad abstracts over is the breaking up of a vector into it's basis elements, using the definition of the linear operator on those, then multiplying by the component of that basis elements and summing the entire result.


``` haskell
instance (Num n) => Monad (LVec n) where
   return e1 = LVec [(1, e1)]
   x >>= f =  LVec $ concatMap (\(n,b)-> runLVec (smult n (f b))) $ runLVec x
```

An alternative specification of the monad involes defining ```join :: m (m a) -> m a``` which compresses two layers of the monad structure to one. In this case, that just distributes a scalar multiplication over a vector $c(a \hat{e}_1 + b \hat{e}_2)=ca \hat{e}_1 + cb \hat{e}_2$


Next Time:
Function Vectors: Vectors as functors over the number

## Footnotes

<a name="rosettastone">1</a>: [https://arxiv.org/abs/0903.0340](https://arxiv.org/abs/0903.0340)

<a name="piponi1">2</a> [http://blog.sigfpe.com/2007/03/monads-vector-spaces-and-quantum.html](http://blog.sigfpe.com/2007/03/monads-vector-spaces-and-quantum.html)



