---
layout: post
title:  "Functor Vector Part 2: Function Vectors"
date:   2017-12-31 19:27:12 -0400
categories: haskell quantum linear
---

## Function Vectors

What is a vector? Is it a thing you can sum and scalar multiply? That is often the starting point in textbooks. Is it a tuple of numbers? A thing you can inner product?

One reasonable operational definition is that it is a thing that you give a basis element and it gives back the component of the vector in this element, in other words a function

``` haskell
type FunVec basis number = basis -> number
```

As functional programmers, this is great news. Vectors are basically functions. We have so many elegant combinators for functions.

Is there a way to convert an ordinary indexed vector into this form? Yes. It is just the function that takes the index and gives the number at that position

```haskell
convert2FunVec v = \i -> v !! i
```

or more tersely

```haskell
convert2FunVec v = flip (!!)
```

and vice versa it is conceivable to perform the opposite, asking a function vector for every basis element and storing them in some container type. More on this later.

We can easily add functions and scalar multiply functions and we have a zero vector.

```
vadd v w = \x -> (v x) + (w x)
smult s w = \x -> s * (w x)
vzero = const 0
```

The direct sum and direct product of function vectors can be also be easily built.

```haskell
directsum :: Vec a c -> Vec b c -> Vec (Either a b) c
directsum = either

directproduct :: (Num c) => Vec a c -> Vec b c -> Vec (a, b) c
directproduct u v = \(x, y) -> (u x) * (v y) 
```


### Dual Vectors

The Dual of vectors are linear valued functions of vectors. They are machines you give vectors and they output numbers. Sometimes dual vectors are called one-forms.

``` haskell
type Dual v number = v -> number  
```

This type unfortunately does not enforce linearity. We are indeed free to square elements if you so wish. Please don't.

Given that vectors are functions, the Dual is an interesting higher-order function

Taking the Dual converts the basis type from contravariant to covariant position. 
Contravariant functors consume their held objects while covariant functors in some sense produce or hold them. 
Every time you cross into the arguments of a higher order function, you flip between contravariant and covariant. Or more mechanically, every time you cross a ```)``` and then an ```->``` going from right to left you flip between contravariant and covariant position. Here are some examples.

```haskell
type Bar = (a->b)->c
type Foo = ((a->b->c)->d)->e->f
```

In type Bar ```a``` and ```c``` are in covariant position, and ```b``` is in contravariant position
In the type Foo, ```f```, ```c``` are in covariant position,  ```a```, ```b```, ```d```, and ```e``` are in contravariant position.

The dual vector will produce basis elements to hand to the vector and then manipulate the produced coefficients linearly. Check out this Phil Freeman talk for more <sup>[1](#freemanprofunctor)</sup>. 

In index notation, a vector is written with upper indices $v^i$ and dual vectors are written with lower indices $w_i$. There is an intriguing connection between the location of these indices (which correspond to our basis types) and the contravariant and covraint nature of the indices.


### Dual Dual ~ Id and the Yoneda Lemma
The word dual implies there ought to be only two things hanging around, and this is true. There is a sense in which the Dual of the Dual gives you back the original thing, like taking the transpose twice. Taking the Dual twice brings the basis back into contravariant position, so it is not insane that there is again a way to pull the whole thing back into the original form.

This is an example of the use of the Yoneda Lemma which states that 
```forall t. (a -> t) -> f t ~ f a```, in this case ```f = Id```.
The hand wavy idea is that if this thing needs to work for all types ```t``` then basically you can only be fmapping under an ```f a``` because there is nowhere else you're gonna get that ```t``` from.

Using this relation we can show that

```forall t. ((a -> t) -> t) -> n ~ (a -> n)```

We can actually derive the equivalence using Djinn.
```doubleDual :: forall t. ((a -> t) -> t) -> n -> (a -> n)
doubledual a b = a (\ c -> c b)```



### Linear Operators
The most straightforward implementation of a linear operator is just as a plain function from vectors to vectors.
```haskell
type LinOp a b c = FunVec a c -> FunVec b c
```

Compared to the Linear monad, it is disappointing that this does not enforce linearity in the slightest, but it is very simple.

Note again that ```b``` is in contravariant position and that ```a``` is in covariant position. In the index analogy, this would like like $A_a^b$

This is ultimately a restricted definition of Linear Operators compared to a matrix. It is tough to see how 

What are the canonical operations we'd like to do with linear operators?

We want to apply them to vectors. Check.
We want to compose them. This is function composition. Check.

But also: 

We want to invert them. ?
We want to find eigenvalues. ?
Other matrix factorizations. ?

It is not entirely clear how to do these, but there are two approahces that come to mind.
On is to tabulate the linear operator back into a matrix and hand it off to a linear algebra package. It is somewhat disappointing, but this is definitely the path of least resistance going forward.
The other possiblility is to use iterative algorithms thet rely only on matrix vector and matrix-matrix products. The algorithms could be written as higher order functions that produce a list containing the iterated results.

Transpose of linear operators: You can apply the metric on each side to turn it into the Dual -> Dual

Linear Operators over Direct Sum or Direct Product spaces are interesting.



There is always the identity matrix which is simply give by the ```id``` function.

The zero matrix is given by ```const (const 0)```

The simple 2x2 block matrix has the type

```haskell
type Block a b c d n = LinOp (Either a b) (Either c d) n
```

We can take the kronecker product of matrices.

Naturality in the basis essentially forces the forms of these. These are very similar to combinators found in the Control.Arrow like ```(***)```.
Maybe I'm wrong, but it seems like the Arrow is being supplanted by the Profunctor in the hearts and minds of Haskellers these days.


```kron :: LinOp a b n -> LinOp c d n -> LinOp (a,c) (b,d) n```

```dsum :: LinOp a b n -> LinOp c d n -> LinOp (Either a c) (Either b d) n```

This is a block matrix with zero matrices as the off diagonals.


We can naturally lift any operator $A$ into an operator that works in a direct product space

```lift a = kron a id ```






### Metrics
A dual vector does not need a defined dot product or metric in order to consume them. What you do need to define a dot product for is converted vectors to dual vectors and vice versa.

The dualizing operator IS the metric.
The metric is an operator that takes two vectors and gives their dot product.
```haskell
type Metric v basis number = v basis number -> v basis number -> number
```

The metric in index notation is $g_{ij}$.

Currying this operation shows that it also can be viewed as an operation that takes a vector and produces a dual vector.
```v -> (v -> number)```
I could just as well write the Metric type as

```haskell
type Metric v basis number = v basis number -> Dual (v basis number) number
```

What this shows if if only use up one of the metric's indices we can convert a vector into a dual vector. $w_j=g_{ij}v^i$

For finite, enumerable types like ```Bool``` it is easy enough to see how we could build a standard metric. We have the ability to probe the entirety of the vector space by holding a list of every possible basis element.

For finite, enumerable types there is a straightforward natural metric

For example 
```haskell
g :: Number a => Metric FunVec Bool a
g v1 v2 = (v1 True) * (v2 True) + (v1 False) * (v2 False)
```


For quasi-infinite basis types like a float (corresponding roughly to functions on the Real domain like $\sin(x)$ and stuff), we need to specify an integration routine. This integration routine is the metric. Dual vectors will have the integration routine already built into them.


## Category Theory & Vectors

So we've explored a bit the idea of using the function itself as a vector type. As part of that, we mentioned that an ordinary array can easily be converted to a function by an indexing function. Is there a way to generalize this for all the other varieties of vectors we could come up with? The answer is yes. The pattern of a container type (functor) that is basically indexable so it is equivalent to some function type over an index is called being a Representable Functor.


### The Function as a Functor

The arrow ```(->)``` is also known as the ```Reader``` functor in Haskell terminology. The function is a functor in its result type. This is the perspective of vectors we will pursue, vectors are functors in their contained numbers.

### Other Vectors can be transformed to Functions.
What about vectors data types that aren't literally function types? Well there is a way to transform back and forth between these vectors and functions.
You can write a function that returns that result of indexing into a vector.
\i -> v !! i = (!!) v
and given a finite basis, you can probe all the values and fill the vector out.

To say that a vector is basically (->) basis is to say that vectors are Representable functors with the Representation type given by the basis. This is a Haskell typeclass that corresponds to an equivlanet concept in category theory.


## Representable Functors and Vectors. 

If a Functor ```f a``` is basically the same thing as the function functor ```b -> a``` for some type ```b```, it is called a representable functor. These are very special functors that inherit lots of properties.

A type family is an advanced Haskell topic, although if you're a brave strong dog, it isn't that scary. Type families are a syntax that let's you define type-level functions: functions that you give a type and they output a type. You could already do this with (List a) for example, but now you can pattern match on the type, letting you decide to do very different things if you're given an Int versus a String.

The Rep type family let's you pattern match to pick different ```b``` for different types.

There is an interesting idea that perhaps Rep should be called Ln (The natural logarithm, let's not use Log. There are already plenty of Log types for recording errors in a file and stuff). In Haskell, there are sum, product, and function types. There is funky algebra for these types. Let's suppose you had a couple finite enums which you took the sums and products of. How do you calculate the number of possible enum values now? It turns out, very aptly, that you translate Sum types into $+$ and Product types into $\times$. For function types, if you think about it ```(a -> b)``` gets counted as $b^a$. This is because you have b possible choices for every value of a that you give the function.
Product types have sum types as their representation type. Just like the log of a product is the sum of the logs of the factors. $\ln(abc) = \ln(a) + \ln(b) + \ln(c)$.  

Vectors are basically big ol' Product types holding many numbers and hence they are represented by a sum type with as many options (index values) as numbers the vector holds. 

A finite type has a natural means

To state that the dual vector is representable is to give a way to convert a covariant to  contravariant functor

```haskell
tabulate :: (Rep f -> a) -> f a
index :: f a -> Rep f -> a
```

In this case ```f a = ((Rep f) -> a) -> a```

```tabulate``` is the upper indexed metric $g^{ij}$ and ```index``` is the lower indexed metric $g_{ij}$

We are truly living in sin from a Haskell perspective. This is a fully indexed formulation of taking the inner product. 


Next Time: Functor Composition as the Kronecker Product, Vectors as functors in other vectors.

## Footnotes



<a name="piponiprofunctor">2</a> [http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html)

<a name="bartoszcoend">1</a>: [https://bartoszmilewski.com/2017/03/29/ends-and-coends/](https://bartoszmilewski.com/2017/03/29/ends-and-coends/)

<a name="freemanprofunctor">1</a>: [https://www.youtube.com/watch?v=OJtGECfksds](https://www.youtube.com/watch?v=OJtGECfksds)


<a name="gibbonsnaperian">1</a>: [https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf)


<a name="piponiyoneda">1</a>: [http://blog.sigfpe.com/2006/11/yoneda-lemma.html](http://blog.sigfpe.com/2006/11/yoneda-lemma.html)

