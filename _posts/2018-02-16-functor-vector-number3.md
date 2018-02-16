---
layout: post
title:  "Functor Vector Part 2: Function Vectors"
date:   2018-2-16 12:27:12 -0400
categories: haskell quantum linear
---

An apologetic warning: I'm not sure this all compiles without adjustment. I've been churning on this too long and my mind has wandered onto other things, so I'm just gonna get it out there.

Check out Ed Kmett's Linear, Conal Elliott's Vector-spaces, and Gibbons' Naperian Functors for more in this vague line (although done better maybe)

## Function Vectors

What is a vector? Is it a thing you can sum and scalar multiply? That is often the starting point in textbooks. Is it a tuple of numbers? A thing you can inner product?

One reasonable operational definition is that it is a thing that you give a basis element and it gives back the component of the vector in this element, in other words a function

``` haskell
type Vec basis number = basis -> number
```

As functional programmers, this is great news. Vectors are basically functions. We have so many elegant combinators for functions.

Is there a way to convert an ordinary indexed vector into this form? Yes. It is just the function that takes the index and gives the number at that position

```haskell
convert2Vec v = \i -> v !! i
```

or more tersely

```haskell
convert2Vec v = flip (!!)
```

and vice versa it is conceivable to perform the opposite, asking a function vector for every basis element and storing them in some container type. More on this in a bit.

We can easily add functions and scalar multiply functions and we have a zero vector.

```
vadd v w = \x -> (v x) + (w x)
smult s w = \x -> s * (w x)
vzero = const 0
```

The direct sum and direct product of function vectors can be also be easily built, which I think is quite cool.

```haskell
directsum :: Vec a c -> Vec b c -> Vec (Either a b) c
directsum = either

directproduct :: (Num c) => Vec a c -> Vec b c -> Vec (a, b) c
directproduct u v = \(x, y) -> (u x) * (v y) 
```


### Representable Functors
What about vectors data types that aren't literally function types? Well there is a way to transform back and forth between these vectors and functions.

To say that a vector-like thing is basically ```(->) basis``` is to say that vectors are Representable functors with the Representation type given by the basis. These are very special functors that inherit lots of properties.

There is an interesting idea that perhaps Rep should be called Ln. In Haskell, there are sum, product, and function types. There is funky algebra for these types. Let's suppose you had a couple finite enums which you took the sums and products of. How do you calculate the number of possible enum values now? It turns out, very aptly, that you translate Sum types into $+$ and Product types into $\times$. For function types, if you think about it ```(a -> b)``` gets counted as $b^a$. This is because you have b possible choices for every value of a that you give the function.
Product types have sum types as their representation type. Just like the log of a product is the sum of the logs of the factors. $\ln(abc) = \ln(a) + \ln(b) + \ln(c)$.  

Vectors are basically big ol' Product types holding many numbers and hence they are represented by a sum type with as many options (index values) as numbers the vector holds. 

### Dual Vectors

The Dual of vectors are linear valued functions of vectors. Mathematicians freak the hell out about dual vectors, so let's give them the benefit of the doubt and take a look. They are machines you give vectors and they output numbers. Sometimes dual vectors are called one-forms. 

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

We can actually derive the equivalence using Djinn, a thingy that derives implementations from type signatures sometimes.
http://www.hedonisticlearning.com/djinn/
```haskell
doubleDual :: forall t. (((a -> t) -> t) -> n) -> (a -> n)
doubledual a b = a (\c -> c b)

doubleDual' :: forall t. (a -> n) -> ((a -> t) -> t) -> n)
doubledual' a b = b a
```

To be perfectly frank, I'm not sure this matches up with the idea that Dual Dual ~ Id, because I don't really think we have ```forall t.```. We specialize t to some kind of number. But the concepts line up tantalizingly close. Maybe I'll update this when I'm more confident.

### Linear Operators
The most straightforward implementation of a linear operator is just as a plain function from vectors to vectors.

```haskell
type LinOp a b c = Vec a c -> Vec b c
```

Compared to the Linear monad, it is disappointing that this does not enforce linearity in the slightest, but it is very simple.

Note again that ```b``` is in contravariant position and that ```a``` is in covariant position. In the index analogy, this would like like $A_a^b$

There is always the identity matrix which is simply give by the ```id``` function.

The zero matrix is given by ```const (const 0)```

The simple 2x2 block matrix has the type

```haskell
type Block a b c d n = LinOp (Either a b) (Either c d) n
```

We can take the kronecker product and direct sum of matrices.

```kron :: LinOp a b n -> LinOp c d n -> LinOp (a,c) (b,d) n```
```kron x y acf = \(b,d) -> (x \a -> (y \c-> acf (a,c)) d) b```
```dsum :: LinOp a b n -> LinOp c d n -> LinOp (Either a c) (Either b d) n```

This is a block matrix with zero matrices as the off diagonals.

There are also linear operaitions on the dual space.

```haskell
type DualOp a b c = Dual (Vec a c) c -> Dual (Vec b c) c
```

These are isomorphic to LinOps with the bases reversed.

```DualOp a b c ~ LinOp b a c```

witnessed by

```dualOp :: DualOp a b c -> LinOp b a c```
```dualOp a vb = \x -> a (\va -> va x) vb```

```dualOp' :: LinOp b a c -> DualOp a b c```
```dualOp' a dva = dva . a ```

Linear Operators inherit scalar multiplication and addition from their vectorial pieces. The apparent deficiency of this approach compared to the matrix representation is that matrix decompositions are at best clunky. This does suck since most of the fun stuff about matrices involves inverting them or taking eigenvalues or something. 

### Metrics
A dual vector does not need a defined dot product or metric in order to consume vectors. What you do need to define a dot product for is to convert vectors to dual vectors and vice versa.

The dualizing operator is the metric.
The metric is an operator that takes two vectors and gives their dot product.

```haskell
type Metric basis number = Vec basis number -> Vec basis number -> number
```

The metric in index notation is $g_{ij}$.

Currying this operation shows that it also can be viewed as an operation that takes a vector and produces a dual vector. I could just as well write the Metric type as

```haskell
type Metric basis number = Vec basis number -> Dual (Vec basis number) number
```

What this shows if if only use up one of the metric's indices we can convert a vector into a dual vector. $w_j=g_{ij}v^i$

For finite, enumerable types like ```Bool``` it is easy enough to see how we could build a standard metric. We have the ability to probe the entirety of the vector space by holding a list of every possible basis element.

For example 
```haskell
g_ij :: Number a => Metric Bool a
g_ij v1 v2 = (v1 True) * (v2 True) + (v1 False) * (v2 False)
```

As a fun little exercise, see if you can derive ```g_ij``` for any type of the Enum and Bounded class.

For quasi-infinite basis types like a float (corresponding roughly to functions on the Real domain like $\sin(x)$ and stuff), we need to specify an integration routine. This integration routine is the metric. Dual vectors will have the integration routine already built into them.

The dual metric
```g^ij :: Dual (Vec a n) n -> Dual (Vec a n) n -> n```

This dual metric is equivalent to 
```dMetric' :: Dual a n -> Vec a n```
via the double dual identity from before

With the metric we can define the transpose of a LinOp. We can post and precompose a LinOp with the two kinds of metrics.

```haskell
transpose :: LinOp a b c -> DualOp a b c
transpose a = g_ij . a . g^ij

transpose' :: LinOp a b c -> LinOp b a c
transpose' =  convert . transpose 
```

As a side note, it is interesting that defining the Dual vector as a representable functor requires giving the metric as the tabulate function. This almost works if not for the typeclass constraint that the functor held type is a scalar which makes it no longer a vanilla Representable instance.

### Existential types and Vector Summation

What the existential does is it does not let us do anything anymore with the Vec other than feed it into the Dual. The type ```a``` cannot unify with anything else. The index becomes a dummy index that we cannot actually access anymore. The ```exists a.``` is very similar to the summation symbol $\sum_a$ which also turns an index into a dummy index.

Not that ```exists``` is not actual Haskell notation. Sorry. You can do the equivalent but you need to construct funky less illuminating types.

Returning to the perspective of functors on the basis, we can find and intersting analogy that has been noted before. I am uncertain whether this is useful or just pure numerology, seeing faces in the tree trunks. So far, it has just been poison to me frankly.

```(Vec b n, Vec b n -> n)```

One way of writing this again to match 

```haskell
exists a. (Vec a number, Dual (Vec a number) number)
```


If we want to guarantee that eventually that first vector will get plugged into that second vector, we can apply an existential qualifier to the front of the type

```exists b. (Vec b n, Vec b n -> n)```

Now this type can only be consumed by a polymorphic function.

```forall b. (Vec b n, Vec b n -> n) -> whatever```

And basically there is nowhere to get a ```b``` type other than to plug the vector into the dual vector. Hence the existentialized pairing is basically delayed application.

This type ```(Vec a n, Vec b n -> n)``` is a Profunctor. 
<sup>[1](#piponiprofunctor)</sup>
It has one type parameter in covraint and one in contravariant position. Matching the two parameters and taking the existential is called taking the coend of the profunctor and it sometimes written $\int^c P(c,c)$. The coend possesses some interesting properties that interplay with Yoneda Lemma in a manner very evocative of calculations in linear algebra.

<sup>[2](#bartoszcoend)</sup>

Next Time: 
I don't know when I'll do the next article in this particular series, so let's sketch out some of the neat things I has intended at least.

String diagrams are a way of drawing monoidal categories. One monoidal category is that of Functors. Each string corresponds to a functor and the diagram is read left to right, with left to right corresponding to functor composition. Natural transformations are nodes, with particular kinds appearing as splitting of lines or bending of lines.

Bending of lines in particular denotes adjunctions. The disappearance of the two functors corresponds to the ability to natural transform that ordering into the identity functor, which you often just leave out of the diagram.

I think that the left adjoint to vectory functors is a tuple of the index type (a,-). This is because one definition of adjunctions is that it is the relationship that makes L a -> b ~ a -> R b. This is closely related to currying.

```sequenceA``` is a way of flipping functors. This may be important for getting the "wrong" cap, the one that adjunction doesn't get you.

Functor composition of vectory functors corresponds to the Kronecker product. You can look at the the typeclass instance for Representable and see that the composition of functors indices the pairing of their indices.

Likewise, the functor Product of two vectory functors is their Direct Sum. Think about that Representable = Ln relationship.

These Functory String diagrams corresponds very well with the notation in quasi Feynman diagrams and quantum circuits and Penrose notation, where side to side composition corresponds to the Kronecker product and nodes are matrices. Cups and caps correspond to usees of the upper index or lower index metric. A cup and cap can be straightened out into a striaght line because those two metrics are inverse.

I say quasi Feynman diagrams because Feynman diagrams are for bosons and fermions, so they don't really use the Kronecker product per say, and the left-right up-down ordering means nothing. They are totally topological. Goldstone diagrams are a variant where time is represented in up-down order, so they get closer.

You can index into this composite functor using fmap, but it kills sharing, which is a huge problem. I'm working on it. One basic possibility is to not use ordinary functor composition.
Instead use 

```type Kron f g a = [(f a, g a)]```

This is sort of a "Free" Kronecker product that keeps them unexpanded. You can still work with it. It is related to Piponi's Linear Monad. It is definitely related to doing perturbation theory on top of free particles.

Another important improvement I think is to use sharing by only referencing by integer or something a globally stored vector to prevent dumb duplication of effort. Also Memoizing.

See you next time, hot dog.

My other blog has a place to comment or reach out to me on the Twitsphere:
[http://www.philipzucker.com/functor-vector-part-2-function-vectors/](http://www.philipzucker.com/functor-vector-part-2-function-vectors/)

## Footnotes



<a name="piponiprofunctor">2</a> [http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html)

<a name="bartoszcoend">1</a>: [https://bartoszmilewski.com/2017/03/29/ends-and-coends/](https://bartoszmilewski.com/2017/03/29/ends-and-coends/)

<a name="freemanprofunctor">1</a>: [https://www.youtube.com/watch?v=OJtGECfksds](https://www.youtube.com/watch?v=OJtGECfksds)


<a name="gibbonsnaperian">1</a>: [https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf)


<a name="piponiyoneda">1</a>: [http://blog.sigfpe.com/2006/11/yoneda-lemma.html](http://blog.sigfpe.com/2006/11/yoneda-lemma.html)

