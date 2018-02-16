---
layout: post
title:  "Functor Vector Part 2: Functors in the Number"
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

Is there a way to convert an ordinary indexed vector into this form? Yes. It is just the function that 
```haskell
convert2FunVec v = \i -> v !! i
```

or more tersely

```haskell
convert2FunVec v = flip (!!)
```

and vice versa it is conceivable to perform the opposite, asking a function vector for every basis element and storing them in some container type. More on this later.

We can easily add functions and scalar multiply functions.

```
vadd v w = \x -> (v x) + (w x)
smult s w = \x -> s * (w x)
```

The direct sum and direct product of function vectors can be also be easily built.

```haskell
directsum :: Vec a c -> Vec b c -> Vec (Either a b) c
directsum = either

directproduct :: (Num c) => Vec a c -> Vec b c -> Vec (a, b) c
directproduct u v = \(x, y) -> (u x) * (v y) 
```


### Dual Vectors

The Dual of vectors are linear valued functions of vectors. They are machines you give vectors and they output numbers, sometimes called one-forms.

``` haskell
type Dual v number = v -> number  
```

This type unfortunately does not enforce linearity. We are indeed free to square elements if you so wish. Please don't.

The Dual is an interesting higher-order function given that vectors are functions.

Taking the Dual converts the basis type from contravariant to covariant position. 
Contravariant functors consume their arguments while covariant functors in some sense produce or hold them. 
Every time you cross into the arguments of a higher order function, you flip between contravariant and covariant. Or more mechanically, every time you cross a ) and then an -> going from right to left you flip between contravaraint and covariant position. Here are some examples.

```haskell
type Bar = (a->b)->c
type Foo = ((a->b->c)->d)->e->f
```

In type Bar ```a``` and ```c``` are in covariant position, and ```b``` is in contravariant position
In the type Foo, ```f```, ```c``` are in covariant position,  ```a```, ```b```, ```d```, and ```e``` are in contravariant position.

In this case the dual vector will produce basis elements to hand to the vector and then manipulate the produced coefficients linearly. Check out this Phil Freeman talk for more. 

In index notation, a vector is written with upper indices $v^i$ and dual vectors are written with lower indices $w_i$. There is an intriguing connection between the location of these indices (which correspond to our basis types) and the contravariant and covraint nature of the indieces.

The word dual implies 2. There is a sense in which the Dual of the Dual gives you back the original thing, like taking the transpose twice.

There is in fact there is a natural sense in which the ```Dual Dual ~ Id``` in Haskell as well

```forall t. ((a -> t) -> t) -> n ~ a -> n```

This is an example of the use of the Yoneda Lemma which states that 
```forall t. (a -> t) -> f t ~ f a```, in this case ```f = Id```.

Taking the Dual twice brings the basis back into contravariant position, so it is not insane that there is again a way to pull the whole thing back into the original form.

We see here a tantalizing connection between the covariant and contravariant notion in Functors and the same words used in vector context.


A dual vector does not need a defined dot product or metric in order to consume them.. What you do need to define a dot product for is converted vectors to dual vectors and vice versa.

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

One way of writing this again to match 

```haskell
exists a. (Vec a number, Dual (Vec a number) number)
```
What the exists does is it does not let us do anything anymore with the Vec other than feed it into the Dual. The type ```a``` cannot unify with anything else. The index becomes a dummy index that we cannot actually access anymore. The ```exists a.``` is very similar to the summation symbol $\sum_a$ which also turns an index into a dummy index.

Returning to the persepctive of functors on the basis, we can find and intersting analogy that has been noted before. I am uncertain whether this is useful or just pure numerology, seeing faces in the tree trunks.

(Vec b n, Vec b n -> n)

If we want to guarantee that eventually that first vector will get plugged into that second vector, we can apply an existential qualifier to the front of the type

exists b. (Vec b n, Vec b n -> n)

Now this type can only be consumed by a polymorphic function.

forall b. (Vec b n, Vec b n -> n) -> whatever

And basically there is nowhere to get a ```b``` type other than to plug the vector into the dual vector. Hence the existentialized pairing is basically delayed application.

This type (Vec a n, Vec b n -> n) is a Profunctor. 
<sup>[1](#piponiprofunctor)</sup>
It has one type parameter in coavraint and one in contravariant position. Matching the two parameters and taking the existential is called taking the coend of the profunctor and it sometimes written $\int^c P(c,c)$. The coend possesses some interesting properties that interplay with Yoneda Lemma in a manner very evocative of calculations in linear algebra.

<sup>[2](#bartoszcoend)</sup>




### Existential types and Vector Summation

What the exists does is it does not let us do anything anymore with the Vec other than feed it into the Dual. The type ```a``` cannot unify with anything else. The index becomes a dummy index that we cannot actually access anymore. The ```exists a.``` is very similar to the summation symbol $\sum_a$ which also turns an index into a dummy index.

Returning to the persepctive of functors on the basis, we can find and intersting analogy that has been noted before. I am uncertain whether this is useful or just pure numerology, seeing faces in the tree trunks. So far, it has just been poison to me frankly.

(Vec b n, Vec b n -> n)

One way of writing this again to match 

```haskell
exists a. (Vec a number, Dual (Vec a number) number)
```


If we want to guarantee that eventually that first vector will get plugged into that second vector, we can apply an existential qualifier to the front of the type

exists b. (Vec b n, Vec b n -> n)

Now this type can only be consumed by a polymorphic function.

forall b. (Vec b n, Vec b n -> n) -> whatever

And basically there is nowhere to get a ```b``` type other than to plug the vector into the dual vector. Hence the existentialized pairing is basically delayed application.

This type (Vec a n, Vec b n -> n) is a Profunctor. 
<sup>[1](#piponiprofunctor)</sup>
It has one type parameter in coavraint and one in contravariant position. Matching the two parameters and taking the existential is called taking the coend of the profunctor and it sometimes written $\int^c P(c,c)$. The coend possesses some interesting properties that interplay with Yoneda Lemma in a manner very evocative of calculations in linear algebra.

<sup>[2](#bartoszcoend)</sup>





For finite enumerable types there is a straightforward natural metric

For example 
```haskell
g :: Number a => Metric FunVec Bool a
g v1 v2 = (v1 True) * (v2 True) + (v1 False) * (v2 False)
```


For quasi-infinite types like a float, we need to specify an integration routine. This is the metric. Dual vectors have the integration routine already built into them.

### Linear Operators
The most straightforward implementation of a linear operator is just as a plain function from vectors to vectors.
```haskell
type LinOp a b c = FunVec a c -> FunVec b c
```
Compared to the Linear monad, it is disappointing that this does not enforce linearity in the slightest, but it is very simple.

Note again that ```b``` is in contravariant position and that ```a``` is in covariant position. In the index analogy, this would like like $A_a^b$

### Foldable
(Enum a, Bounded a) => Foldable (a -> a -> f)
	fold f = fold $ fmap (\x -> f x x) enumerate

trace = fold

(Enum a, Bounded a) => Foldable (a->f) -> (a->f) -> f
	fold a b = fold $ fmap (\x -> (a x) * (b x)) enumerate

	Foldable (a->f, a->f)  where
	



## Category Theory & Vectors

So we've explored a bit the idea of using the function itself as a vector type. As part of that, we mentioned that an ordinary array can easily be converted to a function by an indexing function. Is there a way to generalize this for all the other varieties of vectors we could come up with? The answer is yes. The pattern of a container type (functor) that is basically indexable so it is equivalent to some function type over an index is called being a Representable Functor.

Let's make a small diversion into category theory.

### The Function as a Functor



The arrow ```(->)``` is also known as the ```Reader``` functor in Haskell terminology. The function is a functor in its result type. This is the perspective of vectors we will pursue from now on, vectors are functors in their contained numbers.

### Other Vectors can be transformed to Functions.
What about vectors data types that aren't literally function types? Well there is a way to transform back and forth between these vectors and functions.
You can write a function that returns that result of indexing into a vector.
\i -> v !! i = (!!) v
and given a finite basis, you can probe all the values and fill the vector out.

To say that a vector is basically (->) basis is to say that vectors are Representable functors with the Representation type given by the basis. This is a Haskell typeclass that corresponds to an equivlanet concept in category theory.

A Category is a set of objects and morphisms. One perspective is that Category theory is a simple formalized theory of functions. You get many of the important properties of functions without looking deeply into their implementation. Functions can be composed if one's codomain matches the other's domain. Certain ways of composing functions may be 

The resource that I learned basically everything I know about category theory is Bartosz Milewski's Category Theory for Programmer's, which with the corresponding youtube videos I cannot reccommend heartily enough. 
The category of Sets 


The category that one discusses the most in the context of haskell is the category where types are objects and functions are the morphisms. This is pretty dang similar to Set. The objects are these things with complicated sturcture but we avaoid looking at the internal structure. We usually can't and don't want to know at compile time if an Int is exactly 3. We want to be able to put in different Ints at runtime and have the thing still work.

I think there are a couple of obvious choices of how one might want to  

There is a Functor connecting the Category of Bases to the Category of Vectors.

There is some convenience to being able to map functions between basis labels to functions changing vectors. For example, a simple renaming of the basis becomes simple, or in the context of quantum computing, a classical reversible computation can be mapped directly up to the quantum state.

There is a split brained perspective on most topics in Haskell. Ultimately, Haskell does compile into machine runnable code, so there is an imperative translation of everything it does. On the other hand, there are very abstract and mathematical perspective. The Haskell community by and large does not emphasize the machine aspect. This is not the aspect that makes Haskell unique, and it constrains your mind to thinking in the old ways, ways that are accidents of the engineering realities and compromises of real processor architectures.

Functors are types that are containers of other types. They may hold one or more different copies of their inner types. fmap is a generic function. By its type signature, it cannot reach into and see anything about the object being held, it can only apply the function given.

On the other hand, Functors are a manifestation of the category theoretical functor. This functor is a mapping between categories, mapping objects to objects and morphisms to morphisms such that it plays nice with the composition of morphisms, i.e. it does not matter whether the composition occurs before or after the mapping.
parametric type variables are basically a systematic way of treating pointers. How is it possilbe that the function ```id :: forall a. a -> a``` could possibly work for every type a? It is because a is basically a pointer reference and pointers are a uniform description of all possible types. All pointers are 64-bit integers referring to some spot in memory. Later on in your Haskell learns, you find out about other Kinds than \*, like unboxed types. These are not compatible with the types of \* because they are not pointer references and can't be treated the same way.


Natural transformations are mappings between functors. 
Natural transformations are functions of the form 
```type Nat f g = forall a. f a -> g a```
From the container perspective, these are functions that can only rearrange the container structure and not touch the contained objects. They can copy or discard objects.
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

A finite type has a natural means

To state that the dual vector is representable is to give a way to convert a covariant to  contravariant functor

```haskell
tabulate :: (Rep f -> a) -> f a
index :: f a -> Rep f -> a
```

In this case ```f a = ((Rep f) -> a) -> a```

```tabulate``` is the upper indexed metric $g^{ij}$ and ```index``` is the lower indexed metric $g_{ij}$

We are truly living in sin from a Haskell perspective. This is a fully indexed formulation of taking the inner product. 


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


## Footnotes



<a name="piponiprofunctor">2</a> [http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html)

<a name="bartoszcoend">1</a>: [hhttps://bartoszmilewski.com/2017/03/29/ends-and-coends/](https://bartoszmilewski.com/2017/03/29/ends-and-coends/)

<a name="freemanprofunctor">1</a>: [https://www.youtube.com/watch?v=OJtGECfksds](https://www.youtube.com/watch?v=OJtGECfksds)



