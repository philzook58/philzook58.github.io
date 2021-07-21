---
author: philzook58
comments: true
date: 2020-10-12 14:45:31+00:00
layout: post
link: https://www.philipzucker.com/?p=2873
published: false
slug: Differentiation Lens Redux
title: Differentiation Lens Redux
wordpress_id: 2873
---

Primitive Lenses - two stacks? How would I go about this
2*x ->  

int twice(x){
    return 2 * x
}


push2 dret
call1 twice
push2 dtwice
mov  rsi, rax
call1 twice
push2 dtwice
... and so on

backwards:
    ret2 # pops the second stack and starts off "rop" chain



SP2
SP1

Huh. This _is_ a rop chain.

Primitive Lenses, ROP chains, and wengert tapes.

Discussion of marco zocca blogpost:
https://twitter.com/ocramz_yo/status/1417153500899909636?s=20

Kmett:
Selective Functors
"Constant complement encoding" for linear lenses?
"Does this omit the usual sharing optimizations that a Wengert list gives you? Almost everyone that I see that tries to use delimited continuations winds up paying for the entire tree complexity rather than the graph complexity when computing z = w*w; y = z*z; x = y*y"


Hmm, continuations _are_ the stack. So my two stack idea suggests that we need two types of conitatuions, which as i recall the kiselyov version supports.

https://enzyme.mit.edu/


CPS -> defunctionalize -> the stack is a data structure
The stack is also a bundling of a code pointer (return address) and data. In this sense it is a closure.

For sharing like kmett is talking about, you need to pass in the location to write to. The return void style / the "prolog" style / channel passing style.
In Rust, a hetergenous lifetime vector? subsequent pieces are in the scope of previous guys, i.e. pointers only point backwards? A fun sounding puzzle
s -> (a, b -> t)
(&mut t, s) -> (a, b -> ())
Also could literally thread a stack Vec
(&mut t, s) -> (mut stack) -> a
The stack holds Vec<exists. b -> ()>
(&mut t, s) -> mut stack -> (a, Either *b (b -> ()) ) 
We may choose to allocate space for b and return a reference, otherwise there was already space on stack

We need to decide on a standard of communication to achieve composiabilituy


These are my initial thoughts.
Everyone is tied to look at things from their background and their natural predilections.
My background is physics, engineering, a bit of control theory and now computer science and programming. I am not a hardcore category theory person. It is thought provoking stuff that lives at the periphery of my understanding.

There is a partial order of possible definitions:

One of the strictest ones would be a Haskell function of type a -> (b, b -> a) that obeys the getter and setter laws.
Less strict that that would be to go to s -> (a, b -> t) and/or to remove the restriction of getter and setter laws or to consider isomorphic types like exists e. s -> (e,a) * (e,b) -> t.
Above(?) that would be to consider basically the same form in different languages. You can essentially still talk about functions like that in python using higher order functions for example, although types take a back seat.
Above that might consider the different forms in which essentially the same construct presents itself. Automatic differentiation manifests itself using wengert tapes, using tracing computation graphs with object oriented interfaces, etc. In this sense a lens is a compositional programming abstraction or control flow construct that has one forward pass that saves information, and a backwards pass that may reuse this information. Generalizing this can lead to stream transducers, which don't have a particular pass structure picked at compile time. In this sense lenses live roughly at the same vague level as the notions of first class function, visitor patterns, while loops, etc the closest analogy being first class functions which are things that can take on different forms depending on the language. A first class function is an object that supports a single method call if that is your preferred way of thinking about things. I have wondered if there would be utility to having a language with lens as a primitive notion for efficient compiling rather than encoding lens into objects or closures. Perhaps this would generalize differentiable and probabilistic programming languages? I have no clue what form such a thing would take
At a higher level, these programming constructs are modelling or reflecting something in the physical or mathematical world. Again the analogy between computer functions and mathematical functions or physical processes seems appropriate. A way of formalizing this relationship is probably some kind of functor or homomorphism between these things and here would live something like the mathematical definition you suggest. I suppose only here is where the general abstraction power of category theory really exists.
I personally am inclined to the compositional forward-backward information saving pass "definition" although perhaps this is not a definition by a certain standard.
A honest form of definition might be "things that behave similarly to reverse mode automatic differentiation" because that may be the analogy I go to the most. This may be a rather circular definition for some purposes.



Functional differentiation
Once you explicitly reduce a function to a set of parameters, it becomes ordinary differentiation.

In functional programming, the way to reduce a function to first order data is defunctionalization, tabulation, or closure conversion.

Defunctionalization is like picking some parametrization. Integration can proceed precisely, like for polynomials and some other cases.
Tabulation  (or lazy tabulation) is using that the function is only evaluated at a finite numbers of points, like in numerical integration. This can actually be achieved in user space whereas the others need some kind of metapgoramming or hand compilation.
closure conversion is taking any values closed over and putting them in an environment data structure. One could differentiate with respect to this data.



---

One of my more interesting blog posts is one in which I described how to write a system of reverse mode differentiation combinators by a strong analogy to lenses from functional programming [https://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/](https://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) . I considered it to be a slight twist on Conal Elliot's Essence of AD [http://conal.net/papers/essence-of-ad/](http://conal.net/papers/essence-of-ad/) although there are other sources where you can find similar ideas expressed. 

I have a number of insights I've collected over the last couple years about reverse mode automatic differentiation that I've never collected up into a blog post. I also might be giving a talk that uses some of this soon.

## The Basic Idea: Different modes = orders of multiplication

First off, the chain rule is just multiplication if you suppress the complicated dependence on the base point. D[h(g(f(x))] = h' * g' * f'. For $latex R^1 \rightarrow R^1$ functions, these are scalar multiplications, for higher dimensional functions they are matrix multiplication for which the matrices may rectangular in general. Multiplication is associative. You can choose an association of these multiplications that is most efficient (and they are in general of different efficiency [https://en.wikipedia.org/wiki/Matrix_chain_multiplication](https://en.wikipedia.org/wiki/Matrix_chain_multiplication) ). h' * (g' * f') or (h' * g') * f'. Associated all to the right is forward mode (it follows the order of application), all to the left is reverse mode. Reverse mode association is efficient for maps taking a large number of dimensions to a small number (like evaluating cost functions). I feel like as I've just stated it, it is fairly straightforward in that at least I have not invoked too much terminology.

## Implementing it

Ok, but when we don't suppress the dependence on the base point, things look a little hairer. The two pieces of information we want every function to produce is it's value and its Jacobian matrix. This is a perfectly reasonable thing to write in most languages.

$latex (\sin(\theta)\cos(\phi), \sin(\theta)\sin(\phi), \cos(\theta)$ is a function from $latex \theta, \phi$ to the surface of a 3d sphere. We can further consider a scalar evaluation on this sphere $latex x^2 + y - z$, which is a function $latex R^3 \rightarrow R^1$.

    
    <code>lambda x: (
    [ np.sin(x[0]) * np.cos(x[1]) , np.sin(x[0]) * np.sin(x[1]), np.cos(x[0])],
    [
    [np.cos(x[0]) * np.cos(x[1]), np.cos(x[0]) * np.sin(x[1], -np.sin(x[1]))],
    [-np.sin(x[0]) * np.sin(x[1]), np.sin(x[0]) * np.cos(x[1]), 0]
    ]
       )
    
    lambda y: (y[0] ** 2 + y[1] - y[2], 
    [[2*y[0]],
     [1],
     [-1]]
    )
    
    def compose(g,f):
       def h(x):
          (y, df) = f(x)
          (z, dg) = g(y)
          return (z, dg @ df)
       return h
    
    </code>

Of course the point is not to build these big arbitrary blocks, we want to build these up compositionally even further.

The associativity of matrix multiplication follows exactly the order of compose that one uses, transpose or not. In fact this might be a feature of this perspective, as neither forward nor reverse mode differentiation are optimal associations in general and a user may choose a smart ordering.

## Implementing Linear Operators

While the most elementary way to implement a linear operator is the have a dense 2 dimensional array that is the matrix of that operation, there are other options. Perhaps our operator is sparse, in which case we may want to store a sparse matrix. Another possibility is that our operation is simple to specify in some algorithmic sense, for example the Discrete Fourier Transform can be described as a matrix, but really it is most efficient to describe it as a Fast Fourier Transform subroutine to be called. So we can describe This functional representation is not weird, it is in scipy, which is as mainstream as it gets in scientific computing [https://docs.scipy.org/doc/scipy/reference/generated/scipy.sparse.linalg.LinearOperator.html#scipy.sparse.linalg.LinearOperator](https://docs.scipy.org/doc/scipy/reference/generated/scipy.sparse.linalg.LinearOperator.html#scipy.sparse.linalg.LinearOperator)

[https://github.com/JuliaSmoothOptimizers/LinearOperators.jl](https://github.com/JuliaSmoothOptimizers/LinearOperators.jl)

It is in this form that the reverse mode becomes very similar to the functional programming lens `x -> (y, dy -> dx)`

This achieves an association all to the left in a manner reminiscent of Hughes lists. Hughes lists are a functional representation of lists that results when you partially apply the append operator. When you want to append many lists, the asymptotic complexity depends on the association with which you do so. If you associate to the right it is $latex O(n)$ , but if you associate to the left it ends up being $latex O(n^2)$ because you unnecessarily iterate through the front of the list over and over. When you convert a list to Hughes form, the correct association occurs by default, regardless of . This is because function composition is strongly associative. The different associations are nearly or completely associative on the nose rather than just being equivalent on some semantic level. (The call stack might look a little different, but I don't think in any way. Number of closures and size of creations might be different?)

## What about Dual Numbers?

A common presentation of forward mode differentiation is as computations on dual numbers that pair up numerical values with an "infinitesimal part" $latex x + \epsilon dx". We can then redefine mathemtical operations on these dual numbers to track diervative information. This is similar in some respects to how complex numbers are a pair of real part and imaginary part which have a special definitions.

These functions then have the type `(x,dx) -> (y,dy)`

From a certain perspective, there is something deficient about this dual number representation, in that it is at least structurally possible for the value part of the output to depend on the differential part of the input, when this should never be the case. Every operation of the form `x -> (y, dx -> dy)` can be turned into an operation of the form `(x,dx) -> (y,dy)`, but not vice versa. The first form more accurately captures the dependencies.

Nevertheless, the dual number formulation is very appealing as it can be implemented by operator overloading, and code that is differentiable can be written in a form similar or identical to code that was not written to be differentiated.

Does there exist an equivalent form for reverse mode? `(dx -> dy) ~ forall s. (dy -> s) -> (dx -> s)`. This transformation is very evocative of one saying that linear maps between dx and dy are isomorphic to the adjoint maps taking. Another way of looking at this is that we are taking in a continuation representing Jacobian applications to come. 

`x -> (y, dy -> dx) ~ x -> (y, forall s. (dx -> s) -> (dy ->s)) ~ (x, dx -> s) -> (y, dy -> s)`

Unfortuantely, the domain and codomain are not independent. They have this spooky dependence of the `forall s` and can't obviously be implemented via the operator overloading approach.

If we however monomorphize this s to a scalar `(x, dx -> Double) -> (y, dy -> Double)`, now we have which by the assumption of linearity we haven't lost anything.

## Aren't Lenses getters and setters?

The standard usage of lenses is to get subpieces of a struct or to update that subpiece. They really are a packaging up together of getter and setter functions and are a first class functional representation of getting and setting.

I think it is acceptable to take a hard line and only use the words "lens" for these things, but some communities are taking a more general perspective of what it means to be a lens. 

A lens could also be considered anything of the type `s -> (a, b -> t) ` that composes according to lens composition. In this case, you can find lenses in any place that has a computation that has a forward pass that saves some information and a backwards pass that uses that information.

From this persepctive, lenses are part of a spectrum of control flow techniques that includes continuation passing style, coroutines, iteratees. The difference is that the Lens encodes that the is a single forward and backward pass in the type, whereas the other techniques allow for morew complex 

We can consider extensions of the lens paradigm to include more complicated, yet statically known control flow. We can have multiple forward and backward passes, or we can include an infinite stream of possible passes. These computations are also encodable using coroutine and continuation techniques.

    
    <code>data Lens3 = a -> (b, b -> (a, a -> b))
    data InfLens = a -> (b, b -> (a, InfLens a b)</code>

There and back Again 

## What about the Computation Graph / Wengert Tape?

A common method to implement reverse mode differentiation is to build up a computation graph data structure during the forward pass, which is then traversed to perform the differentiation. This data structure can be viewed as a defunctionalized form of the differentiation lens. 

Defunctionalization gathers up all all instances 

Really this is very closely related to how anonymous functions are implemented as closures. The closure data structure holds.

This is also relevant to an alternative formulation of lenses that is sometimes discussed, the existential form of the lens

    
    <code>data Lens s t a b where
       Lens :: (s -> (a, e)) -> (b,e) -> t) -> Lens s t a b
    
    data Closure a b where
       Closure :: e -> ((a,e) -> b) -> Closure a b
    
     </code>

Haskell does not make a habit of distinguishing between function pointers and closures, but Rust and C++ do for example.

[https://docs.julialang.org/en/v1/devdocs/functions/#Closures](https://docs.julialang.org/en/v1/devdocs/functions/#Closures)

Part of the point of the lens is that some information is maintained from the forward pass for use in the backwards pass. This information is held in a locked up state `e` that via the type system is not introspectable or tamperable for any purpose.

Another perspective. Codata and object orienteds programmiung

## Cotangent Spaces and Linear Functionals

Another way to think about this is to consider mappings of linear functionals w(v)_w_(_v_) of vectors v. For a mapping of vectors, there is a natural adjoint mapping of linear functionals that keeps the value of this application w(v) invariant. If we represent a vector by a column vector of coefficients, it's natural to represent the linear functionals by a row vector of coefficients. Then applying w to v is the row column product $latex w^Tv$ . A mapping v=Au_v_=_Au_ induces a mapping r = A^Tw_r_=_ATw_. Transpose flips the order of multiplication of matrices. (ABC)^T=C^T B^T A^T(_ABC_)_T_=_CTBTAT_. Hence the left association of matrix multiplication corresponds to the right association of transpose multiplication.

## Where does Category Theory come in?

To my taste and ability, not much really.

There is some work on higher order automatic differentiation, as in can we differentiate. A concretly parametrized family of functions, like sines, cosines, gaussians, polynomials, piecewise linear, differentiating with respect to a function is the same thing as differentiating with respect to the parameters, and hence this does not offer anything all that novel. You can write down closed forms of the integrals of these functions as need be. 

From the persepctive of functional programs, it's a little more interesting because the function is opaque to us. An anonymous function is an object that presents a single interface, that it can be evaluated.

I think a standard approach to reverse mode ad is that you build up a computation graph data structure of your computation as you go along. Then you can trace back through this graph when you're done.

There is this notion of a lens not as s -> (a, b -> t) but instead with an explicit existential piece of data around. $latex s -> m \otimes a, m \otimes b -> t  $. The equivalence of these two forms depends upon like... stuff? Coyoneda probably.

Basically this is the defunctionalized form of the regular lens. The existential variable m holds equivalent information to the data closed over in the `b -> t` lambda.

A closure is something like data Closure a b = Closure { exists m. (m, (m -> a -> b)) }. 

We don't have access to a function pointer in bog standard haskell. Maybe as some primitive [https://hackage.haskell.org/package/base-4.14.0.0/docs/Foreign-Ptr.html#g:2](https://hackage.haskell.org/package/base-4.14.0.0/docs/Foreign-Ptr.html#g:2)

We can mock this up a little bit by

Closure conversion and defunctionalization are things living in parallel universes. There is an interplay of open and closed data types, 

    
    <code>class Function k where
        apply :: k a b -> a -> b
    
    Function k => k a b
    -- It is now pretty hard to accidentally caature variables unintentionally.
    Function k a b => k a b
    </code>

Defunctionlaization

Higher order AD, Defunctionalizing AD: Existential Lenses and Wengert Lists

Keldysh contours. Am I insane? The keldysh contour is a forward backwards pass. And you do need to reach across the forward back for some purposes. Also I've mentioned rainbow diagrams before which look like comb diagrams 

keno fisher's ad paper [https://gist.github.com/Keno/4a6507b75288b1fe671e9d1cc683014f](https://gist.github.com/Keno/4a6507b75288b1fe671e9d1cc683014f)

  * [http://conal.net/papers/higher-order-ad/higher-order-ad.pdf](http://conal.net/papers/higher-order-ad/higher-order-ad.pdf)
  * [https://openreview.net/pdf?id=ryxuz9SzDB](https://openreview.net/pdf?id=ryxuz9SzDB)
  * [https://www.irif.fr/~kerjean/papers/dial_diff.pdf](https://www.irif.fr/~kerjean/papers/dial_diff.pdf) Connection to dialectica?Dialectica ~ lens according to jules
  * [https://arxiv.org/pdf/1803.10228.pdf](https://arxiv.org/pdf/1803.10228.pdf) - shift/reset ultimate backprop

Conal makes an interesting point I think that higher order derivatives and differentiating with respect ot functions appear related surprisingly.

Defunctionalization make higher order data first order. This seems related to the notion of using sampling or polynomial parametrization to define functional differentiation. I'm not even sure it's clear how to differentiate sum types. I suppose if you only ever evaluated functions on constants, you could defunctionalize to just the functions evluated on those constants

Would differentiation mean differentiating with respect to the free variables closed over in the function? Differentiating the closure in related terms?

    
    <code>data Closure e v a = {f :: e -> v -> a, env :: e} 
    apply : Closure e v a -> (v -> a)
    apply (Closure f env) = f env
    
    
     
    
    
    </code>

I think these people are too far from physics to maybe even know about functional differentiation.

integral f = (f 0)^2 + (f 1)^2 + (f 2)^2. Automatically differentiate this function. dintegral df = (f 1) * df 1 + (f 2) * df 2 + df 3. What;s wrong with that? Regular dual number approach (f,df).

Okay how about reverse mode. dy -> (v : x -> y) -> dy * v 1 * (f 1) + .

Sure. Seems fine. Ok, the issue must arise when the locations you are evaluating at are not constants.

integral f g = f (g 1) + f (g 2). Right?.  dintegral df dg = partialf (dg 1) + df (g 1) + ... because. This might occur in the expression involving some elastic background.Now I need \delta df which we integrate by parts. Or what about action f = (diff f  1) ** 2 . Now we needed a differentiable function, sure. so the type of action is different action :: Diff Double Double.

Or perhaps we could consider the Romberg integral from hughes paper. The refinement level might depend on how fast oscillating the function is.

eval f x = (f x,  \(dy -> Double) -> (\(df,dx) -> dy (df x + partialf x dx)

Hmm. Yeah. We need the derivative of f, but we don't want it in scope until later. Unless we use it in the primal expression. Well, the eval primitive we know doesn't use it. So it seems fine.

Differentiating an abstract machine.

A function is a data type that presents a single interface, the ability to apply it to arguments. So the only thing you can ever do with a function is toss it around opaquely (copy drop), and evaluate it. This set of evaluations may be  https://twitter.com/SandMouth/status/1270409619693875201?s=20

Higher order exact reals is interesting. Involves precisely calculating functions and sequences. 

