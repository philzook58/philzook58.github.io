---
author: philzook58
comments: true
date: 2020-11-11 00:52:53+00:00
layout: post
link: https://www.philipzucker.com/?p=2729
published: false
slug: Intervals + Automatic Differentiation ~ Exact Reals, Sheaves, Geometry Logic,
title: Intervals + Automatic Differentiation ~ Exact Reals, Sheaves, Geometry Logic,
wordpress_id: 2729
---

Bishop-brouwer - all constructible functions are continuous.

Bauer paper - 

Semidecision in coq
https://www.ps.uni-saarland.de/~smolka/drafts/icl2019.pdf
exists n, f n = true
exists n, f n = True <=> P x -- reflection principle

This means it has a semi decider. It doesn't mean it is semi descdiale

Why bring the nats into it though . What other formulations might there be?
We need to encode non terminating search in some way. So this is related to the nontermination
encodings
Gas. Basically.
I don't think Gas requires stabilization persay usually.
We could go coinductive. 
We could have a kind of a chain of lesser proofs. P (n+1) -> P (n+1)
Can one use Acc? Maybe not? I mean the point is that we have true non termination possibly

What is decision and semidecision

Problems are decidable.
https://en.wikipedia.org/wiki/Decision_problem
Decision problems are a question on an infinite set of inputs.

But what is a question?

https://en.wikipedia.org/wiki/Borel_hierarchy
https://en.wikipedia.org/wiki/F%CF%83_set

We can talk about sets of inputs tapes. (?)
How do we talk about these sets?
Turing machines can halt yes,no, or not terminate

What is an algorithm
What is a computable fucntion

What is a problem?
I think a problem 


https://arxiv.org/pdf/1904.13203.pdf computable analysus and notions of computability in coq



### Lattices & POSets

Categories are hip and cool, but lattices kind of are more conceptually useful more down to earth.


Ed Kmett

Lattices are an algebraic theory of approximation.

Lattices are an important source of categorical constructions.

Lattices are approximate sets.

Lattices are an algebraic structure like a group. They have 2 binary operations that are associative, commutative and idempotent
This leads us to consider free lattices.



Lattices are a partially ordered set with a max and min operation.

Max, supremum, join, union, least upper bound (lub).

Min, infimum, meet, intersection, greatest lower bound. 




Partially ordered sets can be considered as a category where there is either an arrow between two objects or not. This arrow represents one being less than the other. x <= x for all x, so there is always an identity morphism, and inequalities compose. Given a <= b, b <= c, we know that a <= c

https://ncatlab.org/nlab/show/lattice

The meet and join are categorical products and coproducts. The universality properties of the product is exactly the thing that says we got the _least_ upper bound.

The top and bottom of a lattice are  initial and final objects


Mappings between partial orders that preserve the partial order are called monotonic functions. For a monotonic function x <= y implies that f(x) <= f(y)


The lattices that we're talking about are differenty from the lattices in cryptography or crsytallography, which are grids. All these things are called lattices because they can be visualized in a way that looks like a lattice work fence, but they are very distinct.


Monotone functions between posets are Functors because they respect the inequality.
Lattice homomorphisms also respect meet and join. This makes them special functors.




Representing finite posets: 
- Topological sort to give labelling
Vectro clocks





There are different intuitions for what <= should bring to mind, and you can get mentally stuck on them. The first intuition is the naturals or reals with our ordinary notion of inequality. Here the objects are points. Monotonic functions are those that are always nondesreasing, sort of slanted upwards to the right.

Another interesting example is generalized inequalities, which extend ordinary <= to higher dimensions. They are defined x >K= y if x - y is in cone K. Since cones are closed under addition, if x -y is in K, and y - z is in K, then x - z is in K. x - x = 0 is always in K also.
https://see.stanford.edu/materials/lsocoee364a/02ConvexSets.pdf
It is a partial order typically. It may be that x -y nor y - x are in K.
Is <=K a lattice? I think it might be under the right conditions. There is a cone based at x and y, and the intersection of these cones (if it exists) is another (differently shaped) cone at z. The conic closure of this interesected thing has a based point somewhere. Is it unique? You know I'm not sure this works.
It brings to mind special relativity also, with light cones.


Another important one is to use the subset relation of inclusion $$\subseq$$. Now the objects are sets, not points. The intuition is very different here.

Definedness orders. There is an interesting concept that one may consider something to not yet be defined. It eventually will be maybe. But there is an inequality of definedness. `missing` is less defined that `true` or `3`. As the computation proceeds, things become more defined. Lindsey Kuper's thesis. Denotational semantics and bottoms and laziness.



Lattices as truth values. I don't know where i get this notion from. Maybe it's bogus.
When we ask if a cube is in a shape, proper answers might be yes, no, and on the edge. true, false, missing.




A third set of intuitions come from finite lattices.




The notion of "set" is kind of a poor one. It's not well defined in my opinion. The canonical answer of what set means is that it is a thing that is definable and capable of being reasoned about in ZFC. This is not great because ZFC is a nightmarish shitshow that you'll have extreme difficult getting a computer.
The issue comes down to representation. It's all well and good to talk about sets in the abstract, but when you actually need to apply them, you really do need some way to concretely represent them. 
Finite sets can be represented by a list of objects. But what about all the nightmarish sets that exist in the mathematical literature. Surely you don't want to deal with those.

So we can choose to work in families of sets that have nice properties. We can't represent all the operations on sets we might like while stying in the family, and that does sting. But we can make do.

Intervals are a canonical example of this.

The lattice of intervals is distinct from the lattice of sets. It is a sublattice. Every interval is of course a set, but not every set is an interval. We can perform the interval hull operation in order to 

These two mappings are an example of a Galois Connection. Galois Connections are an example of an adjunction.

Other galois connections:
- Floor and injection between the real line and integers, with respect to ordinary <=. John Baez https://www.azimuthproject.org/azimuth/show/Applied+Category+Theory+Course#Course
- Galois connections as "pseodo inverses". You can invert functions by doing the best job you can with respect to some ordering.

Equality is a poset, so in this case galois connections become actually inverses


Much more natural notions of set might include finite sets


A great thing about the lattice abstraction is for fixed point algorithms once you realize you have a lattice, orderings don't matter anymore. 

Knaster Tarski Theorem - An extremely often referenced theorem.

### Truth Values
https://en.wikipedia.org/wiki/Truth_value
{true,false} {0,1}

Where do these live in logic? They seem most likely to live in models.
(true and false or true) vs something with variables in it (p and q or r)

p and q or r does not have a value {true,false}. It does if p,q,r are interpeted as true false
We''r interpeting the dead syntax /\ as the function {(0,0) : 0 , ...}

x + y is not a number. It isn't like 7. 

Synatctic forms are dead.


Kripke model is analog of variable assignments, not of true/false.

It's not true / false.
It's in the semantic relation |= or not


Topos
Orindary functions have a subobject classifier.
Indicator functions are a useful idea
Subsets are represented by parametrizations. An injection into another set./





### Intervals

There are two different kinds of uses for interval arithmetic
- Analyzing data that was uncertain from the get go
- Worrying about the intrinsic rounding errors of an exact mathemtical calculation

Libraries tend to built for one use case or the other. A library that wants to deal with exact mathematical calculation is more likely to have arbitrary precision and be hyper careful to round every calculation in the right direction. This has performance cost. A library meant for deal with uncertain information 

I'm not saying there isn't overlap, it's just be aware of the different desires.

https://fredrikj.net/ Fredrik Johansson is the man I guess.
Arb, Calcium, mpmath, 
https://arxiv.org/abs/2011.01728 calcium paper. It implements a mix of "effective" numbers and exact reals

Arb, MPFI, 
iRRAM

"MPFR is not able to track the accuracy of numbers in a whole program or expression; this is not its goal. Interval arithmetic packages like Arb, MPFI, or Real RAM implementations like iRRAM, which may be based on MPFR, can do that for the user."

https://fredrikj.net/calcium/

When we approximate functions, we pick subfamilies of functions.

We can for example take samples of functions at positions and glue them together, for example via piecewise linear interpolation.
These methods have very low strong guarantees without external reasoning, further information about the functions that you manipulate on paper and penicl.


It is also possible to represent sets of functions. An arbitrary set of functions is a ridiculous thing.

A tube is a natural analog of sampling. We instead store intervals that the function lives between.
We can easily convert symbolic representations to tube form via interval arithmetic.
Interval arithmetic is a compositional technique for combining known bounds of subpieces.


Integration plays nice with tubes, differentiation does not.
We can convert a tube to a verified true bound on it's antiderivative. We cannot go the other way. The tube contains extremely non differentiable jaggedy noisy functions.

Differential equations can often (always?) be converted to integral form.
xdot = f(x,t) is equivalent to x(t) = \int f(x,t) dt

Now however the difficulty is that both sides contain an unknown x so we can't just do the problem.

We can convert integral equations into integral inclusions / inequations.

It is a useful trick for solving equations by converting them into iterative processes. If this process has a fixed point, it is by definition also a solution of the equation. An important question is whether this fixed point is attractive or repulsive. Whether the iterating process is contracting.

If so, then if we worked with a fully expressive function space, we would converge to the solution, or sets of functions would converge to the fixed point set.

There is a galois connection between this space and our tube space. We can take the interval hull of any function set and inject any tube set as an example of a moire general function set.

What are the conditions that guarantee that there exists a fixed point solution in the refined space that injects into something expressible in the abstract function space.


Picard-Lindelof iteration https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem


There is a strange irony that differentiation is symbolically easy and integration symbolically hard, whereas numerically integration seems better behaved than differentiation. Differentiation of a measured function relies on cancellations of nearly identical numbers.


A very good analog for what we are doing is to consider a 2-D space where we descide to use the same interval for both dimension, i.e. we can only represent squares, not rectanbles.

If we consider a convergent process like 
$$x_{n+1} = 0.1(x_{n} - 3) + 3 $$
$$y_{n+1} = 0.1(y_n - 5) + 5 $$
Which has a fixed point solution at x = 3, y = 5.

```python
def update(x):
  x2 = np.zeros(2)
  x2[0] = 0.1*(x[0] - 3) + 3
  x2[1] = 0.1*(x[1] - 5) + 5
  return x2

x = np.array([27,52])
for i in range(100):
  x = update(x)

```


Each iteration when considering an interval box $$[l,r]\times[l,r]$$ becomes

$$l_{n+1} = \min 0.1(l_{n} - 3) + 3 , 0.1(l_{n} - 3) + 3$$ 
$$r_{n+1} = \max 0.1(r_n - 5) + 5,  0.1(r_{n} - 3) + 3$$

Which has a fixed point $$[3,5]\times[3,5]$$. Now obviously the original fixed point is contained in this one. Why is this so? Was that guaranteed to be true? What is the precise mathematical process by which I defined the interval update system from the original system?

We could consider the evolution of finite sets of points

```python
def update_finset(S):
   return [update(x) for x in S]

S = [ np.array([3,4]), np.array([57,34]) ]
for i in range(100):
  S = update_finset(S)
```

We could reason about 

### Propagators

http://lambda-the-ultimate.org/node/3250
The comments also note how strange it is that the paper makes little mention of CSP

-- This is a datified constraint
-- a constraint == a relation
Constraint = [ (x,y,z) | x <- digits,  y <- digits , z <- digits, x + y == z ]

We could join together all the relations, but this leads to enumerative explosion.

Instead we can store a factored representation that over approximates the possibilities.

propagate xs ys zs C = xs `intersect` [ x | (x,y,z) <- C, y' <- ys, y == y', z' <- zs, z == z' ]  , and so on.

This process is polynomial in ?. The process converges because of ?. The ordering doesn't matter because of ?
Stores are well founded. always decreasing, but ascending chain condition, so does temrinate for finite guy

S -> Status x S 
SM = {fix, nofix, subsumed}

fix,nofix,subsumed,
delta
diff(x,y) = delta
apply(delta,y) = x
apply(diff(x,y),y) = x


Events- schulte. These are kmett's filters.

Subsumption. Removing propagators for simpler ones

Contractors rather than effectful propagators. That's how you can make it pure



Explicit tabular representations suck (maybe for large stuff. Lookup tables can be surprisingly effective for small things).

What if we used metaprogramming to SHRED propagators

Instead explicit functional representations { (x,y) -> [z], ()   }
{  (x,y,z) -> ([x], [y], [z]) }
{  ([x],[y],[z]) -> ([x], [y], [z]) }

differential representiations.

contracting and monotonic on stores.
Scholze Course
Compact BitSet based contraints

sparse bitsets - good for sparse coginruous blocks


There us 

propagators in Alexey thesis
propagators in Gecode
Constraint Porgramming Handbook

Davey Priestly book
https://www.wiley.com/en-us/Introduction+to+Lattice+Theory+with+Computer+Science+Applications-p-9781118914373

Ed Kmett
https://www.youtube.com/watch?v=DyPzPeOPgUE boston haskell propagators
https://www.youtube.com/watch?v=D7rlJWc3474 monadic warsaw tutorial
https://www.youtube.com/watch?v=rAQoSjnBvtA&ab_channel=EdwardKmett - propagators live stream
youtube.com/watch?v=-DBsKQMh6n4&ab_channel=EdwardKmett propagator part 2

propagator = monotone function between join semilattice


AC3
dataflow in a cfg

ascending chain condition

ivar and promise. Promises are a definedness thing

datalog - bottom up. semi naive evaluation
bddbdddb 
doop screaming points to analysis

topological order of propagator network

datalog life lesson don't need ascending chain condition

naive propagation 
as long every 

topological sorting means fire less often or do less work
efficient delta representation drastically reduce cost

https://yanniss.github.io/points-to-tutorial15.pdf

a monoid that acts on the state
CRDTs https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type
Lindsey Kuper
filters - You can only observe filters.


If you don't want to perform any operations or receive any information about a set, it might as well be implemented by a rock.

There is a compelling simplicity to attempt to represent sets as functions. That there is one god operation from which you can derive all the others. To some degree this is true, but you always seem to leave something on the table the more you abstract your set. But also things become more composable and you have to write less..

Functions + Promises about behavior. Monotonicity for example. Or convergence

`Point -> Bool` indicator function
`Set -> Bool` or `Set -> Maybe Bool` Inside/Outside/Unknown.

Propagators/Contractors do represent sets, they do it as a partially applied intersection/meet function
`meet s :: Set -> Set`

quantifier representations - partially applied forall or exsists or hilbert epsilon
`(Point -> Bool) -> Point` = forall s


The support functions of LazySets.jl



Fixed Point Theorems
https://en.wikipedia.org/wiki/Fixed-point_theorem
https://link.springer.com/chapter/10.1007/3-540-47797-7_4 - Backhouse - galois connections and fixed point calculus



### Exact Reals

Exact reals 
What are exact reals? Any system that allows for arbitrarily accurate calculations of a number.
That means the object that represents the "real number" must not be just a pile of dead data like a float. It has to somehow be able to receive instruction about the precision required and then output the desired answer.
There is not one option or persepctive on how to represent this concept.

One that is very natural to me though is to represent such a thing as a function that takes in a precision request and outputs something like a number `Precision -> Number`. This precision could be an integer specifying the number of digits of precision, and the Number could be a rational (a numerator and denominator) or some kind of arbitrary precision float data type from a library like MPFR, or perhaps an interval of these things.


How is this different from an interval data type? An interval is a dead data, however an interval library with a precision knob can be the seeds of an exact real.

Here for example is an exact real in python that uses the `mpmath` library for all the heavy lifting. mpath has an interval type which is controlled by a global `dps` digits of precision parameter. By placing the computation of the interval into a thunk, we can compute an answer over and over searching for a small enough precision to get the one desired. This global `dps` parameter can be thought of as a precision parameter to these thunked functions, even though you don't have to pass it, as the result of the thunk depends on it's current value.



There are other formulations that store a computation graph, but this does so implicitly in the thunks.





Another representation might be a stream of improving . In python this would be built as a generator object. The two concepts are interchangeable. One could make a function that runs the generator to the desired place, or one can a generator that just asks all the precisions of the function.

Reusing an interval library like this is not the most efficient way of performing exact real arithmetic.

A fascinating 






Ok, the Bauer paper makes more sense to me.

phi -> phi- phi+


Marshall B paper
Differentiable Marshall B paper https://arxiv.org/pdf/2007.08017.pdf I guess this isn't differentiable marshallb. It's differentiable something

https://www.cambridge.org/core/books/foundations-of-probabilistic-programming/819623B1B5B33836476618AC0621F0EE foundations of probablistic programs. Chapter 3 is touching on some of the same topics

dreal paper
SMT modulo ODE paper


Exact reals::
`[Rational]` -- infinite sequence of rationals
`Stream Rational` slightly different. If [Rational] ends, we assume the last entry is a precise rational. Here, we can never know that
`Int -> Rational`  or `Rational -> Rational`
We can also replace rational (implicilty I'm assuming rational is a pair of ints representing numerator and denominator) with any other enough flexible numeric type. Fixed point, algebraic numbers, others? MPFR which is implemented as roughly some kind of rational or flips to floating point if accuracy is acceptable. Dyadic rationals.)

However, there is more of a conceptual jump to
`[Interval]`
`Int -> Interval`


A third suggestion, take the focus off of the reals and onto the functions for less a set, more Categorical flavor.
Int -> (Int, Num -> Num)  -- my suggested real lens.


Kripke model
Int -> Maybe ()
It's a chain of states labelled by the Int, such that Maybe () is increasing along the chain.
It's a monotonic graph if you call Nothing = 0 and Maybe () = 1
One could also consider counting the number of truth values - cardinality of set. 

This shows that we're in an intuitionistic kripke model
Int -> Maybe () is the model  we can evaluate a fomula under.
M |= \phi
if \phi is an intutionistic tautology, it will hold in M.


Subsets of N as represented by opaque (N -> Bool)

Truth values are (N -> Maybe ()) which tells us if question is true for N < n
(N -> Bool) -> (N -> Maybe ())

Extending what you accept as a notion of truth is very similar to extending what you consider a notion of number.
The only actual numbers are the counting numbers. And yet, one can develop intuition and comfort with the truly bizarre concept of a complex number $a + ib$ and treat it the same for a restricted set of algerbaic manipulations.
I do kind of believe that notions of truth = {true, false} is a fairly natural notion, more natural in some sense than others, and yet there is great utility in expanding your notion of truth. And these other notions of truth obey similar algebraic manipulations or notions of proof, typically just more restricted in some way. Quaternions or matrices are some kind of "number" for the pruposes of algerbaic manipulation, you just gotta be real careful about order of multiplication. I don't think I need to defend the utility of matrix multiplication. It is completely ubiquitously useful in any science that deals with numbers.



equalN :: (N -> Bool) -> (N -> Maybe ()), but in this case we can only know it's falsity. The meaninig of Maybe () is flipped.
equalEmpty :: (N -> Bool) -> (N -> Maybe ()) 


data SemiYes = MeDunno | Yes
data SemiNo  = MeDunno | No
newtype Yes = Yes
newtype No  = No
Maybe Yes
Maybe No

type Approx a = N -> a
type Eventually
type

these are both SemiNo
equalN :: (N -> Bool) -> (N -> SemiNo) # see 1 false and we can say no - other namestautology/everything/complete
equalEmpty :: (N -> Bool) -> (N -> SemiNo) # see 1 true and we can say no - empty

has_even :: (N -> Bool) -> (N -> SemiYes) # see 1 true on an even number
nonempty :: (N -> Bool) -> (N -> SemiYes) # see 1 true and we can say yes.
nontauto :: (N -> Bool) -> (N -> SemiYes)

intersect :: (N -> Bool) -> (N -> Bool) -> (N -> Bool)

exists :: (N -> Bool) -> (N -> Bool) -> (N -> Maybe Yes)
exists s1 s2 = nonempty (intersection s1 s2)

forall :: (N -> Bool) -> (N -> Bool) -> (N -> Maybe No)
forall s1 s2 = everything (diff s2 s1)




has_7 :: (N -> Bool) -> Bool -- decidable
elem :: N -> (N -> Bool) -> Bool - decidable
has_list :: [N] -> (N -> Bool) -> Bool -- this is all from prelude


Escardo posts
Seemingly Impossible Functional Programs  http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/
Searchable data types https://lukepalmer.wordpress.com/2010/11/17/searchable-data-types/
monad for infinite search in finite time http://math.andrej.com/2008/11/21/a-haskell-monad-for-infinite-search-in-finite-time/
synthetic topology of datatypes and classical spaces https://www.cs.bham.ac.uk/~mhe/papers/entcs87.pdf This really lays it all out
smythe 
vickers


Other spaces
(N -> N)
N
N -> Bool

There is something pretty about the conventions of how bottom are treated

-- sierpinski space including bottom
data T = T


id x = x
-- id bot = bot
-- id T = T

f T = undefined
--f bot = bot

f _ = T
-- f bot = T

The final one is not definable. He calls this the content of the halting problem


-- sierpinski space with gas in a total language
data S = Nat -> Maybe ()
-- equivalent
codata Delay = Done | Delay Delay
-- delay monad https://www.cs.ox.ac.uk/ralf.hinze/WG2.8/22/slides/tarmo.pdf

semidecidable indicator function
a -> T


Set disequality is semidecdiable
equal :: (N -> Bool) -> (N -> Bool) -> Maybe No

Hausdorff space = semidecidable diselquelyiu

If you used the exact reals on interval [0,1]
Could you use this for cubical type theory ish?


## Representing Sets

I feel like I wrote this down somewhere before, perhaps when Cody and Zach were talking about \pi_0 and stuff and I had no idea what they were talking about.

I don't know exactly how to organize this information. Is it a table? A graph with splitting nodes, or axes? A table with supported operations.

There are the shadows of intuitionism here or maybe terror of paradox? We don't want to say (a -> Bool) are all kinds of sets. The set of all turing machines that halt.

Sets have some other interesting representations. They can represented by partially applying operators, which are sometimes universal. I'm assuming no Haskell level bottoms here.

For finite sets, we're all good. And we can show how the isomorphism between these representations and an ordinary list representation
`[a]`
`Set a` faster indexing tree based implementation or hash table
`BDD a` decision diagram based representation
`BitVec`
`SparseSet` 
`CompactSet`


`van emde boas trees` - I guess what these support is next/prev operation.

finite sets in finite universe

Finite sets in infinite universe (ridiculously sparse in a sense)


Sparsity is an issue of complexity / performance but it is a clear mirror what is necessary for things that even make sense in an infinite context.
This is a manifestation or another angle on the similarity of the arithmetic and polynomial hierarchy.


cofinite sets in infinite universes (just store the things that aren't in the set) (cosparse)
Neither of these support the complement operation. They are not boolean algebras.
They do support set difference, union, intersection though, which makes the heyting algebras https://en.wikipedia.org/wiki/Heyting_algebra

Do they support infinite union or intersection?
finite sets support infinite intersection
conversely co finite support infinite union



finite and cofinite form a boolean algebra https://en.wikipedia.org/wiki/Cofiniteness
data Fin-CoFin a = Complement [a] | Yes [a]
We just dumbly smash them together


Weakening what you ask for:
Do you need all operations? (do you really need complement? Is relative complement good enough)




Lattices:
Everything is a lattice but these in particular have some notion of an approximate union / intersection
Linear subspaces
Intervals
Balls
Polyhedra
Octagons
Bloom Filters - Are bloom filters a lattice? i think they are. Yes. A Bloom filter can be generalized by a set cover of the universe. 
Then we keep another set structure for the cover instead of the original. disjoint cover? Not sure that's necessary.
We implicitly describe a cover via the hash function in a bloom filter. Compact spaces have finite subcovers... somehting


Convex function defined sets - support functions. Given a direction, find the hyperplane of support.
We can build a polyhedral inner and outer approximation using this.


distance functions - computer graphics



Logical predicate representations - These are connected to 
`Z3_Expr`

Free Syntax Sets
data Set = Union | Emp | Full | Complement | Intersection | Singleton
Ok. But now what?
subset :: Set -> Set -> ?
Not a problem really, we can split case by case down to nothing. Inefficient but it'd work
This is the data structure of finite-cofinite sets.

But what if we use a different base set than Singleton?



What makes ZFC powerful is the axiom schema of comprehension I think.


functional representations
`a -> Bool` is a predicate for a decidable predicate
`a -> Maybe ()` has the interpretation of a semidecidable predicate. (even though it is isomoprhic to the above)

`forall s :: (a -> Bool) -> Bool`
`exists s :: (a -> Bool) -> Bool`
`find s :: (a -> Bool) -> a` hilbert epsilon

When these quantifiers exists on their own, it's with respect to some known universe of values or else you're not even going to be able to define them.

We need a "complete basis" of sets in order to reify. This is just like linear algebra and function representations of linear spaces.
Contravariant and covariant

Type theoretic representations of sets.
I'm going way out of my element here.
(a -> Prop). Very similar in spirit to Bool. Actually, replace Bool with Prop and you get something interesting and reasonable every time.
But what the hell are these things? Well, we've moved into intuitionistic logic. That's confusing


This requires already having a base set representation
`intersect s :: set -> set`

However, if we have multiple lattices of sets
`intersect s:: approx_set -> approx_set` can be a representation of `set`






https://en.wikipedia.org/wiki/Recursive_set decidable. always can know if an element is in or not.


countable sets (computably enumerable)
We consider function parameters to be oracles. There just isn't a way to introspect them. This is a good model, since it makes intuitively clear there is no hope
There is something funny that if I give some example of a function, I'm kind of letting you look inside it
and oftentimes my examples with be decidable.
https://en.wikipedia.org/wiki/Recursively_enumerable_set
possibly infinite streams 
[a] 
Int -> a
semidecidable
open sets
Now it can be interesting to consider the true haskell bottoms.
exists :: (a -> Bool) -> ()  . If this computation terminates, it found something
find :: (a -> Bool) -> a, if this computation terminates it found something

Or if we want to be total
exists :: (a -> Bool) -> (Int -> Maybe ()) where you can give it an amount of gas.


But this is weird now. 


co countable sets. Same thing except
co-semidecidable
closed sets



What is a computer representation of the next level up?
Nested quantifiers. Why is such a thing natural.




Operations and queries on sets
An operation returns a set
a query returns something else.
Constructions on sets. To what degree are constructions and operations distinct?
query : (returns "lesser" things. Points and truth values. )
subset
seteq
find
forall
exists

operations:
union 
complement 
difference
intersection
bigunion :: S S a -> S a
singleton 
image 

construction: (builds new universes for sets to live in)
Product spaces
Disjoint union
Function spaces - This one it isn't clear that it actually constructs new set though.
Power Set

Isomorphisms/representation transformations
reify :: (a -> Bool) -> Set a -- sort of set comprehension
comprehend :: Pred -> Set a
These are inverses to some things I called queries.



Another varianrt: 
Bags = multisets, hyperloglog
Distributions
Lattice truth valued sets?

## Abstract Domains for Real Functions

Spectral vs grid methods. This is
Locality vs globality.
Smoothness 
And the two flow into each other if you use finite elements with higher degrees of flexibility.
Wavelets


Upper lower bound functions

Interval added to polynomial

Intervals on the coefficients

Constraining derivatives is different. We lose something on integration.

Solving the laplace equation

Turning iteration equalities into inclusions (Nielson book)

[https://www.cl.cam.ac.uk/~lp15/papers/Arith/](https://www.cl.cam.ac.uk/~lp15/papers/Arith/) metitarski. Get rid of strange functions by using rigourous polynomial/rational over/under approximations. Otherwise fairly standard resolution proving. + somehow using z3 to prune irrelevant crap

Taking PyRes and boosting it with z3, sympy, cvxpy sounds good

[https://blegat.github.io/publications/](https://blegat.github.io/publications/) Set programming thesis. Sets are a complex object kind of like functions

[https://github.com/SimonRohou/tubex-lib](https://github.com/SimonRohou/tubex-lib) Tubes. Here they implements functions as tubes. Basically a function is a region in 2D space. where every t is covered. A list of times [] and a list of intervals []. The integrals is easy to estimate precisely. This is a realitvely strahgtofeard persepctive. It's like the difference between polynomial methods for functions and just sampling persepctive, spectral vs finite difference

[http://benensta.github.io/pyIbex/](http://benensta.github.io/pyIbex/) [https://www.ensta-bretagne.fr/jaulin/iamooc.html](https://www.ensta-bretagne.fr/jaulin/iamooc.html)

[https://github.com/JuliaReach/ReachabilityAnalysis.jl](https://github.com/JuliaReach/ReachabilityAnalysis.jl) Lots of stuff to dig into here. Many references.

Equations that aren't equations. $latex x = \int \dot{x}dt$. We can turn this into iteration  $latex x_{n+1} = \int \dot{x}{n}dt$ or we can turn this into an inequation $latex x \subset \int \dot{x}dt$. 




11/2020

There exists the peano form and the man value form of the remainder of a taylor expansion. These formula are precise, but non constructive. They posit the existence of a point with such and such a property, but do not tell you how to find it.

The mean value theorem is a consequence of continuity. A function must take on the mean value of two endpoints of a region somewhere. This is also nonconstructive.

If we take use the mean value theorem on the derivative, we get $latex f'(x) = f'(y) 

$latex \exists y.  x_0 <= y <= x  f(x) = f(x_0) + f'(y)(x - x_o)$ The existential form of the approximation law. This is a rearrangement of the mean value theorem. 

A common tact to take is to turn this into a maximal form $latex f(x) <= f(x_0) \max_y  f(y) (x - x_0)$  $latex f(x) >= f(x_0)  + \min_y f(y) (x - x_0)$. These are less precise statement. It is also possible usually to give overestimates and underestimates for f'. One compositional method by which systematically to do so is Interval Arithmetic.

If we consider a floating point value x to represent an exact number, a numerical computer function will compute only some approximate answer $latex f*(x)$ to the ideal one. We could model this as an additive error $latex f*(x) = f(x) + \epsilon(x)$ or as a multiplicative error $latex (1 + \epsilon(x) ) f(x)$. The multiplicative error is more appropriate for modelling floating point.  https://en.wikipedia.org/wiki/Machine_epsilon

This function $latex \epsilon$ should hopefully be small if in any sense f* is a good approximation. It is unlikely that $\epsilon$ is continuous. To know $epsilon$ precisely would be the same as to know f precsiely, which is exactly the thing that is difficult. So we are in a conundrum. 

We can cut the know by determining bounds on $epsilon$. Good computer libraries computer individual primitive functions such that they are accurate to around the last bit  https://en.wikipedia.org/wiki/Unit_in_the_last_place 

[http://fredrikj.net/calcium/](http://fredrikj.net/calcium/) [https://news.ycombinator.com/item?id=24700705](https://news.ycombinator.com/item?id=24700705)

[https://news.ycombinator.com/item?id=23797302](https://news.ycombinator.com/item?id=23797302) Seemingly impossible functional programs discussion

Cantor space (N -> Bool) is compact.Compact is every open cover has a finite subcover yes? And they 

Ulrich Burger article

Simpson exact integration

[http://math.andrej.com/2011/12/06/how-to-make-the-impossible-functionals-run-even-faster/](http://math.andrej.com/2011/12/06/how-to-make-the-impossible-functionals-run-even-faster/)

The difference between exact reals and interval arithmetic is about control of thec accuracy of the output rather than input.

One way of doing this is Thinking of a real number as 

    
    <code>data Real = Approx -> Approx
    
    type Approx = Rational -- a reasonable choice
    
    But another reasonable choice is
    
    data Real   Z  -> Z
    where the first Z is the accurady 2^n  and the second number is the real in fixed point using 2^n
    
    -- The sierpinksi object. Should return control to you for the purposes of interleaving
    -- since haskell is lazy, we don't necessarily need the explicit thunk
    data SemiDecide = Thunk (() -> SemiDecide) | Yes
    
    </code>

Arbitrary precision floats are available as a library in most languages. Julia actually has them by default which impressed me very much.

The difference between arbitrary precision and exact real computation is a bit subtle. In my mind there is a hierarchy

  * Arbitrary precision floats allow you to set a precision  to do a calculation, but does not track the propagated error under multiple calculations
  * Interval arithmetic let's you set an accuracy on the input and propagate the error forward.
  * Exact Reals allow you to request the error of a _result_ of many calculations to arbitrary precision. It then figures out how much error to request of the input.

There is an implication that exact reals are going to be used on continous functions. Why? Because otherwise if you request too small an asccuracy there may be no input accuracy that gurantees it. Consider a step function evaluated at the step. What accuracy of x will guarantee an accuracy < 1 on y? De nada.  In fact the ability to request an accuracy of the output matches the rough structure of the mathematical $latex\epsilon\delta$ definition of continuity.  

We could avoid this restriction by allowing the accuracy function $latex \epsilon_y -> \delta_x $ to be partial $latex \epsilon_y -> Maybe \delta_x $ if that us what we desire.

Interval arithemtic does not have the implication. The only thing that happens if interval arithemtic is applied to a discontuous function is that we may lose the ethereal property that the size of the result interval goes to 0 when the input interval does.

A point of this post is that we can take arbitrary precision and interval calculations along with a sufficiently generic implementation of automatic differentiation and fairly easily boost them into a form of exact reals with some desirable seeming properties.

A Lens is an interesting and useful example of a forward-backward pass algorithm. It may be related to the "There and Back Again" notion of Danvy. 

It is a relative of the coroutine or the stream processor. Whereas stream processors and coroutines allow dynamic choice of control flow, the lens has the static assumption built into it's type sugnature and structure that There will be a single forward and backward pass, in which the backward pass may use information saved from the forward pass. 

We can extend this to multiple passes, or dynamic control flow structure. 

This control flow can be obfuscated somewhat usefully into a continuation passing style. Continuations are well known as being a technique to gain first class access to control flow.

In a previous post, I was noting how similar interval arithmetic is to automatic differentiation. Simple dual number forward mode automatic differentiation carries along an extra number representing the derivative through a calculation. 

This number characterizes the properties of the function in an infinitesimal neighborhood around the evaluation point.

In interval artihmetic, you can carry an $latex \epsilon$ along with a number. This gives a bound on how 

These bounds and the value of the derivatives are directly related by [Taylor's theorem](https://en.wikipedia.org/wiki/Taylor%27s_theorem), something you probably rightfully ignored the first time they taught you it in calculus class.

There is a hierarchy of conditions about the smoothness and well behavedness of functions. [https://en.wikipedia.org/wiki/Lipschitz_continuity](https://en.wikipedia.org/wiki/Lipschitz_continuity) Requiring something be differentiable is stronger than requiring it to be continuous.

I think it often makes sense to consider the accuracy desired from a computation as a statically known (compile time) quantity. Or at least very slowly changing, in which case it makes sense to JIT a fast version. The interval and automatic differentiation passes can be considered a straightforward form of static analysis done in order to produce fast calculation code that is correct to spec.

It may make sense to use raw floats when it is statically known that these are sufficient. This will probably be faster although there will be cost associated with moving in and out of the arbitrary precision library

Belnap Booleans. There is somne funny business associated with the exact reals. Because they are so heavily entrenched in approximation, this infects other data types too. If I want to know if 0 <x < 1, but have only calculated x to precision 7, what is the appropriate boolean answer? The truth is at that precision we don't have enough information to know. In addition, some decisions may not effect the final result sufficiently to be important. if I test if x > 42.8 and then add 0.0000001 to the result if so, 

Higher order exact structures. There has been some interest and work lately in higher order (in the sense of first class fucntions) automatic differentiation. One wants to consider sequences N -> R and functions R -> R also (and beyond).

Heyting algebra and open sets.  The simplicial model of open sets. Points aren't open in the common model. Let's consider a triangulzation of some shape where we have faces, lines, and vertices. A face does not include it's edges, and a line does not include it's vertcies. We have a simple discrete model then of the topology of this shape. The open sets are arbitrary unions of faces, plus we're allowed sets with lines if all the faces that touch those lines are in the set, and vertices if all the lines are in the set. We can consider mappings the powersets of these things to the other powersets. If all the open sets in the codomain come from open sets in the domain, then this is a continuous map. The

[https://dl.acm.org/doi/abs/10.1145/3385412.3386037](https://dl.acm.org/doi/abs/10.1145/3385412.3386037) Toward an API for real numbers

MarshallB used for CAD [https://dl.acm.org/doi/pdf/10.1145/3341703](https://dl.acm.org/doi/pdf/10.1145/3341703)  [https://www.youtube.com/watch?v=h7g4SxKIE7U](https://www.youtube.com/watch?v=h7g4SxKIE7U) - Ben Sherman giving a talk on this [https://www.ben-sherman.net/publications.html](https://www.ben-sherman.net/publications.html)  some other related publications and thesis

  [https://www.youtube.com/watch?v=f8fivVYdGlg](https://www.youtube.com/watch?v=f8fivVYdGlg) - Norbert Muller 

  

Sierpinski space - semidecidable propositions. You can't have a (non trivial) continuous map into the booleans with the discrete topology. Is this a way to force a computation to a certain precision. Sierpinski feels somewhere between unit and bool. It is something like unit with lazy semantics. We only need to force the computation that returns unit when we inspect it

Semidecidable sets and Heyting Algebra. Semidecidable sets have the curious property that the complement may not also be a semidecidable set

Decidable sets and finite sets. 

What is a set?

What questions do we desire to ask of sets. How do we use them? [http://math.andrej.com/2008/02/06/representations-of-uncomputable-and-uncountable-sets/](http://math.andrej.com/2008/02/06/representations-of-uncomputable-and-uncountable-sets/)

  * union
  * intersection
  * complement
  * difference
  * subset inclusion?
  * element of?
  * select arbitrary
  * empty?
  * full?
  * minimum/maximum
  * equality?
  * power set
  * size?
  * comprehension  - a fundamental reflection principle

What are the canonical examples of constructions or questions about sdpecific sets. Uses?

For finite sets we can form a finite list of the objects in it. We can use fast data structures that use the ability of elements to be compared.

One functional formulation of set is (A -> Bool). This is `elem S`. We can reconstruct S given a complete set [  x | x <- enumAll, f x ]

Another functional set is `all S :: (A -> Bool) -> Bool`, `any S :: (A -> Bool) -> Bool`

Instead of directly using a functional representation, we can use an AST that is interpretable into the functional representation. Every data structure is a program with a stretched definition of program. AST v data structure is not a meaningful distinction

For countably infinite sets we can use lazy lists to represent them [ ]

Sets as ASTs of their operations `data SetN = LTE n | union SetN SetN | InterSect Setn Setn | Not SetN.`

Mac Lane and Moredijk

Stone Spaces, Categories Allegories

Topos Logos

CPOs. Partially ordered sets that always 

Lattice, semilattice.

Ed Kmett and his propagators.

Barendregt book

Heyting Algebra - Intuitionisitic logic. => isn't just not A \/ B. Why? Intepreting the => operation into 0, .5,  1. You can calculate a value. Pretty funny. => is interior complement. You miss the boundary.

Boolean algebra

Filters, nets, directed sets, ideals, sieves

directed set any two elements have another element that is an upper bound (not necessaruly least, which distinguishes from filter I think)

Regular Logic and Geometrical logic. Weakened forms of logic. Infinitary disjunction. Not supers sure what that means. Regular has forall x. phi(x) -. psi(x). phi an psi include /\ and exists only. Geometrical logic has inifintary disjunction, which has the flavor of topology

What does a categorical limit have to do with a ordinary notion of limit

Exact Reals. Marshall. My other blog post. Belnap bools. Sierpinski space. Functions to () can be interesting if you consider bottom

Abstract Stone Duality. [http://www.paultaylor.eu/ASD/intawi/intawi.pdf](http://www.paultaylor.eu/ASD/intawi/intawi.pdf) [http://www.paultaylor.eu/](http://www.paultaylor.eu/)

Open subsets are semidecidable

Theory of Approximation. Belnap [http://www.pitt.edu/~belnap/howacomputershouldthink.pdf](http://www.pitt.edu/~belnap/howacomputershouldthink.pdf)

Domain theory. Denotation as computable functions. [http://www.cs.nott.ac.uk/~pszgmh/domains.html](http://www.cs.nott.ac.uk/~pszgmh/domains.html) phenomenol.

[https://en.wikibooks.org/wiki/Haskell/Denotational_semantics](https://en.wikibooks.org/wiki/Haskell/Denotational_semantics)

[http://comonad.com/reader/2015/free-monoids-in-haskell/](http://comonad.com/reader/2015/free-monoids-in-haskell/)

Lisp in Small Pieces. Schmidt denotiational semantics

Monotonic and continous

Dana Scott papers - Data types as lattices, 

[https://en.wikipedia.org/wiki/Domain_theory](https://en.wikipedia.org/wiki/Domain_theory)

[https://en.wikipedia.org/wiki/Scott_continuity](https://en.wikipedia.org/wiki/Scott_continuity)

[https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space](https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space)

[http://math.andrej.com/2014/05/08/seemingly-impossible-proofs/](http://math.andrej.com/2014/05/08/seemingly-impossible-proofs/)

Baire Space.  Cantor Space.

[https://link.springer.com/chapter/10.1007/BFb0055795](https://link.springer.com/chapter/10.1007/BFb0055795) exact real functionals

What about Jules Hedges thesis? Did he say something like the Intermeidate value theorem is a functionaL?

