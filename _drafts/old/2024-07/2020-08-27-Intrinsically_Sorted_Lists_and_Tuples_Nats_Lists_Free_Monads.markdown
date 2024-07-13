---
author: philzook58
comments: true
date: 2020-08-27 16:06:49+00:00
layout: post
link: https://www.philipzucker.com/?p=2519
published: false
slug: Intrinsically Sorted Lists and Tuples, Nats, Lists, Free Monads
title: Intrinsically Sorted Lists and Tuples, Nats, Lists, Free Monads
wordpress_id: 2519
---

Unordered pairs <https://byorgey.github.io/blog/posts/2024/06/25/unordered-n-tuple-product.html>
`(a -> Bool) -> Either Bool (a,a)` That's neat. You find the pieces of a set by using separation predictaes (a form of observation?). You could use separation. It's kind of like delayed notion of ordering. The obvious (a -> Bool) is (> 42) as a splitter for a tree. Observations like these work even in egglog sets.

Sometimes you can express interesting datatypes that feel like they might require dependent types using ordinary datatypes.
A nonempty list is a simple example. This could be represented as a dependent sum `{l : list | l != nil}`, but obviously it is representable as `type 'a nonempty = 'a * 'a list`. You simply unroll the list one layer and remove the nil case. Maybe this is clunky to keep making new types for different prpoperties.

Another interesting one is an intrinsically sorted list of ints. It is simply `type slist = Nil | Cons1 of int * nat list`. The list of nats is a list of _differences_ of subseqeunt elements. This can either represent a ascending list or a descending list

We may think of nat as `type nat = Zero | Succ of nat` or we may think of unsigned integers `uint64` if that tickles some other part of your brain. Obviously peano nats are nothing but toys / proof data. `uint64` there may be something to though.

I think it's interesting to merge the list and nat type even further, floating the Succ. We lose redundant succs then. This is reminscent of a coo ltrick I've seen in de bruijn indices where you float the succ of the variable. This lends itself to equational rewriting (pavel post) and a semantic interpretation (oleg ski).

```ocaml
type slist = Nil | Cons of slist | Succ of slist

(*wrong. Maybe I need to reverse the slist first? 
Or just return the reverse slist

append ~ merge
*)
let append x y = match x,y with
    | Nil, y -> y
    | x, NIl -> x
    | Cons x, y -> Cons (append x y)
    | x, Cons y -> Cons (append x y)
    | Succ x, Succ y -> Succ (append x y)

let single x = 
    let rec worker acc x = match x with
    | Zero -> acc
    | Succ x -> worker (Succ acc) x
    in
    Cons (worker Nil x)

let cons x xs = append (single x) xs

type rlist = Nil | Cons of rlist | Pred of rlist
```

What does it mean generally to take a property and make it baked into the structure of and ADT? Any decidable property we can enumerate. We do desire some kind of pleasant interpretation of the resulting structre rather than an arbitrary enumeration though. Perhaps this means some kind of homomorphism property or efficiency / locality of going in and

Also interesting to consider infinite ascending sequences.

2021-8-18

Abstract Data types vs even open representations that can't even express a violating thing.
Different games.

Even and Odd numbers.
These are of course representable as abstract data types.
They need validators that return options to go into. Int -> Option<Even>

You can either just store the original int, or store the int div 2 so non evens become inexpressible.

This vs { x : nat | exists m, n = 2 * m}
Really the same thing huh. Again brings up what really is the point of dependent types.

only integers greater than 10. Just add 10 to internal rep.
GT<10>

Union - tagged union.
Intersection - tuple.

There are bit patterns on your machine. How we choose to interpret them is up to us.

Ok what about a list of elements that only implement comparison.

```
class Even():
    def __init__(self,x):
        self.x = x / 2
    def __mul__(self,rhs):

```

2020-8-27

There is a fun analogy between Natural numbers, Lists and Free monads.

Nats have many representations. Some of these are things that feel like they are different in standard mathemtics, some are data structure choices

* Peano data type `data Nat = Zero | Succ Nat`
* Bohm-Berarducci/recursor/church encoding `(a -> a) -> a -> a` / (a -> a) -> (a -> a). Which way is nicer to think about? A numeral is a higher order function that applies an incoming function that many times. It's interesting how writing the parenthesis really makes my mind look at it in a different way
* Binary
* Prime factorization
* Free Semiring

Lists also have some interesting representations

* [a]
* Hughes Lists [a] -> [a]
* Bohm bearducci lists. (a -> s -> s) -> s -> s
* Okasaki Lists

Free Monad representations

* data Free f a = Fix (f (Free f a)| Pure a
* Reflection without Remorse
* Codensity monad

There is a little table here in which we can recognize the equivalents to each other in some positions, but not others.

The Nats freely allow you to always add 1, lists freely allow you to append 1 more element, free monads always allow you to wrap one more time with `return`

Difference lists and the integers [[https://en.wikipedia.org/wiki/Difference_list](https://en.wikipedia.org/wiki/Difference_list)](<https://en.wikipedia.org/wiki/Difference_list#:~:text=In%20computer%20science%2C%20the%20term,difference%20of%20those%20two%20lists.&text=The%20second%20data%20structure%20is,with%20an%20efficient%20concatenation%20operation>.). The integers can be thought of as pairs of naturals that are considered equivalent when their difference is equivalent. This is similar to the more familiar construction of the rationals from pairs of integers. The prolog community has a use case for similar flavored lists. Interestingly there is a similar construction that was also found useful for typelevel addition in ocaml [http://www.kb.ecei.tohoku.ac.jp/ml2008/slides/lindley.pdf](http://www.kb.ecei.tohoku.ac.jp/ml2008/slides/lindley.pdf) . Oh. That's interesting. They represent numbers kind of in the church style as the pair ('a, 'a succ succ). This is like my unification relations thing. Is it possible at all to have some kind of branching behavior? I feel like this gives a plausible definition of type subtraction. And similarly type fractions.

    <code>(a' true, 'a, 'b)  and ('b false, 'a, 'b)
    (true, 'a, 'b, 'a)  and (false, 'a, 'b, 'b) or rather ('a, 'b, 'a)  and ('a, 'b, 'b)
    
    zero ~ ('s, 'z, 'z) , (('s,'z1, 'z1), 'z, 'z1 )
    We can use unification to kind of replace higher order functions.</code>

What's next up the chain? An even higher kinded type. Nat :: _, List ::_ -> _, Free :: (_ -> _) -> (_ -> *).  It looks like some kind of bird. `BirdParty :: ((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))`

Is this related to the homotopy path idea? Paths need fancy types because we want to make sure they stay continuous. An intrisnic way to enforce this is to use udlr directions. Bad paths are then unrepresentable. However, There may be obstructions to doing this globally. Boundaries. Perhaps those obstructions are exactly homotopy or some topological concept? We can't get a global chart equivalent to a grid? It seems like a solidly 2 dimensional shape can be triangulated. We need a mapping of moves + position -> newposition.

11/19

Parse Don't Validate [https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/) Alexis King

One of the simplest algorithmic tasks is sorting an array or list.

This is an example where it is interesting to explore how a sorted list can be represented. It is possible to represent sorted lists without using fancy types. The idea is to store your data structure in a way as to make an unsorted value unrepresentable.

It is interesting to consider

Storing Differences

    <code>data Nat = Z | S Nat
    newtype Nat = Nat Int
    newtype SList a = SList [Nat]
    Enum a => SList a -> [a]
    </code>

Bucket Sort. A count can be used to reconstruct a sorted list.

    <code>type SList a = Map a Int
    -- if a = Rep f
    type SList a = f Int</code>

Unique

Sorted Unique

Sorted Tuples

Connection to bosons and fermions

There are three main types of quantum many-particle systems. Distinguishable particles, bosons and fermions.

Suppose we describe a particle that can be on four possible sites. For each of these sites, there is a complex amplitude. The square of this amplitude is the probability that the particle is on the site.

    <code>type Box a = V4 a
    type Q = Complex Double
    type Psi = Box Q
    data Spot = A | B | C | D</code>

If we had two distinguishable particles, we have amplitudes for every possible

    <code>type TwoPart = Box (Box Q)
    type ThreePart = Box (Box (Box Q))</code>

The act of inserting a particle in the box $latex a^\dagger$ would be an operator of the signature

    <code>adag23 :: Spot -> TwoPart -> ThreePart
    adag23 A v = V4 v vzero vzero vzero
    adag23 B v = V4 vzero v vzero vzero
    adag23 C v = V4 vzero vzero  v vzero
    adag23 D v = V4 vzero vzero vzero v</code>

Fock space of distinguishable particles is the[cofree comonad](http://hackage.haskell.org/package/free-5.1.2/docs/Control-Comonad-Cofree.html) of the one particle wavefunction type `Box`. It has an amplitude associated with every number of particle and position combination. It is free closure of kronecker producting states. Tensor producting is a functor.

You can only get away with this kind of shit with laziness.

    <code>data CoFree f a = a :< (f (Cofree f a)) 
    type CoFree Box Q ~ (Q, Psi, TwoPart, ThreePart, ...)  </code>

The first amplitude is that associated with the vacuum state with no particles.

Bosons are described by wavefunctions that are symmetrical with respect to interchange of particles. We could describe this using the `Fock` type above and restricting ourselves only to symmetrically created states. This feels rather inefficient.

Instead we can just count how many particles are in each state.

One technique is to pick a canonical ordering to the states and just list them in order

The counting representation is similar to the bucket sort reprsentation of lists

    <code>
    type Boson = Q (f Int)
    type Fermion = Q (f Bool)</code>

Fermions are wavefunctions described by wavefunctions that are antisymmettric under interchange of two particles. Because of the Pauli-Exclusion principle, no two fermions can be in the same state. This implies that a site can either have a fermion or not .

Unordered pairs. (a,a) -> ({a,a},Bool)

The sorted pair has the universal property that monotonic functions
