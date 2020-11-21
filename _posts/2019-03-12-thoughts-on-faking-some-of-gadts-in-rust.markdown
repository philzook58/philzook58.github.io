---
author: philzook58
comments: true
date: 2019-03-12 19:21:06+00:00
layout: post
link: https://www.philipzucker.com/thoughts-on-faking-some-of-gadts-in-rust/
slug: thoughts-on-faking-some-of-gadts-in-rust
title: Thoughts on Faking Some of GADTs in Rust
wordpress_id: 1867
tags:
- gadts
- haskell
- rust
---

I’m a guy who is somewhat familiar with Haskell who is trying to learn Rust. So I thought I’d try to replicate some cool Haskell functionality in Rust. I would love to hear comments, because I’m trying to learn. I have no sense of Rust aesthetics yet and in particular I have no idea how this interacts with the borrow system. What follows is a pretty rough brain dump


GADTs (Generalized algebraic data types) are an extension in Haskell that allows you to write constrained type signatures for your data constructors. They also change how the type checking of pattern matching is processed.

GADTs are sometimes described/faked by being built by making data types that hold equality/unification constraints. Equality constraints in Haskell like `a ~ Int` are fairly magical and the Rust compiler does not support them in an obvious way. Maybe this is the next project. Figure out how to fake ’em if one can. I don’t think this is promising though, because faking them will be a little wonky, and then GADTs are a little wonky on top of that. See https://docs.rs/refl/0.1.2/refl/ So we’ll go another (related) road.

This is roughly what GADTs look like in Haskell.
```
data MyGadt a where
  TBool :: Bool -> MyGadt Bool
  TInt :: Int -> MyGadt Int
```

And here is one style of encoding using smart constructors and a typeclass for elimination (pattern matching is replicated as a function that takes callbacks for the data held in the different cases). Regular functions can have a restricted type signature than the most general one their implementation implies. The reason to use a typeclass is so that we can write the eliminator as returning the same type that the GADT supplies. There isn’t an explicit equality constraint. A kind of Leibnitz equality `(forall f. f a -> f b)`is hiding in the eliminator. The Leibnitz equality can be used in place of (~) constraints at some manual cost. [](http://code.slipthrough.net/2016/08/10/approximating-gadts-in-purescript/)


```
data MyGadt2 a = TBool2 Bool | TInt2 Int
-- smart constructors. Hide the original constructors
tInt :: Int -> MyGadt2 Int
tInt = TInt

tBool :: Bool -> MyGadt2 Bool
tBool = TBool

-- gadt eliminator
class MyGadtElim a where
   elimMyGadt :: forall f. MyGadt2 a -> (Bool -> f Bool) -> (Int -> f Int) -> f a

instance MyGadtElim Int where
   elimMyGadt (TInt2 x) fb fi = fi x
   elimMyGadt _ _ _ = error "How did TBool2 get type MyGadt2 Int?"
instance MyGadtElim Bool where
   elimMyGadt (TBool2 x) fb fi = fb x
```
The `forall f :: * -> *` is a problem for Rust. Rust does not have higher kinded types, although they can be faked to some degree. https://gist.github.com/CMCDragonkai/a5638f50c87d49f815b8 There are murmurs of Associated Type Constructors / GATs , whatever those are , that help ease the pain, but I’m pretty sure they are not implemented anywhere yet.
I’m going to do something related, a defunctionalization of the higher kinded types. We make an application trait, that will apply the given type function tag to the argument. What I’m doing is very similar to what happens in the singletons library, so we may be getting some things for free.

https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/

```rust
trait App1 { type T;}
Then in order to define a new typelevel function rip out a quick tag type and an App impl.

struct F1 {}
impl App1 for F1{
    type T = Vec>;
}
```
It might be possible to sugar this up with a macro. It may also be possible to write typelevel functions in a point free style without defining new function tag names. The combinators Id, Comp, Par, Fst, Snd, Dup, Const are all reasonably definable and fairly clear for small functions. Also the combinator S if you want to talk SKI combinatory calculus, which is unfit for humans. https://en.wikipedia.org/wiki/SKI_combinator_calculus For currying, I used a number for how many arguments are left to be applied (I’m not sure I’ve been entirely consistent with these numbers). You need to do currying quite manually. It may be better to work with tuplized arguments

```rust
struct Vec1 {} // number is number of aspplications left.
impl App1 for Vec1{
    type T = Vec;
}

struct Id();

impl App1 for Id{
    type T = A; 
}

// partially applied const.
// struct Const()
// call this next one const1
struct Const1();
struct Const(PhantomData); // should be Const1
impl App1 for Const1 { // partial application
    type T = Const;
}

impl App1 for Const{
    type T = B; 
}



struct Fst {}
impl  App1<(A,B)> for Fst {
    type T = A;
} 

struct Snd {}
impl  App1<(A,B)> for Snd {
    type T = B;
} 


struct Dup{}
impl  App1 for Dup {
    type T = (A,A);
} 

struct Par2 {}
struct Par1 (PhantomData);
struct Par (PhantomData , PhantomData );
impl App1 for Par2 {
    type T = Par1;
}
impl App1 for Par1 {
    type T = Par;
}

impl App1<(X,Y)> for Par where F : App1, G : App1  {
    type T = (F::T, G::T);
}

// In order to curry, i think I'd have to define a name for every curried form.


// combinator calculus Const is K, Id is I, and here is S combinator. Yikes.
type I = Id;
type K = Const;

struct S3{}
struct S2(PhantomData);
struct S1(PhantomData, PhantomData);
// struct S(PhantomData, PhantomData, PhantomData);
impl  App1 for S1 where A : App1, B : App1, >::T : App1< >::T > {
    type T =  < >::T   as App1< >::T > >::T;
}  


struct Comp2();
struct Comp1 (PhantomData);
struct Comp (PhantomData, PhantomData);
impl App1 for Comp where G : App1, F : App1<>::T> {
    type T =  >::T>>::T;
}  
Anyway, the following is a translation of the above Haskell (well, I didn’t wrap an actual i64 or bool in there but I could have I think). You need to hide the actual constructors labeled INTERNAL in a user inaccessible module.

enum Gadt {
    TIntINTERNAL(PhantomData),
    TBoolINTERNAL(PhantomData)
    
}
// then build the specialzied constructors that 
fn TBool() -> Gadt{
    Gadt::TBoolINTERNAL(PhantomData)
}

fn TInt() -> Gadt{
    Gadt::TIntINTERNAL(PhantomData)
}
```
The smart constructors put the right type in the parameter spot

Then pattern matching is a custom trait per gadtified type. Is it possible to unify the different elimination traits that will come up into a single Elim trait? I’m 50-50 about whether this is possible. What we’re doing is a kind of fancy map_or_else if that helps you.

https://doc.rust-lang.org/std/option/enum.Option.html#method.map_or_else
```
trait GadtElim {
    type Inner;
fn gadtElim(&self, case1 : >::T   , case2 : >::T ) -> >::T  where 
         F : App1,
         F : App1,
         F : App1;
         

}


impl GadtElim for Gadt {
    type Inner = i64;
    fn gadtElim(&self, case1 : >::T   , case2 : >::T ) -> >::T  where 
         F : App1,
         F : App1,
         F : App1{
        match self{
            Gadt::TIntINTERNAL(PhantomData) => case2,
            Gadt::TBoolINTERNAL(PhantomData) => panic!("Somehow TBool has type Gadt")// Will never be reached though. god willing
        }
    }
}
impl GadtElim for Gadt {
    type Inner = bool;
    fn gadtElim(&self, case1 : >::T , case2 : >::T ) -> >::T  where 
         F : App1,
         F : App1,
         F : App1{
        match self{
            Gadt::TIntINTERNAL(PhantomData) => panic!("Somehow TInt has type Gadt"),
            Gadt::TBoolINTERNAL(PhantomData) => case1 // Will never be reached though. god willing
        }
    }
}
```
Usage. You have to explicitly pass the return type function to the eliminator. No inference is done for you. It’s like Coq’s match but worse. BTW the dbg! macro is the greatest thing on earth. Well done, Rust.
```rust
    let z = TInt().gadtElim::(true , 34);
    let z2 = TBool().gadtElim::(true , 34);

    dbg!(z);
    dbg!(z2);
    struct F7 {} // You need to do this. Kind of sucks. macroify? App!(F = Vec)
    impl App1 for F7 { type T = Vec; }
    dbg!(TInt().gadtElim::(vec!(true,false) , vec!(34,45,4,3,46)));
```
You can make helpers that don’t require explicit types to be given
```rust
fn gadtRec(x : impl GadtElim, case1 : A, case2 : A) -> A {
    x.gadtElim::>(case1 , case2)
}
```
One could also make an Eq a b type with Refl similarly. Then we need typelevel function tags that take two type parameter. Which, with currying or tupling, we may already have.

Questions:

Is this even good? Or is it a road of nightmares? Is this even emulating GADTs or am I just playing phantom type games?

We aren’t at full gadt. We don’t have existential types. Rust has some kind of existential story evolving (already there?), but the state of it is confusing to me. Something to play with. Higher rank functions would help?

Are overlapping typeclasses a problem in Rust?

Again, I have given nearly zero thought to borrowing and how it interacts with this. I’m a Rust n00b. I should think about it. Different eliminators based on whether you own or are borrowing?.

How much of singleton style dependent types do we get from this? It feels like we have already paid the cost of defunctionalizing. http://hackage.haskell.org/package/singletons

My current playground for this is at [](https://github.com/philzook58/typo)

Edit: Rust is an ML with affine types and a syntax facelift roughly. So Ocaml is a good place to pump. Oleg Kiselyov had a fascinating approach that sort of smuggles through an Option type in an equality type using mutation. I wonder how well that would mesh with Rust. It seems obviously not thread safe unless you can make the mutation and matching atomic.

[](http://okmij.org/ftp/ML/GADT.txt)

[](okmij.org/ftp/ML/first-class-modules/)

[](https://blog.janestreet.com/more-expressive-gadt-encodings-via-first-class-modules/)