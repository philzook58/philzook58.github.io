module play where

open import IO

main = run (putStrLn "Hello World")

{-  This is a comment -}
{- You may want detexify open -}


module Boolplay where
  data Bool : Set where
    true : Bool
    false : Bool

  not : Bool -> Bool
  not true = false
  not false = true

  data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero + m = m
  suc n + m = suc (n + m)

  _*_ : Nat -> Nat -> Nat
  zero * m = zero
  suc n * m = m + (n * m)

  _or_ : Bool -> Bool -> Bool
  true or _ = true
  _ or true = true
  false or false = false

  data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A
  identity : {A : Set} -> A -> A
  identity x = x

  zero' : Nat
  zero' = identity zero
  
  identity2 : {A : Set} -> A -> A
  identity2 = \x -> x

  _∘_ : {A  : Set} {B : A -> Set} {C : (x : A) -> B x -> Set}
        (f : { x : A } -> (y : B x) -> C x y )  (g : (x : A) -> B x)
        (x : A) -> C x (g x)
  (f ∘ g) x =  f (g x)

  map : {A B : Set} -> (A -> B) -> List A -> List B
  map f [] = []
  map f (x :: xs) = f x :: (map f xs)


  data Vec (A : Set) : Nat -> Set where
    [] : Vec A zero
    _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

  head : {A : Set} {n : Nat} -> Vec A (suc n) -> A
  head (x :: xs) = x

  vmap : { A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
  vmap f [] = []
  vmap f (x :: xs) = (f x) :: (vmap f xs) 

  data Image_∋_ {A B : Set} (f : A -> B) : B -> Set where
    im : (x : A) -> Image f ∋ f x
  3SUC : Image suc ∋ (suc (suc zero))
  3SUC = im (suc zero)
  inv : { A B : Set} (f : A -> B) (y : B) -> Image f ∋ y -> A
  inv f .(f x) (im x) = x
  data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (suc n)
    fsuc : {n : Nat} -> Fin n -> Fin (suc n)
  magic : {A : Set} -> Fin zero -> A
  magic ()
  _!_ : {A : Set} {n : Nat} -> Vec A n -> Fin n -> A
  (x :: xs) ! fzero = x
  (x :: xs) ! (fsuc i) = xs ! i

  tabulate : {n : Nat} {A : Set} -> (Fin n -> A) -> (Vec A n)
  tabulate {zero} f = []
  tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

  data False : Set where
  record True : Set where
  trivial : True
  trivial = _
  isTrue : Bool -> Set
  isTrue true = True
  isTrue false = False

  data Dec (A : Set) : Set where
   yes : A -> Dec A
   no : (A -> False) -> Dec A

  data le : Nat -> Nat -> Set where
   lerefl : {n : Nat } -> le n n
   lesuc : {n m : Nat} -> le n m -> le n (suc m)

  lezero : (n : Nat) -> le zero n
  lezero zero = lerefl
  lezero (suc n) = lesuc (lezero n)

  lesuc2 : {n m : Nat} -> le n m -> le (suc n) (suc m)
  lesuc2 {zero} {.zero} lerefl = lerefl
  lesuc2 {zero} {.(suc _)} (lesuc p) = lesuc (lesuc2 p)
  lesuc2 {suc n} {suc .n} lerefl = lerefl
  lesuc2 {suc n} {suc m} (lesuc p) = lesuc (lesuc2 p)

  lesecnot : {n m : Nat} -> (le n m -> False) -> le (suc n) (suc m) -> False
  lesecnot f lerefl = f lerefl
  lesecnot {zero} {suc m} f (lesuc p) = lesecnot (λ z → f (lesuc z)) p
  lesecnot {suc n} {suc m} f (lesuc p) = lesecnot (λ z → f (lesuc z)) p
  

  ledec : (n m : Nat) -> Dec (le n m)
  ledec zero zero = yes lerefl
  ledec (suc n) zero = no (λ ())
  ledec zero (suc n)  = yes (lesuc (lezero n))
  ledec (suc n) (suc m) with ledec n m
  ...                        | yes p = yes (lesuc2 p)
  ...                        | no p  = no (lesecnot p)

  min : Nat -> Nat -> Nat {- The proof form of min should be n <= m? No I want a number   -}
  min zero _ = zero
  min _ zero = zero
  min (suc n) (suc m) = suc (min n m)

  min2 : Nat -> Nat -> Nat
  min2 x y with ledec x y
  ...           | yes p = x
  ...           | no p  = y

  pf1 : (x y : Nat) -> le (min2 x y) x
  pf1 zero zero = lerefl
  pf1 zero (suc y) = lerefl
  pf1 (suc x) zero = lesuc (lezero x)
  pf1 (suc x) (suc y) with ledec x y
  ...                      | yes p = lerefl
  ...                      | no p = {!!}
  open import Data.Product
  mintup : Nat × Nat -> Nat
  mintup = uncurry min
  mintup3 : Nat × Nat × Nat -> Nat
  mintup3 (x , ( y , z) ) = min x (min y z)
  max : Nat -> Nat -> Nat
  max zero x = x
  max x zero = x
  max (suc n) (suc m) = suc (max n m)

  sorttup : Nat × Nat -> Nat × Nat
  sorttup (x , y) = (min x y , max x y)
  
  {- Is there an intrinsically commutative definition of addition?
     Vecotr of typex   -}
  open import Data.Sum
  addtype : Set ×  Set -> Set × Set -> Set × Set
  addtype ( a , b  ) (c , d) = ( (a ⊎  c) , (b ⊎ d ) )




open import Function

open import Data.Rational
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

myrat : ℚ
myrat = normalize 1 2

myrat2 : ℚ
myrat2 = normalize 2 4

mypf : myrat ≡ myrat
mypf = refl

mypf2 : myrat ≡ myrat2
mypf2 = refl

mypf3 : (myrat + myrat) ≡ (normalize 1 1)
mypf3 = refl

open import Relation.Nullary
whatis : Dec (myrat ≤ myrat)
whatis = myrat  ≤? myrat


{-
mypf4 : (x : ℚ) -> (0ℚ + x) ≡ x
mypf4 x = {!  !}  
-}
 {-  +-identityʳ  +-identityˡ -}
open import Data.Bool



