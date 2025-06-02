{-# OPTIONS --without-K --safe #-}
--module playin where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat
open import Data.List

-- Escardo


-- Hottest course


-- Jacques Carette: "What I learned from formalizing Category Theory in Agda"
-- https://www.youtube.com/watch?v=VQiQtH47pbM&ab_channel=ToposInstitute


--open import IO
-- https://agda.readthedocs.io/en/latest/getting-started/a-taste-of-agda.html

data mybool : Set where
  mytrue myfalse : mybool
  

-- main = run (putStrLn "Hello, World!")

foo : Bool -> Bool
foo true = false
foo false = true

-- inv : forall x y : A, x = y -> y = x
-- inv x y refl = refl

-- Set got renamed to Type in some libraries?
-- https://proofassistants.stackexchange.com/questions/4189/why-does-agda-use-set-instead-of-type

myid : (X : Set) -> X -> X
myid X x = x

-- ? for goals

myinv : {A : Set} -> (x y : A) -> x ≡ y -> y ≡ x
myinv x y _≡_.refl = _≡_.refl



foo' : ℕ
foo' = 3

mylength : {A : Set} -> List A -> ℕ
mylength [] = 0
mylength (x ∷ xs) = 1 + mylength xs


flum = mylength (1 ∷ [])


data MyFin : ℕ -> Set where
  i : {n : ℕ} -> MyFin(n) -> MyFin (suc n)
  star : {k : ℕ} -> MyFin (suc k)



myfin2 : ℕ -> Set
myfin2 zero = ⊥
myfin2 (suc n) = (MyFin n) ⊎ ⊤

to1 : {n : ℕ} -> MyFin n -> myfin2 n
to1 (i x) = {!   !}
to1 star = {!   !}

