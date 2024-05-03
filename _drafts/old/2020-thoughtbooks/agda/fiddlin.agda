
open import Data.Bool


xor : Bool -> Bool -> Bool
xor true true = false
xor false true = true
xor true false = true
xor false false = false


open import Data.List

open import Data.Unit
--open import Data.Void
open import Data.Float

foo : Float
foo = 1.2

open import Data.Empty

open import Relation.Nullary

buz : ¬ ⊥
buz = λ z → z


isTrue : Bool -> Set
isTrue true = ⊤
isTrue false = ⊥


open import Data.Nat

lt : ℕ -> ℕ -> Bool
lt _ zero = false
lt zero (suc n) = true
lt (suc n) (suc m) = lt n m


length' : {A : Set} -> List A -> ℕ
length' [] = zero
length' (x ∷ xs) = suc (length xs)


lookup' : {A : Set} (l : List A) (n : ℕ) (p : isTrue (lt n (length l))) -> A
lookup' [] n ()
lookup' (x ∷ xs) zero _ = x
lookup' (x ∷ xs) (suc n) p = lookup' xs n p

open import Relation.Binary.PropositionalEquality

data Parity : ℕ -> Set where
   even : (k : ℕ) -> Parity ( k * 2)
   odd : (k : ℕ) -> Parity (1 + k * 2)

parity : (k : ℕ) -> Parity k
parity zero = even zero
parity (suc n) with parity n
...                |  even m = odd m
...                |   odd m = even (suc m)
   


data MyAll {A : Set} (P : A -> Set) : List A -> Set where
  emptall : MyAll P []
  moreall : {x : A} {xs : List A} -> P x -> MyAll P xs -> MyAll P (x ∷ xs)

open import Data.Fin
data Expr n : Set where
  var : Fin n -> Expr n
  ploos : Expr n -> Expr n -> Expr n
  zero : Expr n

