module play where

open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

myadd : ℕ → ℕ → ℕ
myadd zero m = m
myadd (suc n) m = suc (myadd n m)


data Vec (A : Set) : ℕ -> Set where
    [] : Vec A zero
    _∷_ : {n : ℕ} -> A -> Vec A n -> Vec A (suc n)


prf1 : myadd zero zero ≡ zero
prf1 = refl


myaddz : (m : ℕ) -> myadd m zero  ≡ m
myaddz zero = refl
myaddz (suc m) = cong suc (myaddz m)

