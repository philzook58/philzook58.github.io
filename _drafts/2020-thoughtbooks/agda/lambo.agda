


open import Data.Maybe

data Lambo (a : Set) : Set where
  Lam : Lambo (Maybe a) -> Lambo a
  App : Lambo a -> Lambo a -> Lambo a
  Var : a -> Lambo a

id : {A : Set} -> Lambo (Maybe A)
id = Lam (Var nothing) -- identity function

const : {A : Set} -> Lambo (Maybe (Maybe A)) -- const
const = Lam (Lam (Var (just nothing)))




{-
Alternatively we could trasnition this to using 
Fin n 
and and index

-}

{-

locally nameless

-}

open import Data.Nat
open import Data.String
open import Data.Product
open import Data.List

Name : Set
Name = String
mutual 
  record Scope : Set where
    inductive
    constructor Mkscope
    field
      scope : Expr

  data Expr : Set where
    F : Name -> Expr
    B : ℕ -> Expr
    _$$_ : Expr -> Expr -> Expr
    _==>_ : Expr -> Scope -> Expr


abstract : Name -> Expr -> Scope
abstract name expr = Mkscope (nameTo 0 expr) where
  nameTo outer (F name') with n == n
