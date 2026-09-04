{-# OPTIONS --without-K --safe #-}

module intro where

-- https://martinescardo.github.io/HoTTEST-Summer-School/

Type = Set

data Bool : Type where
    true false : Bool

not : Bool -> Bool
not true = false
not false = true

idBool : Bool -> Bool
idBool x = x

idBool' : Bool -> Bool
idBool' = λ (x : Bool) -> x -- \ Gl

id' : (X : Type) -> X -> X
id' X x = x

id : {X : Type} -> X -> X
id x = x

data 𝟘 : Type where

absurd : {X : 𝟘 -> Type} -> (x : 𝟘) -> X x
absurd ()

¬_ : Type -> Type
¬ A = A -> 𝟘