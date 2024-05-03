module dep where

open import Data.Nat
open import Data.String
open import Data.List
open import Data.Bool

{- unlike haskell  need mutual block for mutually recursive definitions-}
mutual
   {- inferable terms. ↓ is typed as \d1  (the numebrs give you options. Look at the bottom bar of emacs. Also you can do the long form ↓ \downarrow  -}
   data Term↓ : Set where
     Inf : Term↑ -> Term↓
     Lam : Term↓ -> Term↓
   {- checkable terms \u1 -}
   data Term↑ : Set where
    Ann : Term↓ -> Ty -> Term↑
    Bound : ℕ -> Term↑
    Free : Name -> Term↑
    _$$_ : Term↑ -> Term↓ -> Term↑

   data Name : Set where
     Global : String -> Name
     Local : ℕ -> Name
     Quote : ℕ -> Name

   data Ty : Set where
     TFree : Name -> Ty
     Fun : Ty -> Ty -> Ty

{- equality function for names. ≡ᵇ is typed \==\^b  . Can I derive this equality somehow? -}
eqname : Name -> Name -> Bool
eqname (Global s) (Global s') = s == s'
eqname (Local n) (Local n') = n ≡ᵇ n'
eqname (Quote n) (Quote n') = n ≡ᵇ n'
eqname _ _ = false

mutual
  {- Need no positivity check because this is in HOAS form. Value occurs in a negative position in the constructor, which is naughty logic wise for some reason.   -}
  {-# NO_POSITIVITY_CHECK #-}
  data Value : Set where
    VLam : (Value -> Value) -> Value
    VNeutral : Neutral -> Value

  {- What is a neutral term? -}
  data Neutral : Set where
    NFree : Name -> Neutral
    NApp : Neutral -> Value -> Neutral
    
  
vfree : Name -> Value
vfree n = VNeutral (NFree n)

{- type Env = [Value] does not need it's own syntaqx in Agda -}
Env : Set
Env = List Value

{- consider using Data.List.lookup for a total version -}
{-# NON_COVERING  #-}
_!!_ : {A : Set} -> List A -> ℕ -> A
(x ∷ xs) !! zero = x
(x ∷ xs) !! (suc n) = xs !! n


mutual 

  eval↑ : Term↑ -> Env -> Value
  eval↑ (Ann e _) d = eval↓ e d
  eval↑ (Free x) d = vfree x
  eval↑ (Bound i) d = d !! i
  eval↑ (e $$ e') d = vapp (eval↑ e d) (eval↓ e' d)

  vapp : Value -> Value -> Value
  vapp (VLam f) v = f v
  vapp (VNeutral n) v = VNeutral (NApp n v)

  eval↓ : Term↓ -> Env -> Value
  eval↓ (Inf i) d = eval↑ i d
  eval↓ (Lam e) d = VLam (\ x -> eval↓ e ( x ∷ d))

data Kind : Set where
  Star : Kind

data Info : Set where
  HasKind : Kind -> Info
  HasType : Ty -> Info

open import Data.Product
Context : Set
Context = List ( Name × Info )
{- There is already a lookup in Data.List, but it is actually an index function -}

open import Data.Maybe
lookup' : Context -> Name -> Maybe Info
lookup' [] _ = nothing
lookup' ( ( n , i ) ∷ xs ) n' with eqname n n'
...                                | true = just i
...                                | false = lookup' xs n'


open import Data.Sum
Result : Set -> Set
Result a = String ⊎ a {- Either has the nightmarish syntax \u+  ⊎ -}

open import Data.Unit
{-
return' : {A : Set} -> A -> Result A
return' x = inj₂ x
-}
throwError : {A : Set} -> String -> Result A
throwError s = inj₁ s


{-
How to get the Sum monad instance in scope

Ok. what the hell is going on here.
Well, there are monad instances consider sum as either functorial in the left or right argument.
Howve,er these are defined sort of oppositely as I expected.
Left has puts the parameter onto the right argument.
I'm sure there is some way of looking at this where it makes sense.
I guess we're fixing the left argument


We need to instantiate a module.
One level is inferred because it is the level of String
But the other level needs to be made explicit

Then open (RawMonad  Thefunctorwiththestuffinit) 
I think this builds out all the useful extra stuff from the basic definition


-}

open import Category.Monad
open import Level
import Data.Sum.Categorical.Left as SL
module SL' = SL String Level.zero
open RawMonad SL'.monad

kind↓ : Context -> Ty -> Kind -> Result ⊤  -- \top ⊤ is  agda stdlib  syntax for ()/unit
kind↓ Γ (TFree x) Star with lookup'  Γ x -- Γ is \GG. \G puts you in greek mode and then you use the equivlanet letter to pick the symbol
...                        | (just (HasKind Star)) = return tt
...                        | nothing  = throwError "unknown identifier"
...                        | _  = throwError "didn't have kind star" 
kind↓ Γ (Fun k k') Star = do kind↓ Γ k Star {- we get do syntax. It desguars to whatever >> and >>= are in scope.-}
                             kind↓ Γ k' Star

type↑ : ℕ -> Context -> Term↑ -> Result Type
type↑ i Γ (Ann e t) = do kind↓ Γ t Star
                         type↓ i Γ e t
                         return t
type↑ i Γ (Free x) with lookup' x Γ
...                    | just (HasType t) = return t
...                    | nothing = throwError "unknonwn idnetifier"
...                    | _ = throwError "should be HaveType"

type↑ i Γ 


type↑0 : Context -> Term↑ -> Result Ty
type↑0 = type↑ 0
