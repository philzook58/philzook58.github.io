module foolin where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Data.Nat using (ℕ; zero; suc)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

{-
C-c C-l: Load the file and type-check it.
C-c C-d: Deduce the type of a given expression.
C-c C-n: Normalise a given expression.
C-c C-,: Shows the type expected in the current hole, along with the types of any local variables.
C-c C-c: Case split on a given variable.
C-c C-SPC: Replace the hole with a given expression, if it has the correct type.
C-c C-r: Refine the hole by replacing it with a given expression applied to an appropriate number of new holes.
C-c C-x C-c (C-x C-c in VS Code): Compile an Agda program.
-}
main : IO ⊤
main = putStrLn "Hello world!"



data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infixr 5 _∷_