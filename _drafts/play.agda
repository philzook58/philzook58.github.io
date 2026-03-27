module play where

open import Data.Nat
open import Data.Product
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Function.Base using (_∘_)
open import Data.Bool

-- Fooling around
module Foolin where
    myadd : ℕ → ℕ → ℕ
    myadd zero m = m
    myadd (suc n) m = suc (myadd n m)

    data Vec1 (A : Set) : ℕ -> Set where
        [] : Vec1 A zero
        _∷_ : {n : ℕ} -> A -> Vec A n -> Vec1 A (suc n)


    prf1 : myadd zero zero ≡ zero
    prf1 = refl



    myaddz : (m : ℕ) -> myadd m zero  ≡ m
    myaddz zero = refl
    myaddz (suc m) = cong suc (myaddz m)

    myaddz' : {n : ℕ} -> myadd n zero  ≡ n
    myaddz' {zero} = refl
    myaddz' {suc n} = myaddz (suc n)

    myadd-assoc : (l m n : ℕ) -> myadd (myadd l m) n ≡ myadd l (myadd m n)
    myadd-assoc zero m n = refl
    myadd-assoc (suc l) m n = cong suc (myadd-assoc l m n)

    myadd-suc : (m n : ℕ) -> myadd m (suc n) ≡ suc (myadd m n)
    myadd-suc zero n = refl
    myadd-suc (suc m) n = cong suc (myadd-suc m n)

    myadd-comm : (m n : ℕ) -> myadd m n ≡ myadd n m
    myadd-comm zero n = sym (myaddz n)
    myadd-comm (suc m) zero = cong suc (myadd-comm m zero)
    myadd-comm (suc m) (suc n) = cong suc (trans (myadd-comm m (suc n)) (sym (myadd-suc n m)))

    myadd1 : (n : ℕ) -> myadd n 1 ≡ suc n
    myadd1 zero = refl
    myadd1 (suc n) = let ih = myadd1 n in cong suc ih

    -- https://agda.readthedocs.io/en/latest/tools/auto.html
    -- auto takes -m and -u to auto find useful constants

    -- _ ∷_  can have partially applied ops
    -- subst - defining ≡ 
    -- 

    -- Dec is kind of like is_diff. It seperates out the propisitions for which we have complete reasoning
    -- Not all propositions are. Incompleteness theorem. 

    -- I bungled this. What does that mean

    {-
    So this is nonsense.
    data MyDec : Set -> Set where
        yes' : (p : Set) -> MyDec p
        no' : (¬p : Set) -> MyDec p 

    Standard lib
    -}
    data MyDec (P : Set) : Set where
        yes' : (p : P) -> MyDec P
        no' : (p : ¬ P) -> MyDec P

    {-
    data MyDec1 : Set  ->  Set₁ where
        yes' : (P : Set) ->  (p : P) -> MyDec1 P
        no' : (P : Set) -> (p : ¬ P) -> MyDec1 P
    -}

    -- NotImplies : Set -> Set -> Set
    -- NotImplies P Q = P ∧ ¬ Q

    -- data vs record. record has stronger eta?
    -- postfix destructor patterns

    -- with notation expands to a where clause with extra args.

    -- avoiding mutual recursion via data
    data MyParity : Bool -> ℕ -> Set where
        even0 : MyParity true zero
        evenS : {n : ℕ} -> MyParity true n -> MyParity false (suc n)
        oddS : {n : ℕ} -> MyParity false n -> MyParity true (suc n)

    MyOdd : ℕ -> Set
    MyOdd n = MyParity false n
    MyEven : ℕ -> Set
    MyEven n = MyParity true n

module WellTyped where

    data MyType : Set where
        MyNat : MyType
        MyBool : MyType
    
    data MyTerm : MyType -> Set where
        LitNat : ℕ -> MyTerm MyNat
        LitBool : Bool -> MyTerm MyBool
        Add : MyTerm MyNat -> MyTerm MyNat -> MyTerm MyNat
        ite : {t : MyType} -> MyTerm MyBool -> MyTerm t -> MyTerm t -> MyTerm t

    mean : MyType -> Set
    mean MyNat = ℕ
    mean MyBool = Bool

    eval : {t : MyType} -> MyTerm t -> mean t
    eval (LitNat n) = n
    eval (LitBool b) = b
    eval (Add t1 t2) = eval t1 + eval t2
    eval (ite b t1 t2) = if eval b then eval t1 else eval t2


module NextFoolin where



