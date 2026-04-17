import Std.Data.HashMap
abbrev Name := String


inductive Term where
  | fvar : Name -> Term
  | bvar : Nat -> Term
  | app : Term -> Term -> Term
  | lam : Term -> Term
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

structure Rename where
  ab : Std.HashMap Name Name
  ba : Std.HashMap Name Name
deriving Inhabited, Repr

def extend (r : Rename) (n₁ n₂ : Name) : Option Rename :=
  if r.ab[n₁]? == some n₂ then

  else
    if r.ba[n₂] != some n₁ then
      none
    else
      some { ab := r.ab.insert n₁ n₂, ba := r.ba.insert n₂ n₁ }

def perm_eq (r : Rename) (t₁ t₂ : Term) : Bool :=
