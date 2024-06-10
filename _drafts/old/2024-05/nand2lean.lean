

inductive Bnand : Bool -> Bool -> Bool -> Prop where
  | nand_true_true : Bnand true true false
  | nand_true_false : Bnand true false true
  | nand_false_true : Bnand false true true
  | nand_false_false : Bnand false false true
--deriving instance Decidable for Bnand


def Bnot (a b : Bool) : Prop := Bnand a a b

-- This kind of let's me observe the not abstraction.
--structure Bnot' (a b : Bool) : Prop where
--  intro :: (h : Bnand a a b)

example : Bnot true false := Bnand.nand_true_true
example : Bnot false true := Bnand.nand_true_true


/-
This is all doofy.

The exercise is kind of to just write an acceptor function or

-/
