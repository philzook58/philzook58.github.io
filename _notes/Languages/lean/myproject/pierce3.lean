/-

The thing about lambdas is that binders are complicated and kind of distraction from some of the main points.

It is also interesting to see how a bunch of stuff works and some different angles of definition.

-/

namespace Term0 

inductive term where
  | true_ : term
  | false_ : term
  | ITE (x y z: term): term
open term
#check ITE true_ true_ true_


-- value as a subset of terms
def value : term -> Bool
| true_ | false_ => true
| (ITE _ _ _) => false

-- A different presentation of subsets
inductive value' : term -> Prop where
  | IsTrue : value' true_
  | IsFalse : value' false_

-- An intrinsic definition
inductive value'' where
  | trueval
  | falseval

-- a step relation

inductive step : term -> term -> Prop where
  | eiftrue : forall t1 t2, step (ITE true_ t1 t2) t1
  | eiffalse : forall t1 t2, step (ITE false_ t1 t2) t2
  | eif : forall t1 t2 t t', step t t' -> step (ITE t t1 t2) (ITE t' t1 t2)

/-
theorem det_step : forall t t' t'', step t t' -> step t t'' -> t' = t'' := by
  intros t
  induction t <;> intros t' t'' h1 h2
  cases h1
  cases h1
  cases h1 <;> cases h2 <;> simp 
  cases a
-/


#print Option



def step' : term -> Option term
| ITE true_ t1 _t2 => some t1
| ITE false_ _t1 t2 => some t2
| ITE t t1 t2 => do 
                   let t' <- step' t
                   return ITE t t1 t2   
| _ => none



-- hmm stack based eval of bexpr is even simpler than int


end Term0


namespace Chap8


inductive term where
| true_
| false_
| ite (cond : term) (then_ : term) (else_ : term)
| zero
| succ (x : term)
| pred (x : term)
| iszero (a : term)

inductive type where
| bool_
| nat

open type
open term

inductive has_type : term -> type -> Prop where
| ttrue : has_type true_ bool_
| tfalse : has_type false_ bool_
| tif : forall cond t2 t3 T, has_type cond bool_ -> has_type t2 T -> has_type t3 T -> has_type (ite cond t2 t3) T 
| tsucc : forall t, has_type t nat -> has_type (succ t) nat
| tpred : forall t, has_type t nat -> has_type (pred t ) nat
| tzero : has_type zero nat
| tiszero : forall t, has_type t nat -> has_type (iszero t) bool_

theorem inver1 : forall R, has_type true_ R -> R = bool_ := by
  intros R hyp
  cases hyp
  simp

/-
#print Exists
#print Sigma
def infer (x : term) : exists R, has_type x R :=
match x with
| true_ =>  (bool_, ttrue)
| false_ => (bool_ , tfalse)
| ite (cond : term) (then_ : term) (else_ : term) => 
   infer
| zero
| succ (x : term)
| pred (x : term)
| iszero (a : term)
-/

end Chap8
