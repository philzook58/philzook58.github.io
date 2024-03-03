-- import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LibrarySearch
-- import Std.Data.List.Basic
-- import Std.Data.Nat.Basic
--open Nat
--#print Nat.
#eval 1 + 1
inductive aexpr where
  | num : ℕ → aexpr
--| var : string → aexpr
  |  add : aexpr → aexpr → aexpr

def eval : aexpr → ℕ
  | .num n => n
  | .add e1 e2 => eval e1 + eval e2

inductive op where
  | add : op
  | push : ℕ → op

-- [@reducible]
abbrev Prog := List op
abbrev Stack := List ℕ

def exec (p : Prog) (s : Stack) : Stack :=
  match p with
  | [] => s
  | (op.add :: p') =>
    match s with
    | (n1 :: n2 :: s') => exec p' ((n1 + n2) :: s')
    | _ => exec p' s
  | (op.push n :: p') => exec p' (n :: s)

def compile : aexpr → Prog
  | .num n => [op.push n]
  | .add e1 e2 => (compile e1) ++ (compile e2) ++ [op.add]
#print List
lemma exec_append : forall p1 p2 s, exec (p1 ++ p2) s = exec p2 (exec p1 s) := by
  intros p1 p2
  induction p1 with
  | nil => simp [exec]
  | cons h t ih =>
    simp [exec]
    cases h with
    | add =>
      intros s
      cases s with
      | nil => simp [exec, ih]
      | cons n1 s' =>
        cases s' with
        | nil => simp [exec, ih]
        | cons n2 s'' =>
          simp [exec]
          rw [ih]
    | push n =>
      simp [exec]
      intros s
      rw [ih]

theorem exec_compile : ∀ e s, exec (compile e) s = eval e :: s := by
  intros e
  induction e with
  | num n => simp [compile, exec, eval]
  | add e1 e2 IHe1 IHe2 =>
    intros s
    --simp [eval, compile, exec_append, exec]
    simp [eval]
    have : exec [op.add] ((eval e2) :: (eval e1) :: s) = (eval e1 + eval e2) :: s := by
      simp [exec, add_comm]
    rw [<- this]
    rw [<- IHe1]
    rw [<- IHe2]
    rw [<- exec_append]
    simp [compile]
    rw [exec_append]

/-
inductive fib : Nat -> Nat -> Type where
  | base0 : fib 0 0
  | base1 : fib 1 1
  | step  : n > 1 -> fib (n-1) a
                 -> fib (n-2) b -> fib n (a+b)

-/
