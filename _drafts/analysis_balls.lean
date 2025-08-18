--import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
open Lean Meta Elab Command


/-
Interesting.
You need the thing applied extensionally to work.
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html
Example here shows that.
I'm confused by what i need imported or not?
-/

set_option trace.Meta.Tactic.simp true
example (x : ℝ) : deriv (fun x => (Real.cos x) * (Real.sin x)) x = (fun x => -Real.sin x * Real.sin x + Real.cos x * Real.cos x) x := by
  simp

/-
elab "#print_expr " t:term : command => do
  let e ← elabTerm t none
  let e ← instantiateMVars e
  logInfo m!"{e}"
-/

#check (1 : ℝ) + 2
#simp (1 : ℝ) + 1 = 2
#norm_num (1 : ℝ) + 1
#eval (1 : ℝ) + 1
#search "Real."
#help command
#loogle Real

-- There's an interesting idea. A command to textually search my theories
-- #explode (1 : ℝ) + 1

example : 1 + 1 = 2 := by
  norm_num

example : |-2| = 2 := by
  norm_num

example (x : ℝ) : |-(|x|)| = |x| := by
  simp?

#check abs_neg
#check abs_abs


--set_option tactic.simp.trace true

example (x : ℝ) : Real.sin (-x) = - Real.sin x  := by
  simp only [Real.sin_neg]

example x (y : ℝ) : Real.sin (-x) = y := by
  simp
  sorry
#simp fun x => Real.sin (-x)
#simp fun x => (Real.sin x)^2 + (Real.cos x)^2

#simp deriv (fun x => (Real.cos (Real.sin x)))
#simp deriv (fun x => (Real.cos x) * (Real.sin x))
#simp deriv (fun x : ℝ  => x)
#loogle deriv
#norm_num Real.sqrt 9
#simp Real.sqrt 9

open Real
example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp
  ring

--example : deriv (fun x => (Real.cos x) * (Real.sin x)) = (fun x => -Real.sin x * Real.sin x + Real.cos x * Real.cos x) := by
--  simp

-- set_option trace.Meta.Tactic.simp true
-- set_option trace.simp.rewrite true
-- set_option trace.simps.verbose true in
set_option trace.Meta.Tactic.simp true
example (x : ℝ) : deriv (fun x => (Real.cos x) * (Real.sin x)) x = (fun x => -Real.sin x * Real.sin x + Real.cos x * Real.cos x) x := by
  simp
  --simp
  --rw [Real.deriv_mul]

example : Real.sqrt 9 = 3 := by
  refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
  --simp only [Nat.ofNat_pos]
  simp
  norm_num


-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Basic.html
