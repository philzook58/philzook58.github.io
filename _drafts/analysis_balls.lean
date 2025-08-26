--import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Lean Meta Elab Command



-- Basic integral example: ∫ x² dx from 0 to 1 = 1/3
open MeasureTheory intervalIntegral

#search "integral_pow."
#check integral_pow

example : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  simp
  norm_num

example : ∫ x in (0:ℝ)..(1:ℝ), x^3 = 1/4 := by
  simp
  norm_num

example : ∫ x in (0:ℝ)..(1:ℝ), x * Real.sin x = Real.sin 1 - Real.cos 1 := by
  -- Define antiderivative F(x) = sin(x) - x*cos(x)
  let F := (fun x => Real.sin x) - (fun x => x * Real.cos x)
  -- Show F'(x) = x*sin(x)
  let hF : forall z, deriv F z = (fun x => x * Real.sin x) z := by
    intros z
    unfold F
    simp

  have h_deriv : ∀ x ∈ Set.uIcc 0 1, HasDerivAt F (Real.cos x - (Real.cos x + x * Real.sin x)) x := by
    intro x _
    unfold F
    apply HasDerivAt.sub
    · exact Real.hasDerivAt_sin x --exact (Real.hasDerivAt_sin x).comp x (hasDerivAt_id x)
    · apply HasDerivAt.mul
      · exact hasDerivAt_id x
      · exact (Real.hasDerivAt_cos x).comp x (hasDerivAt_id x)
  -- Apply fundamental theorem of calculus
  rw [integral_eq_sub_of_hasDerivAt h_deriv]
  -- Evaluate F(1) - F(0)
  simp [F]

--example : ∫ x in (0:ℝ)..(1:ℝ), x * Real.sin x = 42 := by



set_option trace.Meta.Tactic.simp true in
example : ∫ x in (0:ℝ)..(1:ℝ), Real.cos x = Real.sin 1 - Real.sin 0 := by
  simp

#search "integral_deriv_eq."
#search "fundamental theorem of calculus."
-- a strange name for this theorem.
-- I see. intergal of deriv = sub of something
#check intervalIntegral.integral_deriv_eq_sub
-- https://leansearch.net/
#loogle "integral"
#moogle "fundamental theorem of claculus."
#help cat
/-
https://lawrencecpaulson.github.io/2025/08/21/Integrals_II.html
https://lawrencecpaulson.github.io/2025/08/14/Integrals_I.html
-/

-- https://leanprover-community.github.io/contribute/naming.html

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
