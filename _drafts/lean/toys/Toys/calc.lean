import Mathlib.Analysis.Calculus.Deriv.Basic

open Real

#eval 3
-- Define the function
def f (x : ℝ) : ℝ := cos (sin x)

-- Compute its derivative
example (x : ℝ) : deriv f x = -cos x * sin (sin x) := by
  simp [f, deriv_cos, deriv_sin]
