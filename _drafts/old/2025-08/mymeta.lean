import Lean

open Lean Lean.Expr Lean.Meta

-- https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html

#eval show MetaM Unit from do
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat [])
  IO.println s!"Created mvar: {mvar1}"
  --mvar1.mvarId!.assign (.const ``Nat.zero [])
  --isDefEq mvar1 (Expr.const ``Nat.zero [])
  let iseq ← isDefEq mvar1 (Expr.const ``Nat.zero [])
  IO.println s!"Is def eq: {iseq}"
