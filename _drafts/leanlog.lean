import Lean

open Lean Meta Elab Term

#check Sym.BackwardRule.apply
#check Sym.mkBackwardRuleFromDecl

#check MVarId.apply
#check MVarId.rewrite

#check Expr.replace
#check Meta.transform -- hmm like a vistor api
#check Meta.forEachExpr

theorem add_zero : forall x, x + 0 = x := by grind

theorem my_add_zero : ∀ x : Nat, x + 0 = x := by
  grind
#check mkConst

run_elab
  let t ← elabTermAndSynthesize (← `(2 + 0)) none
  let m ← mkFreshExprMVar none
  let h ← mkConstWithFreshMVarLevels ``my_add_zero

  let result ← m.mvarId!.rewrite t h

  logInfo m!"old:        {t}"
  logInfo m!"new:        {result.eNew}"
  logInfo m!"proof:      {result.eqProof}"
  logInfo m!"side goals: {result.mvarIds}"

-- simp

run_elab
  let t <- elabTermAndSynthesize (<- `(2 + 0)) none
  let m <- mkFreshExprMVar none
  m.mvarId!.rewrite' t  ``add_zero
