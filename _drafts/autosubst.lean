/-

(* https://www.ps.uni-saarland.de/autosubst/doc/Plain.Demo.html

https://github.com/uds-psl/autosubst-ocaml

https://github.com/uds-psl/MPCTT interesting book
Inductive term :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Now we can automatically derive the substitution operations and lemmas. This is done by generating instances for the following typeclasses:
Ids term provides the generic identity substitution ids for term. It is always equivalent to the variable constructor of term, i.e. to the unique constructor having a single argument of type var. In this example, ids is convertible to Var.
Rename term provides the renaming operation on term.
Subst term provides the substitution operation on term and needs a Rename instance in the presence of binders.
SubstLemmas term contains proofs for the basic lemmas.
Each instance is inferred automatically by using the derive tactic.
Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

-/

inductive term where
  | Var (x : Nat)
  | App (s t : term)
  | Lam (s : term)
deriving Repr, BEq, Inhabited

namespace autosubst

abbrev var := Nat

def ids : var → term := term.Var

def upren (ξ : var → var) : var → var
  | 0 => 0
  | n + 1 => ξ n + 1

def rename (ξ : var → var) : term → term
  | .Var x => .Var (ξ x)
  | .App s t => .App (rename ξ s) (rename ξ t)
  | .Lam s => .Lam (rename (upren ξ) s)

def ren (ξ : var → var) : var → term := fun x ↦ ids (ξ x)

def up (σ : var → term) : var → term
  | 0 => ids 0
  | n + 1 => rename Nat.succ (σ n)

def subst (σ : var → term) : term → term
  | .Var x => σ x
  | .App s t => .App (subst σ s) (subst σ t)
  | .Lam s => .Lam (subst (up σ) s)

def scomp (σ τ : var → term) : var → term := fun x ↦ subst τ (σ x)

scoped infixl:56 " >> " => scomp
scoped notation:max s ".[" σ "]" => subst σ s

open scoped autosubst

private theorem upren_comp (ξ ζ : var → var) :
    upren (fun x ↦ ζ (ξ x)) = fun x ↦ upren ζ (upren ξ x) := by
  funext x
  cases x <;> rfl

private theorem rename_comp (ξ ζ : var → var) (s : term) :
    rename ζ (rename ξ s) = rename (fun x ↦ ζ (ξ x)) s := by
  induction s generalizing ξ ζ with
  | Var x => rfl
  | App s t ihs iht => simp only [rename, ihs, iht]
  | Lam s ih =>
      change term.Lam (rename (upren ζ) (rename (upren ξ) s)) =
        term.Lam (rename (upren (fun x ↦ ζ (ξ x))) s)
      congr 1
      calc
        rename (upren ζ) (rename (upren ξ) s) =
            rename (fun x ↦ upren ζ (upren ξ x)) s := ih _ _
        _ = rename (upren (fun x ↦ ζ (ξ x))) s :=
          congrArg (fun f ↦ rename f s) (upren_comp ξ ζ).symm

private theorem up_ren (ξ : var → var) : up (ren ξ) = ren (upren ξ) := by
  funext x
  cases x <;> rfl

theorem rename_subst (ξ : var → var) (s : term) : rename ξ s = s.[ren ξ] := by
  induction s generalizing ξ with
  | Var x => rfl
  | App s t ihs iht => simp only [rename, subst, ihs, iht]
  | Lam s ih =>
      simp only [rename, subst]
      rw [ih, up_ren]

private theorem up_ids : up ids = ids := by
  funext x
  cases x <;> rfl

theorem subst_id (s : term) : s.[ids] = s := by
  induction s with
  | Var x => rfl
  | App s t ihs iht => simp only [subst, ihs, iht]
  | Lam s ih =>
      simp only [subst]
      rw [up_ids, ih]

theorem id_subst (σ : var → term) (x : var) : (ids x).[σ] = σ x := rfl

private theorem up_after_upren (ξ : var → var) (τ : var → term) :
    (fun x ↦ up τ (upren ξ x)) = up (fun x ↦ τ (ξ x)) := by
  funext x
  cases x <;> rfl

private theorem subst_after_rename (ξ : var → var) (τ : var → term) (s : term) :
    subst τ (rename ξ s) = subst (fun x ↦ τ (ξ x)) s := by
  induction s generalizing ξ τ with
  | Var x => rfl
  | App s t ihs iht => simp only [rename, subst, ihs, iht]
  | Lam s ih =>
      simp only [rename, subst, ih]
      rw [up_after_upren]

private theorem rename_up (ξ : var → var) (σ : var → term) :
    (fun x ↦ rename (upren ξ) (up σ x)) = up (fun x ↦ rename ξ (σ x)) := by
  funext x
  cases x with
  | zero => rfl
  | succ x =>
      simp only [up]
      rw [rename_comp, rename_comp]
      congr

private theorem rename_after_subst (ξ : var → var) (σ : var → term) (s : term) :
    rename ξ (subst σ s) = subst (fun x ↦ rename ξ (σ x)) s := by
  induction s generalizing ξ σ with
  | Var x => rfl
  | App s t ihs iht => simp only [rename, subst, ihs, iht]
  | Lam s ih =>
      simp only [rename, subst, ih]
      rw [rename_up]

private theorem up_comp (σ τ : var → term) :
    scomp (up σ) (up τ) = up (scomp σ τ) := by
  funext x
  cases x with
  | zero => rfl
  | succ x =>
      simp only [up, scomp]
      rw [subst_after_rename, rename_after_subst]
      congr

theorem subst_comp (σ τ : var → term) (s : term) :
    s.[σ].[τ] = s.[σ >> τ] := by
  induction s generalizing σ τ with
  | Var x => rfl
  | App s t ihs iht => simp only [subst, ihs, iht]
  | Lam s ih =>
      simp only [subst, ih]
      rw [up_comp]

end autosubst

#eval fun sigma x => (Var x).[sigma]
/-
Eval simpl in fun sigma x => (Var x).[sigma].
(* simplifies to sigma x*)

Eval simpl in fun sigma s t => (App s t).[sigma].
(* simplifies to App s.[sigma] t.[sigma]*)

Eval simpl in fun sigma s => (Lam s).[sigma].
(* simplifies to Lam s.[up sigma]*)
-/
