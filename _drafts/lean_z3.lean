import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVDecide
import Lean.Elab.Tactic.Grind
import Aesop
import Lean.Meta.Tactic.Simp
open Lean Elab Tactic Meta
open Lean.Elab.Tactic.BVDecide
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

-- https://www.philipzucker.com/translating-z3-to-coq/
/-
Can I get lean tactics to solve my sudoku problem etc?
-/


theorem foo : exists x, x = 1 ∨ x = 2 := by
  grind

#print Exists

#check PSigma
def foo' : Σ' x, x = 1 ∨ x = 2 := by
  aesop -- grind not happy. Can't get witnesses from grind?


example : ¬exists x : Int, x >= 7 := by
  grind

#eval foo'.fst

theorem biz : exists x, (x = 1 ∨ x = 2) ∧ (x = 3 ∨ x = 1) := by
  aesop

def biz' : Σ' x, (x = 1 ∨ x = 2) ∧ (x = 3 ∨ x = 1) := by
  aesop

def sat (x : Nat) : Bool :=
  (x == 1 || x == 2) && (x == 3 || x == 1)

#eval (List.range 4).find? sat

#eval biz'.fst

-- maybe if we use
def bizz : exists b : Bool, b || !b := by
  decide

--#reduce foo.fst

def prob1 (x : BitVec 4) : Bool := x ≠ 1 ∧ x ≠ 2
example (x : BitVec 4) : x ≠ 1 ∧ x ≠ 2 := by
  -- bv_decide
  sorry

inductive Donkey where
  | red | green | blue
  deriving Inhabited, DecidableEq, Repr, ToExpr

#eval toExpr true
#eval toExpr 4
#eval toExpr "hello"
#eval toExpr #[1,2,3]
#eval toExpr 4.0
#eval toExpr Donkey.red
-- #eval evalExpr Nat (toExpr 4)
--#eval toExpr 4 |> Nat.fromExpr? |> Simp.
/-
example x : prob1 x := by bv_decide
-/

/-

-/

/-
Send more money
minizinc tutorials?
They start getting into optimization and MIP pretty fast


z3 tutoraisl?

Bad cegis / lazy smt?
lazy_smt (grind)
find witness, grind to confirm

Enumerable types - pick upper bound

use pluasible to return random stuff?

bv_find (upperbound := 10) -- enumerate out everything
Or maybe we could do this


Do constraint compiling stuff?

smart alldifferent?

If I want to generate a problem form data, can just simp away the interpreter.
But I can't really call bvdecide on it programmatically?

def main :=
    readfromfile data
    probtype :=
    let sol := apply (bv_find) prob
    print sol.fst

Min = satisfies and there isn't one smaller.
bv_min

Does omega return countermodels? maybe not
-/

---------------------
-- CHATGPT Below here
-- Chatgpt DO NOT EDIT above this point



def myprob (y : Nat) := exists x, x >= y

theorem myprob_proof (y : Nat) : myprob y := ⟨y, Nat.le_refl y⟩

attribute [aesop safe] myprob_proof

def runTacticOnExpr (tactic : Syntax) (target : Expr) : TermElabM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar target `runTacticOnExpr
  let remainingGoals ← Tactic.run proof.mvarId! do
    evalTactic tactic
  unless remainingGoals.isEmpty do
    throwError "tactic left {remainingGoals.length} goals"
  let proof ← instantiateMVars proof
  if proof.hasExprMVar then
    throwError "tactic left metavariables"
  return proof

elab "prove_file_prob" : command => do
  let f <- IO.FS.readFile "/tmp/prob.p"
  Command.liftTermElabM do
    let target ← mkAppM ``myprob #[toExpr f.length]
    let tactic ← `(tactic| aesop)
    let proof ← runTacticOnExpr tactic target
    logInfo m!"{proof}"

prove_file_prob






def modelValue (ce : CounterExample) (x : Expr) : MetaM Expr := do
  for (lhs, v) in ce.equations do
    if ← isDefEq lhs x then return toExpr v.bv
    match_expr lhs with
    | BitVec.ofBool y =>
        if ← isDefEq y x then return toExpr (v.bv == 1)
    | _ =>
        match lhs with
        | .app (.const (.str typeName suffix) levels) y =>
            if suffix == Normalize.enumToBitVecSuffix && (← isDefEq y x) then
              let .inductInfo info ← getConstInfo typeName | unreachable!
              return mkConst info.ctors[v.bv.toNat]! levels
        | _ => pure ()
  let type ← inferType x
  let inst ← synthInstance (← mkAppM ``Inhabited #[type])
  mkAppOptM ``default #[some type, some inst]

partial def withPSigmaVars (target : Expr) (xs : Array Expr)
    (k : Array Expr → Expr → TacticM α) : TacticM α := do
  let target ← whnf target
  if target.getAppFn.isConstOf ``PSigma then
    let #[a, b] := target.getAppArgs | unreachable!
    withLocalDeclD `x a fun x => withPSigmaVars (mkApp b x) (xs.push x) k
  else
    k xs target

partial def mkPSigma (target : Expr) (values : Array Expr) (i := 0) : MetaM (Expr × MVarId) := do
  if h : i < values.size then
    let target ← whnf target
    let #[a, b] := target.getAppArgs | throwError "expected PSigma"
    let (rest, goal) ← mkPSigma (mkApp b values[i]) values (i + 1)
    return (← mkAppOptM ``PSigma.mk #[some a, some b, some values[i], some rest], goal)
  let proof ← mkFreshExprMVar (← whnf target)
  return (proof, proof.mvarId!)

elab "bv_find" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← whnf (← g.getType)
  withPSigmaVars target #[] fun xs body => do
    if xs.isEmpty then throwError "expected PSigma"
    unless ← isProp body do throwError "expected a proposition after PSigma binders"

    let ce ← IO.FS.withTempFile fun _ file => do
      let q ← mkFreshExprMVar (← mkAppM ``Not #[body])
      let ctx ← TacticContext.new file { solverMode := .counterexample }
      let .error ce ← bvDecide' q.mvarId! ctx | throwError "no witness"
      pure ce

    let values ← xs.mapM fun x => modelValue ce x
    let (value, proof) ← mkPSigma target values
    g.assign value
    replaceMainGoal [proof]
    evalTactic (← `(tactic| bv_decide))

def foo6 : Σ' x : BitVec 4, x = 1 ∨ x = 2 := by
  bv_find

#eval foo6.1

def foo8 : Σ' (x y z : Bool), (x && y) == z := by
  bv_find

#eval (foo8.1, foo8.2.1, foo8.2.2.1)

abbrev Digit := BitVec 4

def wide (x : Digit) : BitVec 17 := x.zeroExtend 17

def word4 (a b c d : Digit) : BitVec 17 :=
  1000 * wide a + 100 * wide b + 10 * wide c + wide d

def word5 (a b c d e : Digit) : BitVec 17 :=
  10000 * wide a + 1000 * wide b + 100 * wide c + 10 * wide d + wide e

def foo9 : Σ' (s e n d m o r y : Digit),
    [s, e, n, d, m, o, r, y].Nodup ∧
    s < 10 ∧ e < 10 ∧ n < 10 ∧ d < 10 ∧
    m < 10 ∧ o < 10 ∧ r < 10 ∧ y < 10 ∧
    s ≠ 0 ∧ m ≠ 0 ∧
    word4 s e n d + word4 m o r e = word5 m o n e y := by
  simp [word4, word5, wide, List.nodup_cons]
  bv_find


#eval let ⟨s, e, n, d, m, o, r, y, _⟩ := foo9; (s, e, n, d, m, o, r, y)

inductive Color where
  | red | green | blue
  deriving Inhabited, DecidableEq, Repr

def australia : Σ' (wa nt sa q nsw v t : Color),
    wa ≠ nt ∧ wa ≠ sa ∧ nt ≠ sa ∧ nt ≠ q ∧ sa ≠ q ∧
    sa ≠ nsw ∧ sa ≠ v ∧ q ≠ nsw ∧ nsw ≠ v := by
  bv_find

#eval let ⟨wa, nt, sa, q, nsw, v, t, _⟩ := australia; (wa, nt, sa, q, nsw, v, t)

def polyRootBV : Σ' x : BitVec 8,
    x*x*x + 3*x*x + 4*x + 2 = 0 := by
  bv_find
#eval polyRootBV.1       -- 255#8
#eval polyRootBV.1.toInt -- -1

def grindModelValue (model : Array (Expr × Rat)) (x : Expr) : MetaM Expr := do
  for (lhs, v) in model do
    if ← isDefEq lhs x then
      if v.den == 1 then return toExpr v.num
  throwError "no integral value for {x} in Grind model"

partial def mkPSigmaValue (target : Expr) (values : Array Expr) (proof : Expr)
    (i := 0) : MetaM Expr := do
  if h : i < values.size then
    let target ← whnf target
    let #[a, b] := target.getAppArgs | throwError "expected PSigma"
    let rest ← mkPSigmaValue (mkApp b values[i]) values proof (i + 1)
    mkAppOptM ``PSigma.mk #[some a, some b, some values[i], some rest]
  else
    return proof

def mkBlocker (xs values : Array Expr) : MetaM Expr := do
  let mut same := mkConst ``True
  for x in xs, value in values do
    same ← mkAppM ``And #[same, ← mkEq x value]
  mkAppM ``Not #[same]

def signVariants (values : Array Expr) : MetaM (Array (Array Expr)) := do
  let mut rows : Array (Array Expr) := #[#[]]
  for value in values do
    let neg ← mkAppM ``Neg.neg #[value]
    rows := rows.flatMap fun row => #[row.push value, row.push neg]
  return rows

partial def mkDefaultValue (type : Expr) : TacticM Expr := do
  let type ← whnf type
  match type with
  | .forallE name domain body bi =>
      withLocalDecl name bi domain fun x => do
        mkLambdaFVars #[x] (← mkDefaultValue (body.instantiate1 x))
  | _ =>
      let inst ← synthInstance (← mkAppM ``Inhabited #[type])
      mkAppOptM ``default #[some type, some inst]

def checkGrindCandidate (params : Grind.Params) (xs : Array Expr) (body : Expr)
    (values : Array Expr) : MetaM (Option Expr) := do
  let candidateBody ← whnf (mkAppN (← mkLambdaFVars xs body) values)
  let proof ← mkFreshExprMVar candidateBody
  let checked ← Grind.main proof.mvarId! params
  if checked.failure?.isNone then
    return some (← instantiateMVars proof)
  else
    return none

def grindFindValues (xs : Array Expr) (body : Expr) : TacticM (Array Expr × Expr) := do
  if xs.isEmpty then throwError "expected a witness"
  unless ← isProp body do throwError "expected a proposition after the witnesses"
  let params ← Grind.mkDefaultParams { verbose := false }

  let defaults ← xs.mapM fun x => do
    mkDefaultValue (← inferType x)
  if let some proof ← checkGrindCandidate params xs body defaults then
    return (defaults, proof)

  for x in xs do
    unless ← isDefEq (← inferType x) (mkConst ``Int) do
      throwError "grind_find only searches non-default Int witnesses"

  let rec loop (blockers : Array Expr) : Nat → TacticM (Array Expr × Expr)
    | 0 => throwError "grind_find gave up after 32 candidates"
    | fuel + 1 => do
        let mut searchBody := body
        for blocker in blockers do
          searchBody ← mkAppM ``And #[searchBody, blocker]
        let q ← mkFreshExprMVar (← mkAppM ``Not #[searchBody])
        let result ← Grind.main q.mvarId! params
        let some failed := result.failure? | throwError "no witness"
        let model ← Grind.Arith.Cutsat.mkModel failed
        let values ← xs.mapM fun x => grindModelValue model x
        let variants ← signVariants values
        for candidate in variants do
          if let some proof ← checkGrindCandidate params xs body candidate then
            return (candidate, proof)
        let mut blockers := blockers
        for candidate in variants do
          blockers := blockers.push (← mkBlocker xs candidate)
        loop blockers fuel

  loop #[← mkBlocker xs defaults] 32

elab "grind_find" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← whnf (← g.getType)
  if target.getAppFn.isConstOf ``Subtype then
    let #[a, p] := target.getAppArgs | unreachable!
    withLocalDeclD `x a fun x => do
      let (values, proof) ← grindFindValues #[x] (mkApp p x)
      g.assign (← mkAppOptM ``Subtype.mk #[some a, some p, some values[0]!, some proof])
      replaceMainGoal []
  else
    withPSigmaVars target #[] fun xs body => do
      let (values, proof) ← grindFindValues xs body
      g.assign (← mkPSigmaValue target values proof)
      replaceMainGoal []

def intChoice : Σ' x : Int, x = 1 ∨ x = 2 := by
  grind_find

#eval intChoice.1

def polyRootInt : Σ' x : Int, x^3 + 3*x^2 + 4*x + 2 = 0 := by
  grind_find

#eval polyRootInt.1

def foo17 : {f : Int -> Int // f 3 = f 2} := by
  grind_find
