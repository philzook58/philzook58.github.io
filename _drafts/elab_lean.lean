import Lean
import Mathlib.Tactic.Find
open Lean Meta Elab Term

/-
Ok. Summary.
CoreM is an IO wrapper (and has Env)
MetaM has a metavariable Map
TermElabM has ...
TacticM is very minimal on top of termelabm. Has a mutable goal list

CommandElabM is a completely separate thing
but has lots of components very similar to TermElabM

I think Metaprogramming in Lean has a strange emphasis on macros
Macros are irrelevant for my purposes

Quotation works inside monads. I can't do it "bare".

Parser.runParserCategory let's me turn strings into
Syntax
TSyntax is a light wrapper you can type tag with a syntax kind

run_elab runs TermElabM
run_cmd runs CommandElabM

lake env lean
Env variables vs stdin
Mocking up an actual main isn't that bad.

"Elaboration is Evaluation"



-/


#find (MonadEnv _) -- find is Mathlib stuff
#synth MonadEnv TermElabM

-- not haelper
--example : exists a, MonadEnv a := by constructor; apply?

#check Lean.Meta.acLt -- an LPO like (ground?) ordering


#check Parser.runParserCategory

#check elabTermAndSynthesize
#check Meta.synthInstance
#check Meta.isDefEq

-- run_tactic does inline TacticM actions
#check Elab.runTactic
#check Tactic.run
#check Tactic.evalTactic
#check Tactic.getMainGoal

/-
A regular unification problem is exists x y z, x = y /\ z = y
In classical logic, we can skolemize brutally, to take any
"Unification with parameters"
Generalized unification problem
forall exists forall exists ... t= s /\ u = v /\ ...
Scoping constraints.

But I've been assuming untyped.
In typed it doesn't change much

forall x : Nat, exists y : Bool, ...
Via naive bounded quantifier, we actually introduce some implies
forall x, type(x, Nat) => exists y, type(y, Bool) /\ ...

Dependntly typed unification problem
forall x : A, exists y : B(x), forall z : C(x,y), t = s /\ ...

Dependent lambda prolog?
Types are "attributed variable" like things
-/

run_elab
  let n1 <- Term.mkConst ``Nat
  let n <- elabTermAndSynthesize (<- `(term| Nat)) none
  let g <- Meta.mkFreshExprMVar (some n)
  let t <- g.mvarId!.getType
  let d <- g.mvarId!.getDecl
  g.mvarId!.isAssigned
  logInfo m!"mvarid {g.mvarId!} {t}"
-- lake env lean

run_elab
  -- α β : Type
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  let β ← mkFreshExprMVar (mkSort (.succ .zero))

  let αId := α.mvarId!
  let βId := β.mvarId!

  -- xs : List α
  -- ys : List β
  let listα := mkApp (mkConst ``List [.zero]) α
  let listβ := mkApp (mkConst ``List [.zero]) β

  let xs ← mkFreshExprMVar listα
  let ys ← mkFreshExprMVar listβ

  let xsId := xs.mvarId!
  let ysId := ys.mvarId!

  logInfo m!"before:
    {xs} : {← inferType xs}
    {ys} : {← inferType ys}"

  let ok ← isDefEq xs ys

  logInfo m!"isDefEq returned {ok}"
  logInfo m!"α assignment:  {← getExprMVarAssignment? αId}"
  logInfo m!"β assignment:  {← getExprMVarAssignment? βId}"
  logInfo m!"xs assignment: {← getExprMVarAssignment? xsId}"
  logInfo m!"ys assignment: {← getExprMVarAssignment? ysId}"

run_elab
  let t <- elabTermAndSynthesize (<- `(term| Eq.refl)) none
  logInfo (repr t)
  let ty <- inferType t
  logInfo ty


structure Clause where
  head : Expr
  body : Array Expr
deriving Repr, BEq

run_elab
  let clause : Clause := {head := toExpr 4, body := #[]}
  let goal <- mkFreshExprMVar none
  let b <- isDefEq goal clause.head
  let g1 <- instantiateMVars goal
  logInfo m!"{b} {g1}"



#check toExpr
#check Meta.check
#check Meta.whnf
#check Meta.reduceEval
#check Meta.evalExpr
#check evalTerm -- eval syntax with given type
#check Tactic.evalTactic -- run syntax of a tactic
#check Tactic.run -- turn TacticM -> TermElabM

#check withLCtx
#check getLCtx
#check Tactic.withMainContext
#check MVarId.refl

#check Meta.evalExpr'
#check Lean.Elab.ConfigEval.EvalExpr.evalExpr
#check Meta.inferType
#check Meta.mkAppM
#check mkAppM' -- monadic so it fills in implicits
#check Lean.Elab.Term.elabType

-- #check Command.runTermElabM I don't think I want this one
#check Command.liftTermElabM -- this is the one I want probably
#check Command.liftCoreM -- possilby some of these may hhappen automatically?

#check Command.elabCommand

#check Json.parse
#check instantiateMVars

#check Expr.isAppOf
#check Meta.ppExpr

#check Meta.dsimp
#check Meta.simp

#check Macro.expandMacro?

#check `(1 + 1) -- quoting happens in a monad.
#check `foo -- Name
#check ``Nat  -- also a name, but one that exsists in current scope?

run_cmd
  let name := Lean.mkIdent `foo6
  let cmd <- `(def $name : Nat := 3)
  Command.elabCommand cmd

#check Lean.Elab.Tactic.grind -- tacticM wrapper?
#check Grind.main

/-
Delayed assignment. What is that for?

A model of the different monads.
Mvar's have decls. They have a type, and a context
Context is hyps and vars in scope?
depth is cheaper version?

-/

open Tactic
example : 1 + 1 = 2 := by
  run_tac do
    let goal ← Tactic.getMainGoal
    logInfo m!"current goal: {← goal.getType}"
    Tactic.evalTactic (← `(tactic| grind))
/-
TacticM <- TermElabM <- MetaM <- CoreM
pure inclusion. tactic has list of goals as state



If I show you my datatypes,
you don't need to see the functions


dependent unification problems
simple typed unification
 problems

-/
#print Syntax
-- syntax also has source info and junk. Names vs strings.
inductive MySyntax where
  | node : Array MySyntax -> MySyntax
  | atom : String -> MySyntax
deriving Repr, BEq, Hashable

-- Can I get Mvar to clash scope?

#print Environment
-- Environment mostly doesn't seem that usefl
structure MyEnvironment where

#print CoreM -- freshness counters and environment
abbrev MyCoreM a := IO a

#print MetaM
-- The state of MetaM is mostly metvarcontext
#print MetavarContext
-- There is an installed "default" local context in the Reader
#print LocalContext


-- Do python version of micro-lean meta stack?

#print foo6


run_meta do
  let xs : Expr := toExpr ([1, 2, 3] : List Nat)
  let ys : Expr := toExpr ([10, 20] : List Nat)

  -- mkAppM supplies List.append's implicit element type.
  let appendExpr ← mkAppM ``List.append #[xs, ys]
  let appendType ← inferType appendExpr
  let normal ← reduce appendExpr

  logInfo m!"expression: {appendExpr}"
  logInfo m!"type:       {appendType}"
  logInfo m!"normal:     {normal}"

run_elab do
  let env ← getEnv
  let source := "20 + 2 * 11"

  let stx ←
    match Parser.runParserCategory env `term source with
    | .ok stx   => pure stx
    | .error e  => throwError "parse error: {e}"

  let natType := toTypeExpr Nat
  let expr ← elabTermEnsuringType stx (some natType)
  synthesizeSyntheticMVarsNoPostponing
  let expr ← instantiateMVars expr

  let ty ← inferType expr
  let normal ← reduce expr
  logInfo m!"parsed syntax: {stx}"
  logInfo m!"elaborated:    {expr}"
  logInfo m!"type:          {ty}"
  logInfo m!"normal form:   {normal}"

#check logInfo

run_meta do
  let e ← mkAppM ``Nat.add #[toExpr 0, toExpr 42]
  let simpTheorems ← getSimpTheorems
  let ctx ← Simp.mkContext (simpTheorems := #[simpTheorems])
  --let ctx ← Simp.mkContext
  let (result, _stats) ← Meta.simp e ctx
  logInfo m!"before: {e}"
  logInfo m!"after:  {result.expr}"
  let proof ← result.getProof
  logInfo m!"proof:  {proof}"


run_meta do
  let e ← mkAppM ``Eq #[toExpr 42, toExpr 42]
  logInfo m!"before: {e}"
  let m <- mkFreshExprMVar e
  let (_rem_goals, _termstate) <- runTactic m.mvarId! (<- `(tactic| grind))
  let e <- instantiateMVars m
  logInfo m!"before: {e}"
  return ()

example (a b c : Nat) (h : a = c) : a = b := by
  grind =>
    show_eqcs
    show_state
    sorry

#check Grind.getEqcs
#check Grind.getENode?
#check Grind.getRoot?
#check Grind.isCongrRoot -- is root
-- #check Grind.isCongruentCheck
#check Grind.ENode -- self next root pointers
#check Grind.ENodeMap

#check Grind.GrindM -- built on SymM. egraph is not in GrindM?
#check Grind.Goal
#check Grind.GoalM  -- ah ok. Egraph is in Goal

#check Grind.EMatchTheorem
#check Grind.ematch' -- ' only. Returns instance map if tracing enabled


-- SymM.
-- Lot's of hash consing facilities?
#check Meta.Sym.ExprPtr
/-

Prolog like behavior.
Aesop might be better or worse
It can unwrap some constructors, but not that many

-/

inductive Edge : Nat -> Nat -> Type where
  | edge12 : Edge 1 2
  | edge23: Edge 2 3
  | trans : Edge a b -> Edge b c -> Edge a c
deriving Repr,BEq

example : Edge 1 2 := by
  solve_by_elim
--#check Trans
def foo : Edge 1 3 := by solve_by_elim [Edge.trans]
#print foo
#print Sigma
def foo' : Σ a, Edge 1 a := by
  --constructor
  solve_by_elim [Edge.trans, Sigma.mk]
#print foo'
--example : Trans Edge 1 3 := by
--  solve_by_elim [Edge.trans]



run_elab
  let env ← getEnv
  let binder := mkIdent `n
  let binderType : TSyntax `term :=
    ⟨← ofExcept <| Parser.runParserCategory env `term "Nat" "experiment.txt"⟩
  let body : TSyntax `term :=
    ⟨← ofExcept <| Parser.runParserCategory env `term "n + 0 = n" "experiment.txt"⟩
  let tactic : TSyntax `tactic :=
    ⟨← ofExcept <| Parser.runParserCategory env `tactic "simp" "experiment.txt"⟩

  let formulaStx ← `(∀ $binder : $binderType, $body)
  let tacticSeq ← `(tacticSeq| $tactic:tactic)
  let proofStx ← `(by $tacticSeq)
  logInfo m!"formula syntax: {formulaStx}"
  logInfo m!"proof syntax: {proofStx}"

  let formula ← elabTermAndSynthesize formulaStx (some <| mkSort .zero)
  let proof ← elabTermAndSynthesize proofStx (some formula)
  logInfo m!"formula: {formula}"
  logInfo m!"proof: {proof}"

  addDecl <| .defnDecl {
    name := `generatedFormula
    levelParams := []
    type := mkSort .zero
    value := formula
    hints := .abbrev
    safety := .safe
  }

  addDecl <| .thmDecl {
    name := `generatedProof
    levelParams := []
    type := Lean.mkConst `generatedFormula
    value := proof
  }

#check generatedFormula
#check generatedProof



-- interesting modules
#check Lean.Environment
#check Lean.Declaration
#check Lean.Language.Lean.process -- top level provessing loops?

-- Try making a sexp syntax extensions and parse it

-- https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith
partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

#check Syntax.isNatLit?
#check TSyntax.getNat
run_elab
  let env ← getEnv
  let res ← ofExcept <| Parser.runParserCategory env `arith "1 + 1" "experiment.txt"
  logInfo m!"{res.isNatLit?}"

-- https://github.com/ufmg-smite/lean-smt/blob/main/Smt/Dsl/Sexp.lean
-- https://github.com/ufmg-smite/lean-smt/blob/main/Smt/Data/Sexp.lean
declare_syntax_cat sexp
syntax "(" sexp* ")" : sexp
syntax ident : sexp

#eval `(sexp| (x y (z w)))

inductive Sexp where
  | atom : String -> Sexp
  | list : List Sexp -> Sexp
deriving Repr, Hashable, BEq

partial def denotesexp : Syntax -> Sexp
| `(sexp| $i:ident) => Sexp.atom i.getId.getString!
| _ => Sexp.atom "whatever"

run_elab
  let e <- `(sexp| (x y z))
  return denotesexp e

#check Syntax.mkNumLit "3"

#check Lean.Parser.identFn.run
