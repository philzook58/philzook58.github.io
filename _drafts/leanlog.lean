
/-

Ok so metaprogramming.


-/
import Lean
import Std.Data.HashMap
import Lean.Meta.SynthInstance
import Qq
open Qq Lean
open Lean Lean.Meta Lean.Elab

#check Classical.byCases
#check (1 + 1 : BitVec 8)
--theorem mythm : (Classical.propDecidable (forall (x y : Nat), x + y == y + x)).decide := by grind
#check mythm
theorem mythm : Not (True   /\  (not (Classical.propDecidable (∀ x, (x = x))).decide)) := by grind
#check not

#eval (3 : Nat)
-- https://lean-lang.org/doc/reference/latest///Terms/Type-Ascription/#Lean___Parser___Term___show
#eval show Nat from 3
-- show is just type ascription. Huh


-- getting side effects into typeclass resolution. Could trace them
-- Feed them through inside action.
-- The everything needs to carry this action side thing
class WriteLn (s : String) where
  act : IO Unit
class ReadLine where
  act : IO String

-- Prolog call
--class Call (p : Type)
--instance [p] : Call p where





/-


class Edge (A : Type) (B : Type) where
instance : Edge Nat Nat := {}
instance : Edge Nat String := {}

class Path (A : Type) (B : Type) : Type
instance {x y} [Edge x y] : Path x y := {}
instance {x y z} [Edge x y] [Path y z] : Path x z := {}

https://web.engr.oregonstate.edu/~walkiner/teaching/cs583-sp21/files/Wadler-TypeClasses.pdf
typeclasses. The inst/over system.

outParan, semiOutParam are moding annotations.
Analog also of functional dependency system in Haskell.

Is type "class" somehow akin to a NBG class? Not said in paper.
It is kind of a meta thing
`Coerce a b` is in the orginial wadler paper
https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Coerce.html
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/coercible.pdf
Safe Zero-cost Coercions for Haskell

coerce is realted to subtyping. The doubled pair is kind of reminiscent of birewriting.
Am I insane?
instance Coercible a Int ⇒ Coercible a Age
instance Coercible Int b ⇒ Coercible Age b

coercions and observational type theory

https://dl.acm.org/doi/abs/10.1145/3687997.3695640 Type Checking with Rewriting Rules
https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/draft_type_functions_2008.pdf
ype Checking with Open Type Functions

Hmm. you know, there aren't really lambdas here...
Lambda-less + typeclasses / type functions.


Doing typeclasses or other implicits.
How can I model without going nuts?

-/

class Edge (A : Nat) (B : Nat) where
  eva : {x : Nat // x = A}
  evb : {y : Nat // y = B}

instance : Edge 1 2 where
  eva := ⟨1, rfl⟩
  evb := ⟨2, rfl⟩

instance : Edge 2 3 := {}

class Path (A : Nat) (B : Nat) : Type
instance {x y} [Edge x y] : Path x y := {}

/-
-- https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/#instance-synth
-- outparam gadget. Not a prolog?
-- Parameters to type classes may be marked with gadgets,
which are special versions of the identity function that
cause the elaborator to treat a value differently.
Gadgets never change the meaning of a term,
 but they may cause it to be treated differently
 in elaboration-time search procedur
-/
instance {x y z} [Edge x y] [Path y z] : Path x z := {}




/-
Coercions
https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lean.204.20set_like.html?utm_source=chatgpt.com
https://lean-lang.org/doc/reference/latest/Coercions/#coercions
https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#CoeTC
You can apply a non function type?

coe attribute
↑ ↑  \u  prinst as this
also norm_cast tactic


Unification modulo definitional equality.

-/

--#eval show MetaM Unit from do
#eval do
  let x <- mkFreshExprMVar none
  let y <- mkFreshExprMVar none
  let subst :=  [(x, x), (y, y)] -- Std.HashMap.ofList
  let s <- saveState
  x.mvarId!.assign (mkNatLit 42)
  let res <- isDefEq x y
  let x1 <- instantiateMVars x
  let y1 <- instantiateMVars y
  /-
  let subst := subst.mapM (fun z => do
    let (x,y) : Expr × Expr := z
    let y <- instantiateMVars y
    return (z, y)
  ) -/
  IO.println s!"x: {x1} y: {y1} res {res} {subst}"
  restoreState s
  IO.println s!"x: {x} y: {y} res {res}"
  IO.println s!"x: {x1} y: {y1} res {res}"

--#eval Elab.elabTerm `(1 + 2)
#eval mkConst ``Nat.add
#eval Expr.lam `x (.const `Nat []) (.bvar 0) .default
#eval mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)
#eval q(1 + 2 : Nat)

/-
eval vs reduce vs whnf

-/
#eval reduce q(42 + 1)
#eval whnf q(fun x => 1 + x)
-- https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/Eval.html
#eval evalExpr Nat q(Nat) q(1 + 2 : Nat)
#eval evalExpr' Nat ``Nat q(1 + 2 : Nat)
#eval reduce q(fun x => 1 + x)
--#eval show Syntax from Lean.quote 2




/-
Partially evaluated yallop krishnawsami parser combinators

Kiselyov
Benchamrk them?

strymonas
KMP
pattern matching

What about my fixed point thing. Rationals with compile time denomoniators

-/

def mypow (n : Nat) (x : Q(Nat)) : Q(Nat) :=
  match n with
  | 0 => x
  | .succ n' => q( $x * $(mypow n' x))

#eval (mypow 3 q(2))

/-
locally namless
-/
#eval forallTelescope

/-
Localcontext and mvarcontext
-/

#eval show MetaM Unit from do
  let lctx <- getLCtx -- LocalContext
  let x <- mkFreshExprMVar none
  let mctx <- getMCtx -- MetavarContext
  let env <- getEnv -- Environment
  --dbg_trace mctx -- (reprStr mctx)
  for decl in lctx do
    dbg_trace (decl.userName)
  for (mvarid, decl) in mctx.decls do
    --IO.println "hi"
    dbg_trace (reprStr mvarid)
    --IO.println s!"{reprStr mvarid}"

#eval do
  let res <- Lean.Meta.reduce `(1 + 2)
  IO.println s!"{res}"


elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2 -- Hello World




initialize counter : IO.Ref Nat ← IO.mkRef 0
-- #eval counter.get
-- freaks out if I try to access
/-
def incCounter : IO Nat := do
  let n ← counter.get
  counter.set (n + 1)
  pure (n + 1)

#eval incCounter   -- 1
#eval incCounter   -- 2
-/
unsafe def globalCache : IO.Ref Nat := unsafeBaseIO (IO.mkRef 0)

#eval globalCache.get
#eval show IO Nat from do
  globalCache.set 42
  globalCache.get
#eval globalCache.get -- hmm. didn't work. Too smart for me


/-

prolog

-/

structure Prolog where
  goals : List Expr
deriving Inhabited, Repr, BEq

/-
lambdaMetaTelescope is an open_binder
lambdaTelescope

lettelescope
foralltelescope

abstractM closes binder? wiht loose bvar. Probably not what I want.

-/

-- https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/SynthInstance.html#Lean.Meta.SynthInstance.tryResolve
#eval do
  let e <- reduce q(fun x => 1 + x)
  let (vs, _, e1) <- lambdaMetaTelescope e
  IO.println s!"{vs} {e1}"
  let e <- whnf q(exists x, 1 + x >= 2)
  IO.println s!"{e} ARGS {e.getAppArgs}"
  let (vs, _, e1) <- lambdaMetaTelescope (e.getArg! 1)
  IO.println s!"{vs} {<- reduceAll e1} {<- inferType e1}"
  let ins <- SynthInstance.getInstances q(Inhabited Nat)
  let ins <- synthInstance q(Inhabited Nat)
  IO.println s!"{<- inferType ins}"
  let mvarId <- mkFreshExprMVar none
  let edge := q(fun x => Edge 1 x)
  let (vs, _, e) <- lambdaMetaTelescope edge
  let ins <- synthInstance e
  --IO.println s!"{<- inferType ins}"
  -- open Exists


elab "#mycommand" : command => do
  logInfo "Hello World"
  let e <- getEnv
  -- Lean.addDecl
  return ()

example : ¬ (Not True /\ forall (x y : Nat), x + y = y + x) := by grind
