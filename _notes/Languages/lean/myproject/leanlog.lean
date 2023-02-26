import Lean.Data.PersistentHashSet
import Lean.Data.PersistentHashMap
import Lean.Data.RBMap
import Lean.Data.RBTree
import Mathlib.Data.List.Basic
import Lean
import Qq
import Lean.Meta.Reduce
import Lean.Meta

import Lean.Meta.DiscrTree
open Lean.PersistentHashSet
open Lean (PHashSet)

#check EmptyCollection
def edge1 : PHashSet Int := insert EmptyCollection.emptyCollection 5
def edge : PHashSet Int := insert empty 6
def toList {α : Type}[BEq α] [Hashable α] 
(s : PHashSet α) : List α := 
  fold (fun a b => b :: a) [] s

#eval toList edge
--#eval (Lean.PersistentHashMap.toList edge)

-- list comprehesion sugar example
-- https://github.com/leanprover/lean4-samples/tree/main/ListComprehension


-- RBTRee vs Persistenthash
-- Lookos like RBTree has more functions on it.
#check ()
#check compare
-- hmm. It takes an ordering in the type. Interesting.
def edge3 : Lean.RBTree Int compare := Lean.RBTree.insert Lean.RBTree.empty 7
#eval Lean.RBTree.toArray edge3

-- Oh Std has HashMap and HashSet


#eval #[1,2,3] -- array notation. Cool.

#check (1,2)
#check List.pure
#synth Monad List -- ok I needed to import mathlib to get monad instance for list
abbrev Rel := List (Prod Int Int)
def run (edge path : Rel) : List (Int × Int) := 
  let r2 := edge
  let r1 := do
    --pure (1,2)
    let (x,y) <- edge
    let (y1,z) <- path
    if y == y1 then
      pure (x,z)
    else
      [] --failure -- List isn't altenrative
  r1 ++ r2

-- The stream type is called many  https://leanprover.github.io/functional_programming_in_lean/monads/arithmetic.html#nondeterministic-search
--#check Many No I can't finds this

#eval run [(1,2), (2,3)] []
  --for (x,y) in edge, (y1,z) in path do
  --  pure (x,z)
  --  for (y1,z) in path do
  --  if y == y1 then pure (x,z) else fail

--def run1 edge path :=  ()
  -- Lean.RBTree. edge #[] (fun (x,y) => )

-- lean as an logic automation framework seems fun
-- don't worry about termination or proving anythihng.
-- just reuse parsers and indexing structures

-- Brzowski derivatives
-- generic automata minimization
-- lean-res / metis
-- datalog -> lambda datalog -> egglog



-- Lean Expr
-- https://leanprover-community.github.io/mathlib4_docs/Lean/Expr.html
#print Lean.Expr
open Lean
def bv0 : Expr := .bvar 0
#eval bv0 
#eval toExpr true
#check Expr.const "foo" []
#check `foo -- Name

#check Expr.const `foo []
#check ``Nat.zero -- checks identifier exists


#check Expr.app
#check mkApp2
#check mkAppN -- takes array

-- #eval mkLambdaEx
-- #eval Q(foo bar biz)
def foo := Expr.const ``Nat.zero [] 
-- trick to convert Expr to it's meaning
elab "foo" : term => return foo
#check foo

open Qq
set_option trace.compiler.ir.result true in

#check (q([2,3]) : Expr)

#check Nat.succ
#print Nat
def mypow (n : Nat)  x :=
 match n with 
 | .zero => 1
 | .succ n' => x * (mypow n' x) 
/-
def mypow' (n : Nat) (x : Expr) : Expr :=
 match n with 
 | .zero => q(1)
 | .succ n' => q($x * $(mypow' n' x)) 
 -/
 -- CoreM
 -- MetaM - metavaraibe generation
 --

-- eval also executes MetaM monad
#eval Lean.Meta.reduce q(1 + 2)
#eval (q(1 + 2 : Nat) : Expr)

-- optParam of functions. Huh. Nice.
-- outParam of typeclasses

elab "#mycommand2" : command =>
  logInfo "Hello World"
#mycommand2 -- Hello World

/-
MetaM moand 




-/


def doo : MetaM Expr := do
  let me <- Lean.Meta.mkFreshExprMVar none
  let m := Lean.Expr.mvarId! me
  Lean.MVarId.assign m (Expr.const ``Nat.zero [])
  Lean.instantiateMVars me

#eval doo

-- what the gell is eval show
--#eval show MetaM Unit from doo


-- Meta Basic file. good to peruse
-- https://leanprover-community.github.io/mathlib4_docs/Lean/Meta/Basic.html

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  Lean.Meta.ppExpr (← Lean.Meta.whnf e)

#eval whnf' `(List.append [1,2] [2,3])

-- lazy evaluation is good for reducing the head lazily for matchig

#check Lean.Meta.isDefEq


#eval show MetaM _ from do
  let e := q([1,2])
  let e' := q([1,2])
  let b <- Lean.Meta.isDefEq e e'
  pure b

#eval show MetaM _ from do
  logInfo "hello wolrd"
  dbg_trace "hi there"


axiom edge2 : Int -> Int -> Prop

#eval show MetaM _ from do
  let m <- Lean.Meta.mkFreshExprMVar none
  let m2 <- Lean.Meta.mkFreshExprMVar none
  _ <- Lean.Meta.instantiateForall q(forall x : Nat, x = x) #[m]
  Lean.Meta.instantiateForall q(forall x y, edge2 x y) #[m,m2]



namespace Discrtree
  -- https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTree.lean
  open Lean.Meta.DiscrTree
  --#eval forall x y, edge x y
  #check getMatch
  #check mkConst `foo

  -- ok so we can make discrimination trees. Doesn't actually help us do multipatterns
  #eval show MetaM _ from do
    let fo := mkConst `foo
    let mvar1 ← Lean.Meta.mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
    let d <- insert (empty : Lean.Meta.DiscrTree _ true) fo 42
    let pat := mvar1
    --getMatch d pat
    getUnify d pat

end Discrtree

open Lean.PersistentHashSet
open Lean (PHashSet)

namespace leanlog2

def run (db : PHashSet Expr) : PHashSet Expr := 
  fold (fun acc b => 
  if let .const `edge _ := b then
    
    fold (fun acc c => insert acc c) acc db
  else acc) empty db


#eval toList (run (List.foldl insert empty [mkConst `foo, mkConst `bar ]))




end leanlog2


