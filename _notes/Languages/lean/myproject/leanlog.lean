import Lean.Data.PersistentHashSet
import Lean.Data.PersistentHashMap
import Lean.Data.RBMap
import Lean.Data.RBTree
import Mathlib.Data.List.Basic
open Lean.PersistentHashSet
open Lean (PHashSet)

#check EmptyCollection
def edge1 : PHashSet Int := insert EmptyCollection.emptyCollection 5
def edge : PHashSet Int := insert empty 6
def toList (s : PHashSet Int) := fold (fun a b => b :: a) [] s

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

def run edge path := 
  Lean.RBTree. edge #[] (fun (x,y) )

-- lean as an logic automation framework seems fun
-- don't worry about termination or proving anythihng.
-- just reuse parsers and indexing structures

-- Brzowski derivatives
-- generic automata minimization
-- lean-res / metis
-- datalog -> lambda datalog -> egglog

