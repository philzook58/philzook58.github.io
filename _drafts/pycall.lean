/-
Make ToPython FromPython typeclass, parsers.

call python

-/

import Lean.Elab.Tactic.BVDecide.External
#check System.FilePath
#eval IO.appDir
#eval do
  let ap <- IO.appDir |> liftM
  let dimacs := "/tmp/a.dimacs"
  IO.FS.writeFile dimacs "p cnf 3 2\n1 -3 0\n2 3 -1 0\n" |> liftM
  Lean.Elab.Tactic.BVDecide.External.satQuery (ap / "cadical") dimacs "/tmp/out" 1 false


class ToPython (a : Type) where
  toPython : a -> String

instance : ToPython Nat where
  toPython n := toString n

instance : ToPython Float where
  toPython f := toString f

instance (p : ToPython a) : ToPython (Array a) where
  toPython arr :=
    let elems := arr.map (fun x => p.toPython x)
    "[" ++ String.intercalate ", " elems ++ "]"
