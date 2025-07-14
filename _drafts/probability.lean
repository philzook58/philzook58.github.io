

-- Holtzen notes

-- https://leanprover-community.github.io/mathlib4_docs/Init/Data/Random.html#RandomGen.next
#eval do
  let x <- IO.rand 0 10 |> liftM
  IO.println s!"{x}"
