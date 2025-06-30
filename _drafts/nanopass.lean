/-
Idea. Do Siek book.
Or nanpass paper?


-/

inductive aexpr where
  | const : BitVec 64 → aexpr
  | add : aexpr → aexpr → aexpr

#html "Hello world"
