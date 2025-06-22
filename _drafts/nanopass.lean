

inductive aexpr where
  | const : BitVec 64 → aexpr
  | add : aexpr → aexpr → aexpr
