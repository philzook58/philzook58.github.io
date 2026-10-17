/-
requires ensures clauses
@[spec]

https://lean-lang.org/doc/tutorials/latest/vcgen/
https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/

https://github.com/ilyasergey/lean-vcgen-tutorial

webassembly https://github.com/cajal-technologies/talos
kraken x86


de moura's tutorial?

GOTO to lean?

-/
import Std.WP
import Std.Tactic.Do
open Std.WP Lean.Order

def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out
