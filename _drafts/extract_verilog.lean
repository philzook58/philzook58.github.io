
/-

How can I extract a fraction of lean into C / rust / verilog.
I suppose one could deep embed a dsl but that's a lot of work.



Call yosys.
ebmc

etc


What about verilog -> yosys -> knuckledragger -> lean pipeline?

A little silly, but actually processing the yosys stuff would be pain
A new lean backend would be the most direct route.

There are worse fates for knuckeldragger than to be a translation hub for lean

-/

import Qq
import Lean
open Lean Elab Meta Qq BitVec

-- recursively translate Expr → Verilog ― extend as you need
partial def exprToVerilog (e : Expr) : MetaM String := do
  match e with
  | .lit (.natVal x)      => pure s!"{x}"
  | _ => throwError "exprToVerilog: unsupported {e}"
  /-
  | .app (.app (.const ``BitVec.add ..) a) b =>
      return s!"({← exprToVerilog a} + {← exprToVerilog b})"
  | .app (.app (.const ``BitVec.mul ..) a) b =>
      return s!"({← exprToVerilog a} * {← exprToVerilog b})"
  | .app (.app (.const ``HAnd ..) a) b =>   -- etc.
      return s!"({← exprToVerilog a} & {← exprToVerilog b})"
  | _ => throwError "exprToVerilog: unsupported {e}"
-/

#check 1#10
#eval q( 1#10 )
#check `BitVec.ofNat
#eval Expr.isAppOf q(1#10) `BitVec.ofNat -- whnf and reduce make junk

def mypat := fun x => BitVec.ofNat x
def pmatch (pat : Expr) t := do
  let (vs, _, e1) <- lambdaMetaTelescope pat
  if <- isDefEq e1 t then
    vs.mapM instantiateMVars
  else
    throwError "pmatch: pattern match failed {pat} {t}"

#eval pmatch q(fun x => BitVec.ofNat x) q(BitVec.ofNat 1)

#eval do
  let e <- reduce q(1#10)
  pmatch q(fun x => BitVec.ofNat x) e

--lambdaMetaTelescope mypat

#eval reduce q(1)
#eval do
  let e <- reduce q(1)
  exprToVerilog e
