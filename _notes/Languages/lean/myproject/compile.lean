--def main := IO.println ("hi" ++ "there")

import Lean.Data.HashMap



abbrev Reg : Type := String -- deriving BEq, Hashable, Repr, ToString
def regs : List Reg := List.map (fun n => s!"r{n}") 
                      (List.range 10) 
          
abbrev Var : Type := String -- deriving BEq, Hashable, Repr, ToString
abbrev Env : Type := Lean.HashMap Var Reg
abbrev Code : Type := String -- deriving BEq, Hashable, Repr, ToString
abbrev Expr : Type := Env -> Reg × Code × Env

def fresh (env : List Reg) : Option Reg :=
  List.removeAll regs env |> List.head? 


def add (x y : Expr) : Expr := fun env =>
  let (rx,cx,env) := x env
  let temp := fresh env
  let (ry,cy,env) := y env
  (ry,
   cx ++ 
   s!"mov " ++ 
   cy ++ 
   s!"add {res}, {temp}, {ry}",
   env
  )



/-
def add : Expr -> Expr -> Expr
  | (rx, cx), (ry, cy) => 
    let temp := "r10"
    let res := "r11"
    let insn := s!"mov {temp}, {rx}"
    (res, cx ++ insn ++ cy ++ s!"add {res}, {temp}, {ry}")

-/


/- Nat -> Nat × String -/