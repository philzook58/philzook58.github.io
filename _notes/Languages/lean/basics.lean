#eval 1 + 1 -- it's a nat
#eval String.append "hello" "world"
#eval if 1 > 2 then "yes" else "no"
#eval (1 + 1 : Int)

def hello := "hello"
def Str : Type := String

abbrev N : Type := Nat
#check 1.2

structure Point where
  x : Float
  y : Float
deriving Repr

#check ({x := 1, y := 2} : Point)


inductive MyBool where
  | MyTrue : MyBool
  | MyFalse : MyBool

#check MyBool.MyTrue

#eval Lean.versionString
#eval Lean.

#check fun (x : Nat) => x
#check λ x => x
#eval let y := 2; y + y

