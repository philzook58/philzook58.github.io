import Std.Tactic.BVDecide

example : forall (x : BitVec 32), x ||| x = x := by bv_decide
-- https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/BVDecide.html

-- https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/
#eval 5#8 -- bitvector literals

#eval 5#8 ++ 3#8 -- concat is called  append






inductive Space where
    | ram
    | register
    | unique

structure VarNode n where
    space : Space
    offset : BitVec n
    size : Nat

structure PCodeState bits where
    addr : BitVec bits
    pcode_pc : Nat
    ram : BitVec bits -> BitVec 8
    register : BitVec bits -> BitVec 8
    unique : BitVec bits -> BitVec 8


namespace RiscV

def r0 : BitVec 32 := 0
def r1 : BitVec 32 := 4
def r2 : BitVec 32 := 8

end RiscV

-- def selectappend (le := true) (mem : BitVec 32 -> BitVec 8) (addr : BitVec 32) (size : Nat) : BitVec (size * 8) :=


-- do it by hand?
/-
Make a whole AST yada yada. But then unwrap it in an interpreter.


-/
/-
inductive OpCode2 where
    | INT_ADD
    | INT_SUB
-/
-- def setValue (state : MachineState bits) (output : VarNode bits) :=

/-
def executeBinary (OpCode2) (output : VarNode 32) (input1 : VarNode 32) (input2 : VarNode 32) : PCodeState 32 -> PCodeState 32 :=
    fun state =>
        let val1 := state.register input1.offset
        let val2 := state.register input2.offset
        let result :=
            match OpCode2 with
            | OpCode2.INT_ADD => val1 + val2
            | OpCode2.INT_SUB => val1 - val2
        let newRegister := fun offset =>
            if offset = output.offset then result else state.register offset
        { state with register := newRegister }


/-
def example {} : PCodeState 32 :=
    let pcode_pc := 0
    let addr := 0
    let ram := fun addr => if addr = 0xdeadbeef then 42 else ram addr
    let register := fun offset => if offset = RiscV.r1 then 10 else register offset
-/
