import Std.Data.HashMap
-- could do td4 or nand2tetris cpu

namespace hackcpu

inductive Comp
  | ZERO
  | ONE
  | NEGONE
  | D
  | A
  | M
  | NOTD
  | NOTA
  | NOTM
  | NEGD
  | NEGA
  | NEGM
  | INCD
  | INCA
  | INCM
  | DECD
  | DECA
  | DECM
  | ADD_DA
  | ADD_DM
  | SUB_DA
  | SUB_DM
  | SUB_AD
  | SUB_MD
  | AND_DA
  | AND_DM
  | OR_DA
  | OR_DM
  deriving Repr, BEq, DecidableEq

inductive Dest
  | NULL
  | M
  | D
  | MD
  | A
  | AM
  | AD
  | AMD
  deriving Repr, BEq, DecidableEq

inductive Jump
  | NULL
  | JGT
  | JEQ
  | JGE
  | JLT
  | JNE
  | JLE
  | JMP
  deriving Repr, BEq, DecidableEq

structure Cinstr where
  (comp : Comp)
  (dest : Dest)
  (jump : Jump)
  deriving Repr, BEq, DecidableEq

inductive Insn where
  | AInst (a : BitVec 16)
  | CInst (c : Cinstr)
  deriving Repr, BEq, DecidableEq

structure HackState where
  pc : BitVec 16
  rA : BitVec 16
  rD : BitVec 16
  mem : Std.HashMap (BitVec 16) (BitVec 16)
  progmem : Array Insn
  deriving Repr, Inhabited

def decode (insn : BitVec 16) : Insn := Insn.AInst 0


def evalComp (comp : Comp) (A D M : BitVec 16) : BitVec 16 :=
  match comp with
  | Comp.ZERO     => 0
  | Comp.ONE      => 1
  | Comp.NEGONE   => -1
  | Comp.D        => D
  | Comp.A        => A
  | Comp.M        => M
  | Comp.NOTD     => ~~~ D
  | Comp.NOTA     => ~~~ A
  | Comp.NOTM     => ~~~ M
  | Comp.NEGD     => -D
  | Comp.NEGA     => -A
  | Comp.NEGM     => -M
  | Comp.INCD     => D + 1
  | Comp.INCA     => A + 1
  | Comp.INCM     => M + 1
  | Comp.DECD     => D - 1
  | Comp.DECA     => A - 1
  | Comp.DECM     => M - 1
  | Comp.ADD_DA   => D + A
  | Comp.ADD_DM   => D + M
  | Comp.SUB_DA   => D - A
  | Comp.SUB_DM   => D - M
  | Comp.SUB_AD   => A - D
  | Comp.SUB_MD   => M - D
  | Comp.AND_DA   => D &&& A
  | Comp.AND_DM   => D &&& M
  | Comp.OR_DA    => D ||| A
  | Comp.OR_DM    => D ||| M


def updateDest (dest : Dest) (comp : BitVec 16) (state : HackState) : HackState :=
  match dest with
  | Dest.NULL => state
  | Dest.M    => { state with mem := state.mem.insert state.rA comp }
  | Dest.D    => { state with rD := comp }
  | Dest.MD   => { state with rD := comp, mem := state.mem.insert state.rA comp }
  | Dest.A    => { state with rA := comp }
  | Dest.AM   => { state with rA := comp, mem := state.mem.insert state.rA comp }
  | Dest.AD   => { state with rA := comp, rD := comp }
  | Dest.AMD  => { state with rA := comp, rD := comp, mem := state.mem.insert state.rA comp }


def evalJump (jump : Jump) (comp : BitVec 16) : Bool :=
  match jump with
  | Jump.NULL => false
  | Jump.JGT  => comp > 0
  | Jump.JEQ  => comp = 0
  | Jump.JGE  => comp >= 0
  | Jump.JLT  => comp < 0
  | Jump.JNE  => comp ≠ 0
  | Jump.JLE  => comp ≤ 0
  | Jump.JMP  => true



def execute (instr : Cinstr) (state : HackState) : HackState :=
  let A := state.rA
  let D := state.rD
  let pc := state.pc
  let M := (state.mem[A]?).getD (0 : BitVec 16)
  let comp := evalComp instr.comp A D M
  let state := updateDest instr.dest comp state
  let jump := evalJump instr.jump comp
  if jump then { state with pc := state.rA }
  else { state with pc := state.pc + 1 }


def toyinstr : Cinstr := { comp := Comp.INCD, dest := Dest.D, jump := Jump.NULL }

#eval execute toyinstr (default : HackState)
example (s : HackState) : execute toyinstr s = { s with rD := s.rD + 1, pc := s.pc + 1 } := by
  --simp [execute, evalComp, updateDest, evalJump]
  rfl

/-
def cycle (s : HackState) : Option HackState :=
  let insn ← s.progmem[s.pc] -- fetch
  let s' := match insn with
    | Insn.AInst a => Some { s with rA := a }
    | Insn.CInst c => execute c s
-/

end hackcpu

namespace td4

inductive Instruction
| AddA (immediate : BitVec 4)
| AddB (immediate : BitVec 4)
| MovAFromB
| MovBFromA
| MovAImmediate (immediate : BitVec 4)
| MovBImmediate (immediate : BitVec 4)
| InA
| InB
| OutA
| OutB
| Jmp (address : BitVec 4)
| Jnc (address : BitVec 4)
deriving Repr

structure CPUState where
  a : BitVec 4
  b : BitVec 4
  out : BitVec 4
  pc : BitVec 4
  carry : Bool
  inp : BitVec 4
  program : Array Instruction
  deriving Repr

def executeInstruction : Instruction → CPUState → CPUState
| .AddA im, state =>
  let sum := state.a.toNat + im.toNat
  { state with
    a := BitVec.ofNat 4 (sum % 16),
    carry := sum ≥ 16,
    pc := state.pc + 1 }
| .AddB im, state =>
  let sum := state.b.toNat + im.toNat
  { state with
    b := BitVec.ofNat 4 (sum % 16),
    carry := sum ≥ 16,
    pc := state.pc + 1 }
| .MovAFromB, state =>
  { state with a := state.b, pc := state.pc + 1 }
| .MovBFromA, state =>
  { state with b := state.a, pc := state.pc + 1 }
| .MovAImmediate im, state =>
  { state with a := im, pc := state.pc + 1 }
| .MovBImmediate im, state =>
  { state with b := im, pc := state.pc + 1 }
| .InA, state =>
  { state with a := state.inp, pc := state.pc + 1 }
| .InB, state =>
  { state with b := state.inp, pc := state.pc + 1 }
| .OutA, state =>
  { state with out := state.a, pc := state.pc + 1 }
| .OutB, state =>
  { state with out := state.b, pc := state.pc + 1 }
| .Jmp addr, state =>
  { state with pc := addr }
| .Jnc addr, state =>
  if state.carry then
    { state with pc := state.pc + 1 }
  else
    { state with pc := addr }

def simulate (state : CPUState) (steps : Nat) : CPUState :=
  match steps with
  | 0 => state
  | steps + 1 =>
    if h : state.pc.toNat < state.program.size then
      let inst := state.program[state.pc.toNat]
      simulate (executeInstruction inst state) steps
    else
      state

-- Example usage
def exampleProgram : Array Instruction :=
  #[Instruction.AddB (BitVec.ofNat 4 1),
    Instruction.OutB,
    Instruction.Jmp (BitVec.ofNat 4 0)]

def initialState : CPUState :=
  { a := BitVec.ofNat 4 0,
    b := BitVec.ofNat 4 0,
    out := BitVec.ofNat 4 0,
    pc := BitVec.ofNat 4 0,
    carry := false,
    inp := BitVec.ofNat 4 0,
    program := exampleProgram }

#eval simulate initialState 20


-- https://lean-lang.org/lean4/doc/metaprogramming-arith.html
-- https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html
declare_syntax_cat td4_reg
syntax "A" : td4_reg
syntax "B" : td4_reg

declare_syntax_cat td4_insn
syntax "MOV" td4_reg td4_reg ";" : td4_insn

-- auxiliary notation for translating `arith` into `term`
syntax "`[TD4| " td4_insn "]" : term

macro_rules
  | `(`[TD4| MOV A B;]) => `(Instruction.MovBFromA)
  | `(`[TD4| MOV B A;]) => `(Instruction.MovAFromB)


#eval `[TD4| MOV A B;
]

end td4
