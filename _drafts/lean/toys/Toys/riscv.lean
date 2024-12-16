import Std.Data.HashMap

-- Define types for the components
abbrev GPR_File := Array UInt64  -- General Purpose Registers
abbrev FPR_File := Array Float   -- Floating Point Registers
abbrev CSR_File := Std.HashMap UInt64 UInt64  -- Control Status Registers
abbrev Mem := Std.HashMap UInt64 UInt8        -- Memory
abbrev MMIO := Std.HashMap UInt64 UInt8       -- Memory-Mapped IO
abbrev Priv_Level := UInt8                    -- Privilege level
abbrev RV := String                           -- RISC-V variant (e.g., "RV32I", "RV64I")
abbrev Run_State := String                    -- Run state (e.g., "Running", "Halted")

structure Machine_State where
  f_pc               : UInt64
  f_gprs             : GPR_File
  f_fprs             : FPR_File
  f_csrs             : CSR_File
  f_priv             : Priv_Level
  f_mem              : Mem
  f_mmio             : MMIO
  f_eaddr            : UInt64
  f_wdata            : UInt64
  f_mem_addr_ranges  : List (UInt64 × UInt64)
  f_rv               : RV
  f_run_state        : Run_State
  f_last_instr_trapped : Bool
  f_verbosity        : Int
  deriving Repr, Inhabited

inductive InstrI
  | LUI    (rd : UInt8) (imm20 : UInt32) -- Load Upper Immediate
  | AUIPC  (rd : UInt8) (imm20 : UInt32) -- Add Upper Immediate to PC
  | JAL    (rd : UInt8) (imm21 : UInt32) -- Jump and Link
  | JALR   (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Jump and Link Register
  | BEQ    (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Equal
  | BNE    (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Not Equal
  | BLT    (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Less Than
  | BGE    (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Greater or Equal
  | BLTU   (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Less Than Unsigned
  | BGEU   (rs1 : UInt8) (rs2 : UInt8) (imm13 : UInt32) -- Branch if Greater or Equal Unsigned
  | LB     (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Load Byte
  | LH     (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Load Halfword
  | LW     (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Load Word
  | LBU    (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Load Byte Unsigned
  | LHU    (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Load Halfword Unsigned
  | SB     (rs1 : UInt8) (rs2 : UInt8) (imm12 : UInt32) -- Store Byte
  | SH     (rs1 : UInt8) (rs2 : UInt8) (imm12 : UInt32) -- Store Halfword
  | SW     (rs1 : UInt8) (rs2 : UInt8) (imm12 : UInt32) -- Store Word
  | ADDI   (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Add Immediate
  | SLTI   (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Set Less Than Immediate
  | SLTIU  (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- Set Less Than Immediate Unsigned
  | XORI   (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- XOR Immediate
  | ORI    (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- OR Immediate
  | ANDI   (rd : UInt8) (rs1 : UInt8) (imm12 : UInt32) -- AND Immediate
  | SLLI   (rd : UInt8) (rs1 : UInt8) (shamt : UInt32) -- Shift Left Logical Immediate
  | SRLI   (rd : UInt8) (rs1 : UInt8) (shamt : UInt32) -- Shift Right Logical Immediate
  | SRAI   (rd : UInt8) (rs1 : UInt8) (shamt : UInt32) -- Shift Right Arithmetic Immediate
  | ADD    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Add
  | SUB    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Subtract
  | SLL    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Shift Left Logical
  | SLT    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Set Less Than
  | SLTU   (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Set Less Than Unsigned
  | XOR    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- XOR
  | SRL    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Shift Right Logical
  | SRA    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- Shift Right Arithmetic
  | OR     (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- OR
  | AND    (rd : UInt8) (rs1 : UInt8) (rs2 : UInt8) -- AND
  | FENCE  (fm : UInt32) (pred : UInt32) (succ : UInt32) -- Memory Fence
  | ECALL -- Environment Call
  | EBREAK -- Environment Break
  deriving Repr

-- OPCODES
-- https://github.com/rsnikhil/Forvis_RISCV-ISA-Spec/blob/master/src/Forvis_Spec_I.hs


def funct3_JALR : BitVec 3 := 0b000

-- opcode_BRANCH sub-opcodes
def funct3_BEQ : BitVec 3 := 0b000
def funct3_BNE : BitVec 3 := 0b001
def funct3_BLT : BitVec 3 := 0b100
def funct3_BGE : BitVec 3 := 0b101
def funct3_BLTU : BitVec 3 := 0b110
def funct3_BGEU : BitVec 3 := 0b111

-- opcode_OP_IMM sub-opcodes
def funct3_ADDI : BitVec 3 := 0b000
def funct3_SLTI : BitVec 3 := 0b010
def funct3_SLTIU : BitVec 3 := 0b011
def funct3_XORI : BitVec 3 := 0b100
def funct3_ORI : BitVec 3 := 0b110
def funct3_ANDI : BitVec 3 := 0b111
def funct3_SLLI : BitVec 3 := 0b001
def funct3_SRLI : BitVec 3 := 0b101
def funct3_SRAI : BitVec 3 := 0b101

-- OP_IMM.SLLI/SRLI/SRAI sub-opcodes for RV32
def msbs7_SLLI : BitVec 7 := 0b0000000
def msbs7_SRLI : BitVec 7 := 0b0000000
def msbs7_SRAI : BitVec 7 := 0b0100000

-- OP_IMM.SLLI/SRLI/SRAI sub-opcodes for RV64
def msbs6_SLLI : BitVec 6 := 0b000000
def msbs6_SRLI : BitVec 6 := 0b000000
def msbs6_SRAI : BitVec 6 := 0b010000

-- opcode_OP sub-opcodes
def funct3_ADD : BitVec 3 := 0b000
def funct7_ADD : BitVec 7 := 0b0000000
def funct3_SUB : BitVec 3 := 0b000
def funct7_SUB : BitVec 7 := 0b0100000
def funct3_SLT : BitVec 3 := 0b010
def funct7_SLT : BitVec 7 := 0b0000000
def funct3_SLTU : BitVec 3 := 0b011
def funct7_SLTU : BitVec 7 := 0b0000000
def funct3_XOR : BitVec 3 := 0b100
def funct7_XOR : BitVec 7 := 0b0000000
def funct3_OR : BitVec 3 := 0b110
def funct7_OR : BitVec 7 := 0b0000000
def funct3_AND : BitVec 3 := 0b111
def funct7_AND : BitVec 7 := 0b0000000
def funct3_SLL : BitVec 3 := 0b001
def funct7_SLL : BitVec 7 := 0b0000000
def funct3_SRL : BitVec 3 := 0b101
def funct7_SRL : BitVec 7 := 0b0000000
def funct3_SRA : BitVec 3 := 0b101
def funct7_SRA : BitVec 7 := 0b0100000

-- opcode_MISC_MEM sub-opcodes
def funct3_FENCE : BitVec 3 := 0b000

-- opcode_SYSTEM sub-opcodes
def funct12_ECALL : BitVec 12 := 0b000000000000
def funct12_EBREAK : BitVec 12 := 0b000000000001

def decodeI (instr32 : BitVec 32) : Option InstrI :=
  let opcode := BitVec.extractLsb 6 0 instr32
  let rd := BitVec.extractLsb 11 7 instr32
  let funct3 := BitVec.extractLsb 14 12 instr32
  let rs1 := BitVec.extractLsb 19 15 instr32
  let rs1 := BitVec.extractLsb 19 15 instr32
  let rs1 := BitVec.extractLsb 19 15 instr32
  let rs2 := BitVec.extractLsb 24 20 instr32
  let funct7 := BitVec.extractLsb 31 25 instr32
  let imm12 := BitVec.extractLsb 31 20 instr32
  let imm13 :=
    (BitVec.extractLsb  31 31 instr32).shiftLeft 12 ++
    (BitVec.extractLsb 30 25 instr32).shiftLeft 5 ++
    (BitVec.extractLsb 11 8 instr32).shiftLeft 1 ++
    (BitVec.extractLsb 7 7 instr32).shiftLeft 11
  let imm20 := BitVec.extractLsb 31 12 instr32
  let imm21 :=
    (BitVec.extractLsb 31 31 instr32 ).shiftLeft 20 ++
    (BitVec.extractLsb 30 21 instr32).shiftLeft 1 ++
    (BitVec.extractLsb 20 20 instr32).shiftLeft 11 ++
    (BitVec.extractLsb 19 12 instr32).shiftLeft 12
  match opcode with
  | 0b0110111 => some (InstrI.LUI rd imm20)
  | _ => none


#eval decodeI 0x00000513
