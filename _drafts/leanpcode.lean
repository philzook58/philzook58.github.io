import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Json ToJson FromJson
-- https://proofassistants.stackexchange.com/questions/2501/how-to-handle-data-from-json-files-in-lean-4

-- Look at that haskell pcode interp
-- There was a coq semantics?

namespace X86
  def ram := 0
  def reg := 1
  def unique := 2
  def eax := 0
  def ebx := 4
  -- yada
end


structure varnode where
  space : Nat
  offset: Nat
  size: Nat

inductive binpcode where
  | INT_ADD : binopcode
  | INT_SUB : binopcode
  | INT_MUL : binopcode

structure pcode1 where
  opcode : unopcode
  output : varnode
  input1 : varnode

structure binpcode where
  opcode : binopcode
  output : varnode
  input1 : varnode
  input2 : varnode



inductive pcode where
  binop : binpcode -> pcode
  load : varnode -> varnode -> pcode
  store : varnode -> varnode -> pcode
deriving ToJson, FromJson, Inhabited, Repr

structure State where
  memory : Nat -> Nat -> UInt8
  pc : Nat


-- parser of json. Autiderive some kind of parser?
