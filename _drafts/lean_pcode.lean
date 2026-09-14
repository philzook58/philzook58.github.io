import Philib
import Lean
open Lean

def mythree : String :=  by_elab python "print(\"foo\")" () |>.map toExpr |> liftM
#eval mythree
-- https://www.philipzucker.com/assembly_verify/
#eval IO.FS.writeFile "/tmp/mov.s" r#"
.globl myfunc

.text
    myfunc:
    movq $42, %rax
    ret
"#

-- Maybe just ue python to write a file and then
-- include it.
def myasm : String := include_str "/tmp/mov.s"
#eval myasm

#sh "as /tmp/mov.s -o /tmp/mov" ()
-- #sh "python3 -m pypcode x86:LE:64:default /tmp/mov" ()
/-
0x0/2: JG 0x47
   0: unique[26000:1] = !ZF
   1: unique[26100:1] = OF == SF
   2: unique[26300:1] = unique[26000:1] && unique[26100:1]
   3: if (unique[26300:1]) goto ram[47:8]


Maybe as an alternative to cle, we should use gdb?
-/

def mycode := include_str "/tmp/mov"

#py r#"
import pypcode as pcode
from pypcode import Context
import cle
ctx = Context("x86:LE:64:default")
ld = cle.Loader("/tmp/mov")
myfunc = ld.find_symbol("myfunc")
data = ld.memory.load(myfunc.rebased_addr, 0x7)
#print(data)
#with open("/tmp/mov", "rb") as f:
#print(ctx.disassemble(data))
def vnode_to_dict(vnode):
  return {
    "space" : vnode.space.name,
    "offset" : vnode.offset,
    "size" : vnode.size

  }
def op_to_dict(op):
  return {
    "opcode" : str(op.opcode)[7:], # cut out `OpCode.`
    "output" : vnode_to_dict(op.output) if op.output else None,
    "inputs" : [vnode_to_dict(vnode)  for vnode in op.inputs]
  }



#for op in ctx.translate(data).ops:
#  print(op, op.opcode, op.inputs, op.output)
import json
print(json.dumps([op_to_dict(op) for op in ctx.translate(data).ops]))

print(json.dumps({name : vnode_to_dict(vnode) for name,vnode in ctx.registers.items()}))
"#

def test_ops : Lean.Json :=
  json% [{"opcode": "IMARK",
  "output": null,
  "inputs": [{"space": "ram", "offset": 0, "size": 7}]},
  {"opcode": "COPY",
   "output": {"space": "register", "offset": 0, "size": 8},
   "inputs": [{"space": "const", "offset": 42, "size": 8}]}]

inductive OpCode where
  | IMARK | COPY
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

#eval OpCode.IMARK |> Lean.toJson

structure VNode where
  space : String
  offset : Nat
  size : Nat
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

#guard (json% {"space": "ram", "offset": 0, "size": 7} |> Lean.fromJson? : Except String VNode) |>.isOk

structure Op where
  opcode : OpCode
  output : Option VNode
  inputs : Array VNode
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

#eval (Lean.fromJson? (json% 3) : Except String Nat)

#eval VNode.mk "register" 10 8 |> Lean.toJson

def prog : Array Op := test_ops |> Lean.fromJson? |> Except.toOption |> Option.get!

#eval prog


abbrev State := Std.HashMap String (Std.HashMap Nat (BitVec 8))

def interp_op (op : Op) (state : State) : Except String State :=
  match op.opcode with
  | .IMARK => Except.ok state
  | .COPY => do
          let output <- if op.output.isSome then Except.ok op.output.get! else Except.error "No Output on COPY"
          let input := op.inputs[0]!
          let ival := state.get! input.space |>.get! input.offset
          return state.modify output.space fun mmap => mmap.insert output.offset ival

/-
Even evaluating this is kind of a pain
I do want it to delab to register names?


-/


--#eval interp_op {opcode := .COPY, output := {space := "ram", offset := }, }


/-
We could make a direct lean binding to pcode via rust bindings
or via trail of bits cmake repackaging.
But working off of pypcode is good gettings started?

-/
