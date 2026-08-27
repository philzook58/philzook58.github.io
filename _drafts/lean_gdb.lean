import Philib
import Lean
import Lake.DSL.Meta
import Lake.DSL.Syntax

-- Not working?
--def bizzy := run_io (python "print(3)" ())

/-
Do an entire lean intro file in a single elab call?

-/
/-

initialize mycounter : IO.Ref Nat <- IO.mkRef 0
-- Crashes
run_elab
  mycounter.modify (fun x => x + 1)
-/
/-
#check Lean.registerEnvExtension
initialize mycounter : Lean.EnvExtension Int <- Lean.registerEnvExtension (pure 0)

run_elab
  Lean.MonadEnv.modifyEnv (fun env =>
    mycounter.modifyState env (. + 1))
-/

#eval IO.FS.writeFile "/tmp/foo.c" r#"
int main(){
  for(int i = 0; i < 10; i++){

  }
}
"#
#eval json% {"a" : 3}


-- computer dream machines
-- direct manipulation
def myfoo : String := include_str "/tmp/foo.c"
#print myfoo

def bizzy : String := by_elab
  let result ← liftM <| python "print(3)" ()
  return Lean.toExpr result

#check Lean.Json.parse
def from_string (x : String) : α :=
  Lean.Json.parse x |>.toOption.get!.fromJson
#eval bizzy

#sh "gcc /tmp/foo.c -g -o /tmp/foo" ()
#sh "objdump -d /tmp/foo" ()

/-
gdb mi  https://sourceware.org/gdb/current/onlinedocs/gdb.html/GDB_002fMI.html#GDB_002fMI

-/

-- run_cmd elabCommand
-- #eval elabCommand (<- `(def foo : Nat := 42)

/-
Maybe what I want is to always be working in elab?
I want to create new terms and ask for solutions and stuff.

-/
run_cmd
  let barId := Lean.mkIdent `bar
  Lean.Elab.Command.elabCommand (<- `(def $barId : Nat := 42))
#print bar

initialize myname : String ← IO.FS.readFile "foo.txt"
#print myname -- opaque

/-
What is it _exactly_ that I'm missing.
I could


Maybe try to use OfString
py_def foo := "some python code"
sh_def biz := "some bash code"
import tla?
java -cp tla2tools.sanychecker

dumb mathlib

-/

open Lean Meta Elab Command Term

def ioToExpr [ToExpr α] (x : IO α) : IO Expr :=
  toExpr <$> x

syntax (name := evalDef) "eval_def " ident " := " doSeq : command

@[command_elab evalDef]
unsafe def elabEvalDef : CommandElab
  | `(eval_def $name:ident := $rhs) => do
      let (type, value) ← liftTermElabM do
        let ioExpr ← elabTermEnsuringType (← `(ioToExpr (do $rhs)))
          (mkApp (mkConst ``IO) (mkConst ``Expr))
        synthesizeSyntheticMVarsNoPostponing
        let action ← evalExpr (IO Expr) (mkApp (mkConst ``IO) (mkConst ``Expr))
          (← instantiateMVars ioExpr)
        let value ← action
        pure (← inferType value, value)
      liftCoreM <| addAndCompile <| .defnDecl {
        name := (← getCurrNamespace) ++ name.getId
        levelParams := []
        type, value
        hints := .regular 0
        safety := .safe
      }
  | _ => throwUnsupportedSyntax

eval_def foo := IO.FS.readFile "/tmp/foo.c"
#eval foo

def parseJson! (s : String) : Json :=
  (Json.parse s).toOption.get!

instance : ToExpr Json where
  toTypeExpr := mkConst ``Json
  toExpr j := mkApp (mkConst ``parseJson!) (toExpr j.compress)

eval_def bar1 := return 1 + 1
#eval bar1
eval_def mypyfun := do
  let ret <- python r#"import json; print(json.dumps({"x" : 3}))"# ()
  return (Lean.Json.parse ret |>.toOption.get!)
#eval mypyfun
eval_def mypyfun2  := python r#"import json; print(json.dumps({"x" : 3}))"# ()
#eval Lean.Json.parse mypyfun2

def decodeJson! [FromJson α] [Inhabited α] (s : String) : α :=
  (Json.parse s >>= fromJson?).toOption.get!

syntax:lead (name := pyTerm) "py% " str : term

@[term_elab pyTerm]
def elabPyTerm : TermElab := fun stx expectedType? => do
  let expectedType ← expectedType?.getDM <| throwErrorAt stx "py% needs an expected type"
  match stx with
  | `(py% $code:str) =>
      let script := s!"import json\nprint(json.dumps({code.getString}))"
      let output ← liftM <| python script ()
      let outputSyntax := Syntax.mkStrLit output
      elabTerm (← `(decodeJson! $(⟨outputSyntax⟩))) expectedType
  | _ => throwUnsupportedSyntax

def squares : Array Nat := py% "[i * i for i in range(5)]"
#eval squares
#eval ((py% "(1,2)") : Nat × Nat)
-- cute but fairly useless?
/-
Ok, so I don't really need eval_def.
I can just elab a term

#py r#"
import kdrag as kd
import kdrag.contrib.pcode as pcode
pcode.BinaryContext
"#

wait so is this what run_io% is about?
-/



inductive Foo where
  | biz | boz
deriving ToJson, FromJson, Repr

#eval Foo.biz |> toJson
#check fromJson?
#eval ((Json.str "biz" |> fromJson?) : Except String Foo)
