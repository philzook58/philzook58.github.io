import Philib

#py r#"
if 3 > 0:
  print("hi")
print(3)
print({"hello"})
print(4)"#

open Lean Elab Term

def decodeJson! [FromJson α] [Inhabited α] (json : Json) : α :=
  match fromJson? json with
  | .ok x => x
  | .error e => panic! e

private def elabPythonJson (ref : Syntax) (script : String)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← match expectedType? with
    | none => pure (Lean.mkConst ``Json)
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if expectedType.isMVar then
        expectedType.mvarId!.assign (Lean.mkConst ``Json)
        pure (Lean.mkConst ``Json)
      else
        pure expectedType
  let output ← liftM (m := IO) <| python script ()
  let output := output.trimAscii.toString
  let jsonTerm : Term ← match Parser.runParserCategory (← getEnv) `term s!"json% {output}" with
    | .ok stx => pure ⟨stx⟩
    | .error e => throwErrorAt ref m!"Python did not produce JSON: {e}\noutput: {output}"
  elabTerm (← `(decodeJson! $jsonTerm)) expectedType

syntax:max (name := pyTerm) "py!" str (" with " term)? : term
syntax:max (name := pymodTerm) "pymod!" str (" with " term)? : term

private unsafe def evalPythonInput (ref : Syntax) (input : Term) : TermElabM Json := do
  let jsonExpr ← elabTerm (← `(toJson $input)) (Lean.mkConst ``Json)
  synthesizeSyntheticMVarsNoPostponing
  let jsonExpr ← instantiateMVars jsonExpr
  if jsonExpr.hasFVar then
    throwErrorAt ref "Python input must be closed"
  Meta.evalExpr Json (Lean.mkConst ``Json) jsonExpr

private def pythonInputBinding (input : Json) : String :=
  let quoted := (Json.str input.compress).compress
  s!"lean = json.loads({quoted})\n"

private unsafe def elabPython (ref : Syntax) (code : String) (input? : Option Term)
    (isModule : Bool) (expectedType? : Option Expr) : TermElabM Expr := do
  let binding ← input?.mapM fun input => pythonInputBinding <$> evalPythonInput ref input
  let binding := binding.getD ""
  let script := if isModule then
    s!"import json\n{binding}{code}"
  else
    s!"import json\n{binding}print(json.dumps(\n{code}\n, default=lambda x: x.tolist()))"
  elabPythonJson ref script expectedType?

@[term_elab pyTerm]
unsafe def elabPyTerm : TermElab := fun stx expectedType? => do
  let `(py! $code:str $[with $input]?) := stx | throwUnsupportedSyntax
  elabPython code code.getString input false expectedType?

@[term_elab pymodTerm]
unsafe def elabPymodTerm : TermElab := fun stx expectedType? => do
  let `(pymod! $code:str $[with $input]?) := stx | throwUnsupportedSyntax
  elabPython code code.getString input true expectedType?

def biz : Nat := 3
-- #eval py! s!"{biz} + 3"
#eval py! r#"__import__('numpy').zeros(4)"#
#eval py! r#"{"foo": lean}"# with biz
#eval pymod! r#"
def foo(x):
  return lean * x

print(json.dumps([foo(i) for i in range(4)]))
"# with biz

/-
`py! code` wraps one Python expression in `json.dumps`; `pymod! code` runs a complete
script that prints JSON. An optional `with leanTerm` calls `toJson` and binds the value
as Python's `lean`. The input must be closed and evaluable during elaboration. With no
expected Lean type the result is `Json`; otherwise `decodeJson!` uses `FromJson`.

The VS Code extension JSON adds this grammar contribution:
```
"injectTo": ["source.lean4"],
"embeddedLanguages": {
  "meta.embedded.block.python": "python",
  "meta.embedded.inline.python": "python"
}
```
Its injected grammar matches ordinary and raw strings after `#py`, `py!`, and
`pymod!`. The term-string rules are:
```
"begin": "((?:pymod|py)!)(\\s*)(r#\")"
"begin": "((?:pymod|py)!)(\")"
```
It gives their contents one of those `meta.embedded.*.python` scopes and includes
`source.python`. `.vscode/settings.json` adds:
```
"[lean4]": { "editor.semanticHighlighting.enabled": false }
```
-/
