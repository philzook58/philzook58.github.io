import Lean.Data.Json
import Std.Data.HashMap
--open Lean (Json)
--import System.IO

def readFileContents (filePath : String) : IO Unit := do
  let contents <- IO.FS.readFile filePath
  IO.println s!"Contents of the file:\n{contents}"

#eval readFileContents "/tmp/vampire.smt2"

#eval Lean.Json.parse  "{\"name\": \"Alice\", \"age\": 30}"

def exampleHashMap : Std.HashMap String Int :=
  Std.HashMap.empty.insert "apple" 3 |>.insert "banana" 5

inductive Expr : Type
| uvar : String -> Expr
| app : String -> List Expr -> Expr

deriving instance BEq, Hashable, Inhabited, Repr
  --,Lean.Json.toJson, Lean.Json.FromJson
  for Expr

--open Expr




def pmatch : Expr → Expr → Bool
 | (.app f args), (.app f' args') => f == f' && args == args'
 | _, _ => false



#eval pmatch (.app "a" []) (.app "a" [])
#check pmatch

def eq := Expr × Expr
def rule := Expr × Expr

-- https://github.com/codyroux/knuth-bendix/

def main : IO Unit :=
    do
        IO.println "Hello, world!"
        IO.println "hi"
        IO.println (repr (Expr.App "c" []))
