import Lean
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Command Term Meta

def hello : String := "hello world"
def bash (cmd : String) (_ : Unit) : IO String := do
  let output <- IO.Process.output {
    cmd := "bash",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr
  return output.stdout

def python (code : String) (_ : Unit) : IO String := do
  IO.FS.writeFile "/tmp/temp.py" code -- I did have -c but had bad problems with "
  bash s!"source /home/philip/philzook58.github.io/.venv/bin/activate && python3 /tmp/temp.py" ()




syntax "#sh" str term : command
syntax "#py" str term : command
macro_rules
  | `(#sh $cmd:str $go:term) => `(#eval bash $cmd $go)
  | `(#py $cmd:str $go:term) => `(#eval python $cmd $go)


#py r#"
for i in range(3):
  print(i)
"# ()

#eval getFileName
#eval getRef
#eval getFileMap

def plot (data : List Float) (_ : Unit) : IO Unit := do
  let code := s!"import matplotlib.pyplot as plt; plt.plot({data}); plt.show()"
  let _ <- python code ()
  return ()

def imshow [ToString a] (data : a) (_ : Unit) : IO Unit := do
  let code := s!"import matplotlib.pyplot as plt; plt.imshow({data}); plt.show()"
  let _ <- python code ()
  return ()

--#eval plot [1,2,3]
--#eval imshow [[0,1],[2,0]]


def imageUriHtml (uri : String) : ProofWidgets.Html :=
  .element "img"
    #[
      ("src", Lean.Json.str uri)
    ]
    #[]

def base64File (path : String) : IO String := do
  let out ← IO.Process.output {
    cmd := "base64"
    args := #["-w", "0", path]
  }
  if out.exitCode != 0 then
    throw <| IO.userError out.stderr
  return out.stdout --.trimAsciiEnd.toString

def imgview path := do
  let data <- base64File path
  return imageUriHtml ("data:image/png;base64," ++ data)

#html imgview "/home/philip/Pictures/Screenshots/ordered_resolve.png"


#html do
  let data <- python r#"
import io, base64
import matplotlib.pyplot as plt

plt.plot([1,2,3])

buf = io.BytesIO()
plt.savefig(buf, format="png", bbox_inches="tight")
print(base64.b64encode(buf.getvalue()).decode())
"# ()
  return imageUriHtml ("data:image/png;base64," ++ data)

/-
#html do
  --let data <- bash "base64 -w 0 /home/philip/Pictures/Screenshots/ordered_resolve.png" ()
  return imageUriHtml ("data:image/png;base64," ++ data)

def rawHtmlIframe (s : String) : ProofWidgets.Html :=
  .element "iframe"
    #[
      ("srcDoc", Lean.Json.str s)
    ]
    #[]

#html rawHtmlIframe "<h1>Hello</h1><p><b>Rendered HTML</b></p>"




open scoped ProofWidgets.Jsx
#html<button> hello </button>
#html <img src="/assets/thinning/identity.png" />

open Lean
open scoped ProofWidgets.Jsx

-/

/-
syntax (name := mycommand1) "#sh" : command -- declare the syntax

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#sh -- Hello World
-/


/-
syntax (name := mycommand1) "#sh" str term : command

@[command_elab mycommand1]
def mycommand1Impl : CommandElab
  | `(command| #sh $msg:str $t:term) => do
      if t.raw.isMissing then -- I needed to inspect t to stop this from actually running? How weird.
        return ()
      bash msg.getString ()
  | _ => throwUnsupportedSyntax

#sh "echo hel" ()
-/

-- import LeanPy
/-
import LeanPy
open LeanPy.Python in
@[python "numpy_dot"]
def numpyDot (xs ys : Array Int) : IO Int := do
  init ()                         -- dlopens libpython once
  let np ← import_ "numpy"
  let dot ← np.getAttr "dot"
  let a ← Py.ofList (xs.toList.map Py.ofInt)
  let b ← Py.ofList (ys.toList.map Py.ofInt)
  (← dot.call #[← a, ← b]).toInt


sympy analyze or simp?
getting something automaticaly out of lean would be annoying



-/
