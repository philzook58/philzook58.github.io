import Lean
open Lean Widget

#eval (1 : Nat)


def mkfile (filename : String) (contents : String) : IO Unit :=
  IO.FS.writeFile (System.mkFilePath ["/tmp/",filename]) contents

#eval mkfile "foo.g" r###"
print("hello worlddfsfdsfs")
print("bye nooow")
"###

#eval (· + 3) 2

#eval IO.Process.run { cmd := "python", args := #["/tmp/foo.g"] } >>= IO.println

@[widget_module]
def
helloWidget :
Widget.Module where
  javascript :=
"
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, 'Hello ' + name + '!')
    }"

#widget helloWidget

/-!

# Header one

## Header two
There is n
<https://www.google.com>


https://github.com/andrejbauer/partial-combinatory-algebras
https://reservoir.lean-lang.org/
https://reservoir.lean-lang.org/@leanprover/TensorLib
https://reservoir.lean-lang.org/@leanprover/TenCert
https://reservoir.lean-lang.org/@paulcadman/raylean

https://reservoir.lean-lang.org/@lean-machines-central/lean-machines

https://github.com/wellecks/ntptutorial
https://github.com/ufmg-smite/lean-smt
https://github.com/eric-wieser/lean-matrix-cookbook
https://github.com/opencompl/lean-mlir
-/

namespace mysection

-- I probably want namespace not section to avoid accidental clashes

end mysection


-- https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md


-- https://github.com/Seasawher/mdgen lean
-- https://github.com/arthurpaulino/lean2md python
-- convert this very file into a mardkwon file by swapping
-- /-!  to ``` -/ to ```lean
-- That's crazyyyyy
def convertLeanToMarkdown (input : String) (output : String) : IO Unit := do
  let content ← IO.FS.readFile input
  let lines := content.splitOn "\n"
  let markdown := lines.map (fun line =>
    if line.startsWith "/-!" then
      line.replace "/-!" "" -- Convert documentation comments to Markdown
    else if line.startsWith "--" then
      line.replace "--" ""  -- Convert single-line comments
    else
      "```lean\n" ++ line ++ "\n```" -- Wrap Lean code in Markdown code blocks
  )
  IO.FS.writeFile output (String.intercalate "\n" markdown)

#eval convertLeanToMarkdown "example.lean" "example.md"
