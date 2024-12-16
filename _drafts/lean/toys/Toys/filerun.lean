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

def python (code : String) : IO String := do
  IO.Process.run { cmd := "python", args := #["-c", code] }

#eval python r#"
from kdrag.all import *
import json
x = smt.Real("x")
print(smt.ForAll([x], x + 0 == x))

print('hello world');
print("bye nowddd")


"#



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

section symbo


axiom R : Type

axiom add : R → R → R
axiom mul : R → R → R
axiom neg : R → R
axiom natof : Nat → R
noncomputable instance : Add R where
  add := add
noncomputable instance : Mul R where
  mul := mul
noncomputable instance : Neg R where
  neg := neg
noncomputable instance : OfNat R n where
  ofNat := (natof n)
axiom sin : R → R
axiom cos : R → R
axiom tan : R → R
axiom d : (R -> R) -> (R -> R)

@[simp] axiom add_zero : ∀ (a : R), a + 0 = a
@[simp] axiom add_zero_left : ∀ (a : R), 0 + a = a
@[simp] axiom distrib : ∀ (a b c : R), a * (b + c) = a * b + a * c
@[simp] axiom mul_one : ∀ (a : R), a * 1 = a
@[simp] axiom mul_one_left : ∀ (a : R), 1 * a = a
@[simp] axiom mul_zero : ∀ (a : R), a * 0 = 0
@[simp] axiom neg_neg : ∀ (a : R), - - a = a
@[simp] axiom neg_add : ∀ (a b : R), - (a + b) = - a + - b


@[simp] axiom d_const : ∀ (c : R), d (fun x => c) = fun x => 0
@[simp] axiom d_id : d (fun x => x) = fun x => 1
@[simp] axiom d_add : ∀ (f g : R -> R), d (fun x => f x + g x) = fun x => d f x + d g x
@[simp] axiom d_mul : ∀ (f g : R -> R), d (fun x => f x * g x) = fun x => f x * d g x + d f x * g x
@[simp] axiom d_sin : d sin = cos
@[simp] axiom d_cos (f : R -> R) : d (fun x => cos (f x)) =
  fun x => -sin (f x) * (d f) x

axiom integ : (R → R) → R → R → R

axiom zero : R
--variable (neg : R → R)
--variable (zero one : R)
--variable (of_int : Int → R)

#print add_zero
-- axiom add_assoc : ∀ a b c, add (add a b) c = add a (add b c)


example (a b : R) : a + 0 = b := by
  simp
  sorry
example (a b : R) : 0 + 1*a + 0 = b := by
  simp
  sorry
example (a b : R) (f : R -> R) : d (fun x => cos (cos x)) = f := by
  simp
  sorry


example (a b : R) : exists c, b = c -> add a zero = c := by
  exists c

  intros
  simp
  rewrite [add_zero]


/-
Using lean for synthesis.
Say I have f defined by cases.
Can I derive an inverse function ?g (f x) = x
via unification?
How do we port synthesis strategies




-/

end symbo

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

-- #eval convertLeanToMarkdown "example.lean" "example.md"
