import Lean.Elab.Tactic.BVDecide
import _drafts.Myhelper
--import _drafts.Myhelper.lean

#eval python
r#"
print("hello wordld")
print([] + [1])
"#

#eval bash "echo hello my world && echo bye now"

#eval IO.FS.writeFile "/tmp/hello.c" r#"
#include <stdio.h>
int main(){
  printf("hello world from c\n");
  return 0;
}
"#

-- maybe post application is better. Then we won't execute a partial command
#eval "gcc -o /tmp/hello /tmp/hello.c && /tmp/hello" |> bash



section junk

inductive term where
  | var : Nat → term
  | app : term → term → term
  | abs : term → term

deriving Repr


/-
"print(\"hello world\")"
-/
#eval term.abs (term.app (term.var 0) (term.var 1))

inductive neut where
  | var : Nat → neut
  | app : neut → term → neut
  | abs : neut → neut


inductive value where

end junk


#eval IO.FS.writeFile "/tmp/nbe.py" r#"print("hello world")"#


#eval IO.FS.readFile "/tmp/nbe.py"

#eval IO.Process.run {cmd := "python3", args := #["/tmp/nbe.py"]}


theorem foo2 : forall n : (BitVec 64), (n ||| n) = n := by
  intro n
  bv_decide
