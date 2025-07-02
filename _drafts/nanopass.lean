/-
Idea. Do Siek book.
Or nanpass paper?


-/

inductive aexpr where
  | const : BitVec 64 → aexpr
  | add : aexpr → aexpr → aexpr

--#html "Hello world"

def prog1 := r#"
.global myforty
myforty:
mov 42, %rax
ret
"#


def bash (cmd : String) (_ : Unit) : IO Unit := do
  let output ← IO.Process.output {
    cmd := "bash",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr

#eval do
  IO.FS.writeFile "/tmp/myforty.s" prog1
  bash "gcc -c -o /tmp/myforty.o /tmp/myforty.s" ()
  bash "gcc -shared -o /tmp/myforty.so /tmp/myforty.o" ()
  bash "objdump -t /tmp/myforty.so" ()
