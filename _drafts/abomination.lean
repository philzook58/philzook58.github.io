import Lean
--import _drafts.testy
#eval Lean.Expr.const `hello []

#eval Lean.Name.mkSimple "Hello"

--#eval Lean.Name.mk

-- https://github.com/mirefek/lean-tactic-programming-guide
-- https://web.stanford.edu/class/cs99/

partial def find (uf : Array Nat) (x : Nat) : Nat :=
if uf[x]! == x then x else find uf uf[x]!

--   if x >= uf.size then x else
def makeset (uf : Array Nat) : Array Nat :=
  uf.push uf.size

def empty : Array Nat :=
  Array.mkEmpty 0

def union (uf : Array Nat) (x y : Nat) : Array Nat :=
  let x' := find uf x
  let y' := find uf y
  if x' == y' then uf else
    uf.set! x' y'

#eval let uf := makeset empty
      let uf := makeset uf
      let uf := union uf 0 1
      find uf 2

example : forall x y : Nat, x + y = y + x := by grind


structure LEFind (a : Type) [BEq a] [Hashable a] where
  parents : Std.HashMap a a
  upper : Std.HashSet a


def foo (x : Nat) := Id.run do
  let mut acc := x
  while acc > 0 do
    acc := acc - 1
  return acc

#eval foo 10

partial def LEFind.find [BEq a] [Hashable a] (uf : LEFind a) (x : a) : a := x
  -- uf.parents[x]

def myfoo := 2 + 3


-- https://leanprover-community.github.io/mathlib4_docs/Init/Util.html#ptrEq
#eval ptrEq 5 myfoo
#eval ptrAddrUnsafe "foo"
#eval isExclusiveUnsafe "foo"
#eval dbgTrace "YOYO" (fun _ => 1 + 2)
#eval dbgStackTrace  (fun _ => 1 + 2)
-- do the union find analyses paper stufff




-- Do everything nasty. How do I get pointer equality in Lean?
-- I could probably always write C functions that do bad stuff and bind to them

/-

structure GroupoidUF R where
  parents : Std.HashMap w {v : R w v}

Over equivalence relation sure
But how can you talk about a groupoid? A fun dependent type problem maybe.

How do you make find obviously terminating?

https://leanprover-community.github.io/mathlib4_docs/Batteries/Data/UnionFind/Basic.html
https://leanprover-community.github.io/mathlib4_docs/Aesop/Util/UnionFind.html



Embed a prolog in Lean?
DSL stuff.

Call lua from lean? Attach to different libraries


Do a lean interpreter of pcode.


Can I housefly inside of lean?
A command to pretty print something as C / verilog


https://github.com/tydeu/lean4-alloy


bind arb in?


-/

-- LEAN_EXPORTING is at least one way to make C compiler make symbols global.

def compile_C (code : String) : IO Unit := do
  IO.FS.writeFile "/tmp/leany.c" code
  let stdout <- IO.Process.run {
    cmd := "leanc",
    args := #["-c", "-D", "LEAN_EXPORTING","-fPIC", "-o", "/tmp/leany.o", "/tmp/leany.c"],
  }
  IO.println stdout
  let stdout2 <- IO.Process.run {
    cmd := "leanc",
    args := #["-shared", "-o", "/tmp/leany.so", "/tmp/leany.o"],
  }
  --let dylib <- Lean.Dynlib.load "/tmp/leany.so"
  Lean.loadDynlib "/tmp/leany.so" -- This will load the shared library


-- https://proofassistants.stackexchange.com/questions/4801/how-to-eval-a-ffi-function-in-vscode-in-lean-4
#eval compile_C r#"
#include <stdint.h>
#include <lean/lean.h>
LEAN_EXPORT uint64_t myadd(uint64_t a, uint64_t b) {
return a + b;
}


LEAN_EXPORT lean_object* l_myadd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
//return x_1 + x_2;
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6;
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = myadd(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}


"#

/-
So I can either do it in a separate file.
Seems like supportInterpter was used
Or I need boxed version stub


-/


@[extern "myadd"]
opaque myadd (a b : UInt64) : UInt64

#eval myadd 5 7


-- https://github.com/leanprover/lean4/blob/master/src/lake/examples/precompile/foo/Foo/Hello.lean
@[export hello]
def helloImpl (_ : Unit) := "precompiled world"

@[extern "hello"]
opaque getHello : Unit → String

def hello := getHello ()
#eval hello

#eval do
  let selfmap <- IO.FS.readFile "/proc/self/maps"
  return (selfmap.splitOn "leany")[1]?
  -- grep for "leany.so"
  --return selfmap.splitOn "\n" |>.find? (fun line => String. lean")

#eval do
  let stats <- IO.FS.readFile "/proc/self/stat"
  return stats


#eval ptrAddrUnsafe myadd

--val do
--    let lib <- Lean.Dynlib.load "/tmp/leany.so"
--   Lean.Dynlib.get? lib "l_myadd"


-- https://leanprover-community.github.io/mathlib4_docs/Lean/Compiler/ExternAttr.html#Lean.externAttr
--@[extern cpp inline "#1 + #2"]
--def foo (a b : Int) : Int

def mypow n x :=
  if n == 0 then `1
  else `($x * )
