---
title: "Doing Lean Dirty: Lean as a Jupyter Notebook Replacement"
date: 2025-07-03
---

```lean
import Lean
import Std.Data.HashMap
import Std.Data.HashSet
```

I'm intrigued at replacing my usage of Jupyter notebooks with Lean.

Harry Goldstein has a nice talk about how Lean is a great live coding environment
<https://www.youtube.com/watch?v=c5LOYzZx-0c&t=1s> To some degree this is the grungier version of that.

I was also at PLDI a couple weeks ago where I was exposed to the onslaught of
Leo de Moura's Lean propaganda talk (I also sat next to him at dinner, which was a trip. I kept it cool 😎 ).
It feels like Lean is eating the world.
I have learned and forgotten Lean a few times at this point, but maybe it's time to reassess.

The community (and hence the reading material) is focussed on mathematics and verification. Doing things right.
Being strongly typed.
I do believe being hardcore about this is counter productive to live coding jazz.

But Lean seems completely capable of being used in a dirty way if you start digging
for all the error throwing unsafe hatches you can find.

In this post I'll discuss using bash from lean, writing files, calling python, and doing FFI and unsafe things.
This is the stuff I need to replace my Jupyter notebook needs.

## Preliminaries

Some comments about my unusual workflows.

I use Jupyter notebooks in a polyglot way. I was off them for a long time,
but came back around. They give a nice out of the box experience for live
explorative coding.

I really dislike creating new folders or even files in my drafts working directory.
I consider it to be a speedbump and it is a bummer that so many many ecosystems
and tools require you to write files or init projects to use them.

A lesser known Jupyter feature I consider crucial is the `%%file` magic command.
<https://ipython.readthedocs.io/en/9.0.2/interactive/magics.html#cellmagic-writefile>
I use it to dump right into named files in my `/tmp/` folder which is cleaned up periodically
by the OS. The "nicer" thing to do might be to generate names using things like
`mktemp` or python `tempfile` module, but it just gives overhead for little benefit when
screwing around.

This lets me make a single notebook that can contain everything needed to try a thing.
I can do low level C stuff and objdump and so on in a nice self contained things with commentary.
It is also useful for blogging, where I can `jupyter nbconvert --to markdown` and
know it has everything you need.

I setup a top level lakefile.toml in my blog directory. <https://github.com/philzook58/philzook58.github.io/blob/master/lakefile.toml>
 Lean really likes to be have a fresh VS code window opened at the project level. If you try to open a file not in such a project,
 I've had weird problems

`#eval` is the analog of a Jupyter cell. You should treat it more like a live updating
like Pluto or marimo. Be aware that even stateful commands will be rerun often every time you
edit your file (even before save). So make sure it's ok to rerun these commands.

The main reason I'm using namespaces is so that I can hierarchically navigate my file
in VS code using the outline panel.

# Bash

```lean
namespace Bash
```

Yeah, you can just execute bash commands in #eval.
This is the analog of `!` or `%%bash` in a jupyter notebook.

The extra Unit argument is to allow you to turn the command off.
I suppose you could also just comment the command out.
It also prevents it from running a half complete command while you're still writing it.

Some mistake +- copilot could delete your hard drive, so use caution.

```lean
def bash (cmd : String) (_ : Unit) : IO Unit := do
  let output <- IO.Process.output {
    cmd := "bash",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr


#eval bash "echo 'Hello from Bash!'" ()

end Bash
open Bash
```

# Writing Files

```lean
namespace WritingFiles
```

The analog of `%%file` in a jupyter notebook is `IO.FS.writeFile`.
Really this is more the analog of open(myfile, "w") in python.

```lean
#eval IO.FS.writeFile "/tmp/test.txt" "Hello from Lean!\n"
#eval bash "cat /tmp/test.txt" ()


end WritingFiles
```

# Python Analogs

```lean
namespace Python
```

We can call python as an external process.
Could have rewritten this using `IO.Process.run` but `bash` works too.
Running code in interpolated strings is nasty.

The r#" syntax lets you write raw strings
<https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/#raw-string-literals>
Which is nice when your code has quotes in it.

```lean
def python (code : String) (_ : Unit) : IO Unit := do
  IO.FS.writeFile "/tmp/temp.py" code -- I did have -c but had bad problems with "
  bash s!"source /home/philip/philzook58.github.io/.venv/bin/activate && python3 /tmp/temp.py" ()

#eval python r#"

print('Hello from Python!')
def fib(n):
    if n <= 1:
        return n
    else:
        return fib(n-1) + fib(n-2)

print(fib(10))
"# ()
```

You can also use this to do things like plotting.
Being able to just splice garbage into python code gives you a quick little way
to access the ecosystem for simple tasks.

Lean has it's own plotting story of course <https://github.com/leanprover-community/ProofWidgets4/blob/main/ProofWidgets/Demos/Plot.lean> ,
but I have found using Lean libraries to be
a total pain in the ass (sorry). Or maybe I just haven't figured out the way to not fight it?
Getting a consistent set of packages takes a lot of upkeep and it doesn't
seem to let you YOLO it the way python does.

```lean
def plot (data : List Float) (_ : Unit) : IO Unit := do
  let code := s!"import matplotlib.pyplot as plt; plt.plot({data}); plt.show()"
  python code ()

-- Will pop up a matplotlib window
#eval plot [1.0, 2.0, 3.0, 4.0, 5.0] -- ()

-- You could also bash some gnuplot if that is your thing.


end Python
open Python


namespace DirtyCode
```

How to use lean like python.

I took a look at two python tutorials to see some stuff to consider

- <https://docs.python.org/3/tutorial/controlflow.html>
- <https://learnxinyminutes.com/python/>

```lean
#eval python r#"
x = 17
if x < 0:
    x = 0
    print('Negative changed to zero')
elif x == 0:
    print('Zero')
elif x == 1:
    print('Single')
else:
    print('More')
"# ()

def checkneg (x : Nat) : IO Unit := do
  if x < 0 then
    IO.println "Negative changed to zero"
  else if x == 0 then
    IO.println "Zero"
  else if x == 1 then
    IO.println "Single"
  else
    IO.println "More"
#eval checkneg 17

#eval python r#"
# Measure some strings:
words = ['cat', 'window', 'defenestrate']
for w in words:
    print(w, len(w))
"# ()

def words := ["cat", "window", "defenestrate"]
#eval do
  for w in words do
    IO.println s!"{w} {w.length}"
  return ()

#eval python r#"
for i in range(5):
    print(i)
"# ()

#eval do
  for i in [0:5] do
    IO.println s!"{i}"

#eval python r#"
for n in range(2, 10):
    for x in range(2, n):
        if n % x == 0:
            print(f\"{n} equals {x} * {n//x}\")
            break
"# ()

#eval do
  for n in [2:10] do
    for x in [2:n] do
      if n % x == 0 then
        IO.println s!"{n} equals {x} * {n / x}"
        break
```

# Unsafe Code

I love the dirty escape hatches and knowing about them makes a new innovative language easier to stomach.

If you're learning rust, just use `.clone()`, `Rc`, and `.unwrap()` everywhere.
This advice is not made so obvious because they want
to teach you the "right" way, the advantages and strengths of the systems. I guess you're digging yourself into
a technical debt hole and building bad habits. But in a live coding sketching situation, this stuff rules.

Likewise in Lean, `unsafe`, `partial`, and exclamation mark versions are your friends.

Panicking is a thing. You can use panics to avoid complete pattern matching,
force extraction out of options, lookup into arrays etc.

If you panic, I believe you need to use `unsafe` definitions. Go ahead.

```lean
unsafe def getit (x : Option Int) := x.get!
#eval getit (some 5)
#eval getit none -- panics
#eval #["larry", "joe", "curly"][10]! -- panics

#eval match "larry" with
  | "curly" => "Hello Larry"
  | _ => panic! "Not curly!" -- panics

-- unsafe Casting. Who knows what this is doing really. But fun to find out!
-- https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#unsafeCast
#eval ((unsafeCast (3 : UInt8))  : UInt16)
#eval ((unsafeCast (3120000000 : Int))  : UInt16)
#eval ((unsafeCast "Hello world") : UInt8)
#eval ((unsafeCast (none : Option Nat)) : Int) -- 0
```

Some other fun unsafe code.

- unsafeIO
- pointer equality and addresses
- dbgTrace

```lean
unsafe def foo : Nat :=
  match unsafeIO (IO.println "hello world") with -- need to actually force the exception to see message
  | .ok _ => 42
  | .error _ => panic! "Failed to print hello world"

#eval foo -- prints "hello world" and returns 42

def myfive := 5
-- https://leanprover-community.github.io/mathlib4_docs/Init/Util.html#ptrEq
#eval ptrEq 5 myfive -- true
#eval ptrAddrUnsafe "foo"
#eval isExclusiveUnsafe "foo"
#eval dbgTrace "YOYO" (fun _ => 1 + 2)
#eval dbgStackTrace  (fun _ => 1 + 2)
```

I don't want no termination checker complaining at me.
I want to mutate garbage

Here's a union find loop. I'm not guaranteeing the union find is well formed.
Hence this really could be an infinite loop

Better versions:
<https://leanprover-community.github.io/mathlib4_docs/Aesop/Util/UnionFind.html#Aesop.UnionFind>
<https://leanprover-community.github.io/mathlib4_docs/Batteries/Data/UnionFind/Basic.html#Batteries.UnionFind>

```lean
partial def find (uf : Array Nat) (x : Nat) : Nat := Id.run do
  let mut x := x
  while uf[x]! != x do
    x := uf![x]
  return x

#eval find #[0, 0, 1, 3, 4] 2
-- #eval find #[1, 0, 2, 3, 4] 0  -- doesn't return



end DirtyCode
```

# FFI

```lean
namespace DirtyFFI
```

We can really get into some dirtiness by doing some FFI stuff.

Here's a dumb assembly snippet that returns 42

```lean
#eval IO.FS.writeFile "/tmp/fortytwo.s" r#"
.global myforty
myforty:
movq $42, %rax
ret
"#
```

I can compile and dynamically link this into python as callable.

This is an interesting way to do interactive nanopass compiler development.

```lean
#eval bash "gcc -c -o /tmp/fortytwo.o /tmp/fortytwo.s" ()
#eval bash "gcc -shared -o /tmp/fortytwo.so /tmp/fortytwo.o" ()

#eval python r#"
import cffi
ffi = cffi.FFI()
ffi.cdef("uint64_t myforty();")
lib = ffi.dlopen("/tmp/fortytwo.so")
print(lib.myforty())
"# ()
```

Here is doing something similar in lean.
A difficult is that if you are in the interpreter, it seems you have to
make a __boxed wrapper function.
Lean itself makes this when you compile an @[extern] in a separate file.

`leanc` is a verion of clang shipped with lean. It has baked in the right paths to know where all the lean stuff is.

`lean` is the actual lean executable. You can also run scripts with `--run` and a `main` function.
`-c` outputs C code which is worth checking out. It's fairly straightforward
`--print-libdirs` and `--print-prefix` can show you where to find lean libraries and headers.
`leanshared` is the lean standard library and runtime and other junk precompiled as a shared lib. It's kind of a one stop shop.
There is also `Init_shared.so` which is worth checking out.

Using `cffi` on the python side isn't classy, but I like it. I've never figured out how to use the "oout of line" mode.
Having a build step in python is the worst. Shipping libraries in general is the worst.

```lean
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/FFI.20dynamic.20linking/near/527017847
-- LEAN_EXPORTING is at least one way to make symbols global.
def compile_C (code : String) : IO Unit := do
  IO.FS.writeFile "/tmp/leany.c" code
  bash "leanc -c -DLEAN_EXPORTING -fPIC -o /tmp/leany.o /tmp/leany.c" ()
  bash "leanc -shared -o /tmp/leany.so /tmp/leany.o" ()
  Lean.loadDynlib "/tmp/leany.so" -- This will load the shared library

-- https://proofassistants.stackexchange.com/questions/4801/how-to-eval-a-ffi-function-in-vscode-in-lean-4
#eval compile_C r#"
#include <stdint.h>
#include <lean/lean.h>
LEAN_EXPORT uint64_t myadd(uint64_t a, uint64_t b) {
return a + b;
}

LEAN_EXPORT lean_object* l_DirtyFFI_myadd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
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

@[extern "myadd"]
opaque myadd (a b : UInt64) : UInt64

#eval myadd 5 7 -- returns 12

end DirtyFFI



namespace Leanception
```

Here I export a function from Lean to C, compile it into a shared library.
Then I import it inside of a python module called from inside of lean.

<https://lean-lang.org/doc/reference/4.21.0/Run-Time-Code/Foreign-Function-Interface/>

Backing out how to do this was some work as everything is hidden inside of Lake.

```lean
#eval IO.FS.writeFile "/tmp/myadd.lean" r#"
@[export myadd]
def myadd (a b : UInt64) : UInt64 :=
  a + b
"#

#eval bash "cd /tmp && lean -c /tmp/myadd.c /tmp/myadd.lean" ()
#eval bash "cd /tmp && leanc -o /tmp/myadd.o -c /tmp/myadd.c -DLEAN_EXPORTING" ()
#eval bash "cd /tmp && leanc -shared -o /tmp/myadd.so /tmp/myadd.o -lleanshared_1 -lleanshared -Wl,-rpath=$(lean --print-libdir)" ()

#eval python r#"
import cffi
ffi = cffi.FFI()
ffi.cdef("void lean_initialize_runtime_module();")
ffi.cdef("uint64_t myadd(uint64_t a, uint64_t b);")
lib = ffi.dlopen("/tmp/myadd.so")
lib.lean_initialize_runtime_module()
print(lib.myadd(5, 7))
"# ()



end Leanception
```

# Making the Blog Post

I'm using mdgen <https://github.com/Seasawher/mdgen> to convert a file into markdown.
This inverts the comments and puts the lean code in code blocks.

```bash
 lake exe mdgen pynb/leantmp/ _posts/
```

# Bits and Bobbles

Ultimately, I think the experience is a little clunkier than using Jupyter. Debugging some of that FFI stuff required me to
go back into a Jupyter notebooks.

I am not sure if I can replace python+Jupyter with Lean as it stands, although I'd like to. There's just a bit too much friction where I want no friction.
This is partially unfair. I've spent a lot of time ending up and getting used to the workflow I've got.

One can also use lake into the temporary directory. That might be a better replacement for my raw usage of the lean command line programs

```lean
section BitsAndBobbles
```

Replacements for `jupyter nbconvert`

- Verso
- Lean2Md <https://github.com/arthurpaulino/lean2md>
- mdgen <https://github.com/Seasawher/mdgen>
- Just copy everything into a code block
- <https://github.com/gleachkr/lean.lua> Graham has a pandoc converter

I don't like that I don't automatically see the lean output in my markdown.
Verso seems too fancy for me.
Just putting it in a code block has bad behavior with respect o

I feel a little about Lean the same way I feel about AI.
They are seemingly unstoppable juggernauts whose expressed purpose is
to make me irrelevant and throw me out on the streets.
The FOMO on both is nearly overwhelming.

On the other hand, this view is kind of ridiculous.

Despite being a juggernaut brand name in my bubble, Lean is the underdog more widely.
The developers of Lean are at war with the world, fighting for every scrap they can
get from under the paws of more established languages.

A problem I have with doing things in Lean is that there are too
many smart people already doing seemingly everything there. I'd be lesser drop in the
bucket.

It's important for me at least to try and have an angle.

So here's my angle today: Use lean like a caveman dumbass. If I can't be smarter
maybe I can at least be more obstinate.

# My Workflow

People are a little surprised and aghast that I use Jupyter notebooks in VS Code for
my ideas and blogging.

Shouldn't an aspiring "Real Programmer" know that Jupyter is shit?

The thing is, my ideation process is pure chaos, as evidenced by my "Bits and Bobbles"
sections. There is a lot of half code, copy and pasting.

While I've been facile at python for a decade now, trying to develop a library <https://github.com/philzook58/knuckledragger>
has
taken me to more corners of the language and I've actually been learning a lot.
I do feel recently that I've hit somewhat of a wall.

I also have been in a slightly previous life a staunchly devout functional programmer,
completely in love with Haskell, OCaml, Coq, Agda, Idris etc, preaching about type safety,
playing typelevel metaprogramming games, etc.

I think that these systems are harder to make sketches in.
A point of different languages is that they change how you think.

A similar phenomenon occurs in paper and pencil math vs formalization.
In an even further life ago, I was an aspiring theoretical physicist. I spent years producing
boxes of Calculations and ideations on paper, mushing around
functional integrals in a half dream state. Minus the crushing weight of
my decreasing future career prospects, it was very fun.

Paper and pencil and the computer keyboard make your mind work differently.
Trying to be hyper rigorous vs trying to be maximally novel (from a physicists perspective)
are also very different states of mind with different purposes.
It's actually OK for physical theory to be logically and mathematically inconsistent.
Give 'em 200 years to meditate on what experiment has already shown to be the right answer
and they'll find a way to straighten the math and concepts out. Look at nonstandard analysis for example.
Look at renormalization.

We make discoveries and then we solidify and polish them. The polish can in turn
lead to new discoveries. That's the method.

```lean
#eval Lean.loadDynlib "/tmp/fortytwo.so"

@[extern "myforty"]
opaque myforty (_ : Unit) : UInt64

#eval myforty () -- returns 42


--open Bash

--import _drafts.testy
```

Sadly lean does not have baked in set comprehension / dictionary comprehensions, so far
as I can tell.
You could easily add such a thing using the flexible macro system.
I completely refuse to do so.
I think macros are a noose to hang yourself with and make your code less readable to others.
I completely despise being subjected to other's macros even if I like my own.
So to use them for trivial sugar purposes would be hypocrisy.
I'm not going to maintain some macro library and I'm not going to copy and paste
the macro into my file everything time I want a dictionary.
All that to say it's a different case if it is a standard macro in the standard lib.

```lean
open Std
#eval python r#"
print({1: 'one', 2: 'two', 3: 'three', 4: 'four'})
"# ()


#eval HashMap.ofList [(1, "one"), (2, "two"), (3, "three"), (4, "four")]




-- How does try catch work? I can't find a reference anywhere
#eval do
  try
    pure 10
  catch e =>
    pure 0

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



-- do the union find analyses paper stufff




-- Do everything nasty. How do I get pointer equality in Lean?
-- I could probably always write C functions that do bad stuff and bind to them
```

structure GroupoidUF R where
  parents : Std.HashMap w {v : R w v}

Over equivalence relation sure
But how can you talk about a groupoid? A fun dependent type problem maybe.

How do you make find obviously terminating?

<https://leanprover-community.github.io/mathlib4_docs/Batteries/Data/UnionFind/Basic.html>
<https://leanprover-community.github.io/mathlib4_docs/Aesop/Util/UnionFind.html>

Embed a prolog in Lean?
DSL stuff.

Call lua from lean? Attach to different libraries

Do a lean interpreter of pcode.

Can I housefly inside of lean?
A command to pretty print something as C / verilog

<https://github.com/tydeu/lean4-alloy>

bind arb in?

```lean
def bash (cmd : String) (_ : Unit) : IO Unit := do
  let output <- IO.Process.output {
    cmd := "bash",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr

-- LEAN_EXPORTING is at least one way to make symbols global.
def compile_C (code : String) : IO Unit := do
  IO.FS.writeFile "/tmp/leany.c" code
  bash "leanc -c -DLEAN_EXPORTING -fPIC -o /tmp/leany.o /tmp/leany.c" ()
  bash "leanc -shared -o /tmp/leany.so /tmp/leany.o" ()
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

-- I guess I could generate the C binder code
-- IO.writefile "/tmp/lean.lean"
-- bash "lean -c /tmp/leany.c /tmp/lean.lean"

@[extern "myadd"]
opaque myadd (a b : UInt64) : UInt64

#eval myadd 5 7
```

let out <- IO.Process.output {
  cmd := "leanc",
  args := #["-c", "-D", "LEAN_EXPORTING","-fPIC", "-o", "/tmp/leany.o", "/tmp/leany.c"],
}
IO.println out.stdout
IO.println out.stderr
let out2 <- IO.Process.output {
  cmd := "leanc",
  args := #["-shared", "-o", "/tmp/leany.so", "/tmp/leany.o"],
}
IO.println out2.stdout
IO.println out2.stderr
--let dylib <- Lean.Dynlib.load "/tmp/leany.so"

So I can either do it in a separate file.
Seems like supportInterpter was used
Or I need boxed version stub

```lean
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


-- show drawing diagrams
-- gnuplot
-- bash

def bash (cmd : String) (_ : Unit) : IO Unit := do
  let output <- IO.Process.output {
    cmd := "bash",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr

#eval IO.FS.writeFile "/tmp/circle.svg" r#"
<svg xmlns="http://www.w3.org/2000/svg" width="100" height="100">
  <circle cx="50" cy="50" r="40" stroke="black" stroke-width="2"
   fill="blue" />
    </svg>"#

-- I don't know how to use gnuplot
```

# eval IO.Process.run {

  cmd := "gnuplot",
}

```lean
#eval bash "code /tmp/circle.svg"


def python (cmd : String) (_ : Unit) : IO Unit := do
  let output <- IO.Process.output {
    cmd := "python3",
    args := #["-c", cmd],
  }
  IO.println output.stdout
  IO.println output.stderr

#eval python "print('Hello from Python!')" ()

#eval python s!"
import matplotlib.pyplot as plt
import numpy as np
plt.plot({[1,7,9]})
plt.show()
"

-- packaging it up more nicely
def plot [ToString a] (data : List a) (_ : Unit) : IO Unit := do
  python s!"import matplotlib.pyplot as plt; plt.plot({data}); plt.show()" ()

#eval plot [1, 2, 3, 4, 19]

#eval List.range 20 |>.map (Float.cos ∘ Float.ofNat)

-- Array.tabulate

def linspace (start : Float) (stop : Float) (num : Nat) : Array Float :=
  let step := (stop - start) / Float.ofNat num
  (Array.range (num + 1)).map (fun k => start + step * Float.ofNat k)
#eval linspace 0 10 100 |>.map Float.cos


-- unsafeBaseIO
-- dbgTrace
-- panic!

#eval (panic! "Something went wrong!" : Int)

-- withPtrEq What is this?


-- Lean as a jupyter notebook




-- ooh sorry lean doesn't have operator chaining? Not a modern language like python
#eval 1 < 2 && 2 < 3
-- #eval 1 < 2 < 3
-- of course you could macro it in


-- type and isinstance. Hmm.
-- https://leanprover-community.github.io/mathlib4_docs/Init/Dynamic.html#TypeName


-- This is some haskelly stuff.
-- https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Dynamic.html

unsafe instance : TypeName Nat := TypeName.mk Nat `Nat
-- #eval TypeName.mk Int `Int
-- #eval TypeName.typeName Int
#eval Dynamic.mk 3 |>.get? Nat

structure Foo where
deriving TypeName, Repr

#eval TypeName.typeName Foo
#eval Dynamic.mk Foo.mk |>.get? Foo

-- But is this really isinstance?
-- We'd want a hiearchy of
-- class InstanceOf T T

-- Maybe a better match is coercions
-- https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html#CoeT.mk
```

x = int(input("Please enter an integer: "))
Please enter an integer: 42
if x < 0:
    x = 0
    print('Negative changed to zero')
elif x == 0:
    print('Zero')
elif x == 1:
    print('Single')
else:
    print('More')

Use macros to put full python syntax sugar?
But really what is even left?

```lean
def checkneg (x : Nat) : IO Unit := do
  if x < 0 then
    IO.println "Negative changed to zero"
  else if x == 0 then
    IO.println "Zero"
  else if x == 1 then
    IO.println "Single"
  else
    IO.println "More"
#eval checkneg 42
```

for n in range(2, 10):
    for x in range(2, n):
        if n % x == 0:
            print(n, 'equals', x, '*', n//x)
            break
    else:
        # loop fell through without finding a factor
        print(n, 'is a prime number')

```lean
#eval
for n in [2:10] do
  let mut found := false
  for x in [2:n] do
    if n % x == 0 then
      IO.println s!"{n} equals {x} * {n / x}"
      found := true
      break
  if !found then
    -- loop fell through without finding a factor
    IO.println s!"{n} is a prime number"
```

else
    -- loop fell through without finding a factor
    IO.println s!"{n} is a prime number"

pairs = [(1, 'one'), (2, 'two'), (3, 'three'), (4, 'four')]
pairs.sort(key=lambda pair: pair[1])

```lean
def pairs := [(1, "one"), (2, "two"), (3, "three"), (4, "four")]

-- #eval pairs.sort (fun a b => a.2 < b.2)



-- https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Lean.trustCompiler
```
