---
title: "Semi-Automated Assembly Verification in Python using pypcode Semantics"
date: 2025-07-21
---

I've worked on binary verification tooling for a while.

In our projects, we've often been working on just binary garbage thrown out of a compiler or being reverse engineered or butchered in some other way. A strange lesson is that it is pretty tough to even know what "good" or "correct" should mean in absence of higher levels of source.

An idea that I've liked is adding inline verification annotations into textual assembly somewhat similarly to how they feel in [Dafny](https://dafny.org/) or [Frama-C](https://www.frama-c.com/). This is the more cooperative version of the problem. There is a possible universe in which compilers output this sort of assumption/verification information either textually or dumped into binary metadata <https://www.philipzucker.com/dwarf-patching/> . This would aid translation validation and binary verification immensely in terms of have a goal to verify against.

Some design constraints:

- I strongly prefer that the file has to remain assemblable by the regular binutils toolchain.
- An esoteric ecosystem is kind of a non starter if I want anyone to be using it. Another painful lesson. The intersection of people interested in low level things and Ocaml/Lean/Coq interested is non-zero, but every constraint you put on your audience cuts it down significantly. Because of this, I've been leaning into more Python as a user facing language. It _is_ the most popular language in the world. It _is_ pretty easy / already installed on your system.

[Pypcode](https://github.com/angr/pypcode) is a well packaged version of the binary lifters for the [ghidra](https://github.com/NationalSecurityAgency/ghidra) decompiler and can supply a unified semantics for many architectures. It's stable, well-maintained and funded (NSA). This is a pretty rare combo. I think the programming language and verification community are sleeping on this resource.

I've attacked the problem in various ways before. This is yet another related angle.

- <https://www.philipzucker.com/knuckle_C_pcode/> here I discussed a bit writing my symbolic pcode emulator based on the [official version](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc). The actual code is here <https://github.com/philzook58/knuckledragger/blob/main/kdrag/contrib/pcode/__init__.py> I'm using this sane symbolic executor today. The main difference between this and angr is that I don't partially concretize memory, which is a bit more complete. I tried to use angr quite a bit. Couldn't see how to achieve this (claripy seemingly doesn't even support the theory of arrays). I do however leverage angr's loader ecosystem CLE <https://github.com/angr/cle> and pypcode itself is maintained by the angr team. I do also keep coming back to their design when I wonder how to make an interface to get something or other from the user. They thought it through in many ways.
- <https://www.philipzucker.com/pcode2c-dwarf/> another approach using pypcode to specialize an interpreter to C code so that you can compare to other C code via CBMC. Still an interesting approach for translation validation

## Assembly Annotations

An easy way to make sure the file remains assembleable is to use macros that expand to mostly nothing when assembled, but that I can grep for to find the important metadata.

A more heavy-handed way to go about it might be to build an entire assembly parser, but this is going to suck and not be as portable across architecture or assembler.

The basic things I need to know are

1. Where to start my symbolic executor `kd_entry`
2. Where to stop my symbolic executor `kd_exit`
3. Assertions `kd_assert`
4. `kd_cut` Is a way of thinking about loop invariants. It is a combo assertion and assumption. You have to give it a sufficiently strong summary of the state (invariant), that knowing onl thaty fact about the state is sufficient to prove the things you want to know.
5. What to check after every assembly instruction execution `kd_always`. These are kind of system ubiquitous invariants such as what I may want for "memory is always untouched" or interrupt invariants being satisfied

```python
%%file /tmp/knuckle.s

#precondition
.macro kd_entry label smt_expr
\label :
.endm

.macro kd_assert label smt_expr
\label :
.endm

.macro kd_assume label smt_expr
\label :
.endm

#postcondition
.macro kd_exit label smt_expr 
\label :
.endm

#invariant
.macro kd_cut label smt_expr
\label :
.endm 

.macro kd_always smt_expr
.endm

```

    Overwriting /tmp/knuckle.s

Something that I still think was a good minimally opinionated design choice in CBAT <https://draperlaboratory.github.io/cbat_tools/tutorial.html> <https://www.ndss-symposium.org/wp-content/uploads/bar2024-9-paper.pdf> was to use SMTLib as our specification language. It is a weak and somewhat clunky logic, but it gives you direct access to the solver and you can parse it with no extra work. There are resources out there on using the language.

If you prefer to programmatically generate your specifications, that is still possible via the many widely available smt libraries in different languages. I particular, I've used z3 to construct smtlib expression, which it can dump into a syntactic string.

Here's a toy example of moving `42` into `RAX`. The register names are automatically going to be mapped into pypcode's names <https://api.angr.io/projects/pypcode/en/latest/api.html#pypcode.Context.getAllRegisters>

```python
%%file /tmp/myfunc.s

.include "/tmp/knuckle.s"
.globl myfunc

.text
    kd_entry myfunc "(assert true)"
    movq $42, %rax
    kd_assert my_assert "(assert (= RAX (_ bv42 64)))"
    kd_exit func_end "(assert (= RAX (_ bv42 64)))"
    ret
```

    Overwriting /tmp/myfunc.s

It assembles normally

```python
! as /tmp/myfunc.s -o /tmp/myfunc.o 
```

We can link it into another program and run it

```python
%%file /tmp/test.c
#include <stdio.h>
#include <stdint.h>
uint64_t myfunc();
int main(){
    printf("Result : %ld\n", myfunc());
    return 0;
}

```

    Overwriting /tmp/test.c

```python
! gcc -Wall /tmp/test.c /tmp/myfunc.o -o /tmp/test.out && /tmp/test.out
```

    /usr/bin/ld: warning: /tmp/myfunc.o: missing .note.GNU-stack section implies executable stack
    /usr/bin/ld: NOTE: This behaviour is deprecated and will be removed in a future version of the linker
    Result : 42

# Verification

Now we are going to mildly parse for the appropriate directive lines.

```python
from dataclasses import dataclass, field, asdict
import re
from kdrag.all import *
import kdrag.contrib.pcode as pcode
from collections import defaultdict
import json
# mapping from address to list of (label, expr)
type AddrMap = defaultdict[int, list[tuple[str, smt.BoolRef]]]
@dataclass
class AsmSpec():
    entries : AddrMap = field(default_factory=lambda: defaultdict(list))
    asserts: AddrMap = field(default_factory=lambda: defaultdict(list))
    assumes: AddrMap = field(default_factory=lambda: defaultdict(list))
    exits: AddrMap = field(default_factory=lambda: defaultdict(list))
    cuts: AddrMap = field(default_factory=lambda: defaultdict(list))

    @classmethod
    def of_file(cls, filename : str, ctx : pcode.BinaryContext):
        #pattern = re.compile(r'^\s*(kd_assert|kd_assume|kd_exit|kd_entry|kd_cut)\s+(\w+)\s+"([^"]+)"\s*$')
        pattern = re.compile(
            r'''^\s*
                (kd_assert|kd_assume|kd_exit|kd_entry|kd_cut)
                \s+([A-Za-z_.$][A-Za-z0-9_.$]*) # valid GAS label
                \s*(?:,\s*)?                         # optional comma
                "([^"]+)"                        # quoted formula
                \s*$''',
            re.VERBOSE
        )
        spec = cls()
        with open(filename) as f:
            for line in f.readlines():
                match = pattern.match(line)
                if match:
                    cmd, label, expr = match.groups()
                    addr = ctx.loader.find_symbol(label).rebased_addr
                    expr = smt.parse_smt2_string(expr, decls=ctx.decls)[0]
                    if cmd == 'kd_entry':
                        spec.entries[addr].append((label, expr))
                    elif cmd == 'kd_assert':
                        spec.asserts[addr].append((label, expr))
                    elif cmd == 'kd_assume':
                        spec.assumes[addr].append((label, expr))
                    elif cmd == 'kd_exit':
                        spec.exits[addr].append((label, expr))
                    elif cmd == 'kd_cut':
                        spec.cuts[addr].append((label, expr))
        return spec

    def __repr__(self):
        return json.dumps(asdict(self), indent=2, default=lambda b: b.sexpr())



ctx = pcode.BinaryContext("/tmp/myfunc.o")
spec = AsmSpec.of_file('/tmp/myfunc.s', ctx) 
spec           
```

    {
      "entries": {
        "4194304": [
          [
            "myfunc",
            "true"
          ]
        ]
      },
      "asserts": {
        "4194311": [
          [
            "my_assert",
            "(= RAX #x000000000000002a)"
          ]
        ]
      },
      "assumes": {},
      "exits": {
        "4194311": [
          [
            "func_end",
            "(= RAX #x000000000000002a)"
          ]
        ]
      },
      "cuts": {}
    }

The core verification procedure runs all paths through the program. We can try to be smarter later, but this is good enough for now. By including the notion of cuts, tehre are only a finite number of paths through a cut control flow graph. We do not have the trust another CFG reconstructor since we discover the CFG as we execute.

We seed the execution with the entry points.

We look up in the spec if the current address has an assertion or assumption attached to it. If so we try to discharge it.

Anything that hits an annotated exit kills that path.

If there is an uncut loop or unannotated exit, the thing will run forever and not complete. Either you need to add an annotation or I could set a bounded instruction mode.

```python
def run_all_paths(ctx, spec : AsmSpec, mem=None, verbose=True):
    if mem is None:
        mem = pcode.MemState.Const("mem")
    todo = []
    if len(spec.entries) == 0:
        raise Exception("No entry points found in the assembly specification")
    for addr, label_preconds in spec.entries.items():
        for label, precond in label_preconds:
            if verbose:
                print(f"entry {label} at {addr} with precond {precond}")
            todo.append(pcode.SimState(mem, (addr, 0), [ctx.substitute(mem, precond)]))
    def verif(state, prop):
        return kd.prove(smt.Implies(smt.And(*state.path_cond), ctx.substitute(state.memstate, prop)))
    while todo:
        state = todo.pop()
        addr, pc = state.pc
        if pc != 0: # We don't support intra instruction assertions
            raise Exception(f"Unexpected program counter {pc} at address {hex(addr)}") 
        if addr in spec.cuts:
            raise Exception("Cut not implemented yet")
        if addr in spec.asserts:
            for (label, _assert) in spec.asserts[addr]:
                try:
                    pf = verif(state, _assert)
                    print(f"[✅] assert {label}: {_assert}")
                except Exception as e:
                    print("[❌] Error proving assert", label, _assert, e)
                # maybe prove form (state == current state => assert_expr)
        if addr in spec.exits:
            for label, _exit in spec.exits[addr]:
                try:
                    pf = verif(state, _exit)
                    print(f"[✅] exit {label}: {_exit}")
                except Exception as e:
                    print("[❌] Error proving exit", label, _exit,  e)
            continue # Do not put back on todo
        if addr in spec.assumes:
            for label, _assume in spec.assumes[addr]:
                state._replace(path_cond=state.path_cond + [ctx.substitute(state.memstate, _assume)])
        # Regular execution
        todo.extend(ctx.sym_execute(state.memstate, addr, path_cond=state.path_cond, max_insns=1, verbose=verbose))

run_all_paths(ctx, spec)

```

    entry myfunc at 4194304 with precond True
    Executing 0x400000/7: MOV RAX,0x2a at (4194304, 0) PCODE IMARK ram[400000:7]
    Executing 0x400000/7: MOV RAX,0x2a at (4194304, 1) PCODE RAX = 0x2a
    [✅] assert my_assert: RAX == 42
    [✅] exit func_end: RAX == 42

We can put these pieces together into a single function

```python
import subprocess
def assemble_and_check(filename: str):
    subprocess.run(['as', filename, '-o', '/tmp/kdrag_temp.o'], check=True)
    ctx = pcode.BinaryContext("/tmp/kdrag_temp.o")
    spec = AsmSpec.of_file(filename, ctx)
    print(spec)
    run_all_paths(ctx, spec)
```

# More Examples

Again, these are pretty trivial, but they exposed a lot of surprising issues in my symbolic executor. Not confidence inducing.

```python
%%file /tmp/myfunc_bad.s

.include "/tmp/knuckle.s"
.globl myfunc

.text
    kd_entry myfunc "(assert true)"
    movq $42, %rax
    kd_assert my_assert "(assert (= RAX (_ bv43 64)))"
    kd_exit func_end "(assert (= RAX (_ bv43 64)))"
    ret
```

    Overwriting /tmp/myfunc_bad.s

```python
assemble_and_check('/tmp/myfunc_bad.s')
```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('myfunc', True)]}), asserts=defaultdict(<class 'list'>, {4194311: [('my_assert', RAX == 43)]}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194311: [('func_end', RAX == 43)]}), cuts=defaultdict(<class 'list'>, {}))
    entry myfunc at 4194304 with precond True
    Executing 0x400000/7: MOV RAX,0x2a at (4194304, 0) PCODE IMARK ram[400000:7]
    Executing 0x400000/7: MOV RAX,0x2a at (4194304, 1) PCODE RAX = 0x2a
    [❌] Error proving assert my_assert RAX == 43 (Implies(And(True), 42 == 43), 'Countermodel', [])
    [❌] Error proving exit func_end RAX == 43 (Implies(And(True), 42 == 43), 'Countermodel', [])

```python
%%file /tmp/raxrdi.s
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "(assert true)"
    movq     %rdi, %rax
kd_exit _start_end "(assert (= RAX RDI))"
    ret
```

    Overwriting /tmp/raxrdi.s

```python
assemble_and_check('/tmp/raxrdi.s')
#ctx = pcode.BinaryContext("/tmp/kdrag_temp.o")
#AsmSpec.of_file('/tmp/raxrdi.s', ctx)
```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('_start', True)]}), asserts=defaultdict(<class 'list'>, {}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194307: [('_start_end', RAX == RDI)]}), cuts=defaultdict(<class 'list'>, {}))
    entry _start at 4194304 with precond True
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 0) PCODE IMARK ram[400000:3]
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 1) PCODE RAX = RDI
    [✅] exit _start_end: RAX == RDI

```python
%%file /tmp/inc_rdi.s
.include "/tmp/knuckle.s"
.globl  _start
kd_entry _start "(assert true)"
    lea    1(%rdi), %rax
kd_exit _start_end "(assert (= RAX (bvadd RDI (_ bv1 64))))"
    ret
```

    Overwriting /tmp/inc_rdi.s

```python
assemble_and_check('/tmp/inc_rdi.s')
```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('_start', True)]}), asserts=defaultdict(<class 'list'>, {}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194308: [('_start_end', RAX == RDI + 1)]}), cuts=defaultdict(<class 'list'>, {}))
    entry _start at 4194304 with precond True
    Executing 0x400000/4: LEA RAX,[RDI + 0x1] at (4194304, 0) PCODE IMARK ram[400000:4]
    Executing 0x400000/4: LEA RAX,[RDI + 0x1] at (4194304, 1) PCODE unique[4700:8] = RDI + 0x1
    Executing 0x400000/4: LEA RAX,[RDI + 0x1] at (4194304, 2) PCODE RAX = unique[4700:8]
    [✅] exit _start_end: RAX == RDI + 1

```python
%%file /tmp/mymax.s
.include "/tmp/knuckle.s"
.globl  _start
kd_entry _start "(assert true)"
        movq     %rdi, %rax
        cmp     %rdi, %rsi
        cmovb   %rsi, %rax
kd_exit _start_end "(assert (= RAX (ite (bvult RDI RSI) RDI RSI)))"
#kd_exit _start_end "(assert (or (= RAX RDI) (= RAX RSI)))"
        ret
```

    Overwriting /tmp/mymax.s

```python
assemble_and_check('/tmp/mymax.s')
```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('_start', True)]}), asserts=defaultdict(<class 'list'>, {}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194314: [('_start_end', RAX == If(ULT(RDI, RSI), RDI, RSI))]}), cuts=defaultdict(<class 'list'>, {}))
    entry _start at 4194304 with precond True
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 0) PCODE IMARK ram[400000:3]
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 1) PCODE RAX = RDI
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 0) PCODE IMARK ram[400003:3]
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 1) PCODE unique[3af00:8] = RSI
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 2) PCODE CF = unique[3af00:8] < RDI
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 3) PCODE OF = sborrow(unique[3af00:8], RDI)
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 4) PCODE unique[3b000:8] = unique[3af00:8] - RDI
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 5) PCODE SF = unique[3b000:8] s< 0x0
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 6) PCODE ZF = unique[3b000:8] == 0x0
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 7) PCODE unique[28080:8] = unique[3b000:8] & 0xff
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 8) PCODE unique[28100:1] = popcount(unique[28080:8])
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 9) PCODE unique[28180:1] = unique[28100:1] & 0x1
    Executing 0x400003/3: CMP RSI,RDI at (4194307, 10) PCODE PF = unique[28180:1] == 0x0
    Executing 0x400006/4: CMOVC RAX,RSI at (4194310, 0) PCODE IMARK ram[400006:4]
    Executing 0x400006/4: CMOVC RAX,RSI at (4194310, 1) PCODE unique[39b00:8] = RSI
    Executing 0x400006/4: CMOVC RAX,RSI at (4194310, 2) PCODE unique[39b80:1] = !CF
    Executing 0x400006/4: CMOVC RAX,RSI at (4194310, 3) PCODE if (unique[39b80:1]) goto ram[40000a:8]
    Executing 0x400006/4: CMOVC RAX,RSI at (4194310, 4) PCODE RAX = unique[39b00:8]
    [✅] exit _start_end: RAX == If(ULT(RDI, RSI), RDI, RSI)
    [✅] exit _start_end: RAX == If(ULT(RDI, RSI), RDI, RSI)

```python
%%file /tmp/mymax2.s
.include "/tmp/knuckle.s"
.globl  _start
kd_entry _start "(assert true)"
    mov     %rdi, %rax

    cmp     %rsi, %rdi
    jbe     .done

    mov     %rsi, %rax
kd_exit .done "(assert (= RAX (ite (bvule RDI RSI) RDI RSI)))"
#kd_exit .done "(assert (= RAX RDI))"
    ret
```

    Overwriting /tmp/mymax2.s

```python
assemble_and_check('/tmp/mymax2.s')
```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('_start', True)]}), asserts=defaultdict(<class 'list'>, {}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194315: [('.done', RAX == If(ULE(RDI, RSI), RDI, RSI))]}), cuts=defaultdict(<class 'list'>, {}))
    entry _start at 4194304 with precond True
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 0) PCODE IMARK ram[400000:3]
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 1) PCODE RAX = RDI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 0) PCODE IMARK ram[400003:3]
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 1) PCODE unique[3af00:8] = RDI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 2) PCODE CF = unique[3af00:8] < RSI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 3) PCODE OF = sborrow(unique[3af00:8], RSI)
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 4) PCODE unique[3b000:8] = unique[3af00:8] - RSI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 5) PCODE SF = unique[3b000:8] s< 0x0
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 6) PCODE ZF = unique[3b000:8] == 0x0
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 7) PCODE unique[28080:8] = unique[3b000:8] & 0xff
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 8) PCODE unique[28100:1] = popcount(unique[28080:8])
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 9) PCODE unique[28180:1] = unique[28100:1] & 0x1
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 10) PCODE PF = unique[28180:1] == 0x0
    Executing 0x400006/2: JBE 0x40000b at (4194310, 0) PCODE IMARK ram[400006:2]
    Executing 0x400006/2: JBE 0x40000b at (4194310, 1) PCODE unique[e900:1] = CF || ZF
    Executing 0x400006/2: JBE 0x40000b at (4194310, 2) PCODE if (unique[e900:1]) goto ram[40000b:8]
    Executing 0x400008/3: MOV RAX,RSI at (4194312, 0) PCODE IMARK ram[400008:3]
    Executing 0x400008/3: MOV RAX,RSI at (4194312, 1) PCODE RAX = RSI
    [✅] exit .done: RAX == If(ULE(RDI, RSI), RDI, RSI)
    [✅] exit .done: RAX == If(ULE(RDI, RSI), RDI, RSI)

# Bits and Bobbles

Next steps. make exits and assumes work

- cuts. Invariants are cuts of cfg into a dag. Distinguishing backedges from forward edges
- fixup to work on riscv and 32 bit.
- nicer error output. Negative examples
- Countermodels interpret to be more readable. Give path through program, state at beginning and end.
- Use abstractions so the intermidate symbolic states aren't quite so unreadable
- Hoarize. I've had so many bugs this principled approach might be pretty useful.
- Gotta test that stuff I put in the library
- memory. Gotta inject a `mem` variable.
- prearranged loaded data. Mem does not currently reflect the actual contents of the loading.
- store history just to make debugging easier.
- pre and post conditions on calls? if jump into address already.
- objcopy assertions into section
- Pro / Con of WP?
- kd_always for constantly checked invariants
- A whitelist of jump points. Only allow labelled positions?
- Regular execution or GDB sessions. All the cbat features.
- failsafe. If I grep kd_ in the line, but don't recognize it, I should complain. Multiline smtlib would be nice too.
- The stdlib of helpers.
- speed
- Tracking seen addresses. We may want to track if we never hit a label that has an annotation on it, as this is suspicious.

it could make sense to slot in AFL or angr or Symqemu or whatever instead of my system, checking the same properties. I have designed my semantics to be moderately sound

```python
import json
def make_section(spec : AsmSpec, bin_name: str):
    with open("/tmp/spec.json", "w") as f:
        json.dump(asdict(spec), f, indent=4, default=lambda b: b.sexpr())
    subprocess.run(["objcopy", bin_name, "--add-section", "knucklespec=/tmp/spec.json"], check=True)

assemble_and_check('/tmp/mymax2.s')
ctx = pcode.BinaryContext("/tmp/kdrag_temp.o")
make_section(AsmSpec.of_file('/tmp/mymax2.s', ctx), "/tmp/kdrag_temp.o")

```

    AsmSpec(entries=defaultdict(<class 'list'>, {4194304: [('_start', True)]}), asserts=defaultdict(<class 'list'>, {}), assumes=defaultdict(<class 'list'>, {}), exits=defaultdict(<class 'list'>, {4194315: [('.done', RAX == If(ULE(RDI, RSI), RDI, RSI))]}), cuts=defaultdict(<class 'list'>, {}))
    entry _start at 4194304 with precond True
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 0) PCODE IMARK ram[400000:3]
    Executing 0x400000/3: MOV RAX,RDI at (4194304, 1) PCODE RAX = RDI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 0) PCODE IMARK ram[400003:3]
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 1) PCODE unique[3af00:8] = RDI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 2) PCODE CF = unique[3af00:8] < RSI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 3) PCODE OF = sborrow(unique[3af00:8], RSI)
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 4) PCODE unique[3b000:8] = unique[3af00:8] - RSI
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 5) PCODE SF = unique[3b000:8] s< 0x0
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 6) PCODE ZF = unique[3b000:8] == 0x0
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 7) PCODE unique[28080:8] = unique[3b000:8] & 0xff
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 8) PCODE unique[28100:1] = popcount(unique[28080:8])
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 9) PCODE unique[28180:1] = unique[28100:1] & 0x1
    Executing 0x400003/3: CMP RDI,RSI at (4194307, 10) PCODE PF = unique[28180:1] == 0x0
    Executing 0x400006/2: JBE 0x40000b at (4194310, 0) PCODE IMARK ram[400006:2]
    Executing 0x400006/2: JBE 0x40000b at (4194310, 1) PCODE unique[e900:1] = CF || ZF
    Executing 0x400006/2: JBE 0x40000b at (4194310, 2) PCODE if (unique[e900:1]) goto ram[40000b:8]
    Executing 0x400008/3: MOV RAX,RSI at (4194312, 0) PCODE IMARK ram[400008:3]
    Executing 0x400008/3: MOV RAX,RSI at (4194312, 1) PCODE RAX = RSI
    [✅] exit .done: RAX == If(ULE(RDI, RSI), RDI, RSI)
    [✅] exit .done: RAX == If(ULE(RDI, RSI), RDI, RSI)

```python
! objdump -s --section knucklespec /tmp/kdrag_temp.o
```

    /tmp/kdrag_temp.o:     file format elf64-x86-64
    
    Contents of section knucklespec:
     0000 7b0a2020 20202265 6e747269 6573223a  {.    "entries":
     0010 207b0a20 20202020 20202022 34313934   {.        "4194
     0020 33303422 3a205b0a 20202020 20202020  304": [.        
     0030 20202020 5b0a2020 20202020 20202020      [.          
     0040 20202020 2020225f 73746172 74222c0a        "_start",.
     0050 20202020 20202020 20202020 20202020                  
     0060 22747275 65220a20 20202020 20202020  "true".         
     0070 2020205d 0a202020 20202020 205d0a20     ].        ]. 
     0080 2020207d 2c0a2020 20202261 73736572     },.    "asser
     0090 7473223a 207b7d2c 0a202020 20226173  ts": {},.    "as
     00a0 73756d65 73223a20 7b7d2c0a 20202020  sumes": {},.    
     00b0 22657869 7473223a 207b0a20 20202020  "exits": {.     
     00c0 20202022 34313934 33313522 3a205b0a     "4194315": [.
     00d0 20202020 20202020 20202020 5b0a2020              [.  
     00e0 20202020 20202020 20202020 2020222e                ".
     00f0 646f6e65 222c0a20 20202020 20202020  done",.         
     0100 20202020 20202022 283d2052 41582028         "(= RAX (
     0110 69746520 28627675 6c652052 44492052  ite (bvule RDI R
     0120 53492920 52444920 52534929 29220a20  SI) RDI RSI))". 
     0130 20202020 20202020 2020205d 0a202020             ].   
     0140 20202020 205d0a20 2020207d 2c0a2020       ].    },.  
     0150 20202263 75747322 3a207b7d 0a7d        "cuts": {}.}  

One issue I've perceived is that these systems (and almost all verification tooling) is sort of locked behind ecosystems that are not palatable to a majority of users. Our project cbat was built in OCaml around the Binary Analysis Platform. We did ship docker containers, but I think you had to be _really_ interested in using our tool to make it past the doorway.

In addition to that, it was in essence a fully automatic tool. There was the ability to annotate invariants via command line options, but that was not the expected main use pattern.

Something I've wanted is the ability to break apart the monolithic automated verification query. I've found this very useful in Knuckeldragger and to some degree this is what semi-automated systems like Dafny

I think it is also an appealing design to let you use ordinary the ordinary binutils

One design choice I don't regret in CBAT was to use SMTLib itself as our specification language. It is at least a known established entity you can look up stuff about and it gives you full access to the solvers capabilities.

<https://www.ndss-symposium.org/wp-content/uploads/bar2024-9-paper.pdf>
<https://github.com/draperlaboratory/cbat_tools>

Some other assembly verification stuff

- HOL Light assembly verification <https://github.com/awslabs/s2n-bignum/blob/main/x86/proofs/bignum_add.ml>
- SAIL and islaris <https://dl.acm.org/doi/10.1145/3519939.3523434>
- Risc-V semantics coq <https://github.com/mit-plv/riscv-coq>
- LNSym in lean <https://github.com/leanprover/LNSym>
- ACL2 stuff <https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/?topic=ACL2____X86ISA>
- K framework x86  <https://github.com/kframework/X86-64-semantics>
- Sel4 stuff
- HOL4 myreen <https://www.cl.cam.ac.uk/~mom22/cpp13/paper.pdf> <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-765.pdf>
- <https://fstarlang.github.io/lowstar/html/Introduction.html> Does low* hit assembly or C? <https://github.com/project-everest/vale>
- Cryptol does assembly right?
- <https://arxiv.org/pdf/1907.01283> metamath0
- Compcert semantics
- arm p asl arm specification language <https://github.com/ailrst/aslp>
- <https://www.cs.utexas.edu/~moore/best-ideas/piton/index.html> CLI verified stack <https://www.cs.utexas.edu/~moore/acl2/current/combined-manual/index.html?topic=ACL2____OPERATIONAL-SEMANTICS-2_F5_F5OTHER-EXAMPLES>
- <https://binsec.github.io/>

When you peel off all the sophistry and knee jerk formal methods design patterns, I think binary verification can be fairly intuitive.

When you talk about verification, two topics come up, Weakest precondition and/or Hoare Logic. Weakest precondition or predicate transformer semantics can be viewed in at least two ways

1. Describe program semantics by how you pull a set of program states backwards through the execution of a statement
2. Describe program semantics by the syntactic manipulation of logical formulas constraining program state.

It's the same thing, since formulas describe the set of states for which they evaluate to true, but saying it like 1. feels more semantic and 2. feels more syntactic.

Talking about running a program backwards is a little unintuitive.

Symbolic execution is a pretty evocative term that is more commonly understood in the reversing community. Execute the thing, as you might in an interpreter or emulator, but instead of working on concrete states of concrete u64 etc, work on symbolic states building up a symbolic expression describing the state. This mostly means building up SMT solver expressions describing the current state.

For straight line code, it's all the same. The minimal control flow makes it fairly easy to directly convert statements to expressions.

For DAG-like control flow (if-then-else / switch chains), things are little harder but not so bad. You can finitely enumerate all the paths through the program (although this number is exponentially exploding in the size of the dag).

For arbitrary control flow, it feels more complicated but actually it kind of isn't.

Typed assembly language. I've been saying that type systems can be seen as tactics.
<https://dl.acm.org/doi/10.1007/978-3-031-74776-2_17> BinSub: The Simple Essence of Polymorphic Type Inference for Machine Code

webassembly via ghidra? <https://github.com/nneonneo/ghidra-wasm-plugin/>

dump into dwarf?
<https://github.com/pq-code-package/mlkem-native/tree/main/proofs/hol_light/arm>
<https://github.com/awslabs/s2n-bignum>
<https://github.com/awslabs/s2n-bignum/blob/main/x86/tutorial/simple.ml>

global invariants.
Interrupt_enabled =>

Python smt assertions. just use eval. If smtlib turns you off
Dwarf expr assertions
assembly subprogram assertiosn - the most work. Natural in some sense.

kd_always "(if invarint ...)"

whitelist valid jump locations.

floyd version of logic on flowcharts. What did that look like?

```python
@dataclass
class AsmSpec():
    entries: list[tuple[int, smt.BoolRef]]
    asserts: list[tuple[int, smt.BoolRef]]
    assumes: list[tuple[int, smt.BoolRef]]
    exits: list[tuple[int, smt.BoolRef]]
```

```python
json.dumps(asdict(spec), default=lambda b: b.sexpr())
```

    '{"entries": {"4194304": [["myfunc", "true"]]}, "asserts": {"4194311": [["my_assert", "(= RAX #x000000000000002a)"]]}, "assumes": {}, "exits": {"4194311": [["func_end", "(= RAX #x000000000000002a)"]]}, "cuts": {}}'

```python

```
