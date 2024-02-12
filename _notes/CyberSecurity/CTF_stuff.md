---
author: philzook58
layout: post
title: Binary Analysis & CTF stuff
---

- [Reversing](#reversing)
  - [Disassembly](#disassembly)
  - [Decompiler](#decompiler)
    - [Loop recovery](#loop-recovery)
    - [Interactive](#interactive)
    - [Binary Ninja](#binary-ninja)
      - [Types](#types)
      - [IR Tower](#ir-tower)
    - [Ghidra](#ghidra)
    - [radare](#radare)
    - [Angr](#angr)
  - [Patching](#patching)
  - [Diffing](#diffing)
  - [Binary reversing](#binary-reversing)
- [Debuggers](#debuggers)
- [Code Search](#code-search)
- [Dynamic Binary Instrumentation](#dynamic-binary-instrumentation)
- [Vulnerabilities](#vulnerabilities)
  - [Web App](#web-app)
  - [Windows](#windows)
  - [Mitigations](#mitigations)
- [Exploits](#exploits)
  - [Buffer Overflows](#buffer-overflows)
  - [Primitives](#primitives)
  - [Return Oriented Programming (ROP)](#return-oriented-programming-rop)
    - [JOP COP](#jop-cop)
  - [Data Oriented Programming (DOP)](#data-oriented-programming-dop)
  - [Heap](#heap)
    - [House of Force](#house-of-force)
    - [fastbin dup](#fastbin-dup)
    - [unsafe unlink](#unsafe-unlink)
  - [Type Confusion](#type-confusion)
  - [Kernel](#kernel)
  - [Browser](#browser)
  - [Automated Exploit Generation (AEG)](#automated-exploit-generation-aeg)
- [Elf stuff](#elf-stuff)
- [Virus](#virus)
- [(De)Obfuscation](#deobfuscation)
  - [Mixed Boolean Arithmetic (MBA)](#mixed-boolean-arithmetic-mba)
- [CTF](#ctf)
- [What is Binary Analysis](#what-is-binary-analysis)
  - [Program Analysis](#program-analysis)
  - [How are binaries made](#how-are-binaries-made)
- [Misc](#misc)
- [nmap](#nmap)
      - [Digital forensics](#digital-forensics)
      - [pwn.college](#pwncollege)
  - [Intro](#intro)
    - [binary files](#binary-files)
    - [process loading](#process-loading)
- [shellcode](#shellcode)
  - [Protection](#protection)
  - [pwntools](#pwntools)
  - [Examples from pwn.college](#examples-from-pwncollege)

# Reversing

## Disassembly

disassembler
linear sweep
Shingled
recusrive traversal
anti-disassembly
<https://github.com/AppleReer/Anti-Disassembly-On-Arm64>

[relative disassembler performance](https://twitter.com/richinseattle/status/1468418790006267910?s=20)

capstone <http://www.capstone-engine.org/> - disassembler. converse of key
zydis
xed
distrom
iced
bddisasm
yaxpeax

McSema - older trail of bits lifter. Uses llvm as IR
[remill](https://github.com/lifting-bits/remill) lift to llvm bitcode
anvill processing remill
rellic makes C like code

BAP
ANGR - VEX which is valgrind's ir

gtirb ddisasm grammatech
<https://grammatech.github.io/gtirb/>
<https://github.com/GrammaTech/gtirb> "GTIRB explicitly does NOT represent instructions or instruction semantics but does provide symbolic operand information and access to the bytes. "

Speculative disssembly <https://ieeexplore.ieee.org/document/7745279> decode every offset. Refine blocks. Spedi, open source spcualtive disassembler <https://github.com/abenkhadra/spedi>
Nucleus paper <https://mistakenot.net/papers/eurosp-2017.pdf> Compiler-Agnostic Function Detection in Binaries

superset disassembler kenneth <https://personal.utdallas.edu/~hamlen/bauman18ndss.pdf>
civuentes thesis

probablistic disassembly using proabablistic datalog?
bap mc + datalog?

[Formally Verified Lifting of C-Compiled x86-64 Binaries](https://www.ssrg.ece.vt.edu/papers/pldi22.pdf)
[Scalable validation of binary lifters](https://dl.acm.org/doi/10.1145/3385412.3385964)

- Linear
- Recursive

-

[Disasm.Driver](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Disasm/Driver/index.html)
[](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Disasm/index.html)

Delay slots are an annoyance. Some architectures allow instructions to exist in the shadow of jump instructions that logically execute beofre the jump instruction. This makes sense from a micro architectural perspective, but it is bizarre to disassemble

<https://rev.ng/>
[rev.ng paper](https://hexhive.epfl.ch/publications/files/17CC.pdf)
osr - offset shift range. I;ve seen this called value set analysis?
[rev.ng thesis](https://www.politesi.polimi.it/bitstream/10589/139255/1/main.pdf)

[deepvsa](https://www.usenix.org/system/files/sec19-guo.pdf)

[Analyzing Memory Accesses in x86 Executables Reps and Balakrishnnan](https://research.cs.wisc.edu/wpis/papers/cc04.pdf)

byteweight - bap neural network thing identifies function starts

Ghidra repackaging:
[lifting bits sleigh](https://github.com/lifting-bits/sleigh)
[pypcode](https://github.com/angr/pypcode)
<https://github.com/StarCrossPortal/sleighcraft>
<https://github.com/black-binary/sleigh>

[An Empirical Study on ARM Disassembly Tools](https://github.com/valour01/arm_disasssembler_study)

[ben's ll2l](https://gitlab.com/delysid/ll2l)

<https://github.com/simonlindholm/asm-differ>

## Decompiler

Interesting. they are actuallyb trying to get source that compiles to exactly the assembly. They might have the original tool chain "matching" decompilation
<https://decomp.me/>
<https://github.com/simonlindholm/decomp-permuter>
<https://github.com/matt-kempster/m2c> mips and powerpc decompiler

<https://github.com/zeldaret/oot> ocarina of time deocmpilation <https://objmap.zeldamods.org/#/map/z3,0,0>
<https://github.com/pmret/papermario> paper maro
<https://github.com/pret/pokeemerald> <https://github.com/pret>

<https://github.com/leoetlino/project-restoration>

<https://github.com/trailofbits/BTIGhidra>
bincat
retypd

 <https://x.com/mahal0z/status/1717600833037377613?s=20> <https://www.zionbasque.com/files/publications/sailr_usenix24.pdf> Ahoy SAILR! There is No Need to DREAM of C: A Compiler-Aware Structuring Algorithm for Binary Decompilation
Graph schema matching? Smart methodology. Take codebase, decompile, compare number of gotos in original vs decompiled functions. Find hotspots. Binary search for passes responsible

DREAM
Pheonix

[FoxDec - Formally verified x86-64 decompilation](https://ssrg-vt.github.io/FoxDec/)

relic - no more gotos

a comb for decompiled C <https://rev.ng/downloads/asiaccs-2020-presentation.pdf>

[Cifuentes thesis](https://yurichev.com/mirrors/DCC_decompilation_thesis.pdf) kind of a ludicrous amount of info
"Decompiler compiler" references BB91 BB92 bbl91 bbl93 bow91 bow93
[A Compendium of Formal Techniques for Software Maintenance](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=fdf743acbfa9052b4c8da81fc5d5def39a71e00b)
[the redo project final report](https://www.researchgate.net/publication/2527720_The_REDO_Project_Final_Report/link/560e569a08ae6b29b498635f/download)

[Decompilation: The Enumeration of Types and Grammars](https://dl.acm.org/doi/pdf/10.1145/186025.186093)
[From programs to object code and back again using logic programming: Compilation and decompilation](https://onlinelibrary.wiley.com/doi/abs/10.1002/smr.4360050403)
[The art of computer un-programming: Reverse engineering in Prolog](https://link.springer.com/chapter/10.1007/3-540-55930-2_20)
[Generating Decompilers](https://www.researchgate.net/publication/2524264_Generating_Decompilers/link/0fcfd50c60fe6c4876000000/download)

<https://www2.cs.arizona.edu/~collberg/Teaching/620/1999/Handouts/rmeadows1.pdf>

 [Polymorphic Type Inference for Machine Code](https://arxiv.org/abs/1603.05495)

 [Static Single Assignment for Decompilation - Emmerik](https://yurichev.com/mirrors/vanEmmerik_ssa.pdf)
 <https://twitter.com/brightprogramer/status/1626841275801702400?s=20>

[Decompilers and beyond Ilfak Guilfanov, Hex-Rays SA, 2008](https://web.archive.org/web/20181014083034/https://www.hex-rays.com/products/ida/support/ppt/decompilers_and_beyond_white_paper.pdf)

[Type-Based Decompilation? (or Program Reconstruction via Type Reconstruction)- Alan Mycroft](https://link.springer.com/content/pdf/10.1007/3-540-49099-X_14.pdf)

### Loop recovery

Getting structured control flow from CFG
Stackify <https://gitlab.inria.fr/why3/why3/-/merge_requests/453>

<https://icfp22.sigplan.org/details/icfp-2022-papers/1/Beyond-Relooper-Recursive-Translation-of-Unstructured-Control-Flow-to-Structured-Con>

[havlak and tarjan](https://www.researchgate.net/publication/220404846_Nesting_of_Reducible_and_Irreducible_Loops)
testing redicibility with union find

[A New Algorithm for Identifying Loops in
Decompilation ](https://lenx.100871.net/papers/loop-SAS.pdf)

dfs. label nodes. Intervals of labels are subsets of nodes. timestamp of first visit timestamp of last ivist.
backedge forward edge, cross edge

<https://zenodo.org/record/6727752#.YsxRw9rMI2w>

Also... egraphs

webassembly is at the core of both of these
Allllll things come around
I wonder if webassembly would be a good universal disassembler ir
someone should do that
<https://github.com/nforest/awesome-decompilation>

### Interactive

- IDA
- Ghidra
- Binary Ninja
- Cutter
- angr management
<https://github.com/GrammaTech/gtirb-vscode>

[decompiler explorer](https://github.com/mborgerson/mdec) Hmm. too bad it's not a web service

### Binary Ninja

SCC- shellcde compiler. Why is this a top level thing?

Binary View
Making a plugin - has remote denug to vs code <https://docs.binary.ninja/dev/plugins.html>

`current_function`
`bv.functions`

f.callers
f.callees

#### Types

<https://docs.binary.ninja/guide/type.html#boolean>
` bv.parse_type_string("uint64_t") ` slow but convenient

Type.bool
Type.char

```python
#!/usr/bin/env python3
import binaryninja
with binaryninja.open_view("/bin/ls") as bv:
    print(f"Opening {bv.file.filename} which has {len(list(bv.functions))} functions")

```

#### IR Tower

Lifted IL

LLIL

HLIL

### Ghidra

See ghidra notes

### radare

<https://book.rada.re/first_steps/history.html>

```bash
radare2.ra
radare2.radiff2
radare2.sleighc

```

<https://github.com/radareorg/r2ghidra>

```bash
echo "
int foo(int x) {return x*x + 1;}
" > /tmp/foo.c
gcc /tmp/foo.c -c -o /tmp/foo.o
radare2.r2


```

### Angr

```python
import angr #, monkeyhex
proj = angr.Project('/bin/true')
state = proj.factory.entry_state()
```

```python

code = '''
int fact(int x){
  int acc = 1;
  while(x > 0){
    acc *= x;
    x--;
  }
  return acc;
}
'''
import tempfile
import subprocess
import angr #, monkeyhex
import os
with tempfile.NamedTemporaryFile(suffix=".c") as fp:
  with tempfile.TemporaryDirectory() as mydir:
    fp.write(code.encode())
    fp.flush()
    fp.seek(0)
    print(fp.readlines())
    print(fp.name)
    print(mydir)
    outfile = mydir + "/fact"
    print(outfile)
    print(subprocess.run(["gcc",  "-g",  "-c","-O1", "-o",  outfile, fp.name], check=True))
    print(os.listdir(mydir))
    
    print(subprocess.run(["objdump", "-d", outfile], check=True))

    proj = angr.Project(outfile)
    print(dir(proj))
    print(proj.arch)
    print(proj.entry)
    print(proj.filename)
    print(proj.loader)
    block = proj.factory.block(proj.entry)
    print(block.pp())
    print(block)
    print(block.vex)
    print(block.instructions) # numebr of instryuctions
    print(dir(proj.analyses))
    state = proj.factory.entry_state()
    print(dir(state))
    print(proj.loader.find_symbol("fact"))
    #state = proj.factory.entry_state()
    print(state.step())
    print(dir(state.solver))
    print(state.solver.all_variables)


```

```bash
echo "
int fact(int x){
   int acc = 1;
   for (int i = 1; i < x; i++){
      acc *= i;
   }
   return acc;
}
" > /tmp/fact.c
gcc /tmp/fact.c -c -o /tmp/fact 
```

```bash
echo "
int max(int x){
  return x > 0 ? x : -x;
}
" > /tmp/max.c
gcc /tmp/max.c -c -o /tmp/max 
```

{% raw %}

```python
import angr
p = angr.Project('/tmp/fact')
cfg = p.analyses.CFGFast()
print("This is the graph:", cfg.graph)
entry_func = cfg.kb.functions[p.entry]
print(entry_func.name)
blocks = list(entry_func.blocks)
print(blocks)
irsb = blocks[0].vex
print(dir(entry_func))
print(entry_func.block_addrs)
print(dir(blocks[0]))
print(entry_func.addr)
```

```python
import angr
p = angr.Project('/tmp/max')
cfg = p.analyses.CFGFast()
print("This is the graph:", cfg.graph)
entry_func = cfg.kb.functions[p.entry]
print(entry_func.name)
blocks = list(entry_func.blocks)
print(blocks)
irsb = blocks[0].vex
from pyvex.stmt import *
from pyvex.expr import *



jmp_table = ["""
jump_table:
switch(state.gr[184]){
"""]

#for addr in addrs:
#  jmp_table.append(f"case 0x{addr:x}: goto {label(addr)};")
#jmp_table.append("""
#default:
# assert(false); // unexpected indirect jump
#}
#""")
def proc_binop(expr):
    #print(expr.op)
    # TODO: perhaps I need casts here to signed unsigned?
    if expr.op == "Iop_Sub64":
      return f"({proc_expr(expr.args[0])} - {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Sub32":
      return f"({proc_expr(expr.args[0])} - {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Add64":
      return f"({proc_expr(expr.args[0])} + {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Add32":
      return f"({proc_expr(expr.args[0])} + {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Shr64":
      return f"({proc_expr(expr.args[0])} >> {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_And64":
      return f"({proc_expr(expr.args[0])} & {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Xor64":
      return f"({proc_expr(expr.args[0])} & {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_CmpLT32S":
      return f"({proc_expr(expr.args[0])} < {proc_expr(expr.args[1])})"
    elif expr.op == "Iop_Mul32":
      return f"({proc_expr(expr.args[0])} * {proc_expr(expr.args[1])})"
    else:
      assert False, f"Unimplemented binop {expr.op}"
def proc_unop(expr):
  #print(expr.op)
  if expr.op == "Iop_64to32":
    return f"((int32_t) {proc_expr(expr.args[0])})"
  elif expr.op == "Iop_32Uto64":
    return f"((int64_t) {proc_expr(expr.args[0])})"
  elif expr.op == "Iop_1Uto64":
    return f"((int64_t) {proc_expr(expr.args[0])})"
  elif expr.op == "Iop_64to1":
    return f"((bool) {proc_expr(expr.args[0])})"
  else:
    assert False, f"Unimplemented unop {expr.op}"

def proc_expr(expr : IRExpr):
    #print(expr)
    if isinstance(expr, Binder):
        assert False
    elif isinstance(expr, VECRET):
        assert False
    elif isinstance(expr, GSPTR):
        assert False
    elif isinstance(expr, RdTmp):
        return str(expr)
    elif isinstance(expr, Get):
        assert expr.ty == "Ity_I64"
        return f"state->gr[{expr.offset}]"
    elif isinstance(expr, Qop):
        assert False
    elif isinstance(expr, Triop):
        assert False
    elif isinstance(expr, Binop):
        return proc_binop(expr)
    elif isinstance(expr, Unop):
        return proc_unop(expr)
    elif isinstance(expr, Load):
        #assert expr.ty == "Ity_I32"  # TODO. We need to deal with these types and endianess. Yuck
        return f"state->mem[{expr.addr}]"
    elif isinstance(expr, Const):
        return str(expr)
    elif isinstance(expr, ITE):
        return f"{proc_expr(expr.cond)} ? {proc_expr(expr.iftrue)}: {proc_expr(expr.iffalse)}"
    elif isinstance(expr, CCall):
        assert False
    else:
      assert False

def label(addr):
  return f"L_0x{addr:x}" 
def proc_type(typ):
  if ty == "Ity_I32":
    return "int32_t"
  elif ty == "ItyI64":
    return "int64_t"
  else:
    assert False

def proc_stmt(stmt : IRStmt):
    #print(stmt.tag)
    if isinstance(stmt, NoOp):
         return "// NoOp"
    elif isinstance(stmt, IMark):
        # assert PC = expected pc here?
        # f"assert(state->gr[{}] == stmt.addr);"
        #return f"break; case 0x{stmt.addr:x}: //{label(stmt.addr)}:" # also print original assembly in comment
        return f"//{label(stmt.addr)}:"
    elif isinstance(stmt, AbiHint):
        return f"return; // {stmt}" # TODO: add return parameter? Or state is good. Is abihint always at returns?
    elif isinstance(stmt, Put):

        return f"state->gr[{stmt.offset}] = {proc_expr(stmt.data)};"
        assert False
    elif isinstance(stmt, PutI):
        assert False
    elif isinstance(stmt, WrTmp):
        return f"t{stmt.tmp} = {proc_expr(stmt.data)};"
    elif isinstance(stmt, Store):
        return f"state->mem[{stmt.addr}] = {proc_expr(stmt.data)};"
    elif isinstance(stmt, CAS):
        assert False
    elif isinstance(stmt, LLSC):
        assert False
    elif isinstance(stmt, MBE):
        assert False
    elif isinstance(stmt, Dirty):
        assert False
    elif isinstance(stmt, Exit):
        print(stmt.jk)
        assert stmt.jk == "Ijk_Boring"
        return f"if({proc_expr(stmt.guard)}){{ state->gr[{stmt.offsIP}] = 0x{stmt.dst.value:x}; break; }}"
        # TODO deal with other jumpkind
        # What represents an indirect jump? goto jump_table;
        # elif stmt.jk == "Ijk_Ret" f"return;"
        # elif stmt.jk == Ijk_Call   hmmm. f"{funname}()" maybe?
        # elif stmt.jk == "Ijk_Exit"
    elif isinstance(stmt, LoadG):
        assert False
    else:
      print("unrecognized IRStmt")
      assert False

output = []
tmps = set()
for block in blocks:
  #print(dir(block))
  #print(block.instructions)
  output.append("/*")
  output.append(str(block.disassembly))
  output.append("*/")
  output.append(f"case 0x{block.addr:x}:")
  for stmt in block.vex.statements:
    #stmt.pp()
    output.append(proc_stmt(stmt))
    if isinstance(stmt,WrTmp):
      tmps.add(stmt.tmp)
  # output.append("goto jump_table;")
  output.append("break;")
output.append("default: assert(0); // Unexpected PC value. Something has gone awry.")

#print("\n".join(output))

header = """
#include <stdint.h>
#include <assert.h>
#include <stdbool.h>
#define PUT(reg) reg
#define PC 184

typedef struct state_t 
{
int64_t *mem;
int64_t *gr;
} state_t;
"""



with open("/tmp/decomp.c", "w") as file:
    file.write(header)
    file.write(f"void {entry_func.name}_decomp(state_t *state){{\n") # use entry_func.name?
    file.write("int " + ",".join([f"t{tmp}" for tmp in tmps]) + ";\n") # declare temps
    file.write(f"state->gr[PC] = 0x{entry_func.addr:x};\n") # initilizae PC to entry point
    file.write("while(1){\n") # interpreter loop invariant on PC? Could make gas?
    file.write("switch(state->gr[PC]){") 
    file.writelines([x + "\n" for x in output])
    file.write("}}}\n")
```

```bash
clang-format -i  --style=google /tmp/decomp.c
cat /tmp/decomp.c
gcc /tmp/decomp.c -O2 -c -o /tmp/decomp.o -Wall -Wextra -Wcast-align -Wcast-qual -Wmissing-declarations
esbmc /tmp/decomp.c --function max_decomp #--goto-functions-only
```

Control flow encoding. Do I do separate jump table, go to jump table every time?
`while(true){switch state.gr[pc]{  case: case: case: case default: }  }`
This is fairly conservative.
Big block encoding trusts fall through behavior.
Byte address and then cast mem pointers.

```python
import angr
p = angr.Project('/tmp/fact')
cfg = p.analyses.CFGFast()
print("This is the graph:", cfg.graph)
entry_func = cfg.kb.functions[p.entry]
print(entry_func.name)
blocks = list(entry_func.blocks)
print(blocks)
irsb = blocks[0].vex
import pyvex

stmts = []
counter = 0
def fresh():
  global counter
  counter += 1
  return f"%v{counter}"

def print_expr(dst, expr):
  if isinstance(expr, pyvex.expr.Const):
    stmts.append( { "op": "const", "type": "int", dest: dst, "value": expr.con })
  elif isinstance(expr, pyvex.expr.Binop):
    args = [fresh() for _ in range(2)]
    for a, e in zip(args, expr.child_expressions):
      print_expr(a,e)
    stmts.append({ "op": expr.op, "type": "int", "dest": dst, "args": args })
  elif isinstance(expr, pyvex.expr.RdTmp):
    print(expr.tmp)
    #stmts.append({ "op": "id", "type": "int", "dest": dst, "args":  })
  elif isinstance(expr, pyvex.expr.Get):
    return f"%{expr.offset}"
  else:
    print(expr)
    print(type(expr))
    assert False
  

for stmt in irsb.statements:
    stmt.pp()
    if isinstance(stmt, pyvex.IRStmt.Store):
      expr = print_expr(stmt.data)
      print(stmt.end)
      assert stmt.end == "Iend_LE"
      expr["op"] = "store"
      expr["dest"] = expr.addr
      stmts.append(expr)
    elif isinstance(stmt, pyvex.IRStmt.Put):
      print_expr(stmt.data)
      print(stmt.offset)
    elif isinstance(stmt, pyvex.IRStmt.WrTmp):
      print_expr(stmt.data)
      print(stmt.tmp)
    elif isinstance(stmt, pyvex.IRStmt.IMark):
      pass
    else:
      print(stmt)
      print(type(stmt))
      assert "unrecognized stmt" == None
print(stmts)
```

{% endraw %}

## Patching

See notes on patching

## Diffing

 see note on patching

## Binary reversing

<https://corte.si/posts/visualisation/binvis/index.html> hilbert curves for binary vsiualization
benford's law

binwalk
ofrak
fra
cwechecker

entropy visualization

<https://www.usenix.org/system/files/sec22-burk.pdf> Decomperson: How Humans Decompile
and What We Can Learn From It

[MATE](https://github.com/GaloisInc/MATE)

# Debuggers

See note on debuggers

# Code Search

<https://github.com/bstee615/tree-climber>
<https://github.com/langston-barrett/tree-sitter-souffle>
<https://github.com/weggli-rs/weggli>
<https://github.com/BrianHicks/tree-grepper> isn't semgrep basically a treesitter grepper?

Joern
codeql
semgrep

# Dynamic Binary Instrumentation

dynamorio <https://dynamorio.org/>
frida  <https://frida.re/> injects a quickjs huh
pin <https://www.intel.com/content/www/us/en/developer/articles/tool/pin-a-dynamic-binary-instrumentation-tool.html>

# Vulnerabilities

<https://github.com/river-li/awesome-uefi-security>

[CWE](https://cwe.mitre.org/index.html) - common weakenss enumeration
<https://attack.mitre.org/>

integer overflow <https://cwe.mitre.org/data/definitions/190.html>

[null pointer dereference](https://cwe.mitre.org/data/definitions/476.html)

[sophos - comprehensive exploit prevention 2018](https://www.sophos.com/en-us/medialibrary/Gated-Assets/white-papers/Sophos-Comprehensive-Exploit-Prevention-wpna.pdf)

[Current State of Exploit Dev 2020](https://www.crowdstrike.com/blog/state-of-exploit-development-part-1/)

## Web App

Burp suite

## Windows

[microsoft exploits and exploit kits](https://docs.microsoft.com/en-us/microsoft-365/security/intelligence/exploits-malware?view=o365-worldwide)

## Mitigations

Control Flow integrity is a broad term for many of these
[CONFIRM: Evaluating Compatibility and Relevance of Control-flow Integrity Protections for Modern Software](https://personal.utdallas.edu/~hamlen/xu19-confirm.pdf)

DEP - data execution prevention [executable space protection](https://en.wikipedia.org/wiki/Executable_space_protection) This says DEP is Windows terminology?
[NX bit](https://en.wikipedia.org/wiki/NX_bit)

shadow stack

control flow guard - windows
reverse flow guard
extreme flow guard
kernel data protection

stack canary <https://www.keil.com/support/man/docs/armclang_ref/armclang_ref_cjh1548250046139.htm> -fstack-protector. Guard variable put on stack
SSP stack smashing protection. Stackguard, Propolice. <https://embeddedartistry.com/blog/2020/05/18/implementing-stack-smashing-protection-for-microcontrollers-and-embedded-artistrys-libc/>
[Buffer overflow protection](https://en.wikipedia.org/wiki/Buffer_overflow_protection)

ASLR ASLP A [Address Space Layout Randomization](https://en.wikipedia.org/wiki/Address_space_layout_randomization). Libraries are linked in at a different location. This make code reuse in an exploit more difficult.

Fat pointers

[endbr](https://stackoverflow.com/questions/56905811/what-does-the-endbr64-instruction-actually-do) intel control flow enforcement technology (CET). Valid locations for indirect jumps.

ASLR - Addresses are randomized
cat /proc/mem/self ? To look at what actually loaded
Also ldd shows were libraries get loaded in memory
Stack canaries - set once per binary run, so with forking you can brute force them or maybe leak them?

[checksec](https://github.com/slimm609/checksec.sh) tells you about which things are enabled. <https://opensource.com/article/21/6/linux-checksec> which also has a rundown of the different things and how you could check them manually. Can output into xml, json, csv

gcc options
-no-pie -pie -fpie
-no-stack-protection
-fstack-protector-all
-z execstack makes stack executable

RELRO - relocation read only. GOT table becomes read only. Prevents relocation attacks

binary diversification - compiler differently every time. code reuse becomes way harder [diversification](http://www.diva-portal.org/smash/get/diva2:1232129/FULLTEXT01.pdf) make many versions of binary to make code reuse attacks harder. disunison

# Exploits

## Buffer Overflows

<https://punkx.org/overflow/> a game version of buffer overflows. cool.

[buffer overflow](https://en.wikipedia.org/wiki/Buffer_overflow)
When a buffer overflow occurs you are writing to memory that possibly had a different purpose. Maybe other stack variables, maybe return address pointers, maybe over heap metadata.

Sanitization of user input
Off by one errors
String termination

## Primitives

AWP Arbitrary write primitive [CWE-123: Write-what-where Condition](https://cwe.mitre.org/data/definitions/123.html)
ARP arbitrary read primitive

## Return Oriented Programming (ROP)

[rp](https://github.com/0vercl0k/rp)
[ropper](https://github.com/sashs/Ropper)
[pwntool]

[ropgadget](https://github.com/JonathanSalwan/ROPgadget)
[ropium](https://github.com/Boyan-MILANOV/ropium) supports semantics queries. hmm in cpp. V impressive.

[return to libc](https://en.wikipedia.org/wiki/Return-to-libc_attack) libc is very common and
you can weave together libc calls. "Solar Designer"
[solar designer](https://en.wikipedia.org/wiki/Solar_Designer) 1997

[ropc-llvm](https://github.com/programa-stic/ropc-llvm)
[ropc](https://github.com/pakt/ropc)

[smashing the stack for fun and profit](http://phrack.org/issues/49/14.html) - stacks are no longer executable

<https://acmccs.github.io/papers/geometry-ccs07.pdf> geometry of innocent flesh on the bone. ROP

<https://github.com/sashs/Ropper>

[rop emporium](https://ropemporium.com/)

[rop ftw](https://www.exploit-db.com/docs/english/28479-return-oriented-programming-(rop-ftw).pdf)

pop_gadget ; value ; nextgadget  loads from stack into register

pure buffer overflow from command line:

```C
#include <stdio.h>
int main(int argc, char *argv[])
{
    char buf[256];
    memcpy(buf, argv[1],strlen(argv[1]));
    printf(buf);
}
```

[ropeme](https://github.com/packz/ropeme)

[angrop](https://github.com/angr/angrop)

[rop prevention by binary rewriting](https://github.com/GrammaTech/gtirb-stack-stamp)
[ropguard](https://github.com/ivanfratric/ropguard)

[stack pivoting](https://ir0nstone.gitbook.io/notes/types/stack/stack-pivoting) moving over to a different stack.

ret2libc
ret2dlresolve
ret2csu
ret2plt

<https://medium.com/cyber-unbound/buffer-overflows-ret2libc-ret2plt-and-rop-e2695c103c4c>

### JOP COP

jop rocket. blackhat talk
<https://i.blackhat.com/asia-21/Thursday-Handouts/as-21-Brizendine-Babcock-Prebuilt-Jop-Chains-With-The-Jop-Rocket-wp.pdf>  
<https://github.com/Bw3ll/JOP_ROCKET>

## Data Oriented Programming (DOP)

[Block Oriented Programming](https://arxiv.org/pdf/1805.04767.pdf)

## Heap

<https://c4ebt.github.io/2021/01/22/House-of-Rust.html> house of rust

If you can overwrite a struct that contains a pointer, you can use this to obtain reads or writes when that pointer is read or written.
If the struct contains a code pointer, you get control flow execution.

Heap layout problem
Heap layout manipulation

Metadata

Double free
Use after free

<http://phrack.org/issues/61/6.html> advanced doug lea malloc hacking

<https://milianw.de/blog/heaptrack-a-heap-memory-profiler-for-linux.html>
valgrind massif
perf-mem, valgrind massif, and heaptrack

<https://heap-exploitation.dhavalkapil.com/> <https://github.com/DhavalKapil/heap-exploitation>

advanced doug lea malloc - phreak post

glibc.
`ldd /bib/ls`
libc.so.6 - symbolic link probably
glibc 2.27
libc-2.31.so actually
pie
You can run it? `/lib/x86_64-linux-gnu/libc.so.6`

malloc
chunks of memory
new/delete make_unique

[heap history viewer](https://github.com/thomasdullien/heap_history_viewer)

pwndbg `vis` let's you see allocated chunks. How do it do it?
vmmap also shows memory regions classified
top chunk. I think the top chunk is resized to hand out new memory.
Metadata - size field. prev_in_use flag.
Allocator hands out in discrete sizes, not arbitrarily flexible

[hacktheheap.io](https://twitter.com/wootsecurity/status/1529893232557142037?s=20&t=6BI9d8LKn2fVprDrNxITOw)

[Playing for K(H)eaps: Understanding and Improving Linux Kernel Exploit Reliability](https://www.usenix.org/system/files/sec22fall_zeng.pdf)
defragmentation

slake

[libheap](https://github.com/cloudburst/libheap) examine glibc heap in gdb. seems like there is a python model of heap in here.

[how2heap](https://github.com/shellphish/how2heap)

<https://ir0nstone.gitbook.io/notes/types/heap/bins>

chunks - has prev size, size, info bits. Free chunks have pointers in content
top chunk - large piece of memory new chunks are carved out of
last remainder chunk
tcache
fastbin - last in first out. a stacklike structure

large bins - varying size. chunks put in order

printf("%p") is your friend

free lists
when we call free memory
fastbin. hold free checks of a specific size
set context-sections code
b main
vis to visualize heap
fastbins command -x20 - 0x80
arenas
main arena - glibc data section
pwndbg arena

fd forward pointer

### House of Force

### fastbin dup

arbitrary write
double free
fastbin will return twice.
frame command to
context code

immediate double free is prtoected

free_hook

find_fake_fast
one_gadget - constraints <https://github.com/david942j/one_gadget>

malloc_alloc

### unsafe unlink

n
vis

unsorted bin
doubly linked circular
free unsorted chunks have forward and backward pointers.
new free added to head. malloced from tail

adjeacent chunks get considlated
prev in use flags
unlinking. chunks being removed from doubly linked list

2000 solar designer
voodoo malloc tricks

## Type Confusion

## Kernel

double free ps4 <https://github.com/Cryptogenic/Exploit-Writeups/blob/master/FreeBSD/PS4%205.05%20BPF%20Double%20Free%20Kernel%20Exploit%20Writeup.md>

<https://twitter.com/sirdarckcat/status/1584846038866989056?s=20&t=udFq9u7zLY-5-Ae6VrdqeQ> Joy of explooitation the kernel  <http://slides.kernel.kitchen>

## Browser

<https://twitter.com/5aelo?lang=en>
[Attacking JavaScript Engines: A case study of JavaScriptCore and CVE-2016-4622](http://www.phrack.org/issues/70/3.html#article)

[How I started chasing speculative type confusion bugs in the kernel and ended up with 'real' ones](https://lpc.events/event/16/contributions/1211/)

[Return to sender Detecting kernel exploits with eBPF](https://i.blackhat.com/USA-22/Wednesday/US-22-Fournier-Return-To-Sender.pdf) <https://github.com/Gui774ume/krie>

## Automated Exploit Generation (AEG)

[sean heelan](https://sean.heelan.io/) [thesis](https://seanhn.files.wordpress.com/2020/11/heelan_phd_thesis.pdf)

usenix security
[heaphopper](https://www.usenix.org/conference/usenixsecurity18/presentation/eckert) angr symbolic analysis for heap exploits?
[archeap](https://github.com/sslab-gatech/ArcHeap)
[maze toward heap feng shui](https://www.usenix.org/system/files/sec21fall-wang-yan.pdf)
[backward search from heaphopper](https://scholar.google.com/scholar?start=0&hl=en&as_sdt=40000005&sciodt=0,22&cites=5560685275836890680&scipsc=)
[teerex](https://www.youtube.com/watch?v=HrrPDyHy7v8&list=PLbRoZ5Rrl5leqxwFLw3lAQ9on-fK5xLea&index=48&ab_channel=USENIX) discover of memory corrupton vulen
[symcc]

[crax++](https://github.com/SQLab/CRAXplusplus)

# Elf stuff

See linker
elfmaster
elf reverse

[example interesting elf files](https://github.com/tmpout/elfs) overlaying headers. smallest that doesn't voilate spec

[binary golf workshop](https://github.com/netspooky/bgws)
<https://codegolf.stackexchange.com/> [size coding](http://www.sizecoding.org/wiki/Main_Page)
[dead bytes](https://tmpout.sh/1/1.html) libgolf
[Elf Binary Mangling Pt. 4: Limit Break](https://tmpout.sh/2/11.html)

# Virus

<https://tmpout.sh/2/6.html> Preloading the linker for fun and profit ~ elfmaster
<https://arcana-technologies.io/blog/the-philosophy-of-elves-in-linux-threat-detection/>

<https://www.vx-underground.org/#E:/root> vxunderground
VXHeaven - mirror <https://github.com/opsxcq/mirror-vxheaven.org>
tmp.out
<https://tmpout.sh/3/02.html> second to hell interview <https://github.com/SPTHvx/SPTH>
roy g biv
hh86
herm1t

<https://spthvx.github.io/ezines/> ezines

Language infection project
Valhalla 0-4 zine
Metamorphism, Formal grammars and Undecidable Code Mutatio
"Polymorphism and Grammars" - qozah

see herm1t's metamorphic Linux virus Linux.Lacrimae in [EOF #2](https://spthvx.github.io/ezines/eof2/) and his article “Recompiling the Metamorphism"

From the design of a generic metamorphic engine to a black-box classification of antivirus detection techniques - tau obfuscation
[UNIX ELF Parasites and virus - Silvio Cesare](https://ivanlef0u.fr/repo/madchat/vxdevl/vdat/tuunix02.htm)

More virus ezines <https://ivanlef0u.fr/repo/madchat/vxdevl/vdat/ezines1.htm> ~2000 mostly

<https://privacy-pc.com/articles/vx-the-virus-underground.html> initeresting little article

<http://virus.wikidot.com/>

<https://www.exploit-db.com/> also has zines in papers <https://gitlab.com/exploit-database/exploitdb>

antivirus AV

metamorphic / polymorphic - mutate themselves to avoid simple detection
Relationship to quines?

# (De)Obfuscation

<https://github.com/mrphrazer/obfuscation_detection>
<https://obfuscator.re/omvll/> like obfuscation passes for llvm?
<https://github.com/javascript-obfuscator/javascript-obfuscator>
<https://github.com/HikariObfuscator/Hikari> llvm archived
<https://github.com/Guardsquare/proguard> java
<https://obfuscator.re/dprotect/> bytecode android
<https://github.com/dashingsoft/pyarmor> python

anti hooking - maybe more generally these are anti-RE techniques. debugger detection. VM detection.
control flow breaking
opaque constants

virtual machine VM obfuscation <https://reverseengineering.stackexchange.com/questions/24956/virtual-machine-code-obfuscation-implementation-details>
jit
anti alias analysis
self modification

<https://tigress.wtf/index.html> - C source to source <https://tigress.wtf/transformations.html> list of transformations

## Mixed Boolean Arithmetic (MBA)

<https://arxiv.org/pdf/2209.06335.pdf> Efficient Deobfuscation of Linear Mixed Boolean-Arithmetic
Expressions ∗

<https://www.youtube.com/watch?v=5yDzbFz2yWo&ab_channel=HackInTheBoxSecurityConference> HITB2022SIN #LAB Advanced Code Obfuscation With MBA Expressions - Arnau Gàmez Montolio

<https://archive.bar/pdfs/bar2020-preprint9.pdf> QSynth - A Program Synthesis based Approach for
Binary Code Deobfuscation <https://github.com/quarkslab/qsynthesis>

<https://secret.club/2022/08/08/eqsat-oracle-synthesis.html> <https://github.com/fvrmatteo/oracle-synthesis-meets-equality-saturation>

mixed Boolean arithmetic <https://github.com/softsec-unh/MBA-Solver/blob/main/README.md> mbasolver
<https://github.com/quarkslab/sspam/blob/master/README.md>

<https://github.com/RUB-SysSec/syntia/blob/master/README.md>
<https://github.com/astean1001/ProMBA>
simb
gamba
goomba
msynth <https://github.com/mrphrazer/msynth>

<https://dl.acm.org/doi/pdf/10.1145/3453483.3454068> Boosting SMT Solver Performance on
Mixed-Bitwise-Arithmetic Expressions

Viruses try to obfuscate themselves t avd detection

# CTF

SUID
<https://gtfobins.github.io/> GTFOBins is a curated list of Unix binaries that can be used to bypass local security restrictions in misconfigured systems.

Misconfiguration
<https://osquery.readthedocs.io/en/stable/>

commando vm

[yolo space hacker. steam game of ctf stuff](https://store.steampowered.com/app/1341450/Yolo_Space_Hacker/)
[exploit_me](https://github.com/bkerler/exploit_me) very vulnerable example applications
[pwntools](https://github.com/Gallopsled/pwntools)

pwndbg

cyclic_gen

# What is Binary Analysis

Dynamic - It feels like you're running the binary in some sense. Maybe on an emulated environment
Static - It feels like you're not running the binary

Fuzzing is definitely dynamic.
Dataflow analysis on a CFG is static
There are greys areas. Symbolic execution starts to feel like a grey area. I would consider it to be largely dynamic, but you are executing in a rather odd way.

Trying to understand a binary
Why?

- Finding vulnerabilities for defense or offense
  - buffer overflows
  - double frees
  - use after frees
  - memory leaks - just bad performance
  - info leaks - bad security
- Verification - Did your compiler produce a thing that does what your code said?
- Reversing/Cracking closed source software.
- Patching and Code injection. Finding Bugs for use in speed runs. Game Genie.
- Auditing
- Aids for manual RE work. RE is useful because things may be undocumented intentionally or otherwise. You want to reuse a chip, or turn on secret functionality, or reverse a protocol.
- Discovery of patent violation or GPL violations
- Comparing programs. Discovering what has been patched.

I don't want my information stolen or held ransom. I don't want people peeping in on my conversations. I don't want my computer wrecked. These are all malicious actors
We also don't want our planes and rockets crashing. This does not require maliciousness on anyone's part persay.

- Symbol recovery
- Disassembly
- CFG recovery
- Taint tracking
- symbolic execution

<https://github.com/analysis-tools-dev/dynamic-analysis> A list of tools
<https://analysis-tools.dev/>
[CSE597: Binary-level program analysis Spring 19 Gang Tan](http://www.cse.psu.edu/~gxt29/teaching/cse597s19/schedule.html)

### Program Analysis

What's the difference? Binaries are less structured than what you'll typically find talked about in program analysis literature.

Binaries are tough because we have tossed away or the coupling has become very loose between high level intent and constructs and what is there.

### How are binaries made

C preprocessor -> Maintains file number information isn't that interesting

C compiler -> assembly. You can ask for this assembly with `-S`. You can also
Or more cut up
C -> IR
IR -> MIR (what does gcc do? RTL right? )
MIR -> Asm

# Misc

<https://twitter.com/33y0re/status/1528719776142475264?s=20&t=vcTgXMu6ZeZRjj7LiSMcFg> kernel exploitation brwoser exploitation blog posts

- Arbitrary code guard
- Code interity guard
- hypervisor protected code integrity (HVCI) "the acg of kernel mode"
- vistualization based security VBS. credential guard
- local privilege escalation (LPE)
-

People

- elfmaster ryan oneill
-

cfi directives - call frame information

joern.io
<https://github.com/RUB-SysSec/EvilCoder> automatic bug insertion using joern
phaser
slither

Hiding instructions in instructions
<https://lucris.lub.lu.se/ws/portalfiles/portal/78489284/nop_obfs.pdf>

Thomas stars <https://github.com/bsoddreams?tab=stars>

SGX enclaves

obfuscation
[snapchat](https://hot3eed.github.io/2020/06/18/snap_p1_obfuscations.html)
ollvm
vmprotect <https://github.com/void-stack/VMUnprotect>
opaque preciates - one branch always taken

chris domas <https://github.com/xoreaxeaxeax/movfuscator>
tom 7

[firmadyne](https://github.com/firmadyne/firmadyne) emulating and analyzing firmware

[dronesploit](https://github.com/dhondta/dronesploit)

burp suite
idor - autorize

bloodhound

shellcode encoding and decoding - sometimes you need to avoid things like \0 termination. <https://www.ired.team/offensive-security/code-injection-process-injection/writing-custom-shellcode-encoders-and-decoders>
Shellcode generators. What do they do?
[shellcode database](http://shell-storm.org/shellcode/)

[google dorking](https://github.com/iGotRootSRC/Dorkers) Like using google with special commands? Why "dork"?
shodan

# nmap

-A -T4. OS detection
nmap nse - nmap scriping engine. There is a folder of scripts

p0f - passive sniffing. fingerprinting

[malware reversing class](https://class.malware.re/)
[live overflow youtube](https://www.youtube.com/watch?v=iyAyN3GFM7A)
[](https://guyinatuxedo.github.io/00-intro/index.html)
[exploit education](https://exploit.education/)
[rop emporium](https://ropemporium.com/)
[linux exploitation course](https://twitter.com/binitamshah/status/1492855772384219138?s=20&t=Fyek6pLGPQrxADkntoVadg)
yara - patterns to recognize malware. Byte level patterns?
Sigma
snort

SIEM
IDS - intrusin detection systems
<https://en.wikipedia.org/wiki/Intrusion_detection_system>

shellcode encoder/decoder/generator
<https://www.msreverseengineering.com/blog/2017/7/15/the-synesthesia-shellcode-generator-code-release-and-future-directions>
synesthesia

FLIRT
<https://github.com/avast/retdec>

<https://github.com/grimm-co/NotQuite0DayFriday> exploit examples

Gray Hat Hacking
The Shellcoder's handbook
Attacking network Protocols
Implementing Effective Code Review

<https://objective-see.com/blog/blog_0x64.html>

Hacking:
<http://langsec.org/papers/Bratus.pdf> sergey weird machine paper

<https://github.com/sashs/filebytes>

blackhat
defcon
bluehat
ccc
<https://en.wikipedia.org/wiki/Security_BSides> bsides
ctf
project zero
kpaersky blog <https://usa.kaspersky.com/blog/>
spectre/meltdown
<https://www.youtube.com/watch?v=b7urNgLPJiQ&ab_channel=PinkDraconian>

return oriented programming sounds like my backwards pass.
Huh.

#### Digital forensics

- Volatility <https://www.volatilityfoundation.org/>
- wireshark
- sleuth kit?

radare2, a binary analysis thingo. rax is useful for conversion of hex

binary ninja

ghidra

IDA

RSACTFTool

factordb

manticore

Maybe we should get a docker of all sorts of tools. Kali Linux? [https://github.com/zardus/ctf-tools](https://github.com/zardus/ctf-tools)

klee, afl,  other fuzzers? valgrind

cwe-checker

shellcode

ROP

[https://quipqiup.com/](https://quipqiup.com/) - solve substitution cyphers

[https://github.com/openwall/john](https://github.com/openwall/john) john the ripper. Brute force password cracker

ropper

Best CTFs. I probably don't want the most prestigious ones? They'll be too high level? I want the simple stuff

<https://ctf101.org/> - check out the heap exploitation github thing

pwntools

metasploit, pacu - aws, cobalt strike

and the pwn category of ctf

ROP
JOP
SROP
BOP - block oriented

return 2 libc - a subset of rop?

#### pwn.college

ryan chapman syscall

<http://ref.x86asm.net/>

<https://github.com/revng/revng>

privilege escalation - getuid effective id.. Inherit user and group from parent process.
switching to user resets the setuid bit.
sticky bits
id command

shellcode - binary that launchs the shell system call execv("/bin/sh", NULL, NULL) - args and env params

intel vs at&t syntax
Load up addresses
constantrs in binary with .string
gcc -static -nostdlib
objcopy --section .text=outfile
exiting cleanly is smart. Helps know what is screwing up
ldd

Trying out shellcode
mmap. mprotect?
read()
deref function pointer

gdb
x for eXamine
$rsi
x/5i $rip gives assembly?
x/gx
break *0xx040404
n next
s step
ni
si

strace is useful first debugging

## Intro

system calls
set rax to syscall number.
call syscall instruction
<https://blog.rchapman.org/posts/Linux_System_Call_Table_for_x86_64/>
man yada
strace

- fork
- execve
- read
- write
- wait
- brk - program brk. change size of data segment. sbrk by increments. sbrk(0) returns current address of break

stack. rbp, rsp. stack grows down decreasing. Rsp + 0x8 is on stack, rbp - 8 is on stack
most systems are little endian
calling conventions. rdi rsi rdx rcx r8 r9, return in rax
rbx rbp r12 r13 r14 r15 are callee saved. guaranteed not smashed

<http://ref.x86asm.net/coder64.html> opcode listing
<https://github.com/yrp604/rappel> - assembly repl
<https://github.com/zardus/ctf-tools>

### binary files

    file - tells info about file
    elf - interpreter, 
     - sections - text, plt/got resolve and siprach library calls, data preinitilize data, rodata, global read only,, bss for uniitialized data. sections are not required to run a binary
     - symbols - 
    - segments - where to load

    readelf, objdump, nm - reads symbols, patchelf, objcopy, strip, kaitai struct https://www.intezer.com/blog/malware-analysis/executable-linkable-format-101-part-2-symbols/

### process loading

<https://0xax.gitbooks.io/linux-insides/content/SysCall/linux-syscall-4.html>
   what to load. look for #! or elf magic. /proc/sys/fs/binsmt_misc can match a string there. hand off to elf defined interpeter is dynamically linked.

   Then it's onto ld probably.
   LD_PRELOAD,, LD_LIBRARY_PATH,, DT_RUNTIME in binary file,, system wide /etc/ld.so.conf, /lib and /usr/lib
   relocations updated
   /proc/self/maps
   <https://gist.github.com/CMCDragonkai/10ab53654b2aa6ce55c11cfc5b2432a4>
   libc is almost always linked.
   printf, scanf, socket, atoi, amlloc, free

# shellcode

## Protection

ASLR - Addresses are randomized
cat /proc/mem/self ? To look at what actually loaded
Also ldd shows were libraries get loaded in memory
Stack canaries - set once per binary run, so with forking you can brute force them or maybe leak them?

checksec tells you about which things are enabled.

gcc options
-no-pie
-no-stack-protection

## pwntools

attaching to gdb and/or a process is really useful.
cyclic bytes can let you localize what ends up where in a buffer overflow for example
cyclic_find

## Examples from pwn.college
