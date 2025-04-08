---
title: "\"Verified\" \"Compilation\" of \"Python\" with Knuckledragger, GCC, and Ghidra"
date: 2025-04-08
---

I've been building out some interesting facilities for knuckledragger:

1. An interpreter of a functional subset of the python AST into z3.
2. A C printer / extraction out of a memory management free subset of z3py / smtlib
3. A Ghidra Pcode semantics from assembly to z3py / smtlib

During a conversation with Max Bernstein he paraphrased what I have as a python to C compiler. I hadn't really been thinking about it that way, but it does make for an interesting stunt. Maybe even a useful one. My goal today is to demonstrate a minimal viable product about how this could work together.

You can take a subset of python, reflect it into z3py, manipulate it to a compilable form, print as C, compile using gcc, then lift the assembly back up using pypcode and then turn that back into z3py to compare against the original problem and spec.

This gives a story that this is arguably "verified" assembly production, not perhaps in the manner that the output of [compcert](https://compcert.org/) is but not too far off from how [sel4](https://sel4.systems/)'s assembly code is verified.

![](/assets/knuckle_flow.png)

# Reflecting "Python" to SMTLib

The point of the reflection module of knuckledragger is to be able to use somewhat more natural python syntax as a shorthand for z3py. Python operator overloading does a good job for overloadable expressions. There are many pieces of python that are not overloadable in this manner. The ones most pasinfully felt and still mostly purely functional are the condition constructs `if-elif-else`, `match`, and boolean combinations like `and` `or`.

I had a design for how to deal with an "applicative" subset of python <https://www.philipzucker.com/applicative_python/> that in additi9on to pure expressions allows assignments modelled as `let` and simple conditional control flow that ends in `return`. The basic idea was to traverse the ast as parsed by `ast.parse`. The code that does all this is here <https://github.com/philzook58/knuckledragger/blob/9e0a90d6213d171827fc9b1a1ce85d2ab5999c1c/kdrag/reflect.py#L615>

Dealing with full imperative constructs like array mutation or loops requires more work. For serious emulating something closer to the full python semantics or object model takes outlandish amounts of work and seems of questionable use. Reflecting full-ish python to something compileable or JIT-able is a swamp with a lot of bodies on the road. See for example the Pytorch 2 paper <https://pytorch.org/assets/pytorch2-2.pdf> where they've churned through multiple approaches.

Another approach that I think might be too weird to be useful as anything other than a stunt was symbolically executing the python code <https://www.philipzucker.com/overload_bool/> .

Anyway, you can take a simple maximum function and reflect it into a knuckledragger definition via the `@kd.reflect` decorator. This decorator grabs the ast via `inspect`

```python
import kdrag.reflect as reflect
from kdrag.all import *

@reflect.reflect
def mymax(x : int, y : int) -> int:
    if x > y:
        return x
    else:
        return y

mymax.defn
```

&#8870;ForAll([x, y], mymax(x, y) == If(x > y, x, y))

`mymax` is now a z3 `FuncDeclRef` not a python function. When we call it, we get a symbolic form back.

```python
mymax(1,2)
```

    mymax(1, 2)

The original python function is avaiable under `__wrapped__`. Can use hypothesis fuzzing to help confirm does the same thing as the model.

```python
mymax.__wrapped__(1,2)
```

    2

We can prove a couple trivial properties about this function

```python
import kdrag.smt as smt
import kdrag as kd
x,y = smt.Ints('x y')
kd.prove(smt.ForAll([x,y], mymax(x,y) >= x), unfold=1)
kd.prove(smt.ForAll([x,y], smt.Or(mymax(x,y) <= y, mymax(x,y) <= x)), unfold=1)
```

&#8870;ForAll([x, y], Or(mymax(x, y) <= y, mymax(x, y) <= x))

# SMTLib to C Extraction

I have made an intentionally limited, direct printer of the z3py ast to C. The printer is coded in a direct style and to error out at print time if it hits any default cases.

At the moment, I only support pure expressions over `bool`, `uint8_t`, `uint16_t`, `uint32_t`, and `uint64_t` (pretty pathetic I know). I could in the future support full `int` via GMP, but that is a whole bag of worms. Basic structs should be doable. One of the reasons I made this is to print out specs to be discharged via CBMC.

So we need to connect our currently unimplementable `mymax` function over the integers into one that works over `uint64_t`. They should match on the parts of their shared domain.

It turns out that Integer to bitvector or real casts are not a strong suit of SMT solvers. Kind of a difficult theory I guess. I can get this to automatically prove for bitvector 8, but not for larger bitvector sizes.

```python
x,y = smt.BitVecs("x y", 8)
mymax8 = kd.define("mymax64", [x,y], smt.If(smt.UGT(x,y), x, y))

kd.prove(mymax(smt.BV2Int(x),smt.BV2Int(y)) == smt.BV2Int(mymax8(x,y)), unfold=1)
```

&#8870;mymax(BV2Int(x), BV2Int(y)) == BV2Int(mymax64(x, y))

Fear not! The point of knuckledragger is to being able to go somewhat interactive when you hit a wall like this. I should have more axioms in my stdlib for BV2Int or build up the proofs of the relevant properties. But here we can show using more basic properties of BV2Int to show the equivalence of `mymax` anmd `mymax64` on some inputs.

```python
x,y = smt.BitVecs("x y", 64)
mymax64 = kd.define("mymax64", [x,y], smt.If(smt.UGT(x,y), x, y))

# Two basic facts about BV2Int
bv2int_gt = kd.axiom(smt.ForAll([x,y], (smt.BV2Int(x) > smt.BV2Int(y)) == smt.UGT(x, y)))
c = smt.Bool("c")
bv2int_ite = kd.axiom(smt.ForAll([c,x,y], smt.BV2Int(smt.If(c,x,y)) == smt.If(c,smt.BV2Int(x),smt.BV2Int(y))))

l = kd.Lemma(mymax(smt.BV2Int(x),smt.BV2Int(y)) == smt.BV2Int(mymax64(x,y)))
l.unfold() # unfold definitions of mymax and mymax64
l.rw(bv2int_gt)
l.rw(bv2int_ite)
l.auto()
l.qed()
```

&#8870;mymax(BV2Int(x), BV2Int(y)) == BV2Int(mymax64(x, y))

I'll also note that if you squint, SMTLIB is kind of a barebones first order functional programming language just as much as it is a logic. One that has solver superpowers. `define-fun-rec` + datatypes in particular makes this true. I think this could be an interesting target for a compilers course as discussed by Neel Krishnaswami here <https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html>

The code for this printer is here <https://github.com/philzook58/knuckledragger/blob/9e0a90d6213d171827fc9b1a1ce85d2ab5999c1c/kdrag/printers/c.py#L170> It's pretty straightforward

```python
from kdrag.all import *
import kdrag.printers.c as Cprint


print(Cprint.of_defn(mymax64))
```

    #include <stdint.h>
    #include <stdbool.h>
    uint64_t mymax64(uint64_t x, uint64_t y){
        return ((x > y) ? x : y);
    }
    

As a cute feature, I also have the ability to dynamically link in the resulting code and run it. Vaguely, I know that in Lean, Coq etc it is known that proof by reflection is a useful technique. The fastest way to _prove_ that you get a result from running a program on concrete inputs is to just run it. Also in many respects proofs themselves are the trace objects of proof checking or proof searching / producing programs. If you're doing this, it's important to have a fast runtime and probably python level rewrite rules aren't it. I haven't decided how I should do this, but baby steps.

We can also directly compile and link and then use the resulting function via cffi inside of python.

```python
lib = Cprint.compile_and_link_defn(mymax64)
lib.mymax64(1,17)
```

    17

But now we want to explore the assembly itself. `compile_c` is a simple wrapper to a subprocess call of gcc.

```python
Cprint.compile_c(Cprint.of_defn(mymax64), opts=["-O3"])
```

    '/tmp/tmpz7awy5lg/temp.so'

# Ghidra PCode

I'm kind of bullish on Ghidra PCode as an underutilized source of assembly semantics. Ghidra <https://ghidra-sre.org/> is a reverse engineering tool made by the NSA with about 25 years of work in it. It probably isn't going anywhere. In the right circles it's a huge brand name, but in the compiler / PL circles not so much, which I find an interesting example of siloing. I think it is a possible pragmatic alternative to Sail, ASLp, LLVM for some purposes.

The underlying semantics of ghidra is written in a DSL called SLEIGH. <https://spinsel.dev/assets/2020-06-17-ghidra-brainfuck-processor-1/ghidra_docs/language_spec/html/sleigh.html> "This piece of SLEIGH was originally a separate language, the Semantic Syntax Language (SSL), very loosely based on concepts and a language of the same name developed by Cristina Cifuentes, Mike Van Emmerik and Norman Ramsey, for the University of Queensland Binary Translator (UQBT) project."
<https://github.com/rbran/sleigh-rs>

PCode is the intermediate representation. Pcode is a simple assembly like language of about 30 operations. Itt has arithmetic, stores, loads, conditions and branches mostly. The state of a pcode execution is a program counter and memory. Memory is made of different spaces, each of which is indexable bytes. Registers, actual ram, unique temporary vars, and constants are all different memory spaces which are used uniformaly. Varnodes are the combination of a space index, offsert, and size.

The program counter is an address and a pcode index inside that address. Each real assembly instruction usually compiles to multiple pcode instructions. There can be and needs to be intra assembly instruction pcode relative jumps to model things like conditional moves.

PCode comes vaguely in two varieties High and Low pcode. High pcode comes out of the decompiler. Low pcode is what we're interested in comes out of the lifters

A lesson I have learned <https://www.philipzucker.com/cody_sheffer/> is that I should try to follow existing code or proofs much more closely than I a priori expect to. I should not change names unless necessary. I should not change subproofs. I should not have any respect for my short term memory or ability to perform trivial translations in my head. They pile on fast.

In addition, following the original "spec" code makes a better story that I got it right and that someone can come and audit it later.
The spec of many computational systems is basically an interpreter. The word spec, or mathematical, logical or notational fluff can kind of confuse this and intimidate. Many programmers kind of get the idea of an interpreter.

The c++ code for the ghidra emulator is actually pretty readable and simple. Basically I needed to purify it to explicitly carry around the memory state. I tried to follow the exact code as much as possible including names for my interpreter.
<https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc>
<https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc#L126>

The code of my interpreter is here
<https://github.com/philzook58/knuckledragger/blob/9e0a90d6213d171827fc9b1a1ce85d2ab5999c1c/kdrag/contrib/pcode/__init__.py#L223>

We can take a look at the assembly using objdump.

```python
!objdump -d -F /tmp/tmpgm1gfzq0/temp.so | grep -A 20 "mymax64" 
```

    0000000000001100 <mymax64> (File Offset: 0x1100):
        1100: f3 0f 1e fa           endbr64
        1104: 48 39 fe              cmp    %rdi,%rsi
        1107: 48 89 f8              mov    %rdi,%rax
        110a: 48 0f 43 c6           cmovae %rsi,%rax
        110e: c3                    ret
    
    Disassembly of section .fini:
    
    0000000000001110 <_fini> (File Offset: 0x1110):
        1110: f3 0f 1e fa           endbr64
        1114: 48 83 ec 08           sub    $0x8,%rsp
        1118: 48 83 c4 08           add    $0x8,%rsp
        111c: c3                    ret

Angr <https://angr.io/> is a prominent binary analysis platform for Python. It supports loading and symbolically executing binaries.

The two main place it gets its assembly semantics from are VEX (valgrind) and PCode (ghidra). An appeal of knuckledragger is that I'm supposed to be able to reuse the insane python ecosystem to get distance for cheap. I wanted and consider it a feature to be able to use angr off the shelf, but found it confusing to modify it to my needs. I couldn't get it to work after a few weeks of on and off tinkering. In addition, the symbolic executor uses an abstraction layer claripy instead of z3 directly and doesn't even seem to support smtlib Arrays which seems like a nail in the coffin in terms of using my intended memory model. Angr was not designed for my intended use case (as complete and sound semantics of the binary as is feasible) and it instead of focussed on drilling to find buigs ands vulnerabilities.

Still the project does have some of its pieces separately installable. The existance of `pypcode` <https://github.com/angr/pypcode> and `cle` <https://github.com/angr/cle> are huge boons.

`BinaryContext` is in many ways the analog of an angr `Project`. It is frustrating that I think I am replicating a lot of work that is already inside angr, but  whatyagonnado.

Here I load the binary, find the `mymax64` symbol, and then symbolically execute it. On each branch (the conditional move `cmovae` branches in our pcode rep) we prove that the result in `RAX` is the same value as if we ran our higher level `mymax64` function

```python
import kdrag.contrib.pcode as pcode
from kdrag.all import *
ctx = pcode.BinaryContext("/tmp/tmpgm1gfzq0/temp.so")
mymax64_sym = ctx.loader.find_symbol("mymax64") # find the address of the symbol

# initialize the memory state with the arguments
mem = pcode.MemState.Const("mem")

x,y = smt.Consts("x y", smt.BitVecSort(64))
mem = mem.setvalue(ctx.ctx.registers["RDI"], x)
mem = mem.setvalue(ctx.ctx.registers["RSI"], y)

symstates = ctx.sym_execute(mem, mymax64_sym.rebased_addr, max_insns=4)
for memstate, pc, pathcond in symstates:
    res = memstate.getvalue(ctx.ctx.registers["RAX"])
    kd.prove(kd.QForAll([x,y], smt.And(pathcond), mymax64(x,y) == res), by=[mymax64.defn])

```

# Bits and Bobbles

What I'm excited about is an idea about how to make the above a rigorous statement. The pcode lifter requires a concrete address to work.
The knuckledragger idea is that there is a protected datatype of `kd.Proof` that you only get via calls to `kd.prove` or `kd.axiom`. What we can do is make each binary have an axiom schema of it's behavior at each address. Axiom schema can be python functions. We can add a function to our BinaryContext class that looks like this.

```python
   def exec_axiom(self, addr : int):
        return kd.axiom(smt.ForAll([memstate]), executeOp(self.hash, memstate, addr) == self.executeOp(memstate, addr))
```

The first `executeOp` is a z3 FuncDecl, but the second `self.executeOp` is the python function that actually lifts. This gives us core facts that we can use the knuckeldragger reasoning mechanisms to build larger and larger statements about what the assembly actually does. Note that executeOp is dependent on the binary itself and the decision about where to load it in the form of a hash of the `BinaryContext`.

This reminds me a bit of the datalog disassembler <https://github.com/GrammaTech/ddisasm> which lifted every offset of the binary. Even determining what is code and what is data or instruction boundaries requires control flow reconstruction which is impossible in general (you could encode some halting problem into it).

I think it would be fun to start to build verified abstract interpretations into knuckledragger. Disassembly, Abstract interpretation, decompilation, and symbolic execution are _proof tactics_ from this perspective. HOOOOO BOY. GOOD SHIT.

I need to work on the readability of the lifting. Perhaps I shoukld change my memory model to be 64 -> 64 insterad of 64->8. I would have to translate my addresses, but I think it might be more readable in regards to the data at the addresses.

There is always junction between the formal and informal, because we are informal beings, living in an informal world with informal applications and goals. This is true even for pure mathematics. The mental picture of the mathematician and the exact syntax and rules of the formal system are not a priori in alignment.

Like a weld between disparate materials, this juncture is often a weakpoint of formal modelling of the system and thus should be explicitly tested. Tests are the greatest commonality between the two worlds and are applicable in both. I also have built some facilities for using hypothesis to fuzz between z3 versions and python versions of things

Also tinkering on Rust and Lean printers. Rust is easier to print safe forms of and can be discharged via Kani. Implement ADTs via `Rc`. Lean is eating the proof assitant world but is also a nice functional programming language.

Smtlib extras in cbat <https://github.com/draperlaboratory/cbat_tools/pull/340> . Having multistore and multiselect in smtlib would be nice. It is awkward to read and write them. SMTLib readability and interpretability is really important for experimentation and debuggibng. It enablesy ou try out new encodings without building a whole thing.
I've found it interesting that encoding tircks one might try to imporiove the encoding sometimes have physical reality. Tagged architectures can be ghost modelled.

ASLp <https://github.com/UQ-PAC/aslp>

Direct riscv interpeter

SPIKE interpreter. <https://github.com/riscv-software-src/riscv-isa-sim>

Csimple of yosys. Using CBMC as a piece of the chain is compelling. Yosys used a Csimple backend to use CBMC to compare it's verilog implementation against the spike interpreter C semantics. Clever.

Islaris <https://github.com/rems-project/islaris>

This post is a relative of

- <https://www.philipzucker.com/pcode2c/>
- <https://www.philipzucker.com/pcode2c-dwarf/>
- <https://www.philipzucker.com/bap-chc/>

I've been tinkering with binary + smt for years at this point.

 There is a claim that this chain is more "verified" than other approaches in the sense it is linked through a formal system of knuckledragger/z3.

What now, very hard to read semantics. 1. make them more readable. 2.

```python
insn = ctx.disassemble(foo_sym.rebased_addr)
#print(insn)
pcode.pretty_insn(insn)
addr = foo_sym.rebased_addr + 4
print(pcode.pretty_insn(ctx.disassemble(addr + 7)))

for n, op in enumerate(ctx.translate(addr + 4)):
    nextmem, pc = ctx.executeCurrentOp(op, mem, (addr, n))

        #kd.prove(smt.ForAll([x,y], smt.Or(x == res, y == res)))
    #s.add(smt.Not(smt.Or(res == x)))

    kd.prove(smt.ForAll([x,y], smt.Or(x == res, y == res)), timeout=10000)
    kd.prove(kd.QForAll([x,y], smt.And(pathcond), smt.And(smt.UGE(res, x), smt.UGE(res, y))), timeout=10000)
```

```python
import cle
import pypcode
class BinaryContext():
    def __init__(self, filename):
        self.pcode_cache = {}
        self.insn_cache = {}
        self.filename = filename
        self.ld = cle.loader.Loader(filename)
        self.bin_hash = None
        self.ctx = pypcode.Context("x86:LE:64:default")
    def disassemble(self, addr):
        if addr in self.insn_cache:
            return self.insn_cache[addr]
        memory = self.ld.memory.load(addr, addr, 0x128) # 128 bytes? good enough?
        for insn in self.ctx.disassemble(addr, 0).instructions:
            self.insn_cache[insn.addr] = insn
        return self.insn_cache[addr]
    def translate(self, addr, offset, max_size): ...        
    def execute1(self, memstate, pc): ...



BinaryContext(so_file)
```

    <__main__.BinaryContext at 0x7cb03c731910>

```python
from kdrag.all import *
import kdrag.printers.c as Cprint



x,y = smt.BitVecs("x y", 64)
so_file = Cprint.compile_c(Cprint.cstring("foo", [x,y], smt.If(smt.UGT(x + x*y + 1, x), x , y)), opts=["-O3"])
so_file

```

```python
    def execute1_ax(self, pc): # axiom schema form
        memstate = smt.Const("memstate", Memstate)
        body = self.execute1(memstate, pc)
        smt.Function("execute1_next", LoadData,  MemState, PC, PC)
        smt.Function("execute1_exec", LoadData, MemState, PC,  MemState) # Or make internalized tuple. PCMemState
        return  kd.axiom(smt.ForAll([memstate], execute1_exec(memstate, pc) == body[0])),
                kd.axiom(smt.ForAll([memstate], execute1_next(memstate, pc) == body[1]))
```

      Cell In[14], line 7
        kd.axiom(smt.ForAll([memstate], execute1_next(memstate, pc) == body[1]))
        ^
    IndentationError: unexpected indent

785 + 0 * RAX  maybe a light weight way of annotating expressions. Known fuseaways

```python
import cle
ld = cle.Loader(so_file)
foo_sym = ld.find_symbol("foo")
code = ld.memory.load(foo_sym.rebased_addr, foo_sym.size)

```

```python
hex(foo_sym.relative_addr)
```

    '0x10f9'

```python
import pypcode
ctx = pypcode.Context("x86:LE:64:default")
for ins in ctx.disassemble(code, foo_sym.rebased_addr, 0).instructions:
    print(f"{ins.addr.offset:#x}/{ins.length}: {ins.mnem} {ins.body}")
for op in ctx.translate(code, foo_sym.rebased_addr, 0).ops: #ctx.disassemble(code, foo_sym.rebased_addr, 0):
    print(pypcode.PcodePrettyPrinter.fmt_op(op))
```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[1], line 3
          1 import pypcode
          2 ctx = pypcode.Context("x86:LE:64:default")
    ----> 3 for ins in ctx.disassemble(code, foo_sym.rebased_addr, 0).instructions:
          4     print(f"{ins.addr.offset:#x}/{ins.length}: {ins.mnem} {ins.body}")
          5 for op in ctx.translate(code, foo_sym.rebased_addr, 0).ops: #ctx.disassemble(code, foo_sym.rebased_addr, 0):


    NameError: name 'code' is not defined

```python
from kdrag.contrib.pcode import unop, binop
import kdrag.theories.bitvec as bv

def executeCurrentOp(op, memstate, pc):
    opcode = op.opcode
    if op.opcode == pypcode.OpCode.IMARK:
        return memstate, fallthruOp(pc)
    elif op.opcode == pypcode.OpCode.LOAD:
        return executeLoad(op, memstate), fallthruOp(pc)
    elif op.opcode == pypcode.OpCode.STORE:
        return executeStore(op, memstate), fallthruOp(pc)
    elif op.opcode == pypcode.OpCode.BRANCH:
        return memstate, executeBranch(op, pc)
    elif op.opcode == pypcode.OpCode.CBRANCH:
        cond = executeCBranch(op, memstate)
        (addr1, pcode_pc1) = executeBranch(op, pc)
        (addr2, pcode_pc2) = fallThruOp(pc)
        return memstate, (smt.If(cond, addr1, addr2), smt.If(cond, pcode_pc1, pcode_pc2))
    elif op.opcode in unop:
        return executeUnary(op, memstate), fallthruOp(pc)
    elif op.opcode in binop:
        print(op, memstate)
        return executeBinary(op, memstate), fallthruOp(pc)
    else:
        raise NotImplementedError("Opcode not implemented: ", op.opcode)    

def executeUnary(op, memstate):
    in1 = memstate.getvalue(op.inputs[0])
    out = unop[op.opcode](in1)
    return memstate.setvalue(op.output, out)

def executeBinary(op, memstate):
    in1 = memstate.getvalue(op.inputs[0])
    in2 = memstate.getvalue(op.inputs[1])
    out = binop[op.opcode](in1, in2)
    return memstate.setvalue(op.output, out)

def executeLoad(op, memstate):
    off = memstate.getvalue(op.inputs[1]) # offset to load from
    spc = memstate.getvalue(op.inputs[0]) # memory space
    return memstate.setvalue(op.output, memstate.getvalue_ram(off))

def executeStore(op, memstate):
    val = memstate.getvalue(op.inputs[2]) # value being stored
    off = memstate.getvalue(op.inputs[1]) # offset to store at
    spc = memstate.getvalue(op.inputs[0]) # memory space
    print(spc)
    memstate.setvalue_ram(off, val)

def fallthruOp(pc):
    addr, pcode_pc = pc
    pcode_pc += 1
    if pcode_pc >= len(pcode_cache[addr][1]):
        addr += pcode_cache[addr][0].length
        return (addr, 0)
    else:
        return (addr, pcode_pc)

def executeBranch(op, pc):
    addr, pcode_pc = pc
    destaddr = op.inputs[0]
    if destaddr.space.name == "constant":
        pcode_pc += destaddr.offset
        if pcode_pc == len(pcode_cache[addr][1]):
            fallthruOp((addr, pcode_pc))
        elif pcode_pc < 0 or pcode_pc >= len(pcode_cache[addr][1]):
            raise ValueError(f"Lowlevel Error. Bad intra-instruction branch: {pcode_pc}")
        else:
            return (addr, pcode_pc)
    elif destaddr.space.name == "ram":
        return (destaddr.offset, 0)
    else:
        raise ValueError(f"Unknown branch target: {destaddr.space.name}")

def executeCbranch(op, memstate):
    cond = memstate.getvalue(op.inputs[1])
    return cond != 0

MemSort = smt.ArraySort(smt.BitVecSort(64), smt.BitVecSort(8))
MemStateSort = kd.Struct("MemState", ("ram" , MemSort), ("register", MemSort), ("unique", MemSort))

from dataclasses import dataclass
@dataclass
class MemState():
    mem : smt.DatatypeRef
    def __init__(self, mem):
        self.mem = mem
    def getvalue(self, vnode):
        if vnode.space.name == "const":
            return vnode.offset
        else:
            mem = getattr(self.mem, vnode.space.name)
            if mem is None:
                raise ValueError(f"Unknown memory space: {vnode.space.name}")
            return bv.SelectConcat(mem, vnode.offset, vnode.size)
    def setvalue(self, vnode, value):
        assert vnode.space.name != "const"
        return MemState(self.mem._replace(**{vnode.space.name: bv.StoreConcat(getattr(self.mem, vnode.space.name), addr, value)}))
    def setvalue_ram(self, offset, value):
        return MemState(self.mem._replace(ram = bv.StoreConcat(self.mem.ram, offset, value)))


```

```python
smt.Array("mem", smt.Biv64, 8)
```

```python

pcode_cache = {}
def execute1(code, rebased_addr, offset):
    insn = ctx.disassemble(code, rebased_addr, offset, max_instructions=1).instructions[0]
    print(f"{insn.addr.offset:#x}/{insn.length}: {insn.mnem} {insn.body}")
    ops = ctx.translate(code, rebased_addr, offset, max_bytes=insn.length).ops
    pcode_cache[rebased_addr] = insn, ops
    pc = (rebased_addr, 0)
    memstate = MemState(smt.Const("mem", MemStateSort))
    addr = rebased_addr
    for op in ops:
        print(pypcode.PcodePrettyPrinter.fmt_op(op))
        if op.opcode == pypcode.OpCode.IMARK:
            addr = op.inputs[0].offset
            pcode_pc = 0
        memstate, pc = executeCurrentOp(op, memstate, pc)
        print(memstate, pc)
    return memstate, pc

execute1(code, foo_sym.rebased_addr, 4)
```

    0x4010f9/1: PUSH RBP
    IMARK ram[4010f9:1]
    MemState(mem=mem) (4198649, 1)
    unique[10c00:8] = RBP
    MemState(mem=MemState(ram(mem),
             register(mem),
             Store(Store(Store(Store(Store(Store(Store(Store(unique(mem),
                                            4198649,
                                            Extract(7,
                                            0,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198650,
                                            Extract(15,
                                            8,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198651,
                                            Extract(23,
                                            16,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                           4198652,
                                           Extract(31,
                                            24,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                     4198653,
                                     Extract(39,
                                            32,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                               4198654,
                               Extract(47,
                                       40,
                                       Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                         4198655,
                         Extract(55,
                                 48,
                                 Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                        register(mem)[40]))),
                   4198656,
                   Extract(63,
                           56,
                           Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                         register(mem)[41]),
                                  register(mem)[40]))))) (4198649, 2)
    RSP = RSP - 0x8
    <pypcode.pypcode_native.PcodeOp object at 0x7c647f324810> MemState(mem=MemState(ram(mem),
             register(mem),
             Store(Store(Store(Store(Store(Store(Store(Store(unique(mem),
                                            4198649,
                                            Extract(7,
                                            0,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198650,
                                            Extract(15,
                                            8,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198651,
                                            Extract(23,
                                            16,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                           4198652,
                                           Extract(31,
                                            24,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                     4198653,
                                     Extract(39,
                                            32,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                               4198654,
                               Extract(47,
                                       40,
                                       Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                         4198655,
                         Extract(55,
                                 48,
                                 Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                        register(mem)[40]))),
                   4198656,
                   Extract(63,
                           56,
                           Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(mem)[47],
                                            register(mem)[46]),
                                            register(mem)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                         register(mem)[41]),
                                  register(mem)[40])))))
    MemState(mem=MemState(ram(mem),
             Store(Store(Store(Store(Store(Store(Store(Store(register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(Store(Store(Store(Store(Store(unique(mem),
                                            4198649,
                                            Extract(7,
                                            0,
                                            Concat(..., ...))),
                                            4198650,
                                            Extract(15,
                                            8,
                                            Concat(Concat(...,
                                            ...),
                                            ...[...]))),
                                            4198651,
                                            Extract(23,
                                            16,
                                            Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[40]))),
                                            4198652,
                                            Extract(31,
                                            24,
                                            Concat(Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[41]),
                                            register(mem)[40]))),
                                            4198653,
                                            Extract(39,
                                            32,
                                            Concat(Concat(Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198654,
                                            Extract(47,
                                            40,
                                            Concat(Concat(Concat(Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198655,
                                            Extract(55,
                                            48,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))),
                                            4198656,
                                            Extract(63,
                                            56,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(...[...],
                                            ...[...]),
                                            register(...)[45]),
                                            register(mem)[44]),
                                            register(mem)[43]),
                                            register(mem)[42]),
                                            register(mem)[41]),
                                            register(mem)[40]))))),
                                            4198649,
                                            Extract(7,
                                            0,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(MemState(...,
                                            ...,
                                            ...))[39],
                                            register(MemState(...,
                                            ...,
                                            ...))[38]),
                                            register(MemState(ram(...),
                                            register(...),
                                            Store(..., ..., ...)))[37]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(...,
                                            ...,
                                            ...),
                                            4198656,
                                            Extract(63, 56, ...))))[36]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(...,
                                            ...,
                                            ...),
                                            4198655,
                                            Extract(55, 48, ...)),
                                            4198656,
                                            Extract(63,
                                            56,
                                            Concat(..., ...)))))[35]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(Store(...,
                                            ...,
                                            ...),
                                            4198654,
                                            Extract(47, 40, ...)),
                                            4198655,
                                            Extract(55,
                                            48,
                                            Concat(..., ...))),
                                            4198656,
                                            Extract(63,
                                            56,
                                            Concat(Concat(...,
                                            ...),
                                            ...[...])))))[34]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(Store(Store(...,
                                            ...,
                                            ...),
                                            4198653,
                                            Extract(39, 32, ...)),
                                            4198654,
                                            Extract(47,
                                            40,
                                            Concat(..., ...))),
                                            4198655,
                                            Extract(55,
                                            48,
                                            Concat(Concat(...,
                                            ...),
                                            ...[...]))),
                                            4198656,
                                            Extract(63,
                                            56,
                                            Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[40])))))[33]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(Store(Store(Store(...,
                                            ...,
                                            ...),
                                            4198652,
                                            Extract(31, 24, ...)),
                                            4198653,
                                            Extract(39,
                                            32,
                                            Concat(..., ...))),
                                            4198654,
                                            Extract(47,
                                            40,
                                            Concat(Concat(...,
                                            ...),
                                            ...[...]))),
                                            4198655,
                                            Extract(55,
                                            48,
                                            Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[40]))),
                                            4198656,
                                            Extract(63,
                                            56,
                                            Concat(Concat(Concat(Concat(...,
                                            ...),
                                            ...[...]),
                                            register(...)[41]),
                                            register(mem)[40])))))[32]) -
                                            8)),
                                            4198650,
                                            Extract(15,
                                            8,
                                            Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(MemState(ram(...),
                                            register(...),
                                            Store(..., ..., ...)))[39],
                                            register(MemState(ram(...),
                                            register(...),
                                            Store(..., ..., ...)))[38]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(...,
                                            ...,
                                            ...),
                                            4198656,
                                            Extract(63, 56, ...))))[37]),
                                            register(MemState(ram(mem),
                                            register(mem),
                                            Store(Store(Store(...,
                                            ...,
                                            ...),
                                            4198655,
                                            Extract(55, 48, ...)),
                                            4198656,
                                            Extract(63,
                                            56,
    ...) (4198649, 3)
    *[ram]RSP = unique[10c00:8]
    430399600
    None (4198650, 0)





    (None, (4198650, 0))

```python

```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[2], line 13
         10     def translate(self, addr, offset, max_size): ...
         11     def execute1(self, memstate, pc): ...
    ---> 13 BinaryContext(so_file)


    Cell In[2], line 6, in BinaryContext.__init__(self, filename)
          4 self.insn_cache = {}
          5 self.filename = filename
    ----> 6 self.ld = cle.loader.Loader(filename)
          7 self.bin_hash = None
          8 self.ctx = pypcode.Context(self.ld.arch)


    NameError: name 'cle' is not defined

```python
def sym_execute(self, memstate, addr, trace=None, max_insns=1):
    pc = (addr, 0)
    todo = [(memstate, pc, max_insns)]
    res = []
    while todo:
        memstate, pc, max_insns = todo.pop()
        memstate1, pc1 = self.executeCurrentOp(memstate, pc)
        for addr, pcode_pc in kd.utils.models(pc1):
            if addr != pc[0]:
                max_insns -= 1
            pc = (addr, pcode_pc)
            if max_insns > 0:
                todo.append((memstate, pc, max_insns))
            else:
                res.append((memstate, pc))
    return res
```

You know, readability wise, we'd be better off using an array(64,64)

concat(  ,  , select(select(addr >> 2)))

Cleanness will depend on whether common case is word or half word vs byte manipulations.
Byte miauplations oinly pay 3 junk, but word manipulations pay 8 junk.
Byte manipulatin doesn't mangle the constants

If we don't get a conrete address, use finite model expansion to figure out all possible addresses

```python

addr = foo_sym.rebased_addr  
pcode_pc = 0  
memstate = MemState(smt.Const("mem", MemStateSort))


"""
for op in ctx.translate(code, foo_sym.rebased_addr, max_intructions=1).ops:
    pcode_pc += 1
    if op.opcode == pypcode.OpCode.IMARK:
        addr = op.inputs[0].offset
        pcode_pc = 0
    print(pypcode.PcodePrettyPrinter.fmt_op(op))
    executeCurrentOp(op, memstate, (addr, pcode_pc))
"""


```

```python
import functools
import pypcode
unop = {
    OpCode.COPY : lambda x: x,
    OpCode.INT_2COMP : operator.neg,
    OpCode.INT_NEGATE : operator.invert,
    OpCode.BOOL_NEGATE : lambda x: smt.If(x == TRUE, FALSE, TRUE),
}

binop = {
    OpCode.INT_ADD: operator.add,
    OpCode.INT_SUB: operator.sub,


    OpCode.INT_XOR: operator.xor,
    OpCode.INT_AND: operator.and_,
    OpCode.INT_OR: operator.or_,
    OpCode.INT_LEFT: operator.lshift,
    OpCode.INT_RIGHT: smt.LShR,
    OpCode.INT_SRIGHT: operator.rshift,
    OpCode.INT_MULT: operator.mul,
    OpCode.INT_DIV: smt.UDiv,
    OpCode.INT_REM: smt.URem,
    OpCode.INT_SDIV: operator.truediv,
    OpCode.INT_SREM: smt.SRem,

    OpCode.BOOL_XOR: lambda x,y: smt.If(x == y, FALSE, TRUE),
    OpCode.BOOL_AND: operator.and_,
    OpCode.BOOL_OR: operator.or_,
}

comp = {
    OpCode.INT_EQUAL: operator.eq,
    OpCode.INT_NOTEQUAL: operator.ne,
    OpCode.INT_LESS: smt.ULT,
    OpCode.INT_SLESS: operator.lt,
    OpCode.INT_LESSEQUAL: smt.ULE,
    OpCode.INT_SLESSEQUAL: operator.le,
    OpCode.INT_CARRY: None, # TODO
    OpCode.INT_SCARRY: None, # TODO
    OpCode.INT_SBORROW: None, # TODO
}


@functools.cache
def REG(name, offset):
    return kd.define(name, [], smt.BitVecVal(offset, 64))

def z3_of_varnode(vnode, state):
    print(vnode.space.name)
    if vnode.space.name == "const":
        return vnode.offset
    elif vnode.space.name == "register":
        return bv.SelectConcat(getattr(state, vnode.space.name), REG(vnode.getRegisterName(), vnode.offset), vnode.size)
    else:
        #print(vnode.space.name)
        return bv.SelectConcat(getattr(state, vnode.space.name), vnode.offset, vnode.size)

def store(state, vnode, value):
    if vnode.space.name == "register":
        return state._replace(register=smt.Store(state.register, REG(vnode.getRegisterName(), vnode.offset), value))
    elif vnode.space.name == "ram":
        return state._replace(ram=smt.Store(state.ram, vnode.offset, value))
    elif vnode.space.name == "unique":
        return state._replace(ram=smt.Store(state.unique, vnode.offset, value))
    else:
        raise NotImplementedError("space not implemented", vnode.space.name)

def z3_of_op(op, state):
    opcode = op.opcode
    if opcode == OpCode.IMARK:
        return state
    elif opcode in binop:
        #assert isinstance(opcode, pypcode.OpFormatBinary)
        src1 = z3_of_varnode(op.inputs[0], state)
        src2 = z3_of_varnode(op.inputs[1], state)
        return store(state, op.output, binop[op.opcode](src1, src2))
    elif opcode in unop:
        src = z3_of_varnode(op.inputs[0], state)
        return store(state, op.output, unop[op.opcode](src))
    elif opcode in comp:
        src1 = z3_of_varnode(op.inputs[0], state)
        src2 = z3_of_varnode(op.inputs[1], state)
        return store(state, op.output, smt.If(comp[op.opcode](src1,src2), TRUE, FALSE))
    else:
        raise NotImplementedError("opcode not implemented", op.opcode)

```

```python
tx = ctx.translate(b"\xb8\x05\x00\x00\x00\xbb\x0a\x00\x00\x00\x8d\x0c\x18\x0f\xaf\xd8"
)#b"\xb8\x05\x00\x00\x00")
state = smt.Const("init", State)
for op in tx.ops:
    print(PcodePrettyPrinter.fmt_op(op))
    state = z3_of_op(op, state)
print(state)
```

    IMARK ram[0:5]
    RAX = 0x5
    const
    IMARK ram[5:5]
    RBX = 0xa
    const
    IMARK ram[a:3]
    unique[4600:8] = RBX * 0x1
    register
    const



    ---------------------------------------------------------------------------

    Z3Exception                               Traceback (most recent call last)

    Cell In[47], line 6
          4 for op in tx.ops:
          5     print(PcodePrettyPrinter.fmt_op(op))
    ----> 6     state = z3_of_op(op, state)
          7 print(state)


    Cell In[46], line 77, in z3_of_op(op, state)
         75     src1 = z3_of_varnode(op.inputs[0], state)
         76     src2 = z3_of_varnode(op.inputs[1], state)
    ---> 77     return store(state, op.output, binop[op.opcode](src1, src2))
         78 elif opcode in unop:
         79     src = z3_of_varnode(op.inputs[0], state)


    Cell In[46], line 65, in store(state, vnode, value)
         63     return state._replace(ram=smt.Store(state.ram, vnode.offset, value))
         64 elif vnode.space.name == "unique":
    ---> 65     return state._replace(ram=smt.Store(state.unique, vnode.offset, value))
         66 else:
         67     raise NotImplementedError("space not implemented", vnode.space.name)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3.py:4857, in Store(a, *args)
       4843 def Store(a, *args):
       4844     """Return a Z3 store array expression.
       4845 
       4846     >>> a    = Array('a', IntSort(), IntSort())
       (...)
       4855     proved
       4856     """
    -> 4857     return Update(a, args)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3.py:4825, in Update(a, *args)
       4823     i = a.sort().domain().cast(i)
       4824     v = a.sort().range().cast(v)
    -> 4825     return _to_expr_ref(Z3_mk_store(ctx.ref(), a.as_ast(), i.as_ast(), v.as_ast()), ctx)
       4826 v = a.sort().range().cast(args[-1])
       4827 idxs = [a.sort().domain_n(i).cast(args[i]) for i in range(len(args)-1)]


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3core.py:2287, in Z3_mk_store(a0, a1, a2, a3, _elems)
       2285 def Z3_mk_store(a0, a1, a2, a3, _elems=Elementaries(_lib.Z3_mk_store)):
       2286   r = _elems.f(a0, a1, a2, a3)
    -> 2287   _elems.Check(a0)
       2288   return r


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3core.py:1570, in Elementaries.Check(self, ctx)
       1568 err = self.get_error_code(ctx)
       1569 if err != self.OK:
    -> 1570     raise self.Exception(self.get_error_message(ctx, err))


    Z3Exception: b'domain sort (_ BitVec 64) and parameter sort (_ BitVec 8) do not match'

```python
PC = smt.BitVec("PC", 64)
state = smt.Const("state", State)
undef = smt.Function("undef", smt.BitVecSort(64), State)
fetch = smt.Function("fetch", smt.BitVecSort(64), State, State)
fetch = kd.define("fetch", [PC, op_num, state],
    kd.cond(
(PC == 0,  insn_0(state))
        default=undef(PC)
    )              
    )



```

symbolic execution. metalayer PC opnum. State is symbolic.
deep embed pcode instructions. deep embed interpreter.
Specialize to particular program.
I can also specialize the fields. to flip them up to the metalayer.
I don't have to reveal all at once.

There could be an axiom schema for the program.

discovery of control flow is part of proof burden

lazy every possible address, kind of like datalog disassembly

is it ok that we can have non terminating loops?

Well. actually both of these are in just pure "data" forms. The fixed point hasn't been asserted.

```python
executeCurrentOp = kd.define("executeCurrentOp", [PC, opnum, state], state)
def executecurrentOp(PC, opnum, op):
    insn = pypcode.tx(addr)
    insn.ops[opnum]

@functools.cache
def exec_ax(addr, opnum):
    op = tx.translate(addr,opnum)
    kd.axiom(smt.ForAll([state], exec(PC, opnum, state) == z3_of_op(op, state)))
    if is_fallthrough(op):
        if opnum+1 < len(tx.translate(addr)):
            kd.axiom(smt.ForAll([state], next(PC, opnum, state) == (addr, opnum+1)))
        else:
            kd.axiom(smt.ForAll([state], next(PC, opnum, state) == (addr+len(tx.translate(addr)), 0)))
    else:
        if op.opcde == OpCode.BRANCH:
            kd.axiom(smt.ForAll([state], next(PC, opnum, state) == (op.inputs[0].offset, 0)))


interp(PC, opnum, state, breakpoints) == 
    smt.If(PC == breakpoint, state, 
           interp(next(PC,opnum, state),exec(PC, opnum, state)))


State = kd.Struct(("addr", ), 

```

```python
    """
    elif opcode == OpCode.STORE:
        raise NotImplementedError("opcode not implemented", op.opcode)
    elif opcode == OpCode.LOAD:
        addr = z3_of_varnode(op.inputs[1], state)
        return bv.SelectConcat(state.ram, addr, op.output.size)
    elif opcode == OpCode.BRANCH:
        if op.inputs[0].space.name == "ram":
            return smt.Store(state.register, pc, op.inputs[0].offset)
        else:
            raise NotImplementedError("unsupported pcode realtive", op)
    elif opcode == OpCode.CBRANCH:
        if op.inputs[0].space.name == "ram":
            cond = z3_of_varnode(op.inputs[1], state)
            return smt.If(cond, store(state, pc, op.inputs[0].offset), state)
    """


#def insn

#def trans_rel(pc : pypcode.VarNode, ops):


```

    '\nelif opcode == OpCode.STORE:\n    raise NotImplementedError("opcode not implemented", op.opcode)\nelif opcode == OpCode.LOAD:\n    addr = z3_of_varnode(op.inputs[1], state)\n    return bv.SelectConcat(state.ram, addr, op.output.size)\nelif opcode == OpCode.BRANCH:\n    if op.inputs[0].space.name == "ram":\n        return smt.Store(state.register, pc, op.inputs[0].offset)\n    else:\n        raise NotImplementedError("unsupported pcode realtive", op)\nelif opcode == OpCode.CBRANCH:\n    if op.inputs[0].space.name == "ram":\n        cond = z3_of_varnode(op.inputs[1], state)\n        return smt.If(cond, store(state, pc, op.inputs[0].offset), state)\n'

```python
from pypcode import Context, PcodePrettyPrinter, PcodeOp, OpCode, Varnode
import z3
from kdrag.all import *
import kdrag.theories.bitvec as bv
import operator
#State = smt.DeclareSort("State")

def z3_of_varnode(vnode, state):
    if vnode.space.name == "const":
        return vnode.offset
    else:
        #print(vnode.space.name)
        return bv.SelectConcat(getattr(state, vnode.space.name), vnode.offset, vnode.size)

BV8 = bv.BitVecSort(8)
BV64 = bv.BitVecSort(64)

TRUE = smt.BitVecVal(1, 8)
FALSE = smt.BitVecVal(0, 8)

def BoolToBV8(x):
    return smt.If(x, TRUE, FALSE)



def z3_of_op(op, state):
    inputs = [z3_of_varnode(v, state) for v in op.inputs]

    match op.opcode:
        case OpCode.COPY:
            src = z3_of_varnode(op.inputs[0], state)
            return src
        case OpCode.INT_ADD:
            src1 = z3_of_varnode(op.inputs[0], state)
            src2 = z3_of_varnode(op.inputs[1], state)
            return src1 + src2
        case OpCode.INT_XOR:
            src1 = z3_of_varnode(op.inputs[0], state)
            src2 = z3_of_varnode(op.inputs[1], state)
            return src1 ^ src2
        case OpCode.INT_SLESS:
            src1 = z3_of_varnode(op.inputs[0], state)
            src2 = z3_of_varnode(op.inputs[1], state)
            return BoolToBV8(src1 < src2)
        case OpCode.INT_EQUAL:
            src1 = z3_of_varnode(op.inputs[0], state)
            src2 = z3_of_varnode(op.inputs[1], state)
            return BoolToBV8(src1 == src2)
        case OpCode.INT_AND:
            src1 = z3_of_varnode(op.inputs[0], state)
            src2 = z3_of_varnode(op.inputs[1], state)
            return src1 & src2
        case OpCode.POPCOUNT:
            src = z3_of_varnode(op.inputs[0], state)
            popcount = smt.Function("popcount", BV64, BV8)
            return popcount(src)
        case OpCode.LOAD:
            addr = z3_of_varnode(op.inputs[1], state)
            return bv.SelectConcat(state.ram, addr, op.output.size) # todo: where does that length come from? output node?
        case OpCode.IMARK:
            return None
        case OpCode.RETURN:
            return None
        case _:
            raise NotImplementedError("opcode not implemented", op.opcode)




State = kd.Struct("State", ("ram", smt.ArraySort(BV64, BV8)), 
                          ("register", smt.ArraySort(BV64, BV8)),
                          ("unique", smt.ArraySort(BV64, BV8)))


#smt.ArraySort(smt.IntSort(), smt.ArraySort(smt.BitVecSort(64), smt.BitVecSort(8)))#smt.DeclareSort("State")
state = smt.Const("init_state", State)
ctx = Context("x86:LE:64:default")
tx = ctx.translate(b"\x48\x35\x78\x56\x34\x12\xc3")
for op in tx.ops:
    print(PcodePrettyPrinter.fmt_op(op))
    print(z3_of_op(op, state))
```

    IMARK ram[0:6]
    None
    CF = 0x0
    0
    OF = 0x0
    0
    RAX = RAX ^ 0x12345678
    Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[7],
                                            register(init_state)[6]),
                                            register(init_state)[5]),
                                       register(init_state)[4]),
                                register(init_state)[3]),
                         register(init_state)[2]),
                  register(init_state)[1]),
           register(init_state)[0]) ^
    305419896
    SF = RAX s< 0x0
    If(Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[7],
                                            register(init_state)[6]),
                                            register(init_state)[5]),
                                          register(init_state)[4]),
                                   register(init_state)[3]),
                            register(init_state)[2]),
                     register(init_state)[1]),
              register(init_state)[0]) <
       0,
       1,
       0)
    ZF = RAX == 0x0
    If(Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[7],
                                            register(init_state)[6]),
                                            register(init_state)[5]),
                                          register(init_state)[4]),
                                   register(init_state)[3]),
                            register(init_state)[2]),
                     register(init_state)[1]),
              register(init_state)[0]) ==
       0,
       1,
       0)
    unique[15080:8] = RAX & 0xff
    Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[7],
                                            register(init_state)[6]),
                                            register(init_state)[5]),
                                       register(init_state)[4]),
                                register(init_state)[3]),
                         register(init_state)[2]),
                  register(init_state)[1]),
           register(init_state)[0]) &
    255
    unique[15100:1] = popcount(unique[15080:8])
    popcount(Concat(Concat(Concat(Concat(Concat(Concat(Concat(unique(init_state)[86151],
                                            unique(init_state)[86150]),
                                            unique(init_state)[86149]),
                                            unique(init_state)[86148]),
                                         unique(init_state)[86147]),
                                  unique(init_state)[86146]),
                           unique(init_state)[86145]),
                    unique(init_state)[86144]))
    unique[15180:1] = unique[15100:1] & 0x1
    unique(init_state)[86272] & 1
    PF = unique[15180:1] == 0x0
    If(unique(init_state)[86400] == 0, 1, 0)
    IMARK ram[6:1]
    None
    RIP = *[ram]RSP
    Concat(Concat(Concat(Concat(Concat(Concat(Concat(ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                            register(init_state)[33]),
                                            register(init_state)[32]) +
                                            8 -
                                            0 -
                                            1],
                                            ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                            register(init_state)[33]),
                                            register(init_state)[32]) +
                                            8 -
                                            1 -
                                            1]),
                                            ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                            register(init_state)[33]),
                                            register(init_state)[32]) +
                                            8 -
                                            2 -
                                            1]),
                                       ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                            register(init_state)[33]),
                                            register(init_state)[32]) +
                                         8 -
                                         3 -
                                         1]),
                                ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                            register(init_state)[33]),
                                         register(init_state)[32]) +
                                  8 -
                                  4 -
                                  1]),
                         ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                            register(init_state)[34]),
                                         register(init_state)[33]),
                                  register(init_state)[32]) +
                           8 -
                           5 -
                           1]),
                  ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                            register(init_state)[35]),
                                         register(init_state)[34]),
                                  register(init_state)[33]),
                           register(init_state)[32]) +
                    8 -
                    6 -
                    1]),
           ram(init_state)[Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                            register(init_state)[36]),
                                         register(init_state)[35]),
                                  register(init_state)[34]),
                           register(init_state)[33]),
                    register(init_state)[32]) +
             8 -
             7 -
             1])
    RSP = RSP + 0x8
    Concat(Concat(Concat(Concat(Concat(Concat(Concat(register(init_state)[39],
                                            register(init_state)[38]),
                                            register(init_state)[37]),
                                       register(init_state)[36]),
                                register(init_state)[35]),
                         register(init_state)[34]),
                  register(init_state)[33]),
           register(init_state)[32]) +
    8
    return RIP
    None

```python
%%file /tmp/foo.c

int foo(int x) {
    //assert(x == 0x12345678);
    {
        int b = 4;
    }
    {
        int b = 64;
    }
    int y = x + 42;
    //int y = 14;
    for(int i = 0; i < 10; i++) {
        y = y * 2;
    }
    //y = y * 15;
    int z = y * 3;
    return z;
}
```

    Overwriting /tmp/foo.c

(get-value (|foo::1::y!0@1#1|))
(get-value (|foo::1::y!0@1#2|))
(get-value (|foo::1::y!0@1#3|))
(get-value (|foo::1::y!0@1#4|))
(get-value (|foo::1::y!0@1#5|))
(get-value (|foo::1::y!0@1#6|))
(get-value (|foo::1::y!0@1#7|))
(get-value (|foo::1::y!0@1#8|))
(get-value (|foo::1::y!0@1#9|))
(get-value (|foo::1::z!0@1#1|))
(get-value (|foo::x!0@1#1|))
(get-value (|nondet_symex::nondet0|))
(get-value (|symex::args::0|))

This is some interpretable stuff in the variable names. But it isn't super straightforward.
I can't dig out the return value. COuld do an external assert maybe

# capstone

captsone interpreter
<https://www.capstone-engine.org/>

```python
%%file /tmp/test.c

int myadd(int a, int b) {
    return a + b;
}

```

    Writing /tmp/test.c

```python
! gcc -c -o /tmp/test.so /tmp/test.c
```

```python
from capstone import *

CODE = b"\x55\x48\x8b\x05\xb8\x13\x00\x00"

md = Cs(CS_ARCH_X86, CS_MODE_64)
for i in md.disasm(CODE, 0x1000):
    print("0x%x:\t%s\t%s" %(i.address, i.mnemonic, i.op_str))

```

    0x1000: push rbp
    0x1001: mov rax, qword ptr [rip + 0x13b8]

```python
from capstone import *

CODE = b"\x55\x48\x8b\x05\xb8\x13\x00\x00"
from collections import defaultdict
class State():
    mem = defaultdict(None)
    reg = defaultdict(None)

def interp(op, state):
    
    match op.mnemonic:
        case "add":
            state.reg[op.operands[0].reg] += state[op.operands[1].reg]
        case "sub":
            state[op.operands[0].reg] -= state[op.operands[1].reg]
        case "mov":
            if op.operands[0].type == X86_OP_IMM:
                state[op.operands[0].reg] = op.operands[1].imm
            elif op.operands[0].type == X86_OP_REG:
                op.operands[0].reg = op.operands[1].reg
            elif op.operands[0].type == X86_OP_MEM:
                state[op.operands[0].reg] = mem[state[op.operands[1].reg + op.operands[1].disp]
    return state
state = defaultdict(None)
for i in md.disasm(CODE, 0x1000):
    print(dir(i))
    interp(i, state)

```

    ['_CsInsn__gen_detail', '__class__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattr__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__module__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '__weakref__', '_cs', '_raw', 'address', 'bytes', 'errno', 'group', 'group_name', 'groups', 'id', 'insn_name', 'mnemonic', 'op_count', 'op_find', 'op_str', 'reg_name', 'reg_read', 'reg_write', 'regs_access', 'regs_read', 'regs_write', 'size']
    ['_CsInsn__gen_detail', '__class__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattr__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__module__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '__weakref__', '_cs', '_raw', 'address', 'bytes', 'errno', 'group', 'group_name', 'groups', 'id', 'insn_name', 'mnemonic', 'op_count', 'op_find', 'op_str', 'reg_name', 'reg_read', 'reg_write', 'regs_access', 'regs_read', 'regs_write', 'size']



    ---------------------------------------------------------------------------

    CsError                                   Traceback (most recent call last)

    Cell In[9], line 14
         12 for i in md.disasm(CODE, 0x1000):
         13     print(dir(i))
    ---> 14     interp(i, state)


    Cell In[9], line 9, in interp(op, state)
          7         state[op.operands[0].reg] -= state[op.operands[1].reg]
          8     case "mov":
    ----> 9         state[op.operands[0].reg] = state[op.operands[1].reg]
         10 return state


    File ~/.local/lib/python3.10/site-packages/capstone/__init__.py:777, in CsInsn.__getattr__(self, name)
        775 def __getattr__(self, name):
        776     if not self._cs._detail:
    --> 777         raise CsError(CS_ERR_DETAIL)
        779     attr = object.__getattribute__
        780     if not attr(self, '_cs')._detail:


    CsError: Details are unavailable (CS_ERR_DETAIL)

Ok so it gets hairier and harrier

Getting the smeanuitcs

# Pcode

```python
import pypcode
class State():
    space = defaultdict(defaultdict)

def interp(insn, state):
    match insn.op:
        case pypcode.PcodeOp.INT_ADD:
            

```

```python
%%file /tmp/foo.c
int foo(int x, int y){
    return x > y ? x : y;
}
```

    Writing /tmp/foo.c

```bash
%%bash
gcc /tmp/foo.c -c -o /tmp/foo.o
objdump -d -F /tmp/foo.o
```

    /tmp/foo.o:     file format elf64-x86-64
    
    
    Disassembly of section .text:
    
    0000000000000000 <foo> (File Offset: 0x40):
       0: f3 0f 1e fa           endbr64 
       4: 55                    push   %rbp
       5: 48 89 e5              mov    %rsp,%rbp
       8: 89 7d fc              mov    %edi,-0x4(%rbp)
       b: 89 75 f8              mov    %esi,-0x8(%rbp)
       e: 8b 55 f8              mov    -0x8(%rbp),%edx
      11: 8b 45 fc              mov    -0x4(%rbp),%eax
      14: 39 c2                 cmp    %eax,%edx
      16: 0f 4d c2              cmovge %edx,%eax
      19: 5d                    pop    %rbp
      1a: c3                    ret    

```python
import pypcode
# https://github.com/philzook58/pcode2c/blob/main/pcode2c/printer.py
from pypcode import Context, PcodePrettyPrinter
ctx = Context("x86:LE:64:default")
file_offset = 0x40
filename = "/tmp/foo.o"
size = 0x1a
start_address = 0
with open(filename, "rb") as file:
    file.seek(file_offset)
    code = file.read(size)
res = ctx.translate(code, base_address=start_address)
for op in res.ops:
    print(PcodePrettyPrinter.fmt_op(op))
```

    IMARK ram[0:4]
    IMARK ram[4:1]
    unique[10c00:8] = RBP
    RSP = RSP - 0x8
    *[ram]RSP = unique[10c00:8]
    IMARK ram[5:3]
    RBP = RSP
    IMARK ram[8:3]
    unique[4400:8] = RBP + 0xfffffffffffffffc
    unique[6780:4] = EDI
    *[ram]unique[4400:8] = unique[6780:4]
    IMARK ram[b:3]
    unique[4400:8] = RBP + 0xfffffffffffffff8
    unique[6780:4] = ESI
    *[ram]unique[4400:8] = unique[6780:4]
    IMARK ram[e:3]
    unique[4400:8] = RBP + 0xfffffffffffffff8
    unique[da80:4] = *[ram]unique[4400:8]
    EDX = unique[da80:4]
    RDX = zext(EDX)
    IMARK ram[11:3]
    unique[4400:8] = RBP + 0xfffffffffffffffc
    unique[da80:4] = *[ram]unique[4400:8]
    EAX = unique[da80:4]
    RAX = zext(EAX)
    IMARK ram[14:2]
    unique[27c00:4] = EDX
    CF = unique[27c00:4] < EAX
    OF = sborrow(unique[27c00:4], EAX)
    unique[27d00:4] = unique[27c00:4] - EAX
    SF = unique[27d00:4] s< 0x0
    ZF = unique[27d00:4] == 0x0
    unique[15080:4] = unique[27d00:4] & 0xff
    unique[15100:1] = popcount(unique[15080:4])
    unique[15180:1] = unique[15100:1] & 0x1
    PF = unique[15180:1] == 0x0
    IMARK ram[16:3]
    unique[eb00:1] = OF == SF
    RAX = zext(EAX)
    unique[26980:1] = !unique[eb00:1]
    if (unique[26980:1]) goto ram[19:8]
    EAX = EDX
    IMARK ram[19:1]
    unique[3df80:8] = 0x0
    unique[3df80:8] = *[ram]RSP
    RSP = RSP + 0x8
    RBP = unique[3df80:8]

```python
BV8  = BitVecSort(8)
BV16 = BitVecSort(16)
BV32 = BitVecSort(32)
BV64 = BitVecSort(64)

Select16 = Function("Select16", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(16))
Select32 = Function("Select32", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(32))
Select64 = Function("Select64", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(64))
def MSelect(a, i, n):
    if n == 1:
        return a[i]
    if n == 2:
        return Select16(a, i)
    if n == 4:
        return Select32(a, i)
    if n == 8:
        return Select64(a, i)
    else:
        assert False, "n must be 1, 2, 4 or 8"
Store16 = Function("Store16", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(16), ArraySort(BitVecSort(64), BitVecSort(8)))
Store32 = Function("Store32", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(32), ArraySort(BitVecSort(64), BitVecSort(8)))
Store64 = Function("Store64", ArraySort(BitVecSort(64), BitVecSort(8)), BitVecSort(64), BitVecSort(64), ArraySort(BitVecSort(64), BitVecSort(8)))

def MStore(a,i,v):
    size = v.size()
    if size == 1:
        return Store(a, i, v)
    if size == 2:
        return Store16(a, i, v)
    if size == 4:
        return Store32(a, i, v)
    if size == 8:
        return Store64(a, i, v)
    else:
        assert False, "size must be 1, 2, 4 or 8"
```

```python
state[8,2]
```

Select(state, 8, 2)

```python
from pypcode import OpCode
from z3 import *
Space = StringSort()
Varnode = Datatype('Varnode')
Varnode.declare('v', ('space', Space), ('offset', BitVecSort(64)))
Varnode = Varnode.create()

State = ArraySort(Varnode, BitVecSort(8))
#Store("constant", Lambda([x], x))
x = BitVec("x", 64)
State0 = {"ram" : None, "unique" : None, "const" : Lambda([x], x)}

def varnode(vnode, ):
    if vnode == None:
        return None
    elif vnode.space.name == "const":
        return BitVecVal(vnode.offset, vnode.size * 8)
    return BitVecVal(vnode.offset, vnode.size * 8)

def step(op, state1, state2):
    output = varnode(op.output)
    inputs = [varnode(i) for i in op.inputs]
    match op.opcode:
        case OpCode.IMARK:
            return f"IMARK "
        case OpCode.COPY:
            return MStore(state1, output, state1[inputs[0]])
        case OpCode.INT_SUB:
            return MStore(state1, output, state1[inputs[0]] - state1[inputs[1]])
        case _:
            print("unrecognized opcode", op.opcode)
            assert False
state1, state2 = Consts("state1 state2", State)
for op in res.ops:
    print(step(op, state1, state2))
```

    IMARK 
    IMARK 



    ---------------------------------------------------------------------------

    Z3Exception                               Traceback (most recent call last)

    /tmp/ipykernel_323060/2008195932.py in ?()
         31             print("unrecognized opcode", op.opcode)
         32             assert False
         33 state1, state2 = Consts("state1 state2", State)
         34 for op in res.ops:
    ---> 35     print(step(op, state1, state2))
    

    /tmp/ipykernel_323060/2008195932.py in ?(op, state1, state2)
         23     match op.opcode:
         24         case OpCode.IMARK:
         25             return f"IMARK "
         26         case OpCode.COPY:
    ---> 27             return MStore(state1, output, state1[inputs[0]])
         28         case OpCode.INT_SUB:
         29             return MStore(state1, output, state1[inputs[0]] - state1[inputs[1]])
         30         case _:


    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(self, arg)
       4634         a[i]
       4635         >>> a[i].sexpr()
       4636         '(select a i)'
       4637         """
    -> 4638         return _array_select(self, arg)
    

    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(ar, arg)
       4645     if isinstance(arg, tuple):
       4646         args = [ar.sort().domain_n(i).cast(arg[i]) for i in range(len(arg))]
       4647         _args, sz = _to_ast_array(args)
       4648         return _to_expr_ref(Z3_mk_select_n(ar.ctx_ref(), ar.as_ast(), sz, _args), ar.ctx)
    -> 4649     arg = ar.sort().domain().cast(arg)
       4650     return _to_expr_ref(Z3_mk_select(ar.ctx_ref(), ar.as_ast(), arg.as_ast()), ar.ctx)


    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(self, val)
        601         ToReal(x)
        602         """
        603         if z3_debug():
        604             _z3_assert(is_expr(val), "Z3 expression expected")
    --> 605             _z3_assert(self.eq(val.sort()), "Sort mismatch")
        606         return val


    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(cond, msg)
        105 def _z3_assert(cond, msg):
        106     if not cond:
    --> 107         raise Z3Exception(msg)
    

    Z3Exception: Sort mismatch

<https://spinsel.dev/assets/2020-06-17-ghidra-brainfuck-processor-1/ghidra_docs/language_spec/html/pcoderef.html>

```python
from z3 import *
from collections import namedtuple
def MStore(a,i,v):
    size = v.size()
    assert size in [8,16,32,64]
    select = Function(f"select{size}", MemSort, BitVecSort(64), BitVecSort(size), MemSort)
    return select(a,i,v)
def MSelect(a, i, n):
    assert size in [8,16,32,64]
    select = Function(f"select{n}", MemSort, BitVecSort(64), BitVecSort(n))
    return select(a,i)

def varnode(vnode, state):
    if vnode == None:
        return None
    if vnode.space.name == "const":
        print(vnode.size)
        return BitVecVal(vnode.offset, vnode.size * 8)
    v = BitVecVal(vnode.offset, 64)
    if vnode.space.name == "ram":
        return MSelect(state.ram, v, vnode.size*8)
    elif vnode.space.name == "unique":
        return MSelect(state.unique, v, vnode.size*8)
    elif vnode.space.name == "register":
        return MSelect(state.register,vnode.offset, vnode.size*8)
    else:
        raise ValueError("unrecognized space", vnode.space.name)
def step(op, state1):
    control = None
    output = None
    if op.opcode == OpCode.IMARK:
        return f"IMARK"
    elif op.opcode == OpCode.BRANCH:
        control = True
        return "branch"
    elif op.opcode == OpCode.CBRANCH:
        control = inputs[0] != 0
        return "cbranch"
    elif op.opcode == OpCode.CALL:
        return "call"
    elif op.opcode == OpCode.CALLIND:
        return "callind"
    elif op.opcode == OpCode.RETURN:
        return "return"
    
    inputs = [varnode(i,state) for i in op.inputs]
    if op.opcode == OpCode.STORE:
        #assert op.inputs[0].space.name == "ram"
        return state1._replace(ram = MStore(state1.ram, inputs[1], inputs[2]))
    elif op.opcode == OpCode.LOAD:
        #assert op.inputs[0].space.name == "ram"
        return MSelect(state.ram, inputs[1], 8)
    else:
        output = arith_op(op, inputs)
    
    

def arith_op(op, inputs):
    match op.opcode:
        case OpCode.COPY:
            return inputs[0]
        case OpCode.INT_EQUAL:
            return If(inputs[0] == inputs[1], BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_NOTEQUAL:
            return If(inputs[0] != inputs[1], BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_LESS:
            return If(ULT(inputs[0], inputs[1]), BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_SLESS:
            return If(inputs[0] < inputs[1], BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_LESSEQUAL:
            return If(ULE(inputs[0], inputs[1]), BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_SLESSEQUAL:
            return If(inputs[0] <= inputs[1], BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.INT_ZEXT: 
            return ZeroExt((op.output.size - op.inputs[0].size) * 8, inputs[0])
        case OpCode.INT_SEXT:
            return SignExt((op.output.size - op.inputs[0].size) * 8, inputs[0])
        case OpCode.INT_ADD:
            return inputs[0] + inputs[1]
        case OpCode.INT_SUB:
            return inputs[0] - inputs[1]
        case OpCode.INT_CARRY:
            assert If(BVAddNoOverflow(inputs[0], inputs[1], False), BitVecVal(0, 8), BitVecVal(1, 8))
        case OpCode.INT_SCARRY:
            assert If(BVAddNoOverflow(inputs[0], inputs[1], True), BitVecVal(0, 8), BitVecVal(1, 8))
        case OpCode.INT_SBORROW:
            assert False, "unimplemented"
        case OpCode.INT_2COMP:
            return -inputs[0]
        case OpCode.INT_NEGATE:
            return ~inputs[0]
        case OpCode.INT_XOR:
            return inputs[0] ^ inputs[1]
        case OpCode.INT_AND:
            return inputs[0] & inputs[1]
        case OpCode.INT_OR:
            return inputs[0] | inputs[1]
        case OpCode.INT_LEFT:
            return inputs[0] << inputs[1]
        case OpCode.INT_RIGHT:
            return  LShR(inputs[0], inputs[1])
        case OpCode.INT_SRIGHT:
            return inputs[0] >> inputs[1]
        case OpCode.INT_MULT:
            return inputs[0] * inputs[1]
        case OpCode.INT_DIV:
            return UDiv(inputs[0], inputs[1])
        case OpCode.INT_REM:
            return URem(inputs[0], inputs[1])
        case OpCode.INT_SDIV:
            return inputs[0] / inputs[1]
        case OpCode.INT_SREM:
            return inputs[0] % inputs[1]
        case OpCode.BOOL_NEGATE:
            return If(inputs[0] == 0, BitVecVal(1, 8), BitVecVal(0, 8))       
        case OpCode.BOOL_XOR:
            return If(inputs[0] != inputs[1], BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.BOOL_AND:
            return If(inputs[0] & inputs[1] == 1, BitVecVal(1, 8), BitVecVal(0, 8))
        case OpCode.POPCOUNT:
            return BitVecVal(0, output.size*8)
            for i in range(inputs[0].size()):
                output += (inputs[0] >> i) & 1
        case _:
            raise ValueError("unrecognized opcode", op.opcode)
    return output
State = namedtuple("state", "ram unique register")
MemSort = ArraySort(BitVecSort(64), BitVecSort(8))
state = State(Const("ram", MemSort), Const("unique", MemSort), Const("register", MemSort))
for op in res.ops:
    print(PcodePrettyPrinter.fmt_op(op))
    print(step(op, state))
```

    IMARK ram[0:4]
    IMARK
    IMARK ram[4:1]
    IMARK
    unique[10c00:8] = RBP



    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[77], line 129
        127 for op in res.ops:
        128     print(PcodePrettyPrinter.fmt_op(op))
    --> 129     print(step(op, state))


    Cell In[77], line 46, in step(op, state1)
         43 elif op.opcode == OpCode.RETURN:
         44     return "return"
    ---> 46 inputs = [varnode(i,state) for i in op.inputs]
         47 if op.opcode == OpCode.STORE:
         48     #assert op.inputs[0].space.name == "ram"
         49     return state1._replace(ram = MStore(state1.ram, inputs[1], inputs[2]))


    Cell In[77], line 46, in <listcomp>(.0)
         43 elif op.opcode == OpCode.RETURN:
         44     return "return"
    ---> 46 inputs = [varnode(i,state) for i in op.inputs]
         47 if op.opcode == OpCode.STORE:
         48     #assert op.inputs[0].space.name == "ram"
         49     return state1._replace(ram = MStore(state1.ram, inputs[1], inputs[2]))


    Cell In[77], line 25, in varnode(vnode, state)
         23     return MSelect(state.unique, v, vnode.size*8)
         24 elif vnode.space.name == "register":
    ---> 25     return MSelect(state.register,vnode.offset, vnode.size*8)
         26 else:
         27     raise ValueError("unrecognized space", vnode.space.name)


    Cell In[77], line 9, in MSelect(a, i, n)
          8 def MSelect(a, i, n):
    ----> 9     assert size in [8,16,32,64]
         10     select = Function(f"select{n}", MemSort, BitVecSort(64), BitVecSort(n))
         11     return select(a,i)


    AssertionError: 

```python
def varnode(vnode):
    if vnode == None:
        return None
    v = BitVecVal(vnode.offset, vnode.size * 8)
    if vnode.space.name == "const":
        return v
    elif vnode.space.name == "ram":
        return BitVec("ram", vnode.size*8)
    elif vnode.space.name == "unique":
        return BitVec("unique", vnode.size*8)
    elif vnode.space.name == "register":
        return BitVec(f"register_{vnode.offset}", vnode.size*8)
    else:
        raise ValueError("unrecognized space", vnode.space.name)
def step(op):
    inputs = [varnode(i) for i in op.inputs]
    match op.opcode:
        case OpCode.IMARK:
            return f"IMARK "
        case OpCode.COPY:
            return inputs[0]
        case OpCode.INT_ADD:
            return inputs[0] + inputs[1]
        case OpCode.INT_SUB:
            return inputs[0] - inputs[1]
        case OpCode.STORE:
            pass
        case _:
            print("unrecognized opcode", op.opcode)
            assert False
for op in res.ops:
    print(step(op))

    print(PcodePrettyPrinter.fmt_op(op))
```

    IMARK 
    IMARK ram[0:4]
    IMARK 
    IMARK ram[4:1]
    register_40
    unique[10c00:8] = RBP
    register_32 - 8
    RSP = RSP - 0x8
    None
    *[ram]RSP = unique[10c00:8]
    IMARK 
    IMARK ram[5:3]
    register_32
    RBP = RSP
    IMARK 
    IMARK ram[8:3]
    register_40 + 18446744073709551612
    unique[4400:8] = RBP + 0xfffffffffffffffc
    register_56
    unique[6780:4] = EDI
    None
    *[ram]unique[4400:8] = unique[6780:4]
    IMARK 
    IMARK ram[b:3]
    register_40 + 18446744073709551608
    unique[4400:8] = RBP + 0xfffffffffffffff8
    register_48
    unique[6780:4] = ESI
    None
    *[ram]unique[4400:8] = unique[6780:4]
    IMARK 
    IMARK ram[e:3]
    register_40 + 18446744073709551608
    unique[4400:8] = RBP + 0xfffffffffffffff8
    unrecognized opcode OpCode.LOAD



    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[36], line 32
         30             assert False
         31 for op in res.ops:
    ---> 32     print(step(op))
         34     print(PcodePrettyPrinter.fmt_op(op))


    Cell In[36], line 30, in step(op)
         28 case _:
         29     print("unrecognized opcode", op.opcode)
    ---> 30     assert False


    AssertionError: 

```python
from pwn import asm, context
from pypcode import Context, PcodePrettyPrinter

# Set the pwntools context to RISC-V 32-bit
context.arch = 'riscv32'
context.endian = 'little'

# Define a list of simple RISC-V instructions
instructions = [
    "li t0, 42",        # Load immediate
    "add t1, t0, t0",   # Add t0 + t0 -> t1
    "sub t2, t1, t0",   # Subtract t1 - t0 -> t2
    "lw t3, 0(t0)",     # Load word from memory
    "sw t3, 4(t0)"      # Store word to memory
]
# Assemble the instructions into bytes
assembled_code = b"".join(asm(inst) for inst in instructions)
```

    [!] Could not find system include headers for riscv32-linux

# old angr

WCET
Interrupts
Get semantic into knuckle

Cryptol examples <https://tools.galois.com/cryptol>

Low*  

<https://link.springer.com/chapter/10.1007/978-3-030-45237-7_6> Highly Automated Formal Proofs over Memory Usage of Assembly Code
<https://link.springer.com/10.1007/978-3-319-72308-2_5?fromPaywallRec=false> branch free assembly why3

jvm
evm
wasm
might be interesting targets. hmm.

```python
%%file /tmp/hello.c

int main(){
    return 3;
}
```

    Overwriting /tmp/hello.c

```python
!gcc /tmp/hello.c -o /tmp/hello
```

```python
!objdump -d /tmp/hello | grep main.: -A20
```

    0000000000001129 <main>:
        1129: f3 0f 1e fa           endbr64
        112d: 55                    push   %rbp
        112e: 48 89 e5              mov    %rsp,%rbp
        1131: b8 03 00 00 00        mov    $0x3,%eax
        1136: 5d                    pop    %rbp
        1137: c3                    ret
    
    Disassembly of section .fini:
    
    0000000000001138 <_fini>:
        1138: f3 0f 1e fa           endbr64
        113c: 48 83 ec 08           sub    $0x8,%rsp
        1140: 48 83 c4 08           add    $0x8,%rsp
        1144: c3                    ret

```python
import angr
import archinfo

proj = angr.Project("/tmp/hello")
#arch = archinfo.ArchPcode("x86:LE:64:default")
#proj = angr.Project("/tmp/hello",arch=arch, engine=angr.engines.UberEnginePcode)


```

```python
state = proj.factory.call_state(0x401129)
dir(state.memory)


```

    ['PAGE_TYPE',
     'STRONGREF_STATE',
     'SUPPORTS_CONCRETE_LOAD',
     '_ActionsMixinHigh__make_action',
     '__annotations__',
     '__class__',
     '__class_getitem__',
     '__contains__',
     '__del__',
     '__delattr__',
     '__dict__',
     '__dir__',
     '__doc__',
     '__eq__',
     '__format__',
     '__ge__',
     '__getattribute__',
     '__getstate__',
     '__gt__',
     '__hash__',
     '__init__',
     '__init_subclass__',
     '__le__',
     '__lt__',
     '__module__',
     '__ne__',
     '__new__',
     '__orig_bases__',
     '__parameters__',
     '__reduce__',
     '__reduce_ex__',
     '__repr__',
     '__setattr__',
     '__sizeof__',
     '__str__',
     '__subclasshook__',
     '__weakref__',
     '_add_constraints',
     '_apply_concretization_strategies',
     '_calc_char_num',
     '_calc_page_starts',
     '_cle_loader',
     '_cle_permissions_lookup',
     '_clemory_backer',
     '_concretize_symbolic_write_size',
     '_constrain_underconstrained_index',
     '_convert_to_ast',
     '_create_default_read_strategies',
     '_create_default_write_strategies',
     '_data_from_backer',
     '_data_from_bytes_backer',
     '_data_from_lists_backer',
     '_default_permissions',
     '_default_value',
     '_dict_memory_backer',
     '_divide_addr',
     '_extra_page_kwargs',
     '_find_are_bytes_symbolic',
     '_find_compare',
     '_find_condition',
     '_find_iter_items',
     '_find_process_cases',
     '_get_page',
     '_hash_mapping',
     '_initialize_default_page',
     '_initialize_page',
     '_interleave_ints',
     '_load_one_addr',
     '_load_to_memoryview',
     '_map_page',
     '_mark_updated_mapping',
     '_max_concretize_count',
     '_max_symbolic_size',
     '_merge_labels',
     '_merge_strategies',
     '_merge_values',
     '_name_mapping',
     '_page_kwargs',
     '_pages',
     '_permissions_map',
     '_raise_memory_limit_error',
     '_red_pageno',
     '_remaining_stack',
     '_replace_all',
     '_resolve_location_name',
     '_size_limit',
     '_stack_perms',
     '_store_one_addr',
     '_symbolic_addrs',
     '_unconstrained_range',
     '_unmap_page',
     '_update_mappings',
     '_updated_mappings',
     'addrs_for_hash',
     'addrs_for_name',
     'allocate_stack_pages',
     'category',
     'changed_bytes',
     'changed_pages',
     'compare',
     'concrete_load',
     'concretize_read_addr',
     'concretize_write_addr',
     'copy',
     'copy_contents',
     'endness',
     'erase',
     'find',
     'flush_pages',
     'get_symbolic_addrs',
     'hex_dump',
     'id',
     'init_state',
     'load',
     'map_region',
     'memo',
     'merge',
     'page_size',
     'permissions',
     'read_strategies',
     'register_default',
     'replace_all',
     'set_state',
     'set_strongref_state',
     'state',
     'store',
     'unmap_region',
     'variable_key_prefix',
     'widen',
     'write_strategies']

```python
state.block().pp()
```

            main:
    401129  endbr64 
    40112d  push    rbp
    40112e  mov     rbp, rsp
    401131  mov     eax, 0x3
    401136  pop     rbp
    401137  ret     

```python
state
```

    <SimState @ 0x401129>

```python
class Wrapper():
    def __init__(self, wrapped):
        self.wrapped = wrapped
    def __getattr__(self, item):
        print("getattr", item)
        return getattr(self.wrapped, item)
    
state.memory = Wrapper(state.memory)
state.step(num_inst=4)
```

    WARNING  | 2025-01-28 11:26:00,714 | angr.storage.memory_mixins.default_filler_mixin | Filling register rbp with 8 unconstrained bytes referenced from 0x40112d (main+0x4 in hello (0x112d))





    <IRSB from 0x401129: 1 sat>

```python
simgr = proj.factory.simulation_manager(state)
simgr.step(num_inst=3)
simgr.active[0]
```

    WARNING  | 2025-01-28 11:25:30,798 | angr.storage.memory_mixins.default_filler_mixin | Filling register rbp with 8 unconstrained bytes referenced from 0x40112d (main+0x4 in hello (0x112d))





    <SimState @ 0x401131>

<https://github.com/angr/claripy/issues/171> No array support in clairpy...

```python
import claripy
claripy.
```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[81], line 1
    ----> 1 state.memory.hex_dump()


    TypeError: HexDumperMixin.hex_dump() missing 2 required positional arguments: 'start' and 'size'

```python
state.memory.store(0xdeadbeef, 0x42)
state.memory.load(0xdeadbeef, 8)
```

    WARNING  | 2025-01-28 11:23:18,971 | angr.storage.memory_mixins.bvv_conversion_mixin | Unknown size for memory data 0x42. Default to arch.bits.


    getattr store
    getattr load





    <BV64 0x42>

There's no tutorial, but it's pretty easy to figure out yourself. There's a bunch of examples in this directory: <https://github.com/angr/angr/tree/master/angr/storage/memory_mixins>
basically subclass MemoryMixin and write a load and store method
 on slotted_memory.py

```python
from angr.storage.memory_mixins import MemoryMixin

class CustomMemoryMixin(MemoryMixin):
    def load(self, addr, size=None, **kwargs):
        print(f"Custom Load: Address={addr}, Size={size}")
        return super().load(addr, size, **kwargs)

    def store(self, addr, data, **kwargs):
        print(f"Custom Store: Address={addr}, Data={data}")
        super().store(addr, data, **kwargs)
from angr.storage import Memory

class CustomMemory(CustomMemoryMixin, Memory):
    pass
import angr
import archinfo


```

    ---------------------------------------------------------------------------

    ImportError                               Traceback (most recent call last)

    Cell In[19], line 1
    ----> 1 from angr.storage.memory_mixins import MemoryMixin
          3 class CustomMemoryMixin(MemoryMixin):
          4     def load(self, addr, size=None, **kwargs):


    ImportError: cannot import name 'MemoryMixin' from 'angr.storage.memory_mixins' (/home/philip/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/storage/memory_mixins/__init__.py)

```python
#proj = angr.Project("/tmp/hello")
from angr.storage.memory_mixins import DefaultMemory, AbstractMemory
class CustomMemory():
    def load(self, addr, size=None, **kwargs):
        print(f"Custom Load: Address={addr}, Size={size}")
        return super().load(addr, size, **kwargs)

    def store(self, addr, data, **kwargs):
        print(f"Custom Store: Address={addr}, Data={data}")
        super().store(addr, data, **kwargs)
state = proj.factory.call_state(0x401129, plugins={'memory': DefaultMemory()})
#state.memory = AbstractMemory()
state.block().pp()
print(state.regs.pc)

simgr = proj.factory.simulation_manager(state)
simgr.step(num_inst=2)
simgr.active[0].block().pp()
#simgr.active[0].memory.

#state.memory
```

    ---------------------------------------------------------------------------

    SimMemoryError                            Traceback (most recent call last)

    Cell In[57], line 11
          9         print(f"Custom Store: Address={addr}, Data={data}")
         10         super().store(addr, data, **kwargs)
    ---> 11 state = proj.factory.call_state(0x401129, plugins={'memory': DefaultMemory()})
         12 #state.memory = AbstractMemory()
         13 state.block().pp()


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/factory.py:199, in AngrObjectFactory.call_state(self, addr, *args, **kwargs)
        157 def call_state(self, addr, *args, **kwargs):
        158     """
        159     Returns a state object initialized to the start of a given function, as if it were called with given parameters.
        160 
       (...)
        197     allocations happen at increasing addresses.
        198     """
    --> 199     return self.project.simos.state_call(addr, *args, **kwargs)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/simos/simos.py:258, in SimOS.state_call(self, addr, *args, **kwargs)
        256     if stack_base is not None:
        257         kwargs["stack_end"] = (stack_base + 0x1000) & ~0xFFF
    --> 258     state = self.state_blank(addr=addr, **kwargs)
        259 else:
        260     state = state.copy()


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/simos/linux.py:216, in SimLinux.state_blank(self, fs, concrete_fs, chroot, cwd, pathsep, thread_idx, init_libc, **kwargs)
        214 # pre-grow the stack by 0x20 pages. unsure if this is strictly required or just a hack around a compiler bug
        215 if not self._is_core and hasattr(state.memory, "allocate_stack_pages"):
    --> 216     state.memory.allocate_stack_pages(state.solver.eval(state.regs.sp) - 1, 0x20 * 0x1000)
        218 if self.project.loader.tls.threads:
        219     tls_obj = self.project.loader.tls.threads[thread_idx if thread_idx is not None else 0]


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/storage/memory_mixins/paged_memory/stack_allocation_mixin.py:44, in StackAllocationMixin.allocate_stack_pages(self, addr, size, **kwargs)
         42 pageno = addr // self.page_size
         43 if pageno != self._red_pageno:
    ---> 44     raise SimMemoryError("Trying to allocate stack space in a place that isn't the top of the stack")
         45 num = pageno - ((addr - size + 1) // self.page_size) + 1
         47 result = []


    SimMemoryError: Trying to allocate stack space in a place that isn't the top of the stack

```python
state = SimState(arch="x86", mode="symbolic", plugins={"memory": memcls()})
```

```python

```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[33], line 1
    ----> 1 state.block()


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/sim_state.py:530, in SimState.block(self, *args, **kwargs)
        528 if not args and "addr" not in kwargs:
        529     kwargs["addr"] = self.addr
    --> 530 return self.project.factory.block(*args, backup_state=self, **kwargs)


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/factory.py:386, in AngrObjectFactory.block(self, addr, size, max_size, byte_string, vex, thumb, backup_state, extra_stop_points, opt_level, num_inst, traceflags, insn_bytes, insn_text, strict_block_end, collect_data_refs, cross_insn_opt, load_from_ro_regions, const_prop, initial_regs, skip_stmts)
        380     if byte_string is None:
        381         # assembly failed
        382         raise AngrAssemblyError(
        383             "Assembling failed. Please make sure keystone is installed, and the assembly string is correct."
        384         )
    --> 386 return Block(
        387     addr,
        388     project=self.project,
        389     size=size,
        390     max_size=max_size,
        391     byte_string=byte_string,
        392     vex=vex,
        393     extra_stop_points=extra_stop_points,
        394     thumb=thumb,
        395     backup_state=backup_state,
        396     opt_level=opt_level,
        397     num_inst=num_inst,
        398     traceflags=traceflags,
        399     strict_block_end=strict_block_end,
        400     collect_data_refs=collect_data_refs,
        401     cross_insn_opt=cross_insn_opt,
        402     load_from_ro_regions=load_from_ro_regions,
        403     const_prop=const_prop,
        404     initial_regs=initial_regs,
        405     skip_stmts=skip_stmts,
        406 )


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/block.py:271, in Block.__init__(self, addr, project, arch, size, max_size, byte_string, vex, thumb, backup_state, extra_stop_points, opt_level, num_inst, traceflags, strict_block_end, collect_data_refs, cross_insn_opt, load_from_ro_regions, const_prop, initial_regs, skip_stmts)
        269 if byte_string is None:
        270     if backup_state is not None:
    --> 271         buffer, _, offset = self._vex_engine._load_bytes(addr - thumb, size, state=backup_state)
        272         self._bytes = buffer[offset:]
        273         if type(self._bytes) is memoryview:


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/angr/engines/vex/lifter.py:333, in VEXLifter._load_bytes(self, addr, max_size, state, clemory)
        331                 raise TypeError(f"Unsupported backer type {type(backer)}.")
        332 elif state:
    --> 333     if state.memory.SUPPORTS_CONCRETE_LOAD:
        334         buff = state.memory.concrete_load(addr, max_size)
        335     else:


    AttributeError: 'CustomMemory' object has no attribute 'SUPPORTS_CONCRETE_LOAD'

```python
import claripy
from angr.storage.memory_mixins.memory_mixin import MemoryMixin
from angr.errors import SimMergeError

class SymbolicArrayMemoryMixin(MemoryMixin):
    """
    A simple example of a memory mixin that uses a single claripy Array
    to represent memory. It loads/stores bytes from/to that Array,
    allowing symbolic addresses without concretization.
    """

    def __init__(self, name='sym_mem', domain_bits=64, data_bits=8, **kwargs):
        super().__init__(**kwargs)
        # Create one Array: domain_bits = 64-bit addresses, data_bits = 8-bit data
        self._domain_bits = domain_bits
        self._data_bits = data_bits
        self._mem = claripy.Array(
            name,
            claripy.BVS('addr_dummy', self._domain_bits).sort(),  # domain sort (BitVec 64)
            claripy.BVS('data_dummy', self._data_bits).sort()     # range sort  (BitVec 8)
        )

    def set_state(self, state):
        super().set_state(state)
        # We'll read the default endianness from the state's arch
        self.endness = state.arch.memory_endness

    def copy(self, memo):
        o = super().copy(memo)
        o._domain_bits = self._domain_bits
        o._data_bits = self._data_bits
        o._mem = self._mem
        return o

    def merge(self, others, merge_conditions, common_ancestor=None):
        """
        Merge is done by creating an if-then-else chain over the entire Array.
        If you have N merges, you end up with nested ITE expressions.

        For example, if we have two memory states M1, M2 and a boolean condition c,
        the new memory after merge is:

            M_merged = If(c, M2, M1)

        In a general multi-way merge we do:
            M_merged = ite_cases(
                [(cond1, M1), (cond2, M2), ...],
                <some-default>
            )
        """
        a = self._mem
        # merge_conditions is something like [True, cond1, cond2, ...] (the first is always True for the base)
        for cond, other in zip(merge_conditions[1:], others):
            # If cond is True, pick other's array, else pick the current a
            a = claripy.If(cond, other._mem, a)

        self._mem = a

        # Return True if you want to indicate that a merge occurred
        return True

    def load(self, addr, size=None, **kwargs):
        """
        Load a bitvector of `size` bytes from memory, starting at `addr`.
        We'll automatically handle endianness. By default, `size` can come from
        the state or from your call site. 
        """
        if size is None:
            size = self.state.arch.bytes  # default to arch word

        endness = kwargs.get('endness', self.endness)

        # Collect each byte from the Array.
        # For big-endian: the byte at addr is the high-order bits in the output.
        # For little-endian: the byte at addr is the low-order bits in the output.
        bytes_ = []
        if endness == 'Iend_BE':
            # For big-endian, the leftmost byte is at the lowest address
            for i in range(size):
                byte_i = claripy.Select(self._mem, addr + i)
                bytes_.append(byte_i)
            result = claripy.Concat(*bytes_)
        else:
            # For little-endian, the leftmost byte is at the highest address in the final bitvector
            # so we read them from high address to low in the final Concat
            for i in reversed(range(size)):
                byte_i = claripy.Select(self._mem, addr + i)
                bytes_.append(byte_i)
            result = claripy.Concat(*bytes_)

        return result

    def store(self, addr, data, size=None, **kwargs):
        """
        Store a bitvector `data` into memory at address `addr`.
        We update self._mem with an If-Then-Else chain if addresses are symbolic,
        but claripy.Store does that internally for us.
        """
        if size is None:
            # data.size() is in bits. So we convert to bytes
            size = data.size() // 8

        endness = kwargs.get('endness', self.endness)

        # We slice out each byte from `data` (which is a bitvector of size*8 bits).
        # For big-endian, the most significant byte is data[size*8-1 : (size-1)*8]
        # For little-endian, the least significant byte is data[7:0], next is data[15:8], etc.
        if endness == 'Iend_BE':
            # The left-most byte in `data` goes to the lowest address
            for i in range(size):
                # The i-th byte from the left
                byte_i = data[((size - i) * 8 - 1) : ((size - i - 1) * 8)]
                self._mem = claripy.Store(self._mem, addr + i, byte_i)
        else:
            # The i-th byte from the right
            for i in range(size):
                byte_i = data[(i+1)*8 - 1 : i*8]
                self._mem = claripy.Store(self._mem, addr + i, byte_i)

    #
    # Additional methods (e.g. changed_bytes, default_value, etc.) can be added
    # but are optional depending on how you want this memory model to behave.
    #

```

```python
#from angr.storage.memory_mixins.paged_memory.pages import PageMemory

#class MyMemory(PageMemory, SymbolicArrayMemoryMixin):
#    pass

# Then create a state with your memory
proj = angr.Project('/tmp/hello', load_options={'main_opts': {'custom_base_addr': 0}})
st = proj.factory.full_init_state()
st.memory.mem._add_mixin('symbolic_array', SymbolicArrayMemoryMixin())

```

    CRITICAL | 2025-01-28 11:02:57,499 | cle.backends.backend | Deprecation warning: the custom_base_addr parameter has been renamed to base_addr



    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[58], line 9
          7 proj = angr.Project('/tmp/hello', load_options={'main_opts': {'custom_base_addr': 0}})
          8 st = proj.factory.full_init_state()
    ----> 9 st.memory.mem._add_mixin('symbolic_array', SymbolicArrayMemoryMixin())


    AttributeError: 'DefaultMemory' object has no attribute 'mem'

```python
state = proj.factory.entry_state()
state.block().pp()
```

            _start:
    401040  endbr64 
    401044  xor     ebp, ebp
    401046  mov     r9, rdx
    401049  pop     rsi
    40104a  mov     rdx, rsp
    40104d  and     rsp, 0xfffffffffffffff0
    401051  push    rax
    401052  push    rsp
    401053  xor     r8d, r8d
    401056  xor     ecx, ecx
    401058  lea     rdi, [main]
    40105f  call    qword ptr [0x403fd8]

```python
#proj.factory.call_state(0x401129)
#state = proj.factory.full_init_state(addr=0x401129)
def print_state(state):
    print("rip", state.regs.rip)
    print("rsp", state.regs.rsp)
    print("rbp", state.regs.rbp)
    print("rax", state.regs.rax)
    print("rbx", state.regs.rbx)
    print("stack", state.memory.pp())#.load(state.regs.rsp, 0x1, endness='Iend_BE'))
    print(proj.factory.block(state.addr).pp())
    #for reg in state.arch.register_list:
    #    print(f"{reg.name}: {state.regs.__getattr__(reg.name)}")

state = proj.factory.blank_state(addr=0x401129)
#state = proj.factory.full_init_state()


# Ensure the state uses full symbolic execution
# https://github.com/angr/angr/blob/master/angr/sim_options.py
#state.options.discard(angr.options.APPROXIMATE_GUARDS)  # Prevent guard approximation
#state.options.discard(angr.options.SYMBOLIC_WRITE_ADDRESSES)  # Keep symbolic writes
#state.options.discard(angr.options.SYMBOLIC_READ_ADDRESSES)  # Keep symbolic reads
#state.options.discard(angr.options.CONCRETIZE_SYMBOLIC_WRITE_SIZES)  # Prevent concretizing sizes
#state.options.discard(angr.options.CONCRETIZE_SYMBOLIC_READ_SIZES)  # Prevent concretizing read sizes

state.options.add(angr.options.TRACK_MEMORY_ACTIONS)  # Track memory actions
state.options.add(angr.options.STRICT_PAGE_ACCESS)  # Prevent default concretization of memory access
print(type(state.memory))
print_state(state)
simgr = proj.factory.simulation_manager(state)
for i in range(5):
    simgr.step(num_inst=1)
    new_state = simgr.active[0]
    print_state(new_state)


```

    WARNING  | 2025-01-28 11:03:07,539 | angr.storage.memory_mixins.default_filler_mixin | Filling register rbp with 8 unconstrained bytes referenced from 0x401129 (GLIBC_2.35+0x1129 in ld-linux-x86-64.so.2 (0x1129))
    WARNING  | 2025-01-28 11:03:07,540 | angr.storage.memory_mixins.default_filler_mixin | Filling register rax with 8 unconstrained bytes referenced from 0x401129 (GLIBC_2.35+0x1129 in ld-linux-x86-64.so.2 (0x1129))
    WARNING  | 2025-01-28 11:03:07,541 | angr.storage.memory_mixins.default_filler_mixin | Filling register rbx with 8 unconstrained bytes referenced from 0x401129 (GLIBC_2.35+0x1129 in ld-linux-x86-64.so.2 (0x1129))


    <class 'angr.storage.memory_mixins.DefaultMemory'>
    rip <BV64 0x401129>
    rsp <BV64 0x7ffffffffff0000>
    rbp <BV64 reg_rbp_373_64>
    rax <BV64 reg_rax_374_64>
    rbx <BV64 reg_rbx_375_64>



    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[59], line 29
         27 state.options.add(angr.options.STRICT_PAGE_ACCESS)  # Prevent default concretization of memory access
         28 print(type(state.memory))
    ---> 29 print_state(state)
         30 simgr = proj.factory.simulation_manager(state)
         31 for i in range(5):


    Cell In[59], line 9, in print_state(state)
          7 print("rax", state.regs.rax)
          8 print("rbx", state.regs.rbx)
    ----> 9 print("stack", state.memory.pp())#.load(state.regs.rsp, 0x1, endness='Iend_BE'))
         10 print(proj.factory.block(state.addr).pp())


    AttributeError: 'DefaultMemory' object has no attribute 'pp'

```python
ins = proj.factory.block(0x401129, size=4)
ins
```

    <Block for 0x401129, 4 bytes>

```python
state = proj.factory.call_state(0x401129)
#state.step()
b = state.block()

```

```python
state = proj.factory.call_state(0x401129)
s2 = state.step()
s2, = s2.successors
r = s2.registers
s2.regs.rax
```

    WARNING  | 2025-01-03 09:48:55,915 | angr.storage.memory_mixins.default_filler_mixin | Filling register rbp with 8 unconstrained bytes referenced from 0x40112d (main+0x4 in hello (0x112d))





    <BV64 0x3>

```python

```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[63], line 1
    ----> 1 proj.factory.path()


    AttributeError: 'AngrObjectFactory' object has no attribute 'path'

Right. one of the breakpoints is address concretization. Their memory model is

<https://github.com/angr/angr/blob/master/angr/engines/pcode/emulate.py> basic pcode interpreter
<https://github.com/angr/angr/blob/master/angr/engines/pcode/behavior.py> "behavior". There is a diciontary at the bottom

I can't believe the amount of indirection there is in here.

Ok, but even

Maybe subclass the pcodenegine mixin.

```python
b = angr.engines.pcode.behavior.BehaviorFactory()
from pypcode import OpCode
import claripy
claripy.backends.z3.convert(b.get_behavior_for_opcode(OpCode.BOOL_AND).evaluate_binary(1,1,claripy.BVV(1,8),claripy.BVV(1,8)))
```

    1

```python
x = claripy.BVS("x", 8) #.dbg_repr()
import claripy.backends.backend_z3
#claripy.backends.backend_z3.BackendZ3().convert(x)
claripy.backends.z3.convert(x)
```

x_165_8

```python
state.inspect.
```

    <angr.state_plugins.inspect.SimInspector at 0x799b69cd07c0>

```python
main_symbol = proj.loader.main_object.get_symbol("main")
main_symbol
```

    <Symbol "main" in hello at 0x401129>

pywasm <https://github.com/mohanson/pywasm>

<https://github.com/AntonLydike/riscemu>

<https://github.com/codypierce/pyemu> x86
<https://github.com/ForceBru/PyVM>

<https://github.com/mnaberez/py65> 6502

```python
import riscemu

from riscemu.riscemu_main import RiscemuMain, RunConfig

# Create an instance of the RiscemuMain class
emulator = RiscemuMain()

# Set the configuration (this is just an example; set according to your needs)
config = RunConfig(stack_size=8192, verbosity=1, flen=64)
emulator.cfg = config

# Set the input files (example assembly files)
emulator.input_files = ["path/to/your/assembly/file.asm"]

# Register all available instruction sets and program loaders
emulator.register_all_isas()
emulator.register_all_program_loaders()

# Call the run method to start the emulator
emulator.run()
cpu = UserModeCPU(self.selected_ins_sets, self.cfg)
cpu.setup_stack(self.cfg.stack_size)
cpu.launch(self.cfg.verbosity > 1)
```

    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[14], line 20
         17 emulator.register_all_program_loaders()
         19 # Call the run method to start the emulator
    ---> 20 emulator.run()


    File ~/.local/lib/python3.10/site-packages/riscemu/riscemu_main.py:310, in RiscemuMain.run(self)
        300 """
        301 This assumes that these values were set externally:
        302 
       (...)
        307  - selected_ins_sets: A list of instruction sets the CPU should support.
        308 """
        309 assert self.cfg is not None, "self.cfg must be set before calling run()"
    --> 310 assert self.selected_ins_sets, "self.selected_ins_sets cannot be empty"
        311 assert self.input_files, "self.input_files cannot be empty"
        313 if self.cfg.use_libc:


    AssertionError: self.selected_ins_sets cannot be empty
