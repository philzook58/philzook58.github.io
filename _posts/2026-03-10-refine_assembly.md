---
title: Refinement Modeling and Verification of RISC-V Assembly using Knuckledragger
date: 2026-03-10
---


Binary verification is useful on a couple counts:

1. Some low level code needs to be written in assembly for performance, access to special operations, or very tight timing/memory control.
2. It is a method to catch compiler bugs
3. In the crazy modern age we live in, the idea of directly generating assembly/binary from LLMs is now on the table. Tooling to verify said code may give agents a way to connect it to a language they better understand and is less error prone.

One can get very good at assembly and can develop habits and patterns to write less error prone code. It is nevertheless an open saw blade and is not so hard to mess up an off by 1. Assembly is rather verbose and this leads to a greater difficulty in catching bugs. It also has a pretty austere ecosystem of tooling. You got an editor, an assembler, and a debugger. Godspeed.

Anyhow, I've been working on making binary verification tooling in python based on the pypcode ghidra semantics. I've gone through a number of iterations and ideas that haven't quite panned out. This is the best new version of all of that.

The problem I got stumped on in the previous iteration <https://www.philipzucker.com/asm_verify4/> was that the output of the symbolic executor was just plain too gnarly to debug and manipulate for interactive proof using my knuckledragger system. What I ended up doing was basically writing a high level version of the program in the assertions. If that is how it is going to go, it is better to just do that from the get go. I think this has made for a nicer and more scalable experience.

I have a video of my walking through this notebook here <https://youtu.be/NQGh8rs6Fk8>

The code of the tool is here <https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/contrib/pcode/__init__.py>

# The Basic Idea

We have a simple program which we assemble

```python
%%file /tmp/simple.s

.global simple
.global done
simple:
    mov $1, %rdi
    add %rdi, %rax
    nop
    nop
    nop
done:
    ret

```

```python
! gcc -c /tmp/simple.s -o /tmp/simple.o
```

We can symbolically execute / bounded model check this program. This is a good smoke test to make sure everything is working right and can uncover many bugs

```python
import kdrag.contrib.pcode as pcode

ctx = pcode.BinaryContext("/tmp/simple.o")

init_mem = ctx.init_mem()
def prop_cb(addr, st):
    if addr == ctx.resolve_addr("done"):
        return st.get_reg(ctx, "RAX") == init_mem.get_reg(ctx, "RAX") + 1

ctx.model_check(init_mem, prop_cb, entries=["simple"], exits=["done"], insns=3)

```

    0x400007
    0x40000a
    0x40000b
    0x40000c
    Instruction limit hit. No counterexample found in  3

But the new feature in the system is to specify a function that translates the low level pcode execution model to a higher level model of the users choice. This high level model has a `step` function that specifies transitions of a higher level state. This state is more what the state looks like at a compiler IR level, consisting of a program counter of labels and different logical variable.

The user also needs to specify a definition of how to read the high state from the low state. This is specified in a function `high_low` given to the bisimulation checker. Then simulation relation between these two executions can be performed basically fully automatically by z3. The symbolic executor discovers all possible trace fragments between the labels in the assembly and verifies that all of them correspond to pathways in the high level model.

In terms of equations, there is a square `high_low . step_low = step_high . high_low`. It should not matter if one lifts the state and then executes a high step vs executes a low step and then lifts the state.

![](/assets/high_low_step.png)

```python
import kdrag.contrib.pcode as pcode
import kdrag.smt as smt
import kdrag.reflect as reflect
import kdrag as kd

ctx = pcode.BinaryContext("/tmp/simple.o")

def high_low(addr, memstate):
    i = memstate.get_reg(ctx, "RAX")
    return i

BV64 = smt.BitVecSort(64)
@reflect.reflect
def step(i : BV64) -> BV64:
    return i + 1

ctx.bisim(high_low, step, entries=["simple"], exits=["done"])
```

    Bisimulation proof succeeded  over all paths [('simple', 'done')]

We can then write proofs over this higher level model, which are easier to work with than all the junk ghidra produces to model all the bits and pieces of the assembly.

```python
i = smt.Const("i", BV64)
@kd.Theorem(smt.ForAll([i], step(i) == i +1))
def step_inc(l):
    i = l.fix()
    l.unfold(step)
    l.auto()
step_inc
```

&#x22A8;ForAll(i, step(i) == i + 1)

# Mem Copy

A slightly more involved program is a simple memcopy. This is interesting because memcopy is actually sometimes written in assembly and can involve some somewhat complex logic for loop unrolling or breaking up the copy into words or larger chunks.

Here is a version

```python
%%file /tmp/mycpybad.s
    .text
    .globl mycpy
    .align 2

# a0 is src
# a1 is dst
# a2 is len
mycpy:
.loop:
    lb t0, 0(a0)
    sb t0, 0(a1)
    addi a0, a0, 1
    addi a1, a1, 1
    addi a2, a2, -1
    bne a2, x0, .loop
.done:
    ret
```

```python
! nix-shell -p pkgsCross.riscv32.buildPackages.gcc --run "riscv32-unknown-linux-gnu-gcc -c -O2 /tmp/mycpybad.s  -o /tmp/mycpybad"
```

We can model check it to see if that `len` always is less than it's initial value

```python
from kdrag.contrib.pcode import BinaryContext
import kdrag.contrib.pcode as pcode
ctx = BinaryContext("/tmp/mycpybad", langid="RISCV:LE:32:default")

init_mem = ctx.init_mem()
def prop_cb(addr, mem):
    if addr == ctx.resolve_addr(".loop"):
        return smt.ULE(mem.get_reg(ctx, "a2"), init_mem.get_reg(ctx, "a2"))


ctx.model_check(init_mem, prop_cb, entries=["mycpy"], cuts=[".loop"], exits=[".done"],insns=25)
```

    Unknown reloc 43 on RISCV:LE:32:RV32GC
    Unknown reloc 44 on RISCV:LE:32:RV32GC


    0x400006
    0x40000a
    0x40000c
    0x40000e
    0x400010
    Counterexample found for property:  ULE(4294967295 + select32le(register(state0), &a2),
        select32le(register(state0), &a2))
    addr 0x400010

Oh! What's this? Well, actually, you may have noticed I called this `mycpybad`. It is missing an initial check that if `len = 0` is given causes it to wrap around. This is actually related to a bug we have found in a code base.

We can add in a branch to check for this case.

```python
%%file /tmp/mycpy.s
    .text
    .globl mycpy
    .align 2

# a0 is src
# a1 is dst
# a2 is len
mycpy:
    beq a2, x0, .done
.loop:
    lb t0, 0(a0)
    sb t0, 0(a1)
    addi a0, a0, 1
    addi a1, a1, 1
    addi a2, a2, -1
    bne a2, x0, .loop
.done:
    ret
```

```python
! nix-shell -p pkgsCross.riscv32.buildPackages.gcc --run "riscv32-unknown-linux-gnu-gcc -c -O2 /tmp/mycpy.s  -o /tmp/mycpy"
```

We can model check that the `a2` register which is the `len` field stays less than it's original value. It is also good as a smoke test to state something not true to make sure the executor find it.

```python
from kdrag.contrib.pcode import BinaryContext
import kdrag.contrib.pcode as pcode
from kdrag.all import *
ctx = BinaryContext("/tmp/mycpy", langid="RISCV:LE:32:default")

init_mem = ctx.init_mem()
def prop_cb(addr, mem):
    if addr == ctx.resolve_addr(".loop"):
        #return mem.get_reg(ctx, "a2") != init_mem.get_reg(ctx, "a2") - 2
        return smt.ULE(mem.get_reg(ctx, "a2"), init_mem.get_reg(ctx, "a2"))


ctx.model_check(init_mem, prop_cb, entries=["mycpy"], cuts=[".loop"], exits=[".done"],insns=25)
```

    0x400014
    0x400004
    0x400008
    0x40000c
    0x40000e
    0x400010
    0x400012
    0x400004
    ...
    0x40000e
    0x400010
    0x400012
    0x400004
    0x400014
    0x400008
    Instruction limit hit. No counterexample found in  25

Well, we didn't find anything. maybe there is a violation if we let it run for 26 instructions? 1000 instructions? 100000000 instructions? Hard to say.

But here comes in the simulation module and the unbounded verification it enables.

We can write down a higher level model of the execution and check a simulation between the high and low steps.

The model is written using knuckledragger's reflection feature which hopefully makes it a little more pleasant and readable since it is python syntax. A spec is kind of only as good as it's readability ultimately.

```python
from kdrag.contrib.pcode import BinaryContext
import kdrag.contrib.pcode as pcode
from kdrag.all import *

ctx = BinaryContext("/tmp/mycpy", langid="RISCV:LE:32:default")

PC = kd.Enum("PC", ["mycpy", "loop", "done"])
BV32 = smt.BitVecSort(32)
State = kd.Struct("State", ("pc", PC), ("ram", smt.ArraySort(BV32, smt.BitVecSort(8))), ("len", BV32), ("src", BV32), ("dst", BV32))

labels = {
    "mycpy" : PC.mycpy,
    ".loop" : PC.loop,
    ".done" : PC.done
}
def high_low(addr, memstate):
    for label, pc in labels.items():
        if addr == ctx.resolve_addr(label):
            break
    else:
        raise Exception("Unexpected addr", hex(addr))
    return State(pc=pc, ram=memstate.ram, len=memstate.get_reg(ctx, "a2"), src=memstate.get_reg(ctx,"a0"), dst=memstate.get_reg(ctx,"a1"))


@kd.reflect.reflect
def step(st : State) -> State:
    if st.pc == PC.mycpy:
        if st.len == smt.BitVecVal(0, 32):
            return st._replace(pc = PC.done)
        else:
            return st._replace(pc = PC.loop)
    elif st.pc == PC.loop:
        st = st._replace(ram=smt.Store(st.ram, st.dst, st.ram[st.src]))
        st = st._replace(len=st.len-1)
        st = st._replace(src=st.src+1)
        st = st._replace(dst=st.dst+1)
        if st.len == 0:
            return st._replace(pc = PC.done)
        else:
            return st._replace(pc = PC.loop)
    elif st.pc == PC.done:
        return st
    else:
        return st #kd.Undef(State) # unreachable
```

```python
ctx.bisim(high_low, step, entries=["mycpy"], exits=[".done"], cuts=[".loop"])
```

    Bisimulation proof succeeded  over all paths [('mycpy', '.loop'), ('.loop', '.loop'), ('.loop', '.done')]

Finally, we can also define the transitive closure of this step relation and proof manually that some invariants hold for all time steps.

```python
st0 = smt.Const("st0", State)
t = smt.Int("t")
trans_mycpy = kd.trans(step)
st = trans_mycpy(t, st0)
```

```python
@kd.Theorem(smt.ForAll([t], st0.pc == PC.mycpy, smt.And(
    st0.src + st0.len == st.src + st.len, # The end of array at src is invariant
    st0.dst + st0.len == st.dst + st.len, # The end of array at dst is invariant
)))
def mycpy_inv(l):
    t = l.fix()
    l.induct(t)
    n = l.fix()
    l.auto(by=[trans_mycpy.defn])
    
    l.unfold(trans_mycpy)
    
    l.simp()
    l.auto()

    l.fix()
    l.intros()
    l.unfold(trans_mycpy)
    l.unfold(step)
    l.auto()

mycpy_inv
```

&#x22A8;ForAll(t,
       Implies(pc(st0) == mycpy,
               And(src(st0) + len(st0) ==
                   src(trans_step(t, st0)) +
                   len(trans_step(t, st0)),
                   dst(st0) + len(st0) ==
                   dst(trans_step(t, st0)) +
                   len(trans_step(t, st0)))))

```python
@kd.Theorem(smt.ForAll([t], st0.pc == PC.mycpy,
                        smt.And(smt.ULE(st.len, st0.len),
                                smt.ULE(0, st.len),
                                smt.Implies(st.pc == PC.loop, smt.ULE(1, st.len))
                                )))
def mycpy_len_inv(l):
    t = l.fix()
    l.intros()
    l.induct(t)
    n = l.fix()
    l.auto(by=[trans_mycpy.defn])

    # case 0
    l.unfold(trans_mycpy)
    l.auto()

    n = l.fix()
    l.intros()
    l.unfold(trans_mycpy)
    l.unfold(step)
    l.auto()

mycpy_len_inv
```

&#x22A8;ForAll(t,
       Implies(pc(st0) == mycpy,
               And(ULE(len(trans_step(t, st0)), len(st0)),
                   ULE(0, len(trans_step(t, st0))),
                   Implies(pc(trans_step(t, st0)) == loop,
                           ULE(1, len(trans_step(t, st0)))))))

This is admittedly more work and more conceptually complicated. A lot of value can be delivered by fuzzing and bounded model checking and these should usually be done first.

# Bits and Bobbles

Previous posts:

- <https://www.philipzucker.com/asm_verify4/>
- <https://www.philipzucker.com/asm_verify3/>
- <https://www.philipzucker.com/asm_verify2/>
- <https://www.philipzucker.com/assembly_verify/>

BMC
Example showing failure of off by one error
video?

Soundness document like AWS <https://github.com/awslabs/s2n-bignum/blob/main/doc/s2n_bignum_soundness.md>

It would be reasonable to port this over to lean, which might make it all more official seeming, but there are surely dragons there too. I've spent a lof of time conquering the dragons on the road I've chosen.

Could still cleanup the countermodel output by a lot

Extened to bigger examples
