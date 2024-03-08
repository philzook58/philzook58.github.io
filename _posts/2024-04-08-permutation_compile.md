---
date: 2024-04-08
title: "Copy and Micropatch: Writing Binary Patches in C with Clang preserve_none"
---

I've been working on writing intra-function binary patches using high level C code for a few years.

It is really hard to precisely control some aspects of the assembly coming out of a C compiler. By design, the compiler has the ability to optimize and rearrange the code. This is a good thing, but it can be a problem if you want to write a binary patch in a high level language using a stock compiler.

The main thing you can guarantee about the binary is the ABI, in particular [calling conventions](https://en.wikipedia.org/wiki/Calling_convention). If the compiler doesn't comply wth the ABI, the program won't work.

An interesting technique for using an off the shelf compiler to compile C program fragments is to use ABI abuse to read, write, and preserve registers. This is inspired by [Copy and Patch JIT](https://news.ycombinator.com/item?id=38769874) like that which recently landed in the CPython interpreter.

In the typical x64-64 calling convention the first 6 arguments are passed in registers and the rest on the stack. Because of this, I can directly read rdi, rsi, rdx, rcx, r8, r9.

```C
void PATCHCODE(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9){
    if(rcx >= r8){
        rdi = rsi * rdx; 
    }
}
```

This isn't enough though. You want to use `-O2` and the compiler can see that these aren't realy side effecting so will just delete this code. Plus there is no guarantee that the variable `rdi` stays in the registers `%rdi`. This is true only at exactly the function entry.

So another nice trick is using a tail call giving it the output register values. This leaves the stack alone and just jumps to the new function (assuming that tail call optimization actually triggers). By giving it the same arguments, they _must_ be preserved.

```C
uint64_t CALLBACK(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9);
uint64_t PATCHCODE(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9){
    // Some random patch code here
    if(rcx >= r8){
        rdi = rsi * rdx; 
    }
    // End patchcode
    return CALLBACK(rdi, rsi, rdx, rcx, r8, r9);
}
```

Any arguments after the first six are placed on the stack. In this manner, you can also get read and write access to the stack by appending as many arguments as you need to get to the stack position of interest.

```C
uint64_t PATCHCODE(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9, uint64_t stack_arg1, uint64_t stack_arg2){
    // ...
}
```

Globals can also be accessed ether by declaring them as extern and fixing up later

```C
extern uint32_t bufferposition;
```

Or by directly giving an address literal

```C
const * uint32_t bufferpostion = 0xdeadbeef;
```

Requiring the compiler to preserve this many registers may be undesirable. Actually, it's important to give it little scratch space. One method which is a bit icky but seems to work is to replace the clobberable registers in the `CALLBACK` with uninitialized junk variables.

```C
    uint64_t junk; // uninitialized
    return CALLBACK(rdi, rsi, junk, junk, r8, r9); // allow compiler to clobber rdx and rcx
```

This technique works on any stock compiler on any architecture if you swap out the x86-64 calling convention for that architectures. If your compiler doesn't do tail calls, that isn't a disaster. You may need to cut off call setup at the end of the function if this is the case.

Because of considerations like this, the technique isn't _quite_ reliable enough to be totally automated without a human taking a peek at the assembly.

With the new [`preserve_none`](https://discourse.llvm.org/t/rfc-exposing-ghccc-calling-convention-as-preserve-none-to-clang/74233/27) calling convetion available in clang-19, we get even more control. Now the calling convetion also gives us control over r10, r11, r12, r13, r14, r15, and rax.

```C
uint64_t __attribute__((preserve_none))  CALLBACK(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9, uint64_t r11, uint64_t r12, uint64_t r13, uint64_t r14, uint64_t r15, uint64_t rax);
uint64_t __attribute__((preserve_none)) foo(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9, uint64_t r11, uint64_t r12, uint64_t r13, uint64_t r14, uint64_t r15, uint64_t rax){
       return CALLBACK(rdi, rsi, rdx, rcx, junk, r9, r11, r12, r13, r14, r15, rax);
}
```

For any other precise control you might need, the best option to my knowledge is inlne assembly, which is a tricky fellow. [Inline assembly](https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html) is a useful feature to inject assembly in the middle of a C function.

In an interesting analogy, trying to write a binary micropatch is the except dual of inline assembly. We need to specify what regsters are coming in (input operands) and which are coming out (output operands), where multiple exit possibly return to (gotolabels = different `CALLBACKS`) and control what gets clobbered.

Registers can be marked as unneeded by filling in their slot in the final tail cal callback with a junk variable.

# Bits and Bobbles

I wrote a small ghidra script to wrap calling a compiler in the copy and micropatch style <https://github.com/philzook58/pcode2c/blob/main/ghidra_scripts/compile.py> . It templates out the callng convention. Eventually I could fill in global addresses, pull in names from the ghidra decompiler, and other useful bits if people are excited about that.

I thought maybe the varargs mechanism could be used to access the stack, but tinkring wth it for 10 minutes I wasn't getting good results.

Maybe I can get CALLBACK to be set to the actual patch return address using a const function pointer?

### Permuting Assmbly Registers

An idea I also kind of like is that of applying a textual permutation of registers in the resulting assembly. Like serioualy as dumb as string search and replace of `%rax` -> `%rdi`. In this way you could turn abi registers into ones of interest, or permute a undesired clobber into an ok to clobber

Never quite actually tried it though

{% raw %}

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
def fragment(x, header, invars, outvars):
  return f"""
    vod cb();
    {header}
    void fragment(uint64_t r0, uint64_t r1, uint64_t r2, uint64_t r3, uint64_t r4){{ //varargs
          // inavrs
          {invars}
          // patch code
          {x}
          // stack outvars{outvars}
          cb({outvars});
          return;
    }}
  """
# Hmm. could verify the permutation
def permute(asm, perm):
  # simultaneous replacement
  for k in perm.keys():
    asm = asm.replace(k, "TEMPYTEMPY"+k)
  for k,i in perm.items():
    asm = asm.replace("TEMPYTEMPY"+k, i)
  return asm

def clip_ret(asm):

def used_regs(asm, regs):
  return [reg for reg in regs if asm.find(reg) != -1]


  re.match
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
```

{% endraw %}

### Copy and Patch

[copy and patch compilation](https://twitter.com/cfbolz/status/1516418354579394566?s=20&t=7564nBvc82Jdkz_E3ccZbA)
<https://sillycross.github.io/2023/05/12/2023-05-12/> copy and patch

ok what would it take for this to work?
<https://github.com/llvm/llvm-project/pull/76868>
<https://discourse.llvm.org/t/rfc-exposing-ghccc-calling-convention-as-preserve-none-to-clang/74233/27>

<https://godbolt.org/#z:OYLghAFBqd5QCxAYwPYBMCmBRdBLAF1QCcAaPECAMzwBtMA7AQwFtMQByARg9KtQYEAysib0QXACx8BBAKoBnTAAUAHpwAMvAFYTStJg1AB9U8lJL6yAngGVG6AMKpaAVxYMQAZi6kHAGTwGTAA5dwAjTGIQACYNUgAHVAVCWwZnNw9YmMTk1IFA4LCWSOi4i0wrGwEhAiZiAgz3Tx8KqrTa%2BoJC0Iio2PiFOoamrJicoa6e4tKBgEoLVFdiZHYOAFINAEF1mK8g5DcsAGp1r0ch/EEAOgQz7E2tgHon44AlABEASVJ3oR/3h8ABq/N6OEHvAAcoIAnKCuL53lwckivPDpEiAKygrZAx4vTCqAhRBjHVxBAheGLGAjHcKuKhUKJJFLVBhnABC%2BKeaAYQ2OACoyRSqTTHuTBKLaULefz6YzmXk2acvB9jhAJQQAGySGmCuYaVQwjQmzniik6vWmJgEAjEPD04mmKAJYiYJTEABumGMDAEmDmc2Ox0cW38/g5W0cAGkNRbdbTiPhfprLYmUin43qk6pM4I08cVrnhfmE4XoSXtWXiHDKwXiAi81Xs8im/WuGi69WpG3u9iu9mmKo5mbtqmy9bbfbHT7jC63R7vb7/YHjvxUHHS9nkwP03he9vi%2BPs8gj1nExXj4na1fC43d3eUbeG53nz2Hw3%2B8%2BhyOAOxc7Zg2DF43WAPAhiiD8uA0Y4mAUFgIF2GIGw0JCRy8ACtiAwsUhVNViFw3YOULIdThiYjkVHLCgLwKgIAIvAVUcY5fz/TDsOw4hSLONUpCo7D1l/D5Hmw2iIAFeUmWIFl8lJe4eOOOI2JEjjgwkhkpJk5UFNQjCVODQThMAoCQOgvDjkkGJ%2BJMp44IQpCWFQT0yMxeIXN2TEUKQkAQCQ4gkPo6DA2s4Nb20VwGAAaxCwtMAIZZSVDcNIxjeidwY34c0y09fnCqLMtrBtEQbFEX0y99P0yn8qMMx4OAWWhOExXhPA4LRSFQThmIUJYVkwMifF4AhNHqhZIpAVzrg0LVMUxLwtV/PYuC1LxIUkbFGo4SQWpGjrOF4BQQHiYa2vq0g4FgJA0BYBI6CichKGu276GiZBDkMYAaWICLIr4OhiQIyhwl28IgnqABPTgeFIUHmGIcGAHlwm0TBrCh3hrrYQQEYYWhIdO0gsHpYBHDEWhDu4XgsBYD7xAJ/A3WsPBvQp9rCVR1xiXR8hBEqXbaAdLj4ecLBdrtPAWHRhYqAMYAFAANTwTAAHcEYSRhuf4QQRDEdgey1%2BQlDUXbdF8AwjBAUxjHMAXwkOyAFlQBI2QpgBaBGvF4JyontLB7YgBZLFRtl7AYJwXGaPQAiCXoSn6XwtLSUZPATpU0mmPpol8IOmZqYZGgjrJs8qYOOnzjO46zix8%2BTvRJgaCvZi4QPetWPRlcMAg1YIL4GH4KX9CanaCc6jhjlUSEtVdnVjneox1TtH6gwgXBCBIAbm6GkbA1IcbJBha4YS8SRJBWmJfy1SF5q4X9B624f2tHg6jtIE6tB3zaYgfr39tf7eFm9AxOwkggA%3D%3D> Godbolt example
iframe version. Hmmm. I like that
<iframe width="800px" height="200px" src="https://godbolt.org/e#z:OYLghAFBqd5QCxAYwPYBMCmBRdBLAF1QCcAaPECAMzwBtMA7AQwFtMQByARg9KtQYEAysib0QXACx8BBAKoBnTAAUAHpwAMvAFYTStJg1AB9U8lJL6yAngGVG6AMKpaAVxYMQAZi6kHAGTwGTAA5dwAjTGIQACYNUgAHVAVCWwZnNw9YmMTk1IFA4LCWSOi4i0wrGwEhAiZiAgz3Tx8KqrTa%2BoJC0Iio2PiFOoamrJicoa6e4tKBgEoLVFdiZHYOAFINAEF1mK8g5DcsAGp1r0ch/EEAOgQz7E2tgHon44AlABEASVJ3oR/3h8ABq/N6OEHvAAcoIAnKCuL53lwckivPDpEiAKygrZAx4vTCqAhRBjHVxBAheGLGAjHcKuKhUKJJFLVBhnABC%2BKeaAYQ2OACoyRSqTTHuTBKLaULefz6YzmXk2acvB9jhAJQQAGySGmCuYaVQwjQmzniik6vWmJgEAjEPD04mmKAJYiYJTEABumGMDAEmDmc2Ox0cW38/g5W0cAGkNRbdbTiPhfprLYmUin43qk6pM4I08cVrnhfmE4XoSXtWXiHDKwXiAi81Xs8im/WuGi69WpG3u9iu9mmKo5mbtqmy9bbfbHT7jC63R7vb7/YHjvxUHHS9nkwP03he9vi%2BPs8gj1nExXj4na1fC43d3eUbeG53nz2Hw3%2B8%2BhyOAOxc7Zg2DF43WAPAhiiD8uA0Y4mAUFgIF2GIGw0JCRy8ACtiAwsUhVNViFw3YOULIdThiYjkVHLCgLwKgIAIvAVUcY5fz/TDsOw4hSLONUpCo7D1l/D5Hmw2iIAFeUmWIFl8lJe4eOOOI2JEjjgwkhkpJk5UFNQjCVODQThMAoCQOgvDjkkGJ%2BJMp44IQpCWFQT0yMxeIXN2TEUKQkAQCQ4gkPo6DA2s4Nb20VwGAAaxCwtMAIZZSVDcNIxjeidwY34c0y09fnCqLMtrBtEQbFEX0y99P0yn8qMMx4OAWWhOExXhPA4LRSFQThmIUJYVkwMifF4AhNHqhZIpAVzrg0LVMUxLwtV/PYuC1LxIUkbFGo4SQWpGjrOF4BQQHiYa2vq0g4FgJA0BYBI6CichKGu276GiZBDkMYAaWICLIr4OhiQIyhwl28IgnqABPTgeFIUHmGIcGAHlwm0TBrCh3hrrYQQEYYWhIdO0gsHpYBHDEWhDu4XgsBYD7xAJ/A3WsPBvQp9rCVR1xiXR8hBEqXbaAdLj4ecLBdrtPAWHRhYqAMYAFAANTwTAAHcEYSRhuf4QQRDEdgey1%2BQlDUXbdF8AwjBAUxjHMAXwkOyAFlQBI2QpgBaBGvF4JyontLB7YgBZLFRtl7AYJwXGaPQAiCXoSn6XwtLSUZPATpU0mmPpol8IOmZqYZGgjrJs8qYOOnzjO46zix8%2BTvRJgaCvZi4QPetWPRlcMAg1YIL4GH4KX9CanaCc6jhjlUSEtVdnVjneox1TtH6gwgXBCBIAbm6GkbA1IcbJBha4YS8SRJBWmJfy1SF5q4X9B624f2tHg6jtIE6tB3zaYgfr39tf7eFm9AxOwkggA%3D%3D"></iframe>

ok what would it take for this to work?
<https://github.com/llvm/llvm-project/pull/76868>
<https://discourse.llvm.org/t/rfc-exposing-ghccc-calling-convention-as-preserve-none-to-clang/74233/27>

pahole. pick a hole. Finding holes in data structures. dwarves suite

The recent addition of the [`preserve_none`](https://discourse.llvm.org/t/rfc-exposing-ghccc-calling-convention-as-preserve-none-to-clang/74233/27) calling convention to clang-19 makes ths technique more powerful, as you get control over more registers.

Sometimes it is useful to patch a binary after compilation.

Ths can be to correct some vulnerability or error or perhaps to pirate the latest version of Dog Gun 7.

Once you know the new binary you want you can do this using a imple hex editor or write a script to overwrite the appropriate bytes.
Ghidra is a great for this because it has a feature rich built in assembler. Right click on any instruction and click "Patch Instruction".

You figure ut the binary by running an assembler.

You figure out the assembly by either knowing assembly or sort of writing the appropriate C program, compiling with `-S` and fiddling with the result.

You can patch in an entire function by compiling it an getting it into the binary somewhere.

It is sometimes desirable to make much smaller patches. This is called a "micropatch". We naturally tend to do micropatches when we patch by hand. We want to change some small branch condition, change whch function is called, nop out some instructions, etc. This is more reliable because recompiling the entire function i error prone. The larger the amount of code we need to change, the more of the binary we need to really understand.

I wrote a small Ghidra script to make this easier to do inside of ghidra.

Something I've been following with interest is Copy and Patch JIT compilation.
The basic idea is to compile a bunch of copies of bytecode, one for every possible regiter allocation choice. Then to jit, you run an allocation pass and select the binary copy of the bytecode operation that fits your choice and just memcopy it in to your JITed code.

This technques requires control over the compiler and the ABI. There are a couple of techniques and hacks they use t achive this. One  using a calling conventioned that was put in the for GHC's use. This calling convention passes way more arguments in registers.

## The only thing you can trust is the ABI

It is quite hard to control exactly the assembly that comes out of a C compiler.
This is by design, because the compiler wants freedom to optimize.

There are both the simple form and the extended form.

In the extended form, you can specify OutputOperands, InputOperands, Clobbers, GotoLabels.

I have not found it that reliable to use inlne assembly to write binary micropatches.

<https://github.com/compiler-explorer/compiler-explorer/blob/main/lib/cfg/cfg-parsers/base.ts> cmpiler exporer parse cfg. Neat.
<https://interrupt.memfault.com/blog/measuring-stack-usage> -fstack-usage
<https://stackoverflow.com/questions/74502091/how-to-use-the-output-clang-fsave-optimization-record-command>

 clang++ -fsave-optimization-record

gcc -o outfile -Xlinker --defsym -Xlinker key=0x9000 sourcefile.c
gcc -o outfile -Xlinker --defsym -Xlinker key=0x9000 sourcefile.c

```bash
echo "
#include <stdint.h>
// RDI, RSI, RDX, RCX, R8, R9, R11, R12, R13, R14, R15, RAX
uint64_t __attribute__((preserve_none))  cb(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9, uint64_t r11, uint64_t r12, uint64_t r13, uint64_t r14, uint64_t r15, uint64_t rax);
uint64_t __attribute__((preserve_none)) foo(uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t rcx, uint64_t r8, uint64_t r9, uint64_t r11, uint64_t r12, uint64_t r13, uint64_t r14, uint64_t r15, uint64_t rax){
    rsi = rsi + rax + 12;
    return cb(rdi, rsi, rdx, rcx, r8, r9, r11, r12, r13, r14, r15, rax);
}
" > /tmp/foo.c
clang-19 -O1 -S /tmp/foo.c -o /tmp/foo.s
cat /tmp/foo.s

```

title: Compiling Micropatch program fragments with gcc

title: C program fragments

```bash


```

In the context of the VIBES project, we have been building a compiler that is supposed to take high level code (C-like. It's funny how context dependent what "high level" means) and compiles it to assembly that can be patched in place

1. This is the dual problem to inline assembly. Inline assembly is inserting little chunks of assembly into some bulk C code.

[Inline assembly](https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html) takes in a couple pieces of information.

It needs to know where to read variables from, where to write them to, what registers get clobbered, and what jumps might occur.

It really does not have a sophisticated view into what the assembly is doing. It is basically a format string copy and paste job.

The register allocator of gcc needs to output input to be pasted into the assembly and know what registers to avoid

```bash
echo '
int foo(){
    int src = 42;
    int dst;   

    asm ("mov %1, %0\n\t"
        "add $1, %0\n\t"
        "# hey yo, mtv RAPS %1"

        : "=r" (dst) 
        : "r" (src));

    return dst;
} ' > /tmp/foo.c
gcc /tmp/foo.c -c -S -O1 -o /dev/stdout
```

```x86
foo:
.LFB0:
        .cfi_startproc
        endbr64
        movl    $42, %eax
#APP
# 6 "/tmp/foo.c" 1
        mov %eax, %eax
        add $1, %eax
        # hey yo, mtv RAPS %eax
# 0 "" 2
#NO_APP
        ret
        .cfi_endproc
```

One approach is to use inline assembly in the patch to mov into variables from known registers
Can we use inline assembly to put stuff in the patch

```C

foo(){
    asm(
        "mov %rax, %var1
        mov %rdi, %var2",
        :
        : var1, var2
    )

    var1 += var2;

    asm(
        "mov %var1, %rax\n\t"
        "mov %var2, %rdi"
     : var1, var2
    )
}

```

```C
int foo(){
    asm("", "=r3", var1, "=rax", var2)

}

```

# Tail Calls for Jumps

Tail call elimination can be used for jumps.

```bash
echo '
#include <stdint.h>
// Each possible callback, with parameters for "writes"
int64_t cb_0xdeadbeef(int64_t x);
int64_t fallthrough();

// code has one parameter for each "read"
int64_t foo(int64_t x){
    if(x < 0){
        return cb_0xdeadbeef(x);
    }
    return fallthrough();
} ' > /tmp/foo.c
gcc /tmp/foo.c -fcf-protection=none -fno-pic -c -S -O2 -o /dev/stdout

```

I fiddled with the options until I liked what I saw.

- `-fcf-protection` turns off emitting `endbr64` instructions. You may or may not need these depending.
- `-fno-pic` makes it not use the plt table for finding the callback

#### What about goto?

`goto` doesn't work because C does not support nonlocal goto. <https://gcc.gnu.org/onlinedocs/gcc/Nonlocal-Gotos.html>

It is in general a confusing problem to consider how to work with program fragments / open programs. What I mean by "fragment", "open", or "program" is vague and you may consider your environement of choice.
Open lambda terms for example are lambda terms that have some variables unbound. The trick is in some manner or another have a notion of context or environment that refers to the variables. These dealings are subtle.

Another place where "open programs" may be considered is that of linking and seperate compilation.

If I take the code `x = y + 4;` and put it in a C file and call `gcc`, it has no idea what to do with that.

1. Full function compiling
2. Full state saving and then a function call
3.

The relationship of hgh level code and low level code is intentionally nebulous because we want to allow compilr writers the freedom to achieve optimizations. In olden times, perhaps each chunk of C would translate quite straightforwardly to a chunk of assembly, but this is not guaranteed.

There are some things that must happen however.
It is at least unusual for the program to not obey the application binary interface (ABI), in particular I'm referring to the function calling conventions. Inlining can perhaps be seen as breaking the ABI.

1. `-O0` or `-Og` makes it better
2. Observable effects have to happen, like printing. Although honestly, I'm not going to be that surprised if my prints occur out of order because of some buffering issue.

A whole separate issue is finding space aka code caves in which to place code. It is often the case that micropatching is attempting to add code where there was none before.

1. Find some code to blast
2. Recompile or optimize existing code.
3.
