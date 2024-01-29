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
