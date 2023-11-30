---
layout: post
title: C
---
- [Stuff](#stuff)
  - [CPP](#cpp)
  - [Make](#make)
  - [CMake](#cmake)
- [Loading](#loading)
- [Sanitization](#sanitization)
  - [Build Systems](#build-systems)
  - [Stressing C compilers](#stressing-c-compilers)
  - [Cosmocc](#cosmocc)
- [Allocators](#allocators)
- [GDB](#gdb)
- [Misc](#misc)

# Stuff

[Beej's Guide to C](https://beej.us/guide/bgc/)

<https://stackoverflow.com/questions/7237963/a-c-implementation-that-detects-undefined-behavior>
See compcert and frama-c

static keyword

gcc flags
-E stop after preprcoessor. #include literally includes header file
-s output assembly (don't assemble)
-c output object file

- Wall -Werrer different warning flas <https://stackoverflow.com/questions/399850/best-compiler-warning-level-for-c-c-compilers>
- -ffunction-sections

[suggestions for secure flags](https://twitter.com/kees_cook/status/1588007082288353281?s=20&t=udFq9u7zLY-5-Ae6VrdqeQ)

```
-Wall
-D_FORTIFY_SOURCE=2
-fsanitize=bounds fsanitize-undefined-trap-on-error
-fstrict-flex-arrays
```

[Getting the maximum of your C compiler, for security](https://airbus-seclab.github.io/c-compiler-security/)
[GCC's new fortification level: The gains and costs](https://developers.redhat.com/articles/2022/09/17/gccs-new-fortification-level)

gcc -shared foo.o -o foo.so  - makes a dynamically linkable file. You actually have to make a object file first before you do this

g++ _is_ gcc with some appropriate flags set for C++

`-lgsl` is the same as `-l gsl` and looks in system paths for a file called `libgsl.o`. It automatically appends `.o` and `lib`. Very odd to my sensibilities.

`-I` is useful to help

Header files and prototypes actually become "code" in the sense they are entries in the object file.

### CPP

The C preprocessor.

It can be run on its own

- `#include` literally brings that file in. `<>` vs `""` is a difference in what search path it uses an prioritizes.
- `#define`
mcpp is an alternative

It can be programmed. This is typically ill adviuced <http://conal.net/blog/posts/the-c-language-is-purely-functional> An amusing essay saying that cpp is a pureply function programminbg language

`__COUNTER__` is an autoincrementing thing
There are things for string concatenation

### Make

- <https://learnxinyminutes.com/docs/make/>
- <http://swcarpentry.github.io/make-novice/>

An amusing essay that `make` is logic programming language. It is true.
The file system is the database of sorts.

There is a default makefile that is included with every make invocation if you don't turn it off.

### CMake

<https://learnxinyminutes.com/docs/cmake/>

<https://www.youtube.com/watch?v=zOmUHM0sFOc&ab_channel=CyrillStachniss>

# Loading

<https://news.ycombinator.com/item?id=29104841> <http://dbp-consulting.com/tutorials/debugging/linuxProgramStartup.html>

# Sanitization

Dynamic Bug detection technique
[SoK](https://oaklandsok.github.io/papers/song2019.pdf) sanitizing for security. Really interesting.

<https://github.com/google/sanitizers/wiki>
Address sanitizer [ASAN](https://en.wikipedia.org/wiki/AddressSanitizer)
[memory snatizier](https://clang.llvm.org/docs/MemorySanitizer.html) -fsanitize=memory
<https://github.com/google/sanitizers>
ThreadSanitizier - detect race conditions
UBSan undefine behavior sanitizer

valgrind
SAFECode, and SoftBound

See also notes on CTF stuff and compilers

Shadow memory. mapping of memory to shadow memory where you can hold metadata.
Guard pages - try to access an overflow and hit unmapped page, you'll crash

fat pointers - make pointer a struct
tagged pointer - use unused bits in pointer. 64 bits is too many. ALignment makes low bits unused

[The state of static analysis in the GCC 12 compiler](https://developers.redhat.com/articles/2022/04/12/state-static-analysis-gcc-12-compiler)

- [-fanalyzer](https://gcc.gnu.org/onlinedocs/gcc/Static-Analyzer-Options.html#index-fanalyzer)
- -Wanalyzer-tainted-array-index
- -Wanalyzer-null-dereference

<https://security.googleblog.com/2022/05/retrofitting-temporal-memory-safety-on-c.html>

## Build Systems

Shake
<https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems.pdf> build systems a la carte

## Stressing C compilers

Csmith
[undefined behavior canaries](https://github.com/regehr/ub-canaries)

[a guide to undefined behavior](https://blog.regehr.org/archives/213)

## Cosmocc

<https://github.com/jart/cosmopolitan>

```bash
echo '
// hello.c
#include <stdio.h>

int main() {
  printf("hello world\n");
}
' > /tmp/hello.c
~/Downloads/cosmocc/bin/cosmocc -o /tmp/hello /tmp/hello.c
file /tmp/hello # /tmp/hello: DOS/MBR boot sector; partition 1 : ID=0x7f, active, start-CHS (0x0,0,1), end-CHS (0x3ff,255,63), startsector 0, 4294967295 sectors 
# what
/tmp/hello
/tmp/hello --strace
/tmp/hello --ftrace

```

the strace and ftrace options are cool. WHat else might go in there?

ape command for "faster"?

# Allocators

[DieHard](https://github.com/emeryberger/DieHard) error resitant allocator
Ptmalloc
mimalloc <https://github.com/microsoft/mimalloc> <https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf>
"The other allocators are Google's tcmalloc (tc, tag:gperftools-2.8.1) used in Chrome, Facebook's jemalloc (je, tag:5.2.1) by Jason Evans used in Firefox and FreeBSD, the Intel thread building blocks allocator (tbb, tag:v2020.3), rpmalloc (rp,tag:1.4.1) by Mattias Jansson, the original scalable Hoard (git:d880f72) allocator by Emery Berger [1], the memory compacting Mesh (git:67ff31a) allocator by Bobby Powers et al [8], and finally the default system allocator (glibc, 2.31) (based on PtMalloc2)."
[tcmalloc](https://github.com/gperftools/gperftools)
[jemalloc](https://github.com/jemalloc/jemalloc)
[tbb allocator](https://github.com/intel/tbb)
[rpmalloc](https://github.com/mjansson/rpmalloc)
[hoard](https://github.com/emeryberger/Hoard)
[mesh](https://github.com/plasma-umass/Mesh)

Strategies

- First fit - scan linked list
- next fit - avoid having to scan head where you know you won't find a good block
- best fit - scan entire list

[A memory allocator - doug lea](https://gee.cs.oswego.edu/dl/html/malloc.html)

Metadata is stored next to chunk

- free,in use flags
- size
- pointers in free lists are often stored in same place user data would be

Bins
Coalescing

Top chunk, "the wilderness"

# GDB

[how debuggers work](https://eli.thegreenplace.net/2011/01/27/how-debuggers-work-part-2-breakpoints) int3 and ptrace

[beej's quick guide to gdb](https://beej.us/guide/bggdb/)

help command. lots of stuff

- ni next instruction. next / nexti
- si step stepi
- info all-registers registers
- where
- jump
- display $rax - always print rax. display/10i *$rip
- x/10i $pc - next 10 instructions
- x/10x $sp  look at stack. x/s look at string
- list *$rip shows you a few lines before and after
- layout split asm src. tui disable. tui enable

# Misc

<https://github.com/nothings/stb> stb single-file public domain libraries for C/C++. stb_ds is a hash table and vector
<http://nothings.org/stb_ds>

<https://nullprogram.com/blog/2022/08/08/> The quick and practical "MSI" hash table

<https://twitter.com/moyix/status/1556037995169562624?s=20&t=yqv3psiW3ByDbnVTBLr_GA> audit of list functions

<https://man7.org/linux/man-pages/man7/queue.7.html>
instrusive linked list

[Some Were Meant for C The Endurance of an Unmanageable Language](https://www.humprog.org/~stephen/research/papers/kell17some-preprint.pdf)

[cerberus](https://www.cl.cam.ac.uk/~pes20/cerberus/) simulator of C semantics
K semantics

<https://en.wikipedia.org/wiki/Undefined_behavior>

[foundations of cs](http://infolab.stanford.edu/~ullman/focs.html) kind of cool they do it in C

[All kernighan and ritchie programs](https://github.com/ptdecker/cbasics/tree/master)
[ACSL by example programs](https://github.com/fraunhoferfokus/acsl-by-example/tree/master/StandardAlgorithms)
[svcomp C programs](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/main/c?ref_type=heads)

<https://github.com/gouravthakur39/beginners-C-program-examples/tree/master> beginner C programs

<https://stackoverflow.com/questions/562303/the-definitive-c-book-guide-and-list> book list and guide
