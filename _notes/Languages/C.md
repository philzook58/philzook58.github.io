---
layout: post
title: C
---
[Beej's Guide to C](https://beej.us/guide/bgc/)

<https://stackoverflow.com/questions/7237963/a-c-implementation-that-detects-undefined-behavior>
See compcert and frama-c

static keyword


gcc flags
-E stop after preprcoessor. #include literally includes header file
-s output assembly (don't assemble)
-c output object file

- Wall -Werrer different warning flas https://stackoverflow.com/questions/399850/best-compiler-warning-level-for-c-c-compilers
- -ffunction-sections 

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

https://github.com/google/sanitizers/wiki
Address sanitizer [ASAN](https://en.wikipedia.org/wiki/AddressSanitizer) 
[memory snatizier](https://clang.llvm.org/docs/MemorySanitizer.html) -fsanitize=memory
https://github.com/google/sanitizers
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

https://security.googleblog.com/2022/05/retrofitting-temporal-memory-safety-on-c.html

## Build Systems
Shake
https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems.pdf build systems a la carte



## Stressing C compilers
Csmith
[undefined behavior canaries](https://github.com/regehr/ub-canaries)


[a guide to undefined behavior](https://blog.regehr.org/archives/213)


# Allocators
[DieHard](https://github.com/emeryberger/DieHard) error resitant allocator
Ptmalloc
mimalloc https://github.com/microsoft/mimalloc
"The other allocators are Google's tcmalloc (tc, tag:gperftools-2.8.1) used in Chrome, Facebook's jemalloc (je, tag:5.2.1) by Jason Evans used in Firefox and FreeBSD, the Intel thread building blocks allocator (tbb, tag:v2020.3), rpmalloc (rp,tag:1.4.1) by Mattias Jansson, the original scalable Hoard (git:d880f72) allocator by Emery Berger [1], the memory compacting Mesh (git:67ff31a) allocator by Bobby Powers et al [8], and finally the default system allocator (glibc, 2.31) (based on PtMalloc2)."
[tcmalloc](https://github.com/gperftools/gperftools)
[jemalloc](https://github.com/jemalloc/jemalloc)
[tbb allocator](https://github.com/intel/tbb)
[rpmalloc](https://github.com/mjansson/rpmalloc)
[hoard](https://github.com/emeryberger/Hoard)
[mesh](https://github.com/plasma-umass/Mesh)


[how debuggers work](https://eli.thegreenplace.net/2011/01/27/how-debuggers-work-part-2-breakpoints) int3 and ptrace

# GDB

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