---
layout: post
title: Fuzzing
---

- [Fuzzing](#fuzzing)
  - [Code Coverage](#code-coverage)
  - [Grammar](#grammar)
  - [AFL](#afl)
- [Symbolic Execution](#symbolic-execution)
  - [Reverse Execution](#reverse-execution)
  - [KLEE](#klee)
  - [SymCC](#symcc)
- [Emulation](#emulation)
  - [Qemu](#qemu)
- [Instrumentation](#instrumentation)
  - [Sanitizers](#sanitizers)
  - [Valgrind](#valgrind)

# Fuzzing
<https://github.com/google/atheris>  <https://blog.trailofbits.com/2024/02/23/continuously-fuzzing-python-c-extensions/>

```python
import atheris

with atheris.instrument_imports():
  import some_library
  import sys

def TestOneInput(data):
  some_library.parse(data)

atheris.Setup(sys.argv, TestOneInput)
atheris.Fuzz()

```

<https://www.fuzzingbook.org/>
fusebmc  <https://github.com/kaled-alshmrany/FuSeBMC>

test-comp <https://test-comp.sosy-lab.org/2024/> is basically fuzzing right?

SBFT fuzz comp 2023 <https://arxiv.org/pdf/2304.10070.pdf> e AFL+++ AFLRUSTRUST7 AFLSMART++8  HASTEFUZZ9 LEARNPERFFUZZ LIBAFL LIBFUZZER PASTIS  and SYMSAN

Mayhem
[Fuzzy-sat](https://arxiv.org/pdf/2102.06580.pdf) running smt queries through a fuzzer
Angora
SLF eclipser

[fuzzing challeneges and reflection](https://mboehme.github.io/paper/IEEESoftware20.pdf)

[fuzzing 22](https://twitter.com/c_cadar/status/1521828920869404677?s=20&t=kBQ6NNrdoK-tcIkhvRqktQ)

[google fuzzbench](https://google.github.io/fuzzbench/)

oss-fuzz

[rode0day](https://rode0day.mit.edu/) rolling fuzzing competition

Greybox

- [libfuzzer](https://llvm.org/docs/LibFuzzer.html) `clagg++ -fsantizer=address,fuzzer myfile.cc` [tutorial](https://github.com/google/fuzzing/blob/master/tutorial/libFuzzerTutorial.md)
- honggfuzz

whitebox

- klee
- sage

[Qsym](https://www.usenix.org/conference/usenixsecurity18/presentation/yun) hybrid fuzzing. concolic execution.

[syzkaller](https://github.com/google/syzkaller) kernel fuzzer
go-fuzz
fuzzili
winafl

Fuzzers compile in extra information to give coverage guidance

Fuzzers use a corpus of input

Using fuzzer to solve csp.
Write checker. Fuzz it. It's randomized search

[Fuzzgym](https://arxiv.org/abs/1807.07490) makes a lot of sense to put neural heuristics in there

<https://www.youtube.com/watch?v=sjLFf9q2NRc&ab_channel=FuzzingLabs-PatrickVentuzelo> afl++ qemy
libfuzzer vs afl vs honggfuzz
corpus grammar based fuzzing, differential fuzzing

<https://github.com/airbus-cyber/ghidralligator> ghidra for fuzzing

## Code Coverage

## Grammar

## AFL

```
git clone https://github.com/AFLplusplus/AFLplusplus
cd AFLplusplus
make distrib
sudo make install
```

AFL.  [AFL++](https://aflplus.plus/) fork of afl

<https://aflplus.plus/libafl-book/> book

 [tutorials](https://github.com/AFLplusplus/AFLplusplus/blob/stable/docs/tutorials.md).

compile using afl-clang-fast++ or use qemu mode.

<https://github.com/mykter/afl-training> afl fuzzing training

<https://afl-1.readthedocs.io/en/latest/user_guide.html>

```bash
echo "
int main(){
  if(x > 0){
    assert(0);
  }
  return 42;
}" > /tmp/bug.c
afl-gcc /tmp/bug.c -o /tmp/bug
afl-fuzz -i /tmp/corpus -o /tmp/out /tmp/bug
```

AFT qemu
deferred forkserver
<https://github.com/AFLplusplus/AFLplusplus/blob/stable/instrumentation/README.persistent_mode.md>

# Symbolic Execution

[MAAT](https://maat.re/tutorials/get_started.html) Ttrail of bits using ghidra

<https://github.com/eurecom-s3/symcc>
[symqemu](https://github.com/eurecom-s3/symqemu)

[unicorn](https://www.unicorn-engine.org/) - ripped out the heart of qemu and made it programmatically accessible. Based on an old version of qemu though

KLEE

primus - bap's emulator framework

panda <https://github.com/panda-re/panda> - built on qemu. record and replay executions

[](https://github.com/analysis-tools-dev/dynamic-analysis)

compartment aware fuzzing?

Qsym

## Reverse Execution

Coming back from crashes. Or how to get to bad code spots?

## KLEE

klee rust - alastair reid was pushing

`sudo snap install klee`

<https://klee.github.io/tutorials/testing-function/>

<https://github.com/klee/klee/blob/master/include/klee/klee.h> I don't know if this header has been installed on by system, but I don't need much of it

```bash
echo "
//#include \"klee/klee.h\"
#include <stdint.h>
#include <stddef.h>
void klee_make_symbolic(void *addr, size_t nbytes, const char *name);

int get_sign(int x) {
  if (x == 0)
    return 0;

  if (x < 0)
    return -1;
  else
    return 1;
}
int main() {
  int a;
  klee_make_symbolic(&a, sizeof(a), \"a\");
  return get_sign(a);
}
" > /tmp/get_sign.c
# need llvm bitcode
clang-13  -emit-llvm -c -o /tmp/get_sign.bc /tmp/get_sign.c 
#klee /tmp/get_sign.bc
#cd /tmp
#llvm-dis get_sign.bc
#klee /tmp/get_sign.bc
# I can't get this to work. I guess just use the docker.
docker run -it -v /tmp/get_sign.bc:/tmp/get_sign.bc klee/klee klee /tmp/get_sign.bc
ktest-tool /tmp/ktest-out-0/test000001.ktest
```

files generated:

- info
- ktest files
-

klee.kleaver klee.env klee.stats klee.run klee.replay klee.ktest
ktest-tool <https://klee.github.io/docs/tools/#ktest-tool>
stats - coverage and other stuff in formats from all klee-out directoryes
ktest-gen generate from command line args
ktest-randgen random input

<https://www.youtube.com/watch?v=z6bsk-lsk1Q&ab_channel=AdaLogics>  Introduction to symbolic execution with KLEE - adalogic

gcov <https://gcc.gnu.org/onlinedocs/gcc/Gcov-Intro.html> <https://github.com/gcovr/gcovr> profling data / coverage of lines of code

## SymCC

<https://github.com/eurecom-s3/symcc> don't interpret compile

<https://www.youtube.com/watch?v=htDrNBiL7Y8&ab_channel=AdaLogics> ymbolic execution by compilation with SymCC <https://www.youtube.com/watch?v=zmC-ptp3W3k&ab_channel=AdaLogics>

SymQemu

# Emulation

<https://github.com/nevesnunes/ghidra-plays-mario>

[qiling](https://qiling.io/)

[Icicle: A Re-designed Emulator for Grey-Box Firmware Fuzzing](https://arxiv.org/pdf/2301.13346.pdf) <https://github.com/icicle-emu/icicle-emu> semantics powered by sleigh.

## Qemu

<https://github.com/nyx-fuzz/QEMU-Nyx>
<https://airbus-seclab.github.io/qemu_blog/>
Qemu plugins
Qemu has user land and system

```bash
echo '
#include <stdio.h>
int main(){
  printf("hello world\n");
  return 0;
}
' > /tmp/hello.c
gcc /tmp/hello.c -o /tmp/hello
qemu-x86_64  -strace -singlestep -d in_asm,cpu /tmp/hello 
```

options <https://www.qemu.org/docs/master/user/main.html>

- strace
- trace
- plugin
- d logs
- singlestep (now one-insn-per-tb)

```bash
qemu-x86_64 --help
+ qemu-x86_64 --help
usage: qemu-x86_64 [options] program [arguments...]
Linux CPU emulator (compiled for x86_64 emulation)

Options and associated environment variables:

Argument             Env-variable      Description
-h                                     print this help
-help                                  
-g port              QEMU_GDB          wait gdb connection to 'port'
-L path              QEMU_LD_PREFIX    set the elf interpreter prefix to 'path'
-s size              QEMU_STACK_SIZE   set the stack size to 'size' bytes
-cpu model           QEMU_CPU          select CPU (-cpu help for list)
-E var=value         QEMU_SET_ENV      sets targets environment variable (see below)
-U var               QEMU_UNSET_ENV    unsets targets environment variable (see below)
-0 argv0             QEMU_ARGV0        forces target process argv[0] to be 'argv0'
-r uname             QEMU_UNAME        set qemu uname release string to 'uname'
-B address           QEMU_GUEST_BASE   set guest_base address to 'address'
-R size              QEMU_RESERVED_VA  reserve 'size' bytes for guest virtual address space
-d item[,...]        QEMU_LOG          enable logging of specified items (use '-d help' for a list of items)
-dfilter range[,...] QEMU_DFILTER      filter logging based on address range
-D logfile           QEMU_LOG_FILENAME write logs to 'logfile' (default stderr)
-p pagesize          QEMU_PAGESIZE     set the host page size to 'pagesize'
-singlestep          QEMU_SINGLESTEP   run in singlestep mode
-strace              QEMU_STRACE       log system calls
-seed                QEMU_RAND_SEED    Seed for pseudo-random number generator
-trace               QEMU_TRACE        [[enable=]<pattern>][,events=<file>][,file=<file>]
-plugin              QEMU_PLUGIN       [file=]<file>[,<argname>=<argvalue>]
-version             QEMU_VERSION      display version information and exit

Defaults:
QEMU_LD_PREFIX  = /etc/qemu-binfmt/x86_64
QEMU_STACK_SIZE = 8388608 byte

You can use -E and -U options or the QEMU_SET_ENV and
QEMU_UNSET_ENV environment variables to set and unset
environment variables for the target process.
It is possible to provide several variables by separating them
by commas in getsubopt(3) style. Additionally it is possible to
provide the -E and -U options multiple times.
The following lines are equivalent:
    -E var1=val2 -E var2=val2 -U LD_PRELOAD -U LD_DEBUG
    -E var1=val2,var2=val2 -U LD_PRELOAD,LD_DEBUG
    QEMU_SET_ENV=var1=val2,var2=val2 QEMU_UNSET_ENV=LD_PRELOAD,LD_DEBUG
Note that if you provide several changes to a single variable
the last change will stay in effect.

See <https://qemu.org/contribute/report-a-bug> for how to report bugs.
More information on the QEMU project at <https://qemu.org>.
```

```bash
qemu-x86_64 -d help
Log items (comma separated):
out_asm         show generated host assembly code for each compiled TB
in_asm          show target assembly code for each compiled TB
op              show micro ops for each compiled TB
op_opt          show micro ops after optimization
op_ind          show micro ops before indirect lowering
int             show interrupts/exceptions in short format
exec            show trace before each executed TB (lots of logs)
cpu             show CPU registers before entering a TB (lots of logs)
fpu             include FPU registers in the 'cpu' logging
mmu             log MMU-related activities
pcall           x86 only: show protected mode far calls/returns/exceptions
cpu_reset       show CPU state before CPU resets
unimp           log unimplemented functionality
guest_errors    log when the guest OS does something invalid (eg accessing a
non-existent register)
page            dump pages at beginning of user mode emulation
nochain         do not chain compiled TBs so that "exec" and "cpu" show
complete traces
plugin          output from TCG plugins

strace          log every user-mode syscall, its input, and its result
trace:PATTERN   enable trace events

Use "-d trace:help" to get a list of trace events.
```

<https://github.com/eurecom-s3/symqemu/blame/master/tcg/tcg-op.c> it seems the meat of intrumentation is in tcg-op

TCG is generated against a global context variable.
TCGContext

core
CPUState struct
typedefs.h
CPUArchstate

TCG_REG enum one per arch
target is the system we are emulating. target/whatever/cpu.h has CPUArchState. They are custom per istruvtion

icnlude/tcg/.. has interesting tcg genrating signature

plugin_gen
tcg/reamme
tcg variables

trace. What is this? <https://qemu-project.gitlab.io/qemu/devel/tracing.html>

tci - tiny code interpreter

# Instrumentation

## Sanitizers

This is not emulation. Instrumentation?
ASan <https://www.osc.edu/resources/getting_started/howto/howto_use_address_sanitizer>
`-fsanitize=address`
<https://clang.llvm.org/docs/AddressSanitizer.html>

<https://clang.llvm.org/docs/ControlFlowIntegrity.html> santitize cfi.
<https://dl.acm.org/doi/10.1145/1609956.1609960> Control-flow integrity principles, implementations, and applications

## Valgrind

<https://valgrind.org/>
VEX is the IR in angr

- memcheck - memory error detection
- cachecheck  instruction counts and simple (not trustwothy?) cache simulation
- drd thread error
- massif - heap profile
- dhat - dynamic heap analysis tool
- lackey - example tool
- nulgrind - does nothing. 5x perf hit
- bbv - basic block vector generation. export basic blocks

```bash
echo "
  #include <stdlib.h>

  void f(void)
  {
     int* x = malloc(10 * sizeof(int));
     x[10] = 0;        // problem 1: heap block overrun
  }                    // problem 2: memory leak -- x not freed

  int main(void)
  {
     f();
     return 0;
  }" > /tmp/leak.c
gcc -g -o /tmp/leak /tmp/leak.c
valgrind --leak-check=yes /tmp/leak

```

```bash
valgrind --leak-check=yes /bin/ls .
```
