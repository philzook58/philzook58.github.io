---
title: Validating GDB Interrupt Traces Against a TLA+ Spec
date: 2026-09-04
---

I've been in and around assembly verification for a while now.

There are a couple bitter pills to formal methods:

1. The verification, no matter how careful and rigorous, is only as good as the model insofar as it's engineering utility is concerned.
2. Remodelling the entire universe of computation as it stands so you can simulate and analyze them is a herculean task.
3. The details of how many components work is not even available (microarchitecture of cpus, binary blobs, silicon IP). You can put work into reverse engineering, but mostly all you can do is run the stuff
4. Fuzzing is brutally effective compared to heavier weight formal techniques

There are some sweet suppositories too though:

1. Math and Logic are some of the coolest and beautiful things ever
2. Just because some problems are unsolvable doesn't mean you shouldn't solve the solvable problems

Anyhoo, an angle that I've been trying recently is validating a high level TLA+ spec against as close to the actual system as possible, in particular fuzzing interrupt behavior using GDB and outputting high level trace events. GDB (and it's python scripting api) is quite a nice universal interface for these purposes and allows me to actually run on the hardware via openocd. It quite a bit more likely one has an operating GDB setup compared to a formal spec of the hardware in question.

Sometimes the spec/model implementation of the system has no bugs, and the issue is in an unexpected or subtle difference between the model and the actual thing that gets run. My attempts to consume TLA+, produce an smt formula out of it in python, and then compare against an SMT lift of assembly is just facing an overwhelming wall of complexity <https://www.philipzucker.com/kissin_tla/> . Even if I could get it all to work, it is also of questionable utility vis a vis bitter pill point #1. The SMT model (based in ghidra pcode semantics) is as reasonable of one as I could make, but it has a ton of assumptions and if it's going to be that hard is the juice worth the squeeze?

I still think this is something interesting and ambitious to persue, but doing your formal stuff at the coarser TLA level and validating it against the system using a fuzzing like approach seems more pragmatic.

# TLA JSON Traces

TLC has an interesting option `-loadtrace` it gained somewhat recently. This allows for easy ingestion of traces by other systems in a json format. This is the easy road, but there is also a JSON TLA+ module that enables you to do more flexible things (Merz et al <https://arxiv.org/abs/2404.16075> do it this way).

```python
! curl https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -L -o /tmp/tla2tools.jar
```

      % Total    % Received % Xferd  Average Speed  Time    Time    Time   Current
                                     Dload  Upload  Total   Spent   Left   Speed
      0      0   0      0   0      0      0      0                              0
    100  4.27M 100  4.27M   0      0  6.15M      0                              0

 You can also create the format with `-dumptrace` to see what it looks like. The meat of it is a list of timestamps and state values. Here I took the comomn HourClock example and made the clock value 11 instead of 12, so there is a counterexample.

```python
%%file /tmp/HourClock.tla
----------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLES hr

Init == hr \in 1..11 (* Here I made 11 too small *)

TypeOk == Init

Next == hr' = (hr % 12) + 1

Spec == Init /\ [][Next]_hr

=============================================================================
```

    Overwriting /tmp/HourClock.tla

```python
%%file /tmp/HourClock.cfg
SPECIFICATION Spec
INVARIANT TypeOk
```

    Overwriting /tmp/HourClock.cfg

```python
! java -cp /tmp/tla2tools.jar tlc2.TLC /tmp/HourClock.tla -dumptrace json /tmp/hour_trace.json
```

    TLC2 Version 2026.09.01.002747 (rev: 95b800c)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running breadth-first search Model-Checking with fp 30 and seed -8855051193026396325 with 1 worker on 16 cores with 15416MB heap and 64MB offheap memory [pid: 212036] (Linux 7.0.0-30-generic amd64, Ubuntu 25.0.4 64bit, MSBDiskFPSet, DiskStateQueue).
    Parsing file /tmp/HourClock.tla
    Parsing file /tmp/tlc-8337992476227517303/Naturals.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-8337992476227517303/_JsonTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_JsonTrace.tla)
    Parsing file /tmp/tlc-8337992476227517303/_TLCTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-8337992476227517303/TLC.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-8337992476227517303/TLCExt.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-8337992476227517303/Json.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Json.tla)
    Parsing file /tmp/tlc-8337992476227517303/Sequences.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-8337992476227517303/FiniteSets.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-8337992476227517303/Integers.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module Json
    Semantic processing of module _JsonTrace
    Semantic processing of module _TLCTrace
    Semantic processing of module HourClock
    Linting of module TLCExt
    Linting of module Json
    Linting of module _JsonTrace
    Linting of module _TLCTrace
    Linting of module HourClock
    Starting... (2026-09-02 17:18:45)
    Computing initial states...
    Computed 2 initial states...
    Computed 4 initial states...
    Computed 8 initial states...
    Finished computing initial states: 11 distinct states generated at 2026-09-02 17:18:46.
    Error: Invariant TypeOk is violated.
    Error: The behavior up to this point is:
    State 1: <Initial predicate>
    hr = 11
    
    State 2: <Next line 10, col 9 to line 10, col 27 of module HourClock>
    hr = 12
    
    "CounterExample written: /tmp/hour_trace.json"
    22 states generated, 12 distinct states found, 0 states left on queue.
    The depth of the complete state graph search is 2.
    Finished in 00s at (2026-09-02 17:18:46)
    Trace exploration spec path: /tmp/HourClock_TTrace_1788383925.tla

We can take a look at the json trace

```python
import json
json.load(open("/tmp/hour_trace.json"))
```

    {'counterexample': {'action': [[[1, {'hr': 11}],
        {'name': 'Next',
         'location': {'beginLine': 10,
          'beginColumn': 9,
          'endLine': 10,
          'endColumn': 27,
          'module': 'HourClock'}},
        [2, {'hr': 12}]]],
      'state': [[1, {'hr': 11}], [2, {'hr': 12}]]},
     'vars': ['hr']}

But we don't need to fill in all those fields. Here is a trace that skips 4.

```python
%%file /tmp/hour_trace.json
{
    "vars" : ["hr"],
    "counterexample": {
        "state":
            [
                [1, {"hr" : 1}],
                [2, {"hr" : 2}],
                [3, {"hr" : 3}],
                [4, {"hr" : 5}],
                [5, {"hr" : 6}]
            ],
        "action" : []
    }
}

```

    Overwriting /tmp/hour_trace.json

TLC only makes it through the first 3 states according to the message `The depth of the state graph is 3`. It's subtle, but this is showing this trace is not in the behavior. I think I'm kind of abusing the `-loadtrace` feature, which is why it doesn't show up as big red sad angry letters.

```python
! java -cp /tmp/tla2tools.jar tlc2.TLC /tmp/HourClock.tla -loadtrace json /tmp/hour_trace.json
```

    TLC2 Version 2026.09.01.002747 (rev: 95b800c)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running breadth-first search Model-Checking with fp 116 and seed -4486293823614751512 with 1 worker on 16 cores with 15416MB heap and 64MB offheap memory [pid: 1402344] (Linux 7.0.0-30-generic amd64, Ubuntu 25.0.4 64bit, MSBDiskFPSet, DiskStateQueue).
    Parsing file /tmp/HourClock.tla
    Parsing file /tmp/tlc-4112882943411216787/Naturals.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-4112882943411216787/_TLCTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-4112882943411216787/_JsonTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_JsonTrace.tla)
    Parsing file /tmp/tlc-4112882943411216787/TLC.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-4112882943411216787/TLCExt.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-4112882943411216787/Sequences.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-4112882943411216787/FiniteSets.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-4112882943411216787/Integers.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Parsing file /tmp/tlc-4112882943411216787/Json.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Json.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module _TLCTrace
    Semantic processing of module Json
    Semantic processing of module _JsonTrace
    Semantic processing of module HourClock
    Linting of module TLCExt
    Linting of module _TLCTrace
    Linting of module Json
    Linting of module _JsonTrace
    Linting of module HourClock
    Starting... (2026-09-04 12:09:48)
    Computing initial states...
    Computed 2 initial states...
    Computed 4 initial states...
    Computed 8 initial states...
    Finished computing initial states: 11 states generated, with 1 of them distinct at 2026-09-04 12:09:49.
    Model checking completed. No error has been found.
      Estimates of the probability that TLC did not check all reachable states
      because two distinct states had the same fingerprint:
      calculated (optimistic):  val = 1.8E-18
    14 states generated, 3 distinct states found, 0 states left on queue.
    The depth of the complete state graph search is 3.
    The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).
    Finished in 00s at (2026-09-04 12:09:49)

# An Interrupt Example

It is a challenge to know how to apply TLA+ stuff to systems of interest.

Any concurrent situation is a bit scary and interrupts are  no exception. <https://www.sciencedirect.com/science/article/pii/S1571066107003623>  "Interrupt Verification via Thread Verification" makes some interesting points about the differences between threading and interrupts. Most verification / assurance tooling isn't really geared towards interrupts. They usually target threads. You can try to mangle your code to make it threaded vs interrupty for testing purposes via some macros, but that is alarming in and of itself and of questionable accuracy.

I took a race example from the interrupt section of an embedded textbook (<https://www.amazon.com/dp/0596009836?lv=shuf&channelId=500&plpRedirect=mhFallback> Programming Embedded Systems Chapter 8 Interrupts). It is extremely minimal and yet does demonstrate a reasonable simulacrum of real issues.

An interrupt routine increments a `gIndex` counter and a servicing main loop decrements it.

```python
%%file /tmp/race.c
#include <stdint.h>

#define CLINT_MSIP (*(volatile uint32_t *)0x02000000)


// You need a little initialization code to setup the stack pointer
__asm__(
    ".section .text.init\n"
    ".globl _start\n"
    "_start:\n"
    "la sp, _stack_top\n"
    "call main\n"
    "1: j 1b\n"
);

volatile uint32_t gIndex = 0;

void __attribute__((interrupt("machine"), aligned(4))) interrupt_handler(void) {
    CLINT_MSIP = 0;
    gIndex++;
}

void __attribute__((noinline)) main_loop(void) {
    for (;;)
        if (gIndex)
            gIndex--;
}

void main(void) {
    // register the interrupt handler
    __asm__ volatile("csrw mtvec, %0" :: "r"(interrupt_handler));
    __asm__ volatile("csrsi mie, 8");
    __asm__ volatile("csrsi mstatus, 8");
    main_loop();
}
```

    Overwriting /tmp/race.c

Here's a possible spec of the code. The main loop decrements or the interrupts increments. `msgReceived` and `msgProcessed` are ghost variables so that you can state a useful invariant simply

```python
%%file /tmp/GIndexAtomic.tla
---------------- MODULE GIndexAtomic ----------------
EXTENDS Naturals

VARIABLE gIndex, msgReceived, msgProcessed
vars == <<gIndex, msgReceived, msgProcessed>>
Invariant == /\ msgReceived = msgProcessed + gIndex
             /\ msgReceived >= 0
             /\ gIndex >= 0
             /\ msgProcessed >= 0
Init == /\ gIndex = 0
        /\ msgReceived = 0
        /\ msgProcessed = 0
MainStep == /\ gIndex # 0 
            /\ gIndex' = gIndex - 1
            /\ msgProcessed' = msgProcessed + 1
            /\ UNCHANGED msgReceived
IntStep == /\ gIndex' = gIndex + 1
           /\ msgReceived' = msgReceived + 1
           /\ UNCHANGED msgProcessed
Next == \/ MainStep 
        \/ IntStep
Spec == Init /\ [][Next]_vars
Bound == gIndex <= 10
====================================================
```

```python
%%file /tmp/GIndexAtomic.cfg
SPECIFICATION Spec
INVARIANT Invariant
```

What's the problem?

# The Problem

Let's actually compile this thing.

Blech. loader scripts. I don't know why I find them so disorienting.

```python
%%file /tmp/rv32.ld
ENTRY(_start)
SECTIONS {
    . = 0x80000000;
    .text : { KEEP(*(.text.init)) *(.text*) }
    .rodata : { *(.rodata*) }
    .data : { *(.data*) }
    .bss (NOLOAD) : {
        *(.bss*)
        . = ALIGN(16);
        . += 4K;
        _stack_top = .;
    }
}
```

    Writing /tmp/rv32.ld

```python
! riscv64-unknown-elf-gcc -march=rv32imac_zicsr -mabi=ilp32 -g -O0 -nostdlib -T /tmp/rv32.ld /tmp/race.c -o /tmp/race.elf
```

    /usr/lib/gcc/riscv64-unknown-elf/14.2.0/../../../riscv64-unknown-elf/bin/ld: warning: /tmp/race.elf has a LOAD segment with RWX permissions

Well, the problem is that `gIndex--` isn't actually atomic. It loads into a register `a5`, decrements, and then stores. An interrupt occuring in the section will cause behavior.

The spec has the behavior we want, and it looks like it matches the code according to naive understanding of C, and the issue is only more obvious upon deeper inspection of the assembly. The spec does not actually match the system.

```python
! riscv64-unknown-elf-objdump -d  -S /tmp/race.elf | grep -C 5 "gIndex--"
```

        for (;;)
            if (gIndex)
    8000004c: 800017b7           lui a5,0x80001
    80000050: 0a07a783           lw a5,160(a5) # 800010a0 <gIndex>
    80000054: dfe5                 beqz a5,8000004c <main_loop+0x8>
                gIndex--;
    80000056: 800017b7           lui a5,0x80001
    8000005a: 0a07a783           lw a5,160(a5) # 800010a0 <gIndex>
    8000005e: fff78713           addi a4,a5,-1
    80000062: 800017b7           lui a5,0x80001
    80000066: 0ae7a023           sw a4,160(a5) # 800010a0 <gIndex>

# GDB Tracing

Ok, but we can randomly cause interrupts in a GDB script and emit a json object

```python
%%file /tmp/steps.py
import gdb
import subprocess
import time
import random
import pprint
import json
gdb.execute("set suppress-cli-notifications on")
# get a qemu subprocess started
proc = subprocess.Popen(["qemu-system-riscv32", 
    "-bios", "/tmp/race.elf", 
    "-machine", "virt", 
    "-S", "-s",
    "-display", "none"
    ],stdout=subprocess.DEVNULL)
msgReceived = 0
msgProcessed = 0
trace = [{"msgReceived": msgReceived, "msgProcessed": msgProcessed, "gIndex": 0}]
def record_event():
    trace.append({"msgReceived": msgReceived, "msgProcessed": msgProcessed, "gIndex": int(gdb.parse_and_eval("gIndex"))})
def irq_enabled():
    mstatus = int(gdb.parse_and_eval("$mstatus"))
    mie = int(gdb.parse_and_eval("$mie"))
    mip = int(gdb.parse_and_eval("$mip"))
    return mstatus & 8 and mie & 8 and not mip & 8


try:
    time.sleep(0.1)
    gdb.execute("target remote :1234")
    gdb.Breakpoint("main_loop", temporary=True)
    #gdb.execute("set gIndex = 10")

    # watch changes in gIndex. Easier than picking a program point to observse
    class MyWatchpoint(gdb.Breakpoint):
        def stop(self):
            global msgProcessed, msgReceived, trace
            #msgProcessed += 1
            if int(gdb.parse_and_eval("gIndex")) > trace[-1]["gIndex"]:
                msgReceived += 1
            else:
                msgProcessed += 1
            record_event()
            return True 
    gIndexWrite = MyWatchpoint(spec="gIndex", type=gdb.BP_WATCHPOINT, wp_class=gdb.WP_WRITE)
    gdb.execute("continue")
    for i in range(50):
        #print("gIndex:", gdb.parse_and_eval("gIndex"), gdb.parse_and_eval("$pc"))
        if random.random() < 0.3 and irq_enabled():
            #gdb.execute("set {unsigned int}0x02000000 = 1")
            msgReceived += 1
            gdb.execute("set gIndex = gIndex + 1") # stubbed out. Could call actual code? Does `call` work?
            record_event()
        #print(gdb.execute("list ."))
        gdb.execute(f"si", to_string=True)
except Exception as e:
    print("Exception occurred:", e)
finally:
    proc.terminate() # kill the subprocess
    # dump the TLA+ trace format
    trace_js = json.dumps({"counterexample" : 
        {"state" : list(enumerate(trace)),
        "action" : []}, 
    "vars" : ["msgReceived", "msgProcessed", "gIndex"]
    }, indent=4)
    print(trace_js)
    print("trace length", len(trace))
    with open("/tmp/trace.json", "w") as f:
        f.write(trace_js)
    gdb.execute("quit")
```

    Overwriting /tmp/steps.py

```python
! gdb-multiarch --batch -q -x /tmp/steps.py /tmp/race.elf
```

    Temporary breakpoint 1 at 0x8000004c: file /tmp/race.c, line 25.
    Hardware watchpoint 2: gIndex
    qemu-system-riscv32: terminating on signal 15 from pid 1364310 (gdb-multiarch)
    {
        "counterexample": {
            "state": [
                [
                    0,
                    {
                        "msgReceived": 0,
                        "msgProcessed": 0,
                        "gIndex": 0
                    }
                ],
                [
                    1,
                    {
                        "msgReceived": 1,
                        "msgProcessed": 0,
                        "gIndex": 1
                    }
                ],
                [
                    2,
                    {
                        "msgReceived": 2,
                        "msgProcessed": 0,
                        "gIndex": 2
                    }
                ],
                [
                    3,
                    {
                        "msgReceived": 3,
                        "msgProcessed": 0,
                        "gIndex": 3
                    }
                ],
                [
                    4,
                    {
                        "msgReceived": 4,
                        "msgProcessed": 0,
                        "gIndex": 4
                    }
                ],
                [
                    5,
                    {
                        "msgReceived": 5,
                        "msgProcessed": 0,
                        "gIndex": 5
                    }
                ],
                [
                    6,
                    {
                        "msgReceived": 5,
                        "msgProcessed": 1,
                        "gIndex": 3
                    }
                ],
                [
                    7,
                    {
                        "msgReceived": 6,
                        "msgProcessed": 1,
                        "gIndex": 4
                    }
                ],
                [
                    8,
                    {
                        "msgReceived": 7,
                        "msgProcessed": 1,
                        "gIndex": 5
                    }
                ],
                [
                    9,
                    {
                        "msgReceived": 8,
                        "msgProcessed": 1,
                        "gIndex": 6
                    }
                ],
                [
                    10,
                    {
                        "msgReceived": 8,
                        "msgProcessed": 2,
                        "gIndex": 5
                    }
                ],
                [
                    11,
                    {
                        "msgReceived": 9,
                        "msgProcessed": 2,
                        "gIndex": 6
                    }
                ],
                [
                    12,
                    {
                        "msgReceived": 10,
                        "msgProcessed": 2,
                        "gIndex": 7
                    }
                ],
                [
                    13,
                    {
                        "msgReceived": 10,
                        "msgProcessed": 3,
                        "gIndex": 6
                    }
                ],
                [
                    14,
                    {
                        "msgReceived": 11,
                        "msgProcessed": 3,
                        "gIndex": 7
                    }
                ],
                [
                    15,
                    {
                        "msgReceived": 12,
                        "msgProcessed": 3,
                        "gIndex": 8
                    }
                ],
                [
                    16,
                    {
                        "msgReceived": 13,
                        "msgProcessed": 3,
                        "gIndex": 9
                    }
                ],
                [
                    17,
                    {
                        "msgReceived": 14,
                        "msgProcessed": 3,
                        "gIndex": 10
                    }
                ],
                [
                    18,
                    {
                        "msgReceived": 14,
                        "msgProcessed": 4,
                        "gIndex": 8
                    }
                ],
                [
                    19,
                    {
                        "msgReceived": 15,
                        "msgProcessed": 4,
                        "gIndex": 9
                    }
                ],
                [
                    20,
                    {
                        "msgReceived": 16,
                        "msgProcessed": 4,
                        "gIndex": 10
                    }
                ],
                [
                    21,
                    {
                        "msgReceived": 17,
                        "msgProcessed": 4,
                        "gIndex": 11
                    }
                ],
                [
                    22,
                    {
                        "msgReceived": 18,
                        "msgProcessed": 4,
                        "gIndex": 12
                    }
                ],
                [
                    23,
                    {
                        "msgReceived": 18,
                        "msgProcessed": 5,
                        "gIndex": 10
                    }
                ]
            ],
            "action": []
        },
        "vars": [
            "msgReceived",
            "msgProcessed",
            "gIndex"
        ]
    }
    trace length 24
    A debugging session is active.
    
     Inferior 1 [process 1] will be detached.
    
    Quit anyway? (y or n) [answered Y; input not from terminal]
    Remote connection closed

```python
! java -cp /tmp/tla2tools.jar tlc2.TLC /tmp/GIndexAtomic.tla  -loadtrace json /tmp/trace.json
```

    TLC2 Version 2026.09.01.002747 (rev: 95b800c)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running breadth-first search Model-Checking with fp 128 and seed 1564593503348657566 with 1 worker on 16 cores with 15416MB heap and 64MB offheap memory [pid: 1366318] (Linux 7.0.0-30-generic amd64, Ubuntu 25.0.4 64bit, MSBDiskFPSet, DiskStateQueue).
    Parsing file /tmp/GIndexAtomic.tla
    Parsing file /tmp/tlc-4819236509984017187/Naturals.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-4819236509984017187/_TLCTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-4819236509984017187/_JsonTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_JsonTrace.tla)
    Parsing file /tmp/tlc-4819236509984017187/TLC.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-4819236509984017187/TLCExt.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-4819236509984017187/Sequences.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-4819236509984017187/FiniteSets.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-4819236509984017187/Integers.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Parsing file /tmp/tlc-4819236509984017187/Json.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Json.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module _TLCTrace
    Semantic processing of module Json
    Semantic processing of module _JsonTrace
    Semantic processing of module GIndexAtomic
    Linting of module TLCExt
    Linting of module _TLCTrace
    Linting of module Json
    Linting of module _JsonTrace
    Linting of module GIndexAtomic
    Starting... (2026-09-04 11:58:50)
    Computing initial states...
    Finished computing initial states: 1 distinct state generated at 2026-09-04 11:58:50.
    Model checking completed. No error has been found.
      Estimates of the probability that TLC did not check all reachable states
      because two distinct states had the same fingerprint:
      calculated (optimistic):  val = 2.0E-18
    12 states generated, 6 distinct states found, 0 states left on queue.
    The depth of the complete state graph search is 6.
    The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).
    Finished in 00s at (2026-09-04 11:58:50)

Are you impressed?
`The depth of the complete state graph search is 6.` but the trace length is 24. That's because it can't continue along it. Step 6 is the first place where it diverges from the allowed behavior of the spec. Neat.

# Bits and Bobbles

We want to speed this up. Fuzzing is better when it's fast. It is possible to have hardware tracing

It's possible to get false negatives.

A generic system to write the gdb script to connect it to tla is not so obvious. Watching all variables of the spec is possibly a start. The connection between gdb events and spec events might not be 1-1. It's nice to have the flexibility of a python script, but it also let's you miss stuff.

Smarter Interrupt scheduling. Use Hypothesis to generate interrupt schedule?

When I actually trigger the interrupt instead of using a gdb stub, I'm not executing the issue. I never let gIndex get above 1. I don't know why exactly. Maybe it's qemu behavior?

I can try to make a spec for this.

```python
%%file /tmp/GIndexAtomic.tla
---------------- MODULE GIndexAtomic ----------------
EXTENDS Naturals

VARIABLE gIndex, msgReceived, msgProcessed

TypeOk == gIndex >= 0
Init == gIndex = 0
MainStep == /\ gIndex # 0 /\ gIndex' = gIndex - 1
IntStep == gIndex' = gIndex + 1
Next == MainStep \/ IntStep
Spec == Init /\ [][Next]_gIndex
Bound == gIndex <= 10
====================================================
```

    Overwriting /tmp/GIndexAtomic.tla

```python
%%file /tmp/GIndexAtomic.tla
---------------- MODULE GIndexAtomic ----------------
EXTENDS Naturals

VARIABLE gIndex, msgReceived, msgProcessed
vars == <<gIndex, msgReceived, msgProcessed>>
Invariant == /\ msgReceived = msgProcessed + gIndex
             /\ msgReceived >= 0
             /\ gIndex >= 0
             /\ msgProcessed >= 0
Init == /\ gIndex = 0
        /\ msgReceived = 0
        /\ msgProcessed = 0
MainStep == /\ gIndex # 0 
            /\ gIndex' = gIndex - 1
            /\ msgProcessed' = msgProcessed + 1
            /\ UNCHANGED msgReceived
IntStep == /\ gIndex' = gIndex + 1
           /\ msgReceived' = msgReceived + 1
           /\ UNCHANGED msgProcessed
Next == \/ MainStep 
        \/ IntStep
Spec == Init /\ [][Next]_vars
Bound == gIndex <= 10
====================================================
```

    Overwriting /tmp/GIndexAtomic.tla

```python
%%file /tmp/GIndexAtomic.cfg
SPECIFICATION Spec
INVARIANT Invariant
```

    Overwriting /tmp/GIndexAtomic.cfg

```python
! java -cp /tmp/tla2tools.jar tlc2.TLC /tmp/GIndexAtomic.tla -dfid 10 #-simulate num=1000 -depth 3
```

    TLC2 Version 2026.09.01.002747 (rev: 95b800c)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running depth-first search Model-Checking with fp 32 and seed -8692692803211145160 with 1 worker on 16 cores with 15416MB heap and 64MB offheap memory [pid: 1171791] (Linux 7.0.0-30-generic amd64, Ubuntu 25.0.4 64bit).
    Parsing file /tmp/GIndexAtomic.tla
    Parsing file /tmp/tlc-4706869078922603791/Naturals.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-4706869078922603791/_TLCTrace.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-4706869078922603791/TLC.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-4706869078922603791/TLCExt.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-4706869078922603791/Sequences.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-4706869078922603791/FiniteSets.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-4706869078922603791/Integers.tla (jar:file:/tmp/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module _TLCTrace
    Semantic processing of module GIndexAtomic
    Linting of module TLCExt
    Linting of module _TLCTrace
    Linting of module GIndexAtomic
    Starting... (2026-09-04 10:56:39)
    Finished computing initial states: 1 states generated, with 1 of them distinct.
    Starting level 2: 1 states generated, 1 distinct states found.
    Starting level 3: 2 states generated, 2 distinct states found.
    Starting level 4: 5 states generated, 4 distinct states found.
    Starting level 5: 11 states generated, 6 distinct states found.
    Starting level 6: 21 states generated, 9 distinct states found.
    Starting level 7: 36 states generated, 12 distinct states found.
    Starting level 8: 57 states generated, 16 distinct states found.
    Starting level 9: 85 states generated, 20 distinct states found.
    Starting level 10: 121 states generated, 25 distinct states found.
    166 states generated, 30 distinct states found.
    Finished in 00s at (2026-09-04 10:56:39)

```python

```

Looking at the assembly, we can see that `gIndex--` inside of `main_loop` is actually a couple of instructions loading `gIndex` from memory into a register `a5`, decrementing it into `a4` and then storing it back. Interrupts may occur in between these operations, leading to unintended behavior.

```python
! riscv64-unknown-elf-objdump -d  -S /tmp/race.elf | grep -C 5 "gIndex--"
```

        for (;;)
            if (gIndex)
    8000004c: 800017b7           lui a5,0x80001
    80000050: 0a07a783           lw a5,160(a5) # 800010a0 <gIndex>
    80000054: dfe5                 beqz a5,8000004c <main_loop+0x8>
                gIndex--;
    80000056: 800017b7           lui a5,0x80001
    8000005a: 0a07a783           lw a5,160(a5) # 800010a0 <gIndex>
    8000005e: fff78713           addi a4,a5,-1
    80000062: 800017b7           lui a5,0x80001
    80000066: 0ae7a023           sw a4,160(a5) # 800010a0 <gIndex>

```python
%%file /tmp/race_trace.py
import gdb
import subprocess
import random
trace = []
def trigger_interrupt():
    pc = gdb.parse_and_eval("$pc")
    gdb.execute("jump interrupt_handler")
    gdb.execute("") # temp breakpoint
    trace.append({"gIndex" : gdb.parse_and_eval("gIndex")})
    pc = gdb.parse_and_eval("set $pc = {pc}")



proc = subprocess.POpen(["qemu-systems-riscv32", "/tmp/race.elf", "-machine", "virt", ])
try:
    gdb.Breakpoint("") # get line of gIndex--;
    for i in range(10):
        gdb.execute(f"ni {random.randint(0,10)}") 
        trigger interrupt()
finally:
    proc.terminate()
    json.dumps(trace)
    gdb.execute("quit")
```

This spec does not have a race bug, but it does not accurately reflect the true meaning of the C code.
If we example the assembly, the naively atomic statement `gIndex--` is in fact multiple instructions which move the value of gIndex into a temporary register.

# GDB as a Universal Interface

GDB and other debug infrastructure actually kind of rules. They tend to exist because developer's like debuggers. But the debug metadata in binaries is kind of the only translation validation artifact that exists. GDB stepping of a system is more often available than a simulator of the system.

GDB also works across many languages and it by and is more accurate than most simulators.

The very act of attaching a debugger does mean you are examining something a little different than the real system. It is important to be aware of that. The act of observaing any system tends to change it in some small way. Timing bugs may be harder to see. But it is pretty good.

GDB also has a quote nice python scripting interface, which includes being able to import regular python packages. In this case, I think it is interesting to leverage the Hypothesis property based testing library <https://hypothesis.readthedocs.io/en/latest/> inside of the gdb script driver.

```python

```

# Extracting Traces

```python
from dataclasses import dataclass
@dataclass
class Clock:
    hr : int
    def tick(self):
        self.hr = self.hr % 12 + 1

import random
vars = ['hr']

state = Clock(hr=random.randint(1, 12))
trace = []
for t in range(15):
    state.tick()
    trace.append([t, {"hr" : state.hr}])

json.dumps({"counterexample" : {"state" : trace, "action" : []}, "vars" : vars})


```

    '{"counterexample": {"state": [[0, {"hr": 4}], [1, {"hr": 5}], [2, {"hr": 6}], [3, {"hr": 7}], [4, {"hr": 8}], [5, {"hr": 9}], [6, {"hr": 10}], [7, {"hr": 11}], [8, {"hr": 12}], [9, {"hr": 1}], [10, {"hr": 2}], [11, {"hr": 3}], [12, {"hr": 4}], [13, {"hr": 5}], [14, {"hr": 6}]], "action": []}, "vars": ["hr"]}'

# Bits and Bobbles

```python
from pathlib import Path
from dataclasses import dataclass, replace
import dataclasses
import json
import re

import kdrag.solvers.tla as tla
from hypothesis import given, settings, strategies as st
```

Connect python functions to TLA first? Hypothesis testing?

It could be kind of fun to mock locking or something to emit action labels / trace events. This could be somewhat transparent (opaque? depends on your preferred term)

```python
%%file /tmp/HourClock.tla
---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

HCini == hr \in 1 .. 12
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
Next == HCnxt \/ UNCHANGED hr
HC == HCini /\ [][HCnxt]_hr
====
```

    Overwriting /tmp/HourClock.tla

```python
%%file /tmp/HourClock.cfg
INIT HCini
NEXT Next
```

    Overwriting /tmp/HourClock.cfg

```python
@dataclass(frozen=True)
class ClockState:
    hr: int


def tick(state):
    return replace(state, hr=state.hr % 13 + 1)


def stutter(state):
    return replace(state)


actions = {"tick": tick, "stutter": stutter}


@st.composite
def hourclock_traces(draw, max_steps=10):
    state = ClockState(draw(st.integers(1, 12)))
    trace = [state]
    names = draw(st.lists(st.sampled_from(list(actions)), max_size=max_steps))
    for name in names:
        state = actions[name](state)
        trace.append(state)
    return trace
```

```python
%%prun
def validate_trace(trace : list[ClockState]) -> bool:
    states = [dataclasses.asdict(state) for state in trace]
    data = {
        "vars": ["hr"],
        "counterexample": {
            "state": [[i, state] for i, state in enumerate(states, 1)],
            "action": [],
        },
    }
    tracefile = "/tmp/hourclock_trace.json"
    Path(tracefile).write_text(json.dumps(data))
    out = tla.run_tools([
        "tlc2.TLC",
        "-workers", "1",
        "-loadTrace", "json", tracefile,
        "-config", "/tmp/HourClock",
        "/tmp/HourClock.tla",
    ]).decode()
    print(out)
    #assert "No error has been found." in out, "Trace is invalid"
    depth = int(re.search(r"The depth .* is (\d+)\.", out).group(1))
    return depth >= len(trace)


assert validate_trace([ClockState(12), ClockState(1), ClockState(1)])
assert not validate_trace([ClockState(1), ClockState(3)])
```

    TLC2 Version 2026.07.14.071606 (rev: 227f61b)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running breadth-first search Model-Checking with fp 103 and seed 1047999301453507687 with 1 worker on 16 cores with 15207MB heap and 64MB offheap memory [pid: 1334020] (Linux 7.0.0-28-generic amd64, Ubuntu 21.0.11 64bit, MSBDiskFPSet, DiskStateQueue).
    Parsing file /tmp/HourClock.tla
    Parsing file /tmp/tlc-8557857232466255485/Naturals.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-8557857232466255485/_TLCTrace.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-8557857232466255485/_JsonTrace.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/_JsonTrace.tla)
    Parsing file /tmp/tlc-8557857232466255485/TLC.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-8557857232466255485/TLCExt.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-8557857232466255485/Sequences.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-8557857232466255485/FiniteSets.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-8557857232466255485/Integers.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Parsing file /tmp/tlc-8557857232466255485/Json.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Json.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module _TLCTrace
    Semantic processing of module Json
    Semantic processing of module _JsonTrace
    Semantic processing of module HourClock
    Linting of module TLCExt
    Linting of module _TLCTrace
    Linting of module Json
    Linting of module _JsonTrace
    Linting of module HourClock
    Starting... (2026-08-14 13:37:33)
    Computing initial states...
    Computed 2 initial states...
    Computed 4 initial states...
    Computed 8 initial states...
    Finished computing initial states: 12 states generated, with 1 of them distinct at 2026-08-14 13:37:33.
    Model checking completed. No error has been found.
      Estimates of the probability that TLC did not check all reachable states
      because two distinct states had the same fingerprint:
      calculated (optimistic):  val = 2.2E-17
    42 states generated, 15 distinct states found, 0 states left on queue.
    The depth of the complete state graph search is 14.
    The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 and the 95th percentile is 2).
    Finished in 00s at (2026-08-14 13:37:33)
    
    TLC2 Version 2026.07.14.071606 (rev: 227f61b)
    Warning: Please run the Java VM, which executes TLC with a throughput optimized garbage collector, by passing the "-XX:+UseParallelGC" property.
    (Use the -nowarning option to disable this warning.)
    Running breadth-first search Model-Checking with fp 18 and seed -7791428038699950807 with 1 worker on 16 cores with 15207MB heap and 64MB offheap memory [pid: 1334104] (Linux 7.0.0-28-generic amd64, Ubuntu 21.0.11 64bit, MSBDiskFPSet, DiskStateQueue).
    Parsing file /tmp/HourClock.tla
    Parsing file /tmp/tlc-15397707271026478307/Naturals.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
    Parsing file /tmp/tlc-15397707271026478307/_TLCTrace.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
    Parsing file /tmp/tlc-15397707271026478307/_JsonTrace.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/_JsonTrace.tla)
    Parsing file /tmp/tlc-15397707271026478307/TLC.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
    Parsing file /tmp/tlc-15397707271026478307/TLCExt.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
    Parsing file /tmp/tlc-15397707271026478307/Sequences.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
    Parsing file /tmp/tlc-15397707271026478307/FiniteSets.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
    Parsing file /tmp/tlc-15397707271026478307/Integers.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
    Parsing file /tmp/tlc-15397707271026478307/Json.tla (jar:file:/home/philip/vibe_coding/knuck_anal/knuckledragger/src/kdrag/solvers/tla2tools.jar!/tla2sany/StandardModules/Json.tla)
    Semantic processing of module Naturals
    Semantic processing of module Sequences
    Semantic processing of module FiniteSets
    Semantic processing of module TLC
    Semantic processing of module Integers
    Semantic processing of module TLCExt
    Semantic processing of module _TLCTrace
    Semantic processing of module Json
    Semantic processing of module _JsonTrace
    Semantic processing of module HourClock
    Linting of module TLCExt
    Linting of module _TLCTrace
    Linting of module Json
    Linting of module _JsonTrace
    Linting of module HourClock
    Starting... (2026-08-14 13:37:34)
    Computing initial states...
    Computed 2 initial states...
    Computed 4 initial states...
    Computed 8 initial states...
    Finished computing initial states: 12 states generated, with 1 of them distinct at 2026-08-14 13:37:34.
    Model checking completed. No error has been found.
      Estimates of the probability that TLC did not check all reachable states
      because two distinct states had the same fingerprint:
      calculated (optimistic):  val = 7.0E-19
    14 states generated, 1 distinct states found, 0 states left on queue.
    The depth of the complete state graph search is 1.
    The average outdegree of the complete state graph is 0 (minimum is 0, the maximum 0 and the 95th percentile is 0).
    Finished in 00s at (2026-08-14 13:37:34)
    
     

             3569 function calls (3551 primitive calls) in 1.515 seconds
    
       Ordered by: internal time
    
       ncalls  tottime  percall  cumtime  percall filename:lineno(function)
           78    1.469    0.019    1.469    0.019 {method 'poll' of 'select.poll' objects}
            4    0.034    0.008    0.034    0.008 {method 'poll' of 'select.epoll' objects}
            2    0.002    0.001    0.002    0.001 {method '__exit__' of 'sqlite3.Connection' objects}
           78    0.002    0.000    1.471    0.019 selectors.py:402(select)
            2    0.001    0.001    1.309    0.654 subprocess.py:2062(_communicate)
            2    0.001    0.000    0.001    0.000 {built-in method _posixsubprocess.fork_exec}
           82    0.001    0.000    0.001    0.000 {built-in method posix.read}
            2    0.001    0.000    0.001    0.000 {built-in method posix.waitpid}
           23    0.000    0.000    0.000    0.000 socket.py:623(send)
            2    0.000    0.000    0.002    0.001 subprocess.py:807(__init__)
           82    0.000    0.000    0.000    0.000 selectors.py:275(_key_from_fd)
            4    0.000    0.000    0.201    0.050 base_events.py:1910(_run_once)
           96    0.000    0.000    0.000    0.000 <frozen posixpath>:71(join)
           80    0.000    0.000    0.000    0.000 selectors.py:66(__len__)
            6    0.000    0.000    0.000    0.000 {built-in method _io.open}
          176    0.000    0.000    0.000    0.000 {method 'append' of 'list' objects}
            1    0.000    0.000    0.000    0.000 {method 'disable' of '_lsprof.Profiler' objects}
          122    0.000    0.000    0.000    0.000 {built-in method builtins.len}
            2    0.000    0.000    0.002    0.001 subprocess.py:1791(_execute_child)
            6    0.000    0.000    0.000    0.000 encoder.py:205(iterencode)
      458/450    0.000    0.000    0.000    0.000 {built-in method builtins.isinstance}
            4    0.000    0.000    0.000    0.000 iostream.py:655(write)
           96    0.000    0.000    0.000    0.000 subprocess.py:1880(<genexpr>)
            2    0.000    0.000    0.000    0.000 {method '__exit__' of '_io._IOBase' objects}
           96    0.000    0.000    0.000    0.000 <frozen os>:812(fsencode)
            7    0.000    0.000    0.000    0.000 attrsettr.py:66(_get_attr_opt)
           96    0.000    0.000    0.000    0.000 enum.py:1544(_get_value)
            8    0.000    0.000    0.000    0.000 {method 'close' of '_io.BufferedReader' objects}
            4    0.000    0.000    0.000    0.000 interactiveshell.py:3051(write)
           82    0.000    0.000    0.000    0.000 subprocess.py:1239(_remaining_time)
           78    0.000    0.000    0.000    0.000 subprocess.py:1247(_check_timeout)
            6    0.000    0.000    0.000    0.000 {built-in method posix.pipe}
           21    0.000    0.000    0.000    0.000 enum.py:1551(__or__)
          1/0    0.000    0.000    0.000          <string>:1(validate_trace)
            2    0.000    0.000    1.513    0.757 subprocess.py:506(run)
            7    0.000    0.000    0.000    0.000 attrsettr.py:43(__getattr__)
            1    0.000    0.000    0.002    0.002 history.py:1025(writeout_cache)
           80    0.000    0.000    0.000    0.000 selectors.py:272(get_map)
            3    0.000    0.000    0.000    0.000 socket.py:771(recv_multipart)
            2    0.000    0.000    1.512    0.756 subprocess.py:1165(communicate)
           42    0.000    0.000    0.000    0.000 enum.py:726(__call__)
            4    0.000    0.000    0.034    0.008 selectors.py:451(select)
            2    0.000    0.000    0.000    0.000 <frozen os>:625(get_exec_path)
           23    0.000    0.000    0.000    0.000 traitlets.py:629(get)
           23    0.000    0.000    0.000    0.000 traitlets.py:676(__get__)
            1    0.000    0.000    0.003    0.003 decorator.py:232(fun)
            2    0.000    0.000    0.000    0.000 socket.py:700(send_multipart)
            1    0.000    0.000    0.000    0.000 iostream.py:616(_flush)
          102    0.000    0.000    0.000    0.000 <frozen posixpath>:41(_get_sep)
            9    0.000    0.000    0.000    0.000 typing.py:392(inner)
           11    0.000    0.000    0.000    0.000 enum.py:1562(__and__)
            1    0.000    0.000    0.000    0.000 inspect.py:3102(_bind)
            8    0.000    0.000    0.000    0.000 selectors.py:21(_fileobj_to_fd)
            4    0.000    0.000    0.000    0.000 selectors.py:365(unregister)
            2    0.000    0.000    0.000    0.000 subprocess.py:1688(_get_handles)
           25    0.000    0.000    0.000    0.000 {built-in method builtins.hasattr}
          103    0.000    0.000    0.000    0.000 {method 'encode' of 'str' objects}
           42    0.000    0.000    0.000    0.000 enum.py:1129(__new__)
         10/5    0.000    0.000    0.000    0.000 dataclasses.py:1325(_asdict_inner)
            6    0.000    0.000    0.000    0.000 <frozen posixpath>:179(dirname)
            6    0.000    0.000    0.000    0.000 encoder.py:183(encode)
            3    0.000    0.000    0.001    0.000 zmqstream.py:573(_handle_events)
            3    0.000    0.000    0.000    0.000 iostream.py:259(schedule)
            6    0.000    0.000    0.000    0.000 __init__.py:183(dumps)
            2    0.000    0.000    0.000    0.000 pathlib.py:437(__str__)
            2    0.000    0.000    0.000    0.000 subprocess.py:1282(_close_pipe_fds)
            1    0.000    0.000    0.000    0.000 session.py:754(send)
          202    0.000    0.000    0.000    0.000 {built-in method posix.fspath}
           94    0.000    0.000    0.000    0.000 {method 'startswith' of 'bytes' objects}
            5    0.000    0.000    0.000    0.000 dataclasses.py:1271(fields)
            3    0.000    0.000    0.000    0.000 traitlets.py:708(__set__)
            8    0.000    0.000    0.000    0.000 {built-in method posix.close}
            3    0.000    0.000    0.000    0.000 traitlets.py:689(set)
            2    0.000    0.000    0.000    0.000 iostream.py:710(_flush_buffers)
            4    0.000    0.000    0.000    0.000 selectors.py:234(register)
            6    0.000    0.000    0.001    0.000 subprocess.py:2021(_wait)
            3    0.000    0.000    0.000    0.000 traitlets.py:718(_validate)
           94    0.000    0.000    0.000    0.000 {method 'endswith' of 'bytes' objects}
            2    0.000    0.000    0.000    0.000 {built-in method builtins.print}
            2    0.000    0.000    0.000    0.000 {method 'search' of 're.Pattern' objects}
            2    0.000    0.000    0.000    0.000 pathlib.py:387(_parse_path)
            2    0.000    0.000    0.000    0.000 pathlib.py:1007(open)
            1    0.000    0.000    0.000    0.000 {method 'execute' of 'sqlite3.Connection' objects}
            4    0.000    0.000    0.000    0.000 zmqstream.py:653(_rebuild_io_state)
          1/0    0.000    0.000    0.000          tla.py:84(run_tools)
            2    0.000    0.000    0.000    0.000 traitlets.py:3631(set)
            2    0.000    0.000    0.000    0.000 pathlib.py:357(__init__)
            3    0.000    0.000    0.000    0.000 threading.py:1220(is_alive)
            5    0.000    0.000    0.000    0.000 dataclasses.py:1301(asdict)
           12    0.000    0.000    0.000    0.000 {built-in method builtins.next}
            4    0.000    0.000    0.001    0.000 events.py:86(_run)
            1    0.000    0.000    0.000    0.000 traitlets.py:1527(_notify_observers)
            1    0.000    0.000    0.002    0.002 history.py:93(only_when_enabled)
            4    0.000    0.000    0.000    0.000 selectors.py:247(unregister)
            1    0.000    0.000    0.000    0.000 session.py:690(serialize)
           22    0.000    0.000    0.000    0.000 {built-in method builtins.getattr}
            2    0.000    0.000    0.000    0.000 contextlib.py:567(__exit__)
            3    0.000    0.000    0.000    0.000 traitlets.py:727(_cross_validate)
            8    0.000    0.000    0.000    0.000 selectors.py:215(_fileobj_lookup)
            3    0.000    0.000    0.000    0.000 zmqstream.py:614(_handle_recv)
            7    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:1390(_handle_fromlist)
            2    0.000    0.000    0.000    0.000 pathlib.py:1041(write_text)
            2    0.000    0.000    0.000    0.000 {method 'isoformat' of 'datetime.datetime' objects}
            1    0.000    0.000    0.000    0.000 asyncio.py:225(add_callback)
            9    0.000    0.000    0.000    0.000 base_events.py:734(time)
            4    0.000    0.000    0.000    0.000 contextlib.py:530(callback)
            4    0.000    0.000    0.000    0.000 zmqstream.py:676(_update_handler)
            2    0.000    0.000    0.001    0.000 ioloop.py:742(_run_callback)
            4    0.000    0.000    0.000    0.000 selectors.py:351(register)
            4    0.000    0.000    0.000    0.000 queue.py:97(empty)
            9    0.000    0.000    0.000    0.000 {built-in method posix.getpid}
            6    0.000    0.000    0.000    0.000 typing.py:1258(__hash__)
            2    0.000    0.000    0.000    0.000 pathlib.py:1159(__init__)
            1    0.000    0.000    0.000    0.000 decorator.py:200(fix)
            1    0.000    0.000    0.000    0.000 iostream.py:718(_rotate_buffers)
            4    0.000    0.000    0.000    0.000 <frozen os>:680(__getitem__)
            4    0.000    0.000    0.000    0.000 {method 'split' of 'str' objects}
            3    0.000    0.000    0.000    0.000 contextlib.py:141(__exit__)
            4    0.000    0.000    0.000    0.000 selector_events.py:750(_process_events)
            2    0.000    0.000    0.000    0.000 events.py:36(__init__)
            6    0.000    0.000    0.001    0.000 subprocess.py:1259(wait)
           10    0.000    0.000    0.000    0.000 dataclasses.py:1289(_is_dataclass_instance)
            2    0.000    0.000    0.000    0.000 __init__.py:174(search)
            4    0.000    0.000    0.000    0.000 <frozen os>:762(encode)
            3    0.000    0.000    0.000    0.000 iostream.py:157(_handle_event)
            1    0.000    0.000    0.000    0.000 session.py:649(msg)
            2    0.000    0.000    0.000    0.000 traitlets.py:3474(validate)
            4    0.000    0.000    0.000    0.000 typing.py:1465(__subclasscheck__)
           11    0.000    0.000    0.000    0.000 {built-in method builtins.max}
            2    0.000    0.000    0.000    0.000 warnings.py:182(_add_filter)
            2    0.000    0.000    0.000    0.000 pathlib.py:407(_load_parts)
           62    0.000    0.000    0.000    0.000 typing.py:2154(cast)
            8    0.000    0.000    0.000    0.000 {method 'fileno' of '_io.BufferedReader' objects}
            2    0.000    0.000    0.000    0.000 jsonutil.py:107(json_default)
            4    0.000    0.000    0.001    0.000 {method 'run' of '_contextvars.Context' objects}
            2    0.000    0.000    0.000    0.000 selectors.py:209(__init__)
            2    0.000    0.000    0.000    0.000 iostream.py:278(_really_send)
            1    0.000    0.000    0.000    0.000 traitlets.py:2558(_validate_bounds)
            4    0.000    0.000    0.000    0.000 typing.py:1194(__instancecheck__)
            4    0.000    0.000    0.000    0.000 iostream.py:577(_schedule_flush)
            4    0.000    0.000    0.000    0.000 iostream.py:505(parent_header)
            2    0.000    0.000    0.000    0.000 pathlib.py:1166(__new__)
            1    0.000    0.000    0.000    0.000 base_events.py:767(call_at)
            3    0.000    0.000    0.000    0.000 zmqstream.py:546(_run_callback)
            2    0.000    0.000    0.000    0.000 __init__.py:45(binpath)
          6/3    0.000    0.000    0.000    0.000 {method 'acquire' of '_thread.lock' objects}
            3    0.000    0.000    0.000    0.000 contextlib.py:104(__init__)
            2    0.000    0.000    0.000    0.000 traitlets.py:3624(validate_elements)
            1    0.000    0.000    0.000    0.000 inspect.py:3237(bind)
            1    0.000    0.000    0.000    0.000 asyncio.py:210(call_at)
            2    0.000    0.000    0.000    0.000 pathlib.py:551(drive)
            1    0.000    0.000    0.000    0.000 session.py:675(sign)
            4    0.000    0.000    0.000    0.000 {built-in method _abc._abc_subclasscheck}
            4    0.000    0.000    0.000    0.000 session.py:92(json_packer)
            1    0.000    0.000    0.000    0.000 traitlets.py:1512(_notify_trait)
            1    0.000    0.000    0.000    0.000 traitlets.py:2635(validate)
            2    0.000    0.000    0.000    0.000 selectors.py:268(close)
            3    0.000    0.000    0.000    0.000 contextlib.py:299(helper)
            3    0.000    0.000    0.000    0.000 iostream.py:138(_event_pipe)
            4    0.000    0.000    0.000    0.000 {method 'update' of '_hashlib.HMAC' objects}
            2    0.000    0.000    0.000    0.000 warnings.py:482(__enter__)
            1    0.000    0.000    0.000    0.000 base_events.py:814(_call_soon)
            2    0.000    0.000    0.000    0.000 selectors.py:347(__init__)
            4    0.000    0.000    0.000    0.000 {method 'join' of 'bytes' objects}
            4    0.000    0.000    0.000    0.000 {method 'decode' of 'bytes' objects}
            2    0.000    0.000    0.000    0.000 warnings.py:166(simplefilter)
            2    0.000    0.000    0.000    0.000 traitlets.py:2304(validate)
            2    0.000    0.000    0.001    0.000 subprocess.py:2008(_try_wait)
            1    0.000    0.000    0.000    0.000 {method 'copy' of '_hashlib.HMAC' objects}
            2    0.000    0.000    0.000    0.000 subprocess.py:1092(__exit__)
            2    0.000    0.000    0.000    0.000 __init__.py:280(_compile)
            1    0.000    0.000    0.000    0.000 traitlets.py:1523(notify_change)
            4    0.000    0.000    0.000    0.000 {built-in method builtins.issubclass}
           12    0.000    0.000    0.000    0.000 {method 'append' of 'collections.deque' objects}
            2    0.000    0.000    0.000    0.000 iostream.py:276(<lambda>)
            1    0.000    0.000    0.000    0.000 session.py:600(msg_id)
            1    0.000    0.000    0.000    0.000 inspect.py:2918(apply_defaults)
            1    0.000    0.000    0.000    0.000 ioloop.py:596(call_later)
            2    0.000    0.000    0.000    0.000 <frozen posixpath>:138(splitroot)
            4    0.000    0.000    0.000    0.000 iostream.py:550(_is_master_process)
            4    0.000    0.000    0.000    0.000 {built-in method sys.intern}
            1    0.000    0.000    0.000    0.000 threading.py:311(_acquire_restore)
            2    0.000    0.000    0.000    0.000 asyncio.py:200(_handle_events)
            3    0.000    0.000    0.000    0.000 contextlib.py:132(__enter__)
            2    0.000    0.000    0.000    0.000 pathlib.py:447(__fspath__)
            4    0.000    0.000    0.000    0.000 zmqstream.py:532(sending)
            4    0.000    0.000    0.000    0.000 <frozen abc>:121(__subclasscheck__)
            1    0.000    0.000    0.000    0.000 base_events.py:743(call_later)
            1    0.000    0.000    0.000    0.000 threading.py:308(_release_save)
           10    0.000    0.000    0.000    0.000 dataclasses.py:1286(<genexpr>)
            2    0.000    0.000    0.000    0.000 subprocess.py:1120(__del__)
            1    0.000    0.000    0.000    0.000 history.py:1017(_writeout_output_cache)
           10    0.000    0.000    0.000    0.000 {method '__exit__' of '_thread.lock' objects}
            2    0.000    0.000    0.000    0.000 subprocess.py:1961(_handle_exitstatus)
            1    0.000    0.000    0.000    0.000 inspect.py:2865(args)
            2    0.000    0.000    0.000    0.000 ioloop.py:541(time)
            2    0.000    0.000    0.000    0.000 contextlib.py:481(__init__)
            1    0.000    0.000    0.000    0.000 {built-in method now}
            1    0.000    0.000    0.000    0.000 hmac.py:122(copy)
            7    0.000    0.000    0.000    0.000 {built-in method __new__ of type object at 0xa44b40}
            2    0.000    0.000    0.000    0.000 selectors.py:202(__exit__)
            2    0.000    0.000    0.000    0.000 {built-in method _abc._abc_instancecheck}
            1    0.000    0.000    0.000    0.000 session.py:272(msg_header)
            2    0.000    0.000    0.000    0.000 {method 'remove' of 'list' objects}
            3    0.000    0.000    0.000    0.000 threading.py:1153(_wait_for_tstate_lock)
            1    0.000    0.000    0.000    0.000 session.py:645(msg_header)
            1    0.000    0.000    0.000    0.000 session.py:198(utcnow)
            1    0.000    0.000    0.000    0.000 {method 'hexdigest' of '_hashlib.HMAC' objects}
            4    0.000    0.000    0.000    0.000 {built-in method math.ceil}
            2    0.000    0.000    0.000    0.000 warnings.py:503(__exit__)
            2    0.000    0.000    0.000    0.000 subprocess.py:1233(poll)
            1    0.000    0.000    0.000    0.000 {method 'getvalue' of '_io.StringIO' objects}
            4    0.000    0.000    0.000    0.000 queue.py:209(_qsize)
           10    0.000    0.000    0.000    0.000 {method 'get' of 'dict' objects}
            4    0.000    0.000    0.000    0.000 {method 'write' of '_io.StringIO' objects}
            2    0.000    0.000    0.000    0.000 {built-in method builtins.sorted}
            1    0.000    0.000    0.000    0.000 iostream.py:587(_schedule_in_thread)
            4    0.000    0.000    0.000    0.000 {method 'rfind' of 'str' objects}
            2    0.000    0.000    0.000    0.000 iostream.py:213(_is_master_process)
            2    0.000    0.000    0.000    0.000 threading.py:299(__enter__)
            1    0.000    0.000    0.000    0.000 events.py:111(__init__)
            1    0.000    0.000    0.002    0.002 history.py:1009(_writeout_input_cache)
            3    0.000    0.000    0.000    0.000 {built-in method _thread.allocate_lock}
            2    0.000    0.000    0.000    0.000 threading.py:302(__exit__)
            2    0.000    0.000    0.000    0.000 iostream.py:216(_check_mp_mode)
            2    0.000    0.000    0.000    0.000 <frozen _collections_abc>:804(get)
            7    0.000    0.000    0.000    0.000 {method 'upper' of 'str' objects}
            1    0.000    0.000    0.000    0.000 threading.py:627(clear)
            9    0.000    0.000    0.000    0.000 {built-in method time.monotonic}
            4    0.000    0.000    0.000    0.000 displaypub.py:172(is_publishing)
            4    0.000    0.000    0.000    0.000 {method 'unregister' of 'select.poll' objects}
            2    0.000    0.000    0.000    0.000 {built-in method sys.exc_info}
            1    0.000    0.000    0.000    0.000 session.py:281(extract_header)
            8    0.000    0.000    0.000    0.000 {method 'extend' of 'list' objects}
            8    0.000    0.000    0.000    0.000 {method 'join' of 'str' objects}
            4    0.000    0.000    0.000    0.000 {built-in method builtins.min}
            1    0.000    0.000    0.000    0.000 inspect.py:2888(kwargs)
            2    0.000    0.000    0.000    0.000 <frozen abc>:117(__instancecheck__)
            2    0.000    0.000    0.000    0.000 {method 'rfind' of 'bytes' objects}
            2    0.000    0.000    0.000    0.000 <frozen os>:766(decode)
            2    0.000    0.000    0.000    0.000 warnings.py:456(__init__)
            2    0.000    0.000    0.000    0.000 subprocess.py:268(_cleanup)
            2    0.000    0.000    0.000    0.000 traitlets.py:3486(validate_elements)
            1    0.000    0.000    0.000    0.000 hmac.py:161(hexdigest)
            1    0.000    0.000    0.000    0.000 base_events.py:785(call_soon)
            4    0.000    0.000    0.000    0.000 hmac.py:117(update)
            1    0.000    0.000    0.000    0.000 {built-in method _asyncio.get_running_loop}
            4    0.000    0.000    0.000    0.000 <string>:1(<lambda>)
            1    0.000    0.000    0.000    0.000 {built-in method builtins.locals}
            2    0.000    0.000    0.000    0.000 pathlib.py:429(_format_parsed_parts)
            1    0.000    0.000    0.000    0.000 {built-in method _heapq.heappush}
            2    0.000    0.000    0.000    0.000 {method 'group' of 're.Match' objects}
            4    0.000    0.000    0.000    0.000 contextlib.py:475(_create_cb_wrapper)
            2    0.000    0.000    0.000    0.000 {built-in method _contextvars.copy_context}
            7    0.000    0.000    0.000    0.000 {method 'popleft' of 'collections.deque' objects}
            4    0.000    0.000    0.000    0.000 encoder.py:105(__init__)
            4    0.000    0.000    0.000    0.000 contextlib.py:477(_exit_wrapper)
            2    0.000    0.000    0.000    0.000 jsonutil.py:38(_ensure_tzinfo)
            2    0.000    0.000    0.000    0.000 base_events.py:1895(_add_callback)
            5    0.000    0.000    0.000    0.000 {method '__exit__' of '_thread.RLock' objects}
            4    0.000    0.000    0.000    0.000 contextlib.py:548(_push_exit_callback)
            4    0.000    0.000    0.000    0.000 {method 'register' of 'select.poll' objects}
            5    0.000    0.000    0.000    0.000 {method 'values' of 'dict' objects}
            7    0.000    0.000    0.000    0.000 zmqstream.py:528(receiving)
           10    0.000    0.000    0.000    0.000 inspect.py:2777(kind)
            5    0.000    0.000    0.000    0.000 {method 'items' of 'dict' objects}
            2    0.000    0.000    0.000    0.000 tz.py:74(utcoffset)
            2    0.000    0.000    0.000    0.000 {built-in method select.poll}
            1    0.000    0.000    0.000    0.000 {method 'values' of 'mappingproxy' objects}
            4    0.000    0.000    0.000    0.000 {method 'pop' of 'dict' objects}
            4    0.000    0.000    0.000    0.000 {method 'get' of '_contextvars.ContextVar' objects}
            2    0.000    0.000    0.000    0.000 {method 'clear' of 'dict' objects}
            2    0.000    0.000    0.000    0.000 {method 'replace' of 'str' objects}
            6    0.000    0.000    0.000    0.000 {built-in method builtins.hash}
            3    0.000    0.000    0.000    0.000 {method 'items' of 'mappingproxy' objects}
            1    0.000    0.000    0.000    0.000 {method 'close' of '_io.StringIO' objects}
            1    0.000    0.000    0.000    0.000 iostream.py:271(send_multipart)
            2    0.000    0.000    0.000    0.000 history.py:1066(hold)
            4    0.000    0.000    0.000    0.000 subprocess.py:1311(_on_error_fd_closer)
            1    0.000    0.000    0.000    0.000 {built-in method _heapq.heappop}
            4    0.000    0.000    0.000    0.000 {built-in method builtins.any}
            6    0.000    0.000    0.000    0.000 {built-in method _warnings._filters_mutated}
            1    0.000    0.000    0.000    0.000 iostream.py:725(_hooks)
            4    0.000    0.000    0.000    0.000 {built-in method _io.text_encoding}
            2    0.000    0.000    0.000    0.000 {method '__enter__' of '_thread.lock' objects}
            3    0.000    0.000    0.000    0.000 threading.py:601(is_set)
            2    0.000    0.000    0.000    0.000 {built-in method time.time}
            4    0.000    0.000    0.000    0.000 subprocess.py:1973(_internal_poll)
            2    0.000    0.000    0.000    0.000 {method 'insert' of 'list' objects}
            1    0.000    0.000    0.000    0.000 events.py:127(__lt__)
            2    0.000    0.000    0.000    0.000 {method 'count' of 'list' objects}
            2    0.000    0.000    0.000    0.000 subprocess.py:481(__init__)
            2    0.000    0.000    0.000    0.000 {built-in method sys.audit}
            1    0.000    0.000    0.000    0.000 threading.py:314(_is_owned)
            4    0.000    0.000    0.000    0.000 displayhook.py:118(is_active)
            2    0.000    0.000    0.000    0.000 {method 'startswith' of 'str' objects}
            2    0.000    0.000    0.000    0.000 {built-in method builtins.iter}
            2    0.000    0.000    0.000    0.000 {method 'write' of '_io.TextIOWrapper' objects}
            2    0.000    0.000    0.000    0.000 {built-in method posix.WIFSTOPPED}
            4    0.000    0.000    0.000    0.000 inspect.py:2765(name)
            4    0.000    0.000    0.000    0.000 {method 'pop' of 'collections.deque' objects}
            2    0.000    0.000    0.000    0.000 {method 'rstrip' of 'str' objects}
            2    0.000    0.000    0.000    0.000 base_events.py:539(_check_closed)
            2    0.000    0.000    0.000    0.000 <frozen codecs>:186(__init__)
            2    0.000    0.000    0.000    0.000 iostream.py:255(closed)
            4    0.000    0.000    0.000    0.000 inspect.py:3058(parameters)
            2    0.000    0.000    0.000    0.000 {method 'add' of 'set' objects}
            2    0.000    0.000    0.000    0.000 subprocess.py:2164(_save_input)
            2    0.000    0.000    0.000    0.000 {method 'endswith' of 'str' objects}
            2    0.000    0.000    0.000    0.000 pathlib.py:560(root)
            1    0.000    0.000    0.000    0.000 zmqstream.py:684(<lambda>)
            2    0.000    0.000    0.000    0.000 base_events.py:2005(get_debug)
            1    0.000    0.000    0.000    0.000 {method 'release' of '_thread.lock' objects}
            1    0.000    0.000    0.000    0.000 <string>:2(__init__)
            2    0.000    0.000    0.000    0.000 selectors.py:63(__init__)
            2    0.000    0.000    0.000    0.000 pathlib.py:569(_tail)
            1    0.000    0.000    0.000    0.000 inspect.py:2857(__init__)
            2    0.000    0.000    0.000    0.000 contextlib.py:564(__enter__)
            1    0.000    0.000    0.000    0.000 {method 'copy' of 'dict' objects}
            2    0.000    0.000    0.000    0.000 {built-in method posix.waitstatus_to_exitcode}
            2    0.000    0.000    0.000    0.000 subprocess.py:1089(__enter__)
            2    0.000    0.000    0.000    0.000 selectors.py:199(__enter__)
            1    0.000    0.000    0.000    0.000 hmac.py:139(_current)

```python
@settings(max_examples=10, deadline=None)
@given(hourclock_traces())
def test_python_hourclock_refines_tla(trace):
    assert validate_trace(trace), trace


test_python_hourclock_refines_tla()
```

    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[9], line 7
          1 @settings(max_examples=10, deadline=None)
          2 @given(hourclock_traces())
          3 def test_python_hourclock_refines_tla(trace):
          4     assert validate_trace(trace), trace
    ----> 7 test_python_hourclock_refines_tla()


    Cell In[9], line 2, in test_python_hourclock_refines_tla()
          1 @settings(max_examples=10, deadline=None)
    ----> 2 @given(hourclock_traces())
          3 def test_python_hourclock_refines_tla(trace):
          4     assert validate_trace(trace), trace
          7 test_python_hourclock_refines_tla()


        [... skipping hidden 1 frame]


    Cell In[9], line 4, in test_python_hourclock_refines_tla(trace)
          1 @settings(max_examples=10, deadline=None)
          2 @given(hourclock_traces())
          3 def test_python_hourclock_refines_tla(trace):
    ----> 4     assert validate_trace(trace), trace


    AssertionError: [ClockState(hr=9), ClockState(hr=10), ClockState(hr=11), ClockState(hr=12), ClockState(hr=13)]

    Falsifying example: test_python_hourclock_refines_tla(
        trace=[ClockState(hr=9),
         ClockState(hr=10),
         ClockState(hr=11),
         ClockState(hr=12),
         ClockState(hr=13)],
    )

cerberus
cbmc

renode
actually control the hardware? gdb scrpit from python

<https://arxiv.org/abs/2404.16075> merz Validating Traces of Distributed Programs Against TLA+ Specifications

<https://www.youtube.com/watch?v=NZmON-XmrkI> Validating System Executions with the TLA+ Tools Markus A Kuppe, Microsoft

<https://www.youtube.com/watch?v=W6DrQk8o5tk>

<https://docs.tlapl.us/using:tlc:trace_validation>

<https://pron.github.io/files/Trace.pdf> ron pressler trace vliation 2018

It's surprising there is an json tlc module. also an IO module?

tla importer could wrap exprssion in dummy module.

```python
def expr(e : str, variables=[], constants=[]):
    with write() as f:
        f.write("----- KDRAGDUMMY --------)
        f.write(f"VARIABLES {v})
        f.write(f"KDRAGEXPR == {e}\n")
        f.write(f"==================")
    mod = Module.load_file("/tmp/KDRAGDUMMY.tla")
    mod.infer_sorts()
    return mod.action("KDRAGEXPR")
```

Yea, maybe I'm getting closer to SPIN?

cocotb might be kind of interesting...
spike or sail derived emulator?
Try a bunch of them?

```python
%%file /tmp/hour.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>   

typedef struct ClockState {
    int hr;
} ClockState;

ClockState state;

void tick(){
    state.hr = state.hr % 13 + 1;
}

void main(){
    srand(time(NULL));
    state.hr = rand() % 12 + 1;
    printf("[");
    for(int t = 0; t < 100; t++){
        printf("[%d, { hr : %d }]\n", t, state.hr);
        tick();
    }
    printf("]");
}

```

    Overwriting /tmp/hour.c

```python
! gcc -o /tmp/hour /tmp/hour.c && /tmp/hour
```

    [[0, { hr : 3 }]
    [1, { hr : 4 }]
    [2, { hr : 5 }]
    [3, { hr : 6 }]
    [4, { hr : 7 }]
    [5, { hr : 8 }]
    [6, { hr : 9 }]
    [7, { hr : 10 }]
    [8, { hr : 11 }]
    [9, { hr : 12 }]
    [10, { hr : 13 }]
    [11, { hr : 1 }]
    [12, { hr : 2 }]
    [13, { hr : 3 }]
    [14, { hr : 4 }]
    [15, { hr : 5 }]
    [16, { hr : 6 }]
    [17, { hr : 7 }]
    [18, { hr : 8 }]
    [19, { hr : 9 }]
    [20, { hr : 10 }]
    [21, { hr : 11 }]
    [22, { hr : 12 }]
    [23, { hr : 13 }]
    [24, { hr : 1 }]
    [25, { hr : 2 }]
    [26, { hr : 3 }]
    [27, { hr : 4 }]
    [28, { hr : 5 }]
    [29, { hr : 6 }]
    [30, { hr : 7 }]
    [31, { hr : 8 }]
    [32, { hr : 9 }]
    [33, { hr : 10 }]
    [34, { hr : 11 }]
    [35, { hr : 12 }]
    [36, { hr : 13 }]
    [37, { hr : 1 }]
    [38, { hr : 2 }]
    [39, { hr : 3 }]
    [40, { hr : 4 }]
    [41, { hr : 5 }]
    [42, { hr : 6 }]
    [43, { hr : 7 }]
    [44, { hr : 8 }]
    [45, { hr : 9 }]
    [46, { hr : 10 }]
    [47, { hr : 11 }]
    [48, { hr : 12 }]
    [49, { hr : 13 }]
    [50, { hr : 1 }]
    [51, { hr : 2 }]
    [52, { hr : 3 }]
    [53, { hr : 4 }]
    [54, { hr : 5 }]
    [55, { hr : 6 }]
    [56, { hr : 7 }]
    [57, { hr : 8 }]
    [58, { hr : 9 }]
    [59, { hr : 10 }]
    [60, { hr : 11 }]
    [61, { hr : 12 }]
    [62, { hr : 13 }]
    [63, { hr : 1 }]
    [64, { hr : 2 }]
    [65, { hr : 3 }]
    [66, { hr : 4 }]
    [67, { hr : 5 }]
    [68, { hr : 6 }]
    [69, { hr : 7 }]
    [70, { hr : 8 }]
    [71, { hr : 9 }]
    [72, { hr : 10 }]
    [73, { hr : 11 }]
    [74, { hr : 12 }]
    [75, { hr : 13 }]
    [76, { hr : 1 }]
    [77, { hr : 2 }]
    [78, { hr : 3 }]
    [79, { hr : 4 }]
    [80, { hr : 5 }]
    [81, { hr : 6 }]
    [82, { hr : 7 }]
    [83, { hr : 8 }]
    [84, { hr : 9 }]
    [85, { hr : 10 }]
    [86, { hr : 11 }]
    [87, { hr : 12 }]
    [88, { hr : 13 }]
    [89, { hr : 1 }]
    [90, { hr : 2 }]
    [91, { hr : 3 }]
    [92, { hr : 4 }]
    [93, { hr : 5 }]
    [94, { hr : 6 }]
    [95, { hr : 7 }]
    [96, { hr : 8 }]
    [97, { hr : 9 }]
    [98, { hr : 10 }]
    [99, { hr : 11 }]
    ]

```python
%%file /tmp/hour.c
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
  
typedef struct ClockState {
    int hr;
} ClockState;

ClockState state;

void tick(){
    state.hr = state.hr % 13 + 1;
}

int main(){
    srand(time(NULL));
    state.hr = rand() % 12 + 1;
    for(int t = 0; t < 100; t++){
        tick();
    }
    return 0;
}
```

    Overwriting /tmp/hour.c

```python
! gcc -g -Wall -o /tmp/hour /tmp/hour.c
```

import gdb only works inside GDB's embedded Python.
 GDB/MI i  <https://sourceware.org/gdb/current/onlinedocs/gdb.html/GDB_002fMI.html>
 Is this overwrought?
 Should I just make a python scriper and load it from inside gdb or script gdb in some other way

 <https://www.youtube.com/watch?v=xt9v5t4_zvE> lisa roach - extended gdb with python. Very fun
Could this be a road into some whackasmackadoo tower of interpreters stuff?

Hmm. Control renode via gdb? <https://renode.readthedocs.io/en/latest/debugging/gdb.html>
<https://github.com/matgla/Renode_RP2040>
<https://github.com/wokwi/rp2040js>

Worry: instrumentation may change system. printf has locks in pico for example
Make instrumentation so cheap you leave it on? (antithesis right?)
Or further testing required anyhow

```python
import os
os.getpid()
```

```python
%%file /tmp/printhello.py

import gdb
gdb.execute("call \"Python)


```

```python
%%file /tmp/hourclock.gdb
set pagination off
set confirm off
set debuginfod enabled off
break tick
commands
  silent
  printf "CLOCK %d\n", state.hr
  continue
end
run
```

```python
import subprocess

result = subprocess.run(
    ["gdb", "-q", "--batch", "-x", "/tmp/hourclock.gdb", "/tmp/hour"],
    capture_output=True, text=True, check=True,
)
c_trace = [
    ClockState(int(hr))
    for hr in re.findall(r"^CLOCK (\d+)$", result.stdout, re.MULTILINE)
]
c_trace[:10], len(c_trace)
```

```python
import sys
sys.version
sys.executable

```

    '/home/philip/philzook58.github.io/.venv/bin/python'

```python

```

    1285037

```python
! gdb -ex "python import sys; print(sys.version); print(sys.executable)" -ex "quit"
```

    [35;1mGNU gdb (Ubuntu 15.1-1ubuntu1~24.04.1) 15.1[m
    Copyright (C) 2024 Free Software Foundation, Inc.
    License GPLv3+: GNU GPL version 3 or later <[32mhttp://gnu.org/licenses/gpl.html[m>
    This is free software: you are free to change and redistribute it.
    There is NO WARRANTY, to the extent permitted by law.
    Type "show copying" and "show warranty" for details.
    This GDB was configured as "x86_64-linux-gnu".
    Type "show configuration" for configuration details.
    For bug reporting instructions, please see:
    [32m<https://www.gnu.org/software/gdb/bugs/>[m.
    Find the GDB manual and other documentation resources online at:
        <[32mhttp://www.gnu.org/software/gdb/documentation/[m>.
    
    For help, type "help".
    Type "apropos word" to search for commands related to "word".
    3.12.3 (main, Jun 19 2026, 12:46:00) [GCC 13.3.0]
    /usr/bin/python

# Renode

```python
%%file /tmp/hourclock_rv.c
typedef struct { volatile unsigned int hr; } ClockState;
volatile ClockState state = {1};
extern char __stack_top[];
int main(void);

__attribute__((naked, section(".text.start")))
void _start(void) {
    __asm__ volatile("la sp, __stack_top\n"
                     "call main\n"
                     "ebreak\n"
                     "1: j 1b");
}

__attribute__((noinline)) void tick(void) { state.hr = state.hr % 12 + 1; }
__attribute__((noinline)) void tick_done(void) {}

int main(void) {
    for(int i = 0; i < 10; i++) {
        tick();
        tick_done();
    }
    return 0;
}

```

    Overwriting /tmp/hourclock_rv.c

```python
%%file /tmp/hourclock_rv.ld
ENTRY(_start)
SECTIONS {
    . = 0x80000000;
    .text : { KEEP(*(.text.start)) *(.text*) }
    .rodata : { *(.rodata*) }
    .data : { *(.data*) }
    .bss : { *(.bss*) *(COMMON) }
    . = ALIGN(16);
    . += 0x1000;
    __stack_top = .;
}

```

    Overwriting /tmp/hourclock_rv.ld

```python
%%file /tmp/hourclock.resc
mach create "hourclock"
machine LoadPlatformDescriptionFromString """
cpu: CPU.RiscV64 @ sysbus
    cpuType: "rv64imac"
    privilegedArchitecture: PrivilegedArchitecture.Priv1_12
    timeProvider: empty

ram: Memory.MappedMemory @ sysbus 0x80000000
    size: 0x100000
"""
sysbus LoadELF @/tmp/hourclock_rv.elf
machine StartGdbServer 3333

```

    Overwriting /tmp/hourclock.resc

```python
%%file /tmp/hourclock_renode.py
import gdb
import json

trace = []

class TickDone(gdb.Breakpoint):
    def stop(self):
        trace.append({"hr": int(gdb.parse_and_eval("state.hr"))})
        return False

TickDone("tick_done")
gdb.execute("monitor start")
gdb.execute("continue")
print("CLOCKTRACE " + json.dumps(trace))

```

    Overwriting /tmp/hourclock_renode.py

```python
!riscv64-unknown-elf-gcc -march=rv64imac -mabi=lp64 -mcmodel=medany \
    -g -O0 -ffreestanding -nostdlib -Wl,-T,/tmp/hourclock_rv.ld \
    -o /tmp/hourclock_rv.elf /tmp/hourclock_rv.c

```

    /usr/lib/gcc/riscv64-unknown-elf/13.2.0/../../../riscv64-unknown-elf/bin/ld: warning: /tmp/hourclock_rv.elf has a LOAD segment with RWX permissions

```python
import json
import re
import subprocess

renode = subprocess.Popen(
    ["dotnet", "/opt/renode/bin/Renode.dll",
     "--disable-xwt", "--plain", "--config",
     "/tmp/hourclock-renode-config", "/tmp/hourclock.resc"],
    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT, text=True,
)
try:
    result = subprocess.run([
        "gdb-multiarch", "-q", "--batch", "/tmp/hourclock_rv.elf",
        "-ex", "target remote :3333",
        "-ex", "source /tmp/hourclock_renode.py",
    ], capture_output=True, text=True, timeout=20)
    result.check_returncode()
    match = re.search(r"^CLOCKTRACE (.*)$", result.stdout, re.MULTILINE)
    assert match, result.stdout + result.stderr
    renode_trace = [ClockState(**st) for st in json.loads(match.group(1))]
finally:
    renode.terminate()
    renode.wait(timeout=5)

renode_trace

```

    ---------------------------------------------------------------------------

    TimeoutExpired                            Traceback (most recent call last)

    Cell In[3], line 14
         12 try:
         13     time.sleep(1)
    ---> 14     result = subprocess.run([
         15         "gdb-multiarch", "-q", "--batch", "/tmp/hourclock_rv.elf",
         16         "-ex", "target remote :3333",
         17         "-ex", "source /tmp/hourclock_renode.py",
         18     ], capture_output=True, text=True, timeout=20)
         19     result.check_returncode()
         20     match = re.search(r"^CLOCKTRACE (.*)$", result.stdout, re.MULTILINE)


    File /usr/lib/python3.12/subprocess.py:550, in run(input, capture_output, timeout, check, *popenargs, **kwargs)
        548 with Popen(*popenargs, **kwargs) as process:
        549     try:
    --> 550         stdout, stderr = process.communicate(input, timeout=timeout)
        551     except TimeoutExpired as exc:
        552         process.kill()


    File /usr/lib/python3.12/subprocess.py:1209, in Popen.communicate(self, input, timeout)
       1206     endtime = None
       1208 try:
    -> 1209     stdout, stderr = self._communicate(input, endtime, timeout)
       1210 except KeyboardInterrupt:
       1211     # https://bugs.python.org/issue25942
       1212     # See the detailed comment in .wait().
       1213     if timeout is not None:


    File /usr/lib/python3.12/subprocess.py:2116, in Popen._communicate(self, input, endtime, orig_timeout)
       2111     raise RuntimeError(  # Impossible :)
       2112         '_check_timeout(..., skip_check_and_raise=True) '
       2113         'failed to raise TimeoutExpired.')
       2115 ready = selector.select(timeout)
    -> 2116 self._check_timeout(endtime, orig_timeout, stdout, stderr)
       2118 # XXX Rewrite these to use non-blocking I/O on the file
       2119 # objects; they are no longer using C stdio!
       2121 for key, events in ready:


    File /usr/lib/python3.12/subprocess.py:1253, in Popen._check_timeout(self, endtime, orig_timeout, stdout_seq, stderr_seq, skip_check_and_raise)
       1251     return
       1252 if skip_check_and_raise or _time() > endtime:
    -> 1253     raise TimeoutExpired(
       1254             self.args, orig_timeout,
       1255             output=b''.join(stdout_seq) if stdout_seq else None,
       1256             stderr=b''.join(stderr_seq) if stderr_seq else None)


    TimeoutExpired: Command '['gdb-multiarch', '-q', '--batch', '/tmp/hourclock_rv.elf', '-ex', 'target remote :3333', '-ex', 'source /tmp/hourclock_renode.py']' timed out after 20 seconds

# Pico trace

interrupt triggering?
send over hypothesis generated interrupt schedule?
hardware watchpoints

Could ingest TLA spec and directly look for violations in the fuzzer.
python script could generate hypotheses itself and just stream out traces.

If we ingest TLA spec, instead of using TLC, could check directly in python. Best to do both? Maybe being in python could inform hypothesis more (in interview they mentioned it peeks at source code?)

```
import tla
tla.Module.of_()


```

Errors in gdb script

TICKSTART TICKEND. Maybe actions are kind of spread over time not an instant?

```python
Path("/tmp/picohour").mkdir(exist_ok=True)
```

```python
%%file /tmp/picohour/CMakeLists.txt
cmake_minimum_required(VERSION 3.13)
set(PICO_BOARD pico2)
set(PICO_SDK_PATH /home/philip/.pico-sdk/sdk/2.3.0)
set(PICO_TOOLCHAIN_PATH /home/philip/.pico-sdk/toolchain/15_2_Rel1)
set(picotool_DIR /home/philip/.pico-sdk/picotool/2.3.0/picotool)
include(/home/philip/.pico-sdk/sdk/2.3.0/external/pico_sdk_import.cmake)

project(hourclock C CXX ASM)
pico_sdk_init()

add_executable(hourclock hourclock.c)
target_link_libraries(hourclock pico_stdlib)
```

    Overwriting /tmp/picohour/CMakeLists.txt

```python
%%file /tmp/picohour/hourclock.c
#include "pico/stdlib.h"

typedef struct { volatile unsigned int hr; } ClockState;
volatile ClockState state = {1};

__attribute__((noinline)) void trace_point(void) { __asm volatile ("nop"); }
__attribute__((noinline)) void trace_done(void) { __asm volatile ("nop"); }

int main(void) {
    trace_point();
    for (int i = 0; i < 10; i++) {
        state.hr = state.hr % 12 + 1;
        trace_point();
    }
    trace_done();
    while (true) tight_loop_contents();
}

```

    Overwriting /tmp/picohour/hourclock.c

```python
import subprocess
subprocess.run(["cmake", "-S", "/tmp/picohour", "-B", "/tmp/picohour/build",
                "-G", "Ninja", "-DCMAKE_BUILD_TYPE=Debug"], check=True)
subprocess.run(["cmake", "--build", "/tmp/picohour/build"], check=True)
```

    [0mPICO_SDK_PATH is /home/philip/.pico-sdk/sdk/2.3.0[0m
    [0mTarget board (PICO_BOARD) is 'pico2'.[0m
    [0mUsing board configuration from /home/philip/.pico-sdk/sdk/2.3.0/src/boards/include/boards/pico2.h[0m
    [0mPico Platform (PICO_PLATFORM) is 'rp2350-arm-s'.[0m


    -- The C compiler identification is GNU 13.2.1
    -- The CXX compiler identification is GNU 13.2.1
    -- The ASM compiler identification is GNU
    -- Found assembler: /usr/bin/arm-none-eabi-gcc
    -- Detecting C compiler ABI info
    -- Detecting C compiler ABI info - done
    -- Check for working C compiler: /usr/bin/arm-none-eabi-gcc - skipped
    -- Detecting C compile features
    -- Detecting C compile features - done
    -- Detecting CXX compiler ABI info
    -- Detecting CXX compiler ABI info - done
    -- Check for working CXX compiler: /usr/bin/arm-none-eabi-g++ - skipped
    -- Detecting CXX compile features
    -- Detecting CXX compile features - done


    [0mBuild type is Debug[0m
    [0mUsing regular optimized debug build (set PICO_DEOPTIMIZED_DEBUG=1 to de-optimize)[0m
    [0mUsing picotool from /home/philip/.pico-sdk/picotool/2.3.0/picotool/picotool[0m


    -- Found Python3: /home/philip/philzook58.github.io/.venv/bin/python3.12 (found version "3.12.3") found components: Interpreter
    -- Configuring done (0.7s)


    [0mTinyUSB available at /home/philip/.pico-sdk/sdk/2.3.0/lib/tinyusb/hw/bsp/rp2040; enabling build support for USB.[0m
    [0mCompiling TinyUSB with CFG_TUSB_DEBUG=1[0m
    [0mBTstack available at /home/philip/.pico-sdk/sdk/2.3.0/lib/btstack[0m
    [0mcyw43-driver available at /home/philip/.pico-sdk/sdk/2.3.0/lib/cyw43-driver[0m
    [0mmbedtls available at /home/philip/.pico-sdk/sdk/2.3.0/lib/mbedtls[0m
    [0mlwIP available at /home/philip/.pico-sdk/sdk/2.3.0/lib/lwip[0m
    [0mC library type is newlib[0m


    -- Generating done (0.1s)
    -- Build files have been written to: /tmp/picohour/build
    [1/4] Generating bs2_default_padded.S
    [2/4] Building ASM object pico-sdk/src/rp2350/boot_stage2/CMakeFiles/bs2_default_library.dir/bs2_default_padded.S.o
    [3/4] Building C object CMakeFiles/hourclock.dir/hourclock.c.o
    [4/4] Linking CXX executable hourclock.elf





    CompletedProcess(args=['cmake', '--build', '/tmp/picohour/build'], returncode=0)

```python
%%file /tmp/picohour/trace.py

import gdb
import json

trace = []

class TracePoint(gdb.Breakpoint):
    def stop(self):
        trace.append({"hr": int(gdb.parse_and_eval("state.hr"))})
        return False

TracePoint("trace_point")
gdb.Breakpoint("trace_done")
gdb.execute("monitor reset init")
gdb.execute("load")
gdb.execute("continue")
print("CLOCKTRACE " + json.dumps(trace))

```

    Overwriting /tmp/picohour/trace.py

```python
import re
import json
from dataclasses import dataclass, replace
@dataclass
class ClockState:
    hr : int
openocd = subprocess.Popen([
    "/home/philip/.pico-sdk/openocd/0.12.0+dev/openocd",
    "-s", "/home/philip/.pico-sdk/openocd/0.12.0+dev/scripts",
    "-f", "interface/cmsis-dap.cfg", "-f", "target/rp2350.cfg",
    "-c", "adapter speed 5000",
], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
try:
    for line in openocd.stdout:
        if "Listening on port 3333 for gdb connections" in line:
            break
    result = subprocess.run([
        "gdb-multiarch", "-q", "--batch", "/tmp/picohour/build/hourclock.elf",
        "-ex", "target extended-remote localhost:3333",
        "-ex", "source /tmp/picohour/trace.py",
    ], capture_output=True, text=True, check=True, timeout=30)
finally:
    openocd.terminate()
    openocd.wait(timeout=5)

match = re.search(r"^CLOCKTRACE (.*)$", result.stdout, re.MULTILINE)
assert match, result.stdout + result.stderr
pico_trace = [ClockState(**st) for st in json.loads(match.group(1))]
pico_trace
```

    [ClockState(hr=1),
     ClockState(hr=2),
     ClockState(hr=3),
     ClockState(hr=4),
     ClockState(hr=5),
     ClockState(hr=6),
     ClockState(hr=7),
     ClockState(hr=8),
     ClockState(hr=9),
     ClockState(hr=10),
     ClockState(hr=11)]

# rust

```python
%%file /tmp/hourclock.rs

struct ClockState {
    hr: u32,
}
impl ClockState {
    fn new(hr: u32) -> Self {
        assert!(hr >= 1 && hr <= 12);
        ClockState { hr }
    }
    fn tick(&mut self) {
        self.hr = (self.hr + 1) % 12;
    }
}

fn main(){
    let mut clock = ClockState::new(12);
    for i in 0..100 {
        clock.tick();
        'mylabel: for _ in 0..0 {}
        // MYLABEL
        println!("CLOCK {} { { hr : {} } }", i, clock.hr);
    }
}

```

    Overwriting /tmp/hourclock.rs

Ok so add some sigil and grep for it.
It breaks at the next one?
Or add ranges that correspond to actions?

Tick = ("main:23","main:24")

check for atomiciity? If another action starts
watchpoint on all variables. But what if variable is in

// IncStart
gIndex++
// IncEnd

Then we probably would find a discrepancy

Ok. the other bit is random stepping

```python
with open("/tmp/hourclock.rs", "r") as f:
    for n, line in enumerate(f.readlines()):
        if "MYLABEL" in line:
            print(n+1) # line labels start at 1
```

    20

<https://www.sourceware.org/gdb/current/onlinedocs/gdb.html/Tracepoints.html#Tracepoints> This sounds really useful

ActionStart/ActionEnd?
Or a single Action time point?
Labelling can be embedded via comments
I haven’t really found a good way to have stable rust labels
Loop labels i don’t think persist in debug data?
Python can grep for comments and hence line number though
I think the diffference of next vs step would be enough for the simple race to be picked up as gindex++ not being atomic
If i used start end style action labels, it’ll see that increment isn’t atomic

```python
! rustc -g -C debuginfo=2 -o /tmp/hourclock /tmp/hourclock.rs && /tmp/hourclock
```

    [1m[33mwarning[0m[1m: unused label[0m
      [1m[94m--> [0m/tmp/hourclock.rs:19:9
       [1m[94m|[0m
    [1m[94m19[0m [1m[94m|[0m         'mylabel: for _ in 0..0 {}
       [1m[94m|[0m         [1m[33m^^^^^^^^[0m
       [1m[94m|[0m
       [1m[94m= [0m[1mnote[0m: `#[warn(unused_labels)]` (part of `#[warn(unused)]`) on by default
    


    [1m[33mwarning[0m[1m: 1 warning emitted[0m
    
    CLOCK 0 { hr : 1 }
    CLOCK 1 { hr : 2 }
    CLOCK 2 { hr : 3 }
    CLOCK 3 { hr : 4 }
    CLOCK 4 { hr : 5 }
    CLOCK 5 { hr : 6 }
    CLOCK 6 { hr : 7 }
    CLOCK 7 { hr : 8 }
    CLOCK 8 { hr : 9 }
    CLOCK 9 { hr : 10 }
    CLOCK 10 { hr : 11 }
    CLOCK 11 { hr : 0 }
    CLOCK 12 { hr : 1 }
    CLOCK 13 { hr : 2 }
    CLOCK 14 { hr : 3 }
    CLOCK 15 { hr : 4 }
    CLOCK 16 { hr : 5 }
    CLOCK 17 { hr : 6 }
    CLOCK 18 { hr : 7 }
    CLOCK 19 { hr : 8 }
    CLOCK 20 { hr : 9 }
    CLOCK 21 { hr : 10 }
    CLOCK 22 { hr : 11 }
    CLOCK 23 { hr : 0 }
    CLOCK 24 { hr : 1 }
    CLOCK 25 { hr : 2 }
    CLOCK 26 { hr : 3 }
    CLOCK 27 { hr : 4 }
    CLOCK 28 { hr : 5 }
    CLOCK 29 { hr : 6 }
    CLOCK 30 { hr : 7 }
    CLOCK 31 { hr : 8 }
    CLOCK 32 { hr : 9 }
    CLOCK 33 { hr : 10 }
    CLOCK 34 { hr : 11 }
    CLOCK 35 { hr : 0 }
    CLOCK 36 { hr : 1 }
    CLOCK 37 { hr : 2 }
    CLOCK 38 { hr : 3 }
    CLOCK 39 { hr : 4 }
    CLOCK 40 { hr : 5 }
    CLOCK 41 { hr : 6 }
    CLOCK 42 { hr : 7 }
    CLOCK 43 { hr : 8 }
    CLOCK 44 { hr : 9 }
    CLOCK 45 { hr : 10 }
    CLOCK 46 { hr : 11 }
    CLOCK 47 { hr : 0 }
    CLOCK 48 { hr : 1 }
    CLOCK 49 { hr : 2 }
    CLOCK 50 { hr : 3 }
    CLOCK 51 { hr : 4 }
    CLOCK 52 { hr : 5 }
    CLOCK 53 { hr : 6 }
    CLOCK 54 { hr : 7 }
    CLOCK 55 { hr : 8 }
    CLOCK 56 { hr : 9 }
    CLOCK 57 { hr : 10 }
    CLOCK 58 { hr : 11 }
    CLOCK 59 { hr : 0 }
    CLOCK 60 { hr : 1 }
    CLOCK 61 { hr : 2 }
    CLOCK 62 { hr : 3 }
    CLOCK 63 { hr : 4 }
    CLOCK 64 { hr : 5 }
    CLOCK 65 { hr : 6 }
    CLOCK 66 { hr : 7 }
    CLOCK 67 { hr : 8 }
    CLOCK 68 { hr : 9 }
    CLOCK 69 { hr : 10 }
    CLOCK 70 { hr : 11 }
    CLOCK 71 { hr : 0 }
    CLOCK 72 { hr : 1 }
    CLOCK 73 { hr : 2 }
    CLOCK 74 { hr : 3 }
    CLOCK 75 { hr : 4 }
    CLOCK 76 { hr : 5 }
    CLOCK 77 { hr : 6 }
    CLOCK 78 { hr : 7 }
    CLOCK 79 { hr : 8 }
    CLOCK 80 { hr : 9 }
    CLOCK 81 { hr : 10 }
    CLOCK 82 { hr : 11 }
    CLOCK 83 { hr : 0 }
    CLOCK 84 { hr : 1 }
    CLOCK 85 { hr : 2 }
    CLOCK 86 { hr : 3 }
    CLOCK 87 { hr : 4 }
    CLOCK 88 { hr : 5 }
    CLOCK 89 { hr : 6 }
    CLOCK 90 { hr : 7 }
    CLOCK 91 { hr : 8 }
    CLOCK 92 { hr : 9 }
    CLOCK 93 { hr : 10 }
    CLOCK 94 { hr : 11 }
    CLOCK 95 { hr : 0 }
    CLOCK 96 { hr : 1 }
    CLOCK 97 { hr : 2 }
    CLOCK 98 { hr : 3 }
    CLOCK 99 { hr : 4 }

watch clock.hr
condition 1
display clock.hr
list .

```python
%%file /tmp/hourclock_gdb.py
import gdb
#print("hello world")


gdb.write("hello world\n")

gdb.execute("set pagination off")
gdb.execute("file /tmp/hourclock")
gdb.execute("info functions")
#gdb.execute("list Clockstate.tick")

# shell commands
res = gdb.execute("! ls")
print(res) # nothin. Ok
gdb.execute("set confirm off")
gdb.execute("set debuginfod enabled off")
#gdb.execute("start")
gdb.execute("start")
import random

gdb.execute(f"n {random.randint(1, 12)}")
gdb.execute("run") # run > /tmp/myoutfile


gdb.execute("quit")

```

    Overwriting /tmp/hourclock_gdb.py

```python
! gdb -ex "source /tmp/hourclock_gdb.py"    # /tmp/hourclock -ex "quit"
```

    [35;1mGNU gdb (Ubuntu 15.1-1ubuntu1~24.04.1) 15.1[m
    Copyright (C) 2024 Free Software Foundation, Inc.


    [Thread debugging using libthread_db enabled]
    Using host libthread_db library "[32m/lib/x86_64-linux-gnu/libthread_db.so.1[m".
    
    Temporary breakpoint 1, [33mhourclock::main[m () at [32m/tmp/hourclock.rs[m:16
    16     [01;34mlet[m [01;34mmut[m clock [31m=[m ClockState[31m::[m[01mnew[m[31m([m[35m12[m[31m);[m
    CLOCK 0 { hr : 1 }
    CLOCK 1 { hr : 2 }
    17     [01;34mfor[m i [01;34min[m [35m0[m[31m..[m[35m100[m [31m{[m
    [Thread debugging using libthread_db enabled]
    Using host libthread_db library "[32m/lib/x86_64-linux-gnu/libthread_db.so.1[m".
    CLOCK 0 { hr : 1 }
    CLOCK 1 { hr : 2 }
    CLOCK 2 { hr : 3 }
    CLOCK 3 { hr : 4 }
    CLOCK 4 { hr : 5 }
    CLOCK 5 { hr : 6 }
    CLOCK 6 { hr : 7 }
    CLOCK 7 { hr : 8 }
    CLOCK 8 { hr : 9 }
    CLOCK 9 { hr : 10 }
    CLOCK 10 { hr : 11 }
    CLOCK 11 { hr : 0 }
    CLOCK 12 { hr : 1 }
    CLOCK 13 { hr : 2 }
    CLOCK 14 { hr : 3 }
    CLOCK 15 { hr : 4 }
    CLOCK 16 { hr : 5 }
    CLOCK 17 { hr : 6 }
    CLOCK 18 { hr : 7 }
    CLOCK 19 { hr : 8 }
    CLOCK 20 { hr : 9 }
    CLOCK 21 { hr : 10 }
    CLOCK 22 { hr : 11 }
    CLOCK 23 { hr : 0 }
    CLOCK 24 { hr : 1 }
    CLOCK 25 { hr : 2 }
    CLOCK 26 { hr : 3 }
    CLOCK 27 { hr : 4 }
    CLOCK 28 { hr : 5 }
    CLOCK 29 { hr : 6 }
    CLOCK 30 { hr : 7 }
    CLOCK 31 { hr : 8 }
    CLOCK 32 { hr : 9 }
    CLOCK 33 { hr : 10 }
    CLOCK 34 { hr : 11 }
    CLOCK 35 { hr : 0 }
    CLOCK 36 { hr : 1 }
    CLOCK 37 { hr : 2 }
    CLOCK 38 { hr : 3 }
    CLOCK 39 { hr : 4 }
    CLOCK 40 { hr : 5 }
    CLOCK 41 { hr : 6 }
    CLOCK 42 { hr : 7 }
    CLOCK 43 { hr : 8 }
    CLOCK 44 { hr : 9 }
    CLOCK 45 { hr : 10 }
    CLOCK 46 { hr : 11 }
    CLOCK 47 { hr : 0 }
    CLOCK 48 { hr : 1 }
    CLOCK 49 { hr : 2 }
    CLOCK 50 { hr : 3 }
    CLOCK 51 { hr : 4 }
    CLOCK 52 { hr : 5 }
    CLOCK 53 { hr : 6 }
    CLOCK 54 { hr : 7 }
    CLOCK 55 { hr : 8 }
    CLOCK 56 { hr : 9 }
    CLOCK 57 { hr : 10 }
    CLOCK 58 { hr : 11 }
    CLOCK 59 { hr : 0 }
    CLOCK 60 { hr : 1 }
    CLOCK 61 { hr : 2 }
    CLOCK 62 { hr : 3 }
    CLOCK 63 { hr : 4 }
    CLOCK 64 { hr : 5 }
    CLOCK 65 { hr : 6 }
    CLOCK 66 { hr : 7 }
    CLOCK 67 { hr : 8 }
    CLOCK 68 { hr : 9 }
    CLOCK 69 { hr : 10 }
    CLOCK 70 { hr : 11 }
    CLOCK 71 { hr : 0 }
    CLOCK 72 { hr : 1 }
    CLOCK 73 { hr : 2 }
    CLOCK 74 { hr : 3 }
    CLOCK 75 { hr : 4 }
    CLOCK 76 { hr : 5 }
    CLOCK 77 { hr : 6 }
    CLOCK 78 { hr : 7 }
    CLOCK 79 { hr : 8 }
    CLOCK 80 { hr : 9 }
    CLOCK 81 { hr : 10 }
    CLOCK 82 { hr : 11 }
    CLOCK 83 { hr : 0 }
    CLOCK 84 { hr : 1 }
    CLOCK 85 { hr : 2 }
    CLOCK 86 { hr : 3 }
    CLOCK 87 { hr : 4 }
    CLOCK 88 { hr : 5 }
    CLOCK 89 { hr : 6 }
    CLOCK 90 { hr : 7 }
    CLOCK 91 { hr : 8 }
    CLOCK 92 { hr : 9 }
    CLOCK 93 { hr : 10 }
    CLOCK 94 { hr : 11 }
    CLOCK 95 { hr : 0 }
    CLOCK 96 { hr : 1 }
    CLOCK 97 { hr : 2 }
    CLOCK 98 { hr : 3 }
    CLOCK 99 { hr : 4 }
    [Inferior 1 (process 2747733) exited normally]

```python
! rustup target list
```

    aarch64-apple-darwin
    aarch64-apple-ios
    aarch64-apple-ios-macabi
    aarch64-apple-ios-sim
    aarch64-apple-tvos
    aarch64-apple-tvos-sim
    aarch64-apple-visionos
    aarch64-apple-visionos-sim
    aarch64-apple-watchos
    aarch64-apple-watchos-sim
    aarch64-linux-android
    aarch64-pc-windows-gnullvm
    aarch64-pc-windows-msvc
    aarch64-unknown-freebsd
    aarch64-unknown-fuchsia
    aarch64-unknown-linux-gnu
    aarch64-unknown-linux-musl
    aarch64-unknown-linux-ohos
    aarch64-unknown-none
    aarch64-unknown-none-softfloat
    aarch64-unknown-uefi
    arm-linux-androideabi
    arm-unknown-linux-gnueabi
    arm-unknown-linux-gnueabihf
    arm-unknown-linux-musleabi
    arm-unknown-linux-musleabihf
    arm64ec-pc-windows-msvc
    armv5te-unknown-linux-gnueabi
    armv5te-unknown-linux-musleabi
    armv7-linux-androideabi
    armv7-unknown-linux-gnueabi
    armv7-unknown-linux-gnueabihf
    armv7-unknown-linux-musleabi
    armv7-unknown-linux-musleabihf
    armv7-unknown-linux-ohos
    armv7a-none-eabi
    armv7a-none-eabihf
    armv7r-none-eabi
    armv7r-none-eabihf
    armv8r-none-eabihf
    i586-unknown-linux-gnu
    i586-unknown-linux-musl
    i686-linux-android
    i686-pc-windows-gnu
    i686-pc-windows-gnullvm
    i686-pc-windows-msvc
    i686-unknown-freebsd
    i686-unknown-linux-gnu
    i686-unknown-linux-musl
    i686-unknown-uefi
    loongarch64-unknown-linux-gnu
    loongarch64-unknown-linux-musl
    loongarch64-unknown-none
    loongarch64-unknown-none-softfloat
    nvptx64-nvidia-cuda
    powerpc-unknown-linux-gnu
    powerpc64-unknown-linux-gnu
    powerpc64-unknown-linux-musl
    powerpc64le-unknown-linux-gnu
    powerpc64le-unknown-linux-musl
    riscv32i-unknown-none-elf
    riscv32im-unknown-none-elf
    [1mriscv32imac-unknown-none-elf[0m [1m[94m(installed)[0m
    riscv32imafc-unknown-none-elf
    riscv32imc-unknown-none-elf
    riscv64a23-unknown-linux-gnu
    riscv64gc-unknown-linux-gnu
    riscv64gc-unknown-linux-musl
    riscv64gc-unknown-none-elf
    riscv64imac-unknown-none-elf
    s390x-unknown-linux-gnu
    sparc64-unknown-linux-gnu
    sparcv9-sun-solaris
    thumbv6m-none-eabi
    thumbv7a-none-eabi
    thumbv7a-none-eabihf
    thumbv7em-none-eabi
    thumbv7em-none-eabihf
    thumbv7m-none-eabi
    thumbv7neon-linux-androideabi
    thumbv7neon-unknown-linux-gnueabihf
    thumbv7r-none-eabi
    thumbv7r-none-eabihf
    thumbv8m.base-none-eabi
    thumbv8m.main-none-eabi
    thumbv8m.main-none-eabihf
    thumbv8r-none-eabihf
    wasm32-unknown-emscripten
    wasm32-unknown-unknown
    wasm32-wasip1
    wasm32-wasip1-threads
    wasm32-wasip2
    wasm32v1-none
    x86_64-apple-darwin
    x86_64-apple-ios
    x86_64-apple-ios-macabi
    x86_64-fortanix-unknown-sgx
    x86_64-linux-android
    x86_64-pc-solaris
    x86_64-pc-windows-gnu
    x86_64-pc-windows-gnullvm
    x86_64-pc-windows-msvc
    x86_64-unknown-freebsd
    x86_64-unknown-fuchsia
    x86_64-unknown-illumos
    [1mx86_64-unknown-linux-gnu[0m [1m[94m(installed)[0m
    x86_64-unknown-linux-gnuasan
    x86_64-unknown-linux-gnumsan
    x86_64-unknown-linux-gnutsan
    x86_64-unknown-linux-gnux32
    x86_64-unknown-linux-musl
    x86_64-unknown-linux-ohos
    x86_64-unknown-netbsd
    x86_64-unknown-none
    x86_64-unknown-redox
    x86_64-unknown-uefi

# Qemu
<https://qemu-project.gitlab.io/qemu/system/gdb.html>
ok, but qemu-system and userland are different beasts

```python
%%file /tmp/hourclock.rs

struct ClockState {
    hr: u32,
}
impl ClockState {
    fn new(hr: u32) -> Self {
        assert!(hr >= 1 && hr <= 12);
        ClockState { hr }
    }
    fn tick(&mut self) {
        self.hr = (self.hr + 1) % 12;
    }
}

fn main(){
    let mut clock = ClockState::new(12);
    loop {
        clock.tick();
    }
}
```

    Overwriting /tmp/hourclock.rs

```python
! rustc -g -C opt-level=0 /tmp/hourclock.rs -o /tmp/hourclock-x86_64
```

```python
%%file /tmp/gdb_qemu.py
import gdb
import json
import os

gdb.execute("set debuginfod enabled off")
gdb.execute("target remote :1234")
gdb.Breakpoint("hourclock::ClockState::tick")
gdb.execute("continue")
results = []
for n in json.loads(os.environ["GDB_STEPS"]):
    gdb.execute(f"next {n}")
    results.append(int(gdb.parse_and_eval("self.hr")))
gdb.write("GDB_RESULTS " + json.dumps(results) + "\n")

```

    Overwriting /tmp/gdb_qemu.py

```python
import json, os, subprocess, time
from hypothesis import given, settings, strategies as st

def run_gdb(steps):
    qemu = subprocess.Popen(["qemu-x86_64", "-g", "1234", "/tmp/hourclock-x86_64"])
    try:
        time.sleep(0.1)
        gdb = subprocess.run([
            "gdb", "-q", "--batch", "/tmp/hourclock-x86_64",
            "-ex", "source /tmp/gdb_qemu.py",
        ], capture_output=True, text=True, env=os.environ | {"GDB_STEPS": json.dumps(steps)})
    finally:
        qemu.terminate()
        qemu.wait()
    assert gdb.returncode == 0, gdb.stdout + gdb.stderr
    marker = "GDB_RESULTS "
    line = next((line for line in gdb.stdout.splitlines() if line.startswith(marker)), None)
    assert line is not None, gdb.stdout + gdb.stderr
    return json.loads(line.removeprefix(marker))

@settings(max_examples=10, deadline=None)
@given(st.lists(st.integers(min_value=1, max_value=12), min_size=1, max_size=10))
def test(steps):
    assert len(run_gdb(steps)) == len(steps)

test()
```

    [{'steps': [1], 'results': [1]},
     {'steps': [3], 'results': [1]},
     {'steps': [3, 7, 4], 'results': [1, 2, 3]},
     {'steps': [7, 7, 2, 10, 7, 4, 8, 6, 4, 9],
      'results': [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]},
     {'steps': [11, 1, 11, 8, 11, 10, 8, 6], 'results': [1, 2, 2, 3, 4, 5, 6, 7]},
     {'steps': [10, 9], 'results': [1, 2]},
     {'steps': [5, 6, 7, 11, 1, 3, 2, 1, 9, 12],
      'results': [1, 2, 3, 4, 5, 5, 6, 7, 7, 8]},
     {'steps': [8, 1, 11, 7, 12, 11, 4, 8, 6, 5],
      'results': [1, 2, 2, 3, 4, 5, 6, 7, 8, 9]},
     {'steps': [2, 6, 8, 6, 10, 11, 4, 7, 8, 9],
      'results': [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]},
     {'steps': [2], 'results': [1]}]

```python

```

# riscv32 system

```python
%%file /tmp/hourclock_rv32.rs
#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;

global_asm!(r#"
    .section .text.init
    .globl _start
_start:
    la sp, _stack_top
    call rust_main
1:  j 1b
"#);

#[repr(C)]
pub struct ClockState { pub hr: u32 }

#[no_mangle]
pub static mut state: ClockState = ClockState { hr: 12 };

#[no_mangle]
pub extern "C" fn rust_main() -> ! {
    for _ in 0..100 {
        unsafe { state.hr = state.hr % 13 + 1 }
    }
    loop { unsafe { asm!("wfi") } }
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! { loop {} }
```

    Overwriting /tmp/hourclock_rv32.rs

```python
%%file /tmp/rv32.ld
ENTRY(_start)
SECTIONS {
    . = 0x80000000;
    .text : { KEEP(*(.text.init)) *(.text*) }
    .rodata : { *(.rodata*) }
    .data : { *(.data*) }
    .bss (NOLOAD) : {
        *(.bss*)
        . = ALIGN(16);
        . += 4K;
        _stack_top = .;
    }
}
```

    Overwriting /tmp/rv32.ld

```python
! rustc +1.94.0 --target riscv32imac-unknown-none-elf -g -C opt-level=0 -C panic=abort -C link-arg=-T/tmp/rv32.ld -C link-arg=--no-relax /tmp/hourclock_rv32.rs -o /tmp/hourclock-rv32.elf
```

```python
%%file /tmp/gdb_rv32.py
import gdb, json, site, subprocess, time

site.addsitedir("/home/philip/philzook58.github.io/.venv/lib/python3.12/site-packages")
from hypothesis import given, settings, strategies as st

elf = gdb.current_progspace().filename
qemu = subprocess.Popen([
    "qemu-system-riscv32", "-machine", "virt", "-bios", "none",
    "-kernel", elf, "-S", "-gdb", "tcp::1235",
    "-display", "none", "-serial", "none", "-monitor", "none",
], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

try:
    time.sleep(0.1)
    gdb.execute("set suppress-cli-notifications on")
    gdb.execute("set architecture riscv:rv32", to_string=True)
    gdb.execute("target remote :1235", to_string=True)
    try:
        gdb.execute("set language rust", to_string=True)
        gdb.parse_and_eval("hourclock_rv32::state.hr")
        state = "hourclock_rv32::state.hr"
    except gdb.error:  # the C example
        gdb.execute("set language c", to_string=True)
        state = "state.hr"
    watch = gdb.Breakpoint(
        state, type=gdb.BP_WATCHPOINT,
        wp_class=gdb.WP_WRITE, internal=True)
    watch.silent = True
    runs = []

    @settings(deadline=None)
    @given(st.integers(min_value=1, max_value=10))
    def test(ticks):
        gdb.execute("monitor system_reset", to_string=True)
        gdb.execute("load", to_string=True)
        trace = [int(gdb.parse_and_eval(state))]
        for _ in range(ticks):
            gdb.execute("continue", to_string=True)
            trace.append(int(gdb.parse_and_eval(state)))
        runs.append(trace)

    test()
    for trace in runs:
        print(json.dumps({
            "vars": ["hr"],
            "counterexample": {
                "state": [[i, {"hr": hr}] for i, hr in enumerate(trace, 1)],
                "action": [],
            },
        }))
finally:
    try:
        gdb.execute("disconnect", to_string=True)
    except gdb.error:
        pass
    if qemu.poll() is None:
        qemu.terminate()
    qemu.wait()
```

    Overwriting /tmp/gdb_rv32.py

```python
trace_lines = ! gdb-multiarch -q --batch /tmp/hourclock-rv32.elf -x /tmp/gdb_rv32.py
traces = [json.loads(line) for line in trace_lines]
for trace in traces:
    print(json.dumps(trace))
```

    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}], [7, {"hr": 5}], [8, {"hr": 6}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}], [7, {"hr": 5}], [8, {"hr": 6}], [9, {"hr": 7}], [10, {"hr": 8}], [11, {"hr": 9}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}], [7, {"hr": 5}], [8, {"hr": 6}], [9, {"hr": 7}], [10, {"hr": 8}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}], [7, {"hr": 5}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}]], "action": []}}
    {"vars": ["hr"], "counterexample": {"state": [[1, {"hr": 12}], [2, {"hr": 13}], [3, {"hr": 1}], [4, {"hr": 2}], [5, {"hr": 3}], [6, {"hr": 4}], [7, {"hr": 5}], [8, {"hr": 6}], [9, {"hr": 7}]], "action": []}}

```python
from pathlib import Path
import kdrag.solvers.tla as tla
import re
for i, trace in enumerate(traces):
    tracefile = f"/tmp/hourclock_trace_{i}.json"
    print(trace)
    Path(tracefile).write_text(json.dumps(trace))
    out = tla.run_tools([
        "tlc2.TLC",
        "-workers", "1",
        "-loadTrace", "json", tracefile,
        "-config", "/tmp/HourClock",
        "/tmp/HourClock.tla",
    ]).decode()
    depth = int(re.search(r"The depth .* is (\d+)\.", out).group(1))
    if depth < len(trace["counterexample"]["state"]):
        states = trace["counterexample"]["state"]
        raise AssertionError(
            f"TLC rejected transition: {states[depth - 1][1]} -> {states[depth][1]}"
        )
print(f"{len(traces)} traces passed")
```

    {'vars': ['hr'], 'counterexample': {'state': [[1, {'hr': 12}], [2, {'hr': 13}]], 'action': []}}



    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[92], line 18
         16     if depth < len(trace["counterexample"]["state"]):
         17         states = trace["counterexample"]["state"]
    ---> 18         raise AssertionError(
         19             f"TLC rejected transition: {states[depth - 1][1]} -> {states[depth][1]}"
         20         )
         21 print(f"{len(traces)} traces passed")


    AssertionError: TLC rejected transition: {'hr': 12} -> {'hr': 13}

## C

```python
%%file /tmp/hourclock_rv32.c
__asm__(
    ".section .text.init\n"
    ".globl _start\n"
    "_start:\n"
    "la sp, _stack_top\n"
    "call c_main\n"
    "1: j 1b\n"
);

typedef struct { volatile unsigned int hr; } ClockState;
ClockState state = {12};

__attribute__((noreturn)) void c_main(void) {
    for (int i = 0; i < 100; ++i)
        state.hr = state.hr % 12 + 1;
    for (;;) __asm__ volatile("wfi");
}
```

```python
! riscv64-unknown-elf-gcc -march=rv32imac -mabi=ilp32 -mcmodel=medany -g -O0 -ffreestanding -nostdlib -T /tmp/rv32.ld -Wl,--no-relax,--no-warn-rwx-segments /tmp/hourclock_rv32.c -o /tmp/hourclock-rv32-c.elf
```

```python
! gdb-multiarch -q --batch /tmp/hourclock-rv32-c.elf -x /tmp/gdb_rv32.py
```

# Simple Interrupt

```python
%%file /tmp/GIndexAtomic.tla
---------------- MODULE GIndexAtomic ----------------
EXTENDS Naturals

VARIABLE gIndex

Init == gIndex = 0
MainStep == /\ gIndex # 0 /\ gIndex' = gIndex - 1
IntStep == gIndex' = gIndex + 1
Next == MainStep \/ IntStep \/ UNCHANGED gIndex
Bound == gIndex <= 10
====================================================
```

    Overwriting /tmp/GIndexAtomic.tla

```python
%%file /tmp/GIndexAtomic.cfg
INIT Init
NEXT Next
CONSTRAINT Bound
```

    Overwriting /tmp/GIndexAtomic.cfg

clint core local interrupt - MSIP = macine software interrupt pending
plic platform level interrupt controller

```python
%%file /tmp/gindex_rv32.c
#include <stdint.h>

#define CLINT_MSIP (*(volatile uint32_t *)0x02000000)

__asm__(
    ".section .text.init\n"
    ".globl _start\n"
    "_start:\n"
    "la sp, _stack_top\n"
    "call main\n"
    "1: j 1b\n"
);

volatile uint32_t gIndex = 0;

void __attribute__((interrupt("machine"), aligned(4))) interrupt_handler(void) {
    CLINT_MSIP = 0;
    gIndex++;
}

void __attribute__((noinline)) main_loop(void) {
    for (;;)
        if (gIndex)
            gIndex--;
}

void main(void) {
    __asm__ volatile("csrw mtvec, %0" :: "r"(interrupt_handler));
    __asm__ volatile("csrsi mie, 8");
    __asm__ volatile("csrsi mstatus, 8");
    main_loop();
}
```

    Overwriting /tmp/gindex_rv32.c

```python
! riscv64-unknown-elf-gcc -march=rv32imac_zicsr -mabi=ilp32 -mcmodel=medany -g -O0 -ffreestanding -nostdlib -T /tmp/rv32.ld -Wl,--no-relax,--no-warn-rwx-segments /tmp/gindex_rv32.c -o /tmp/gindex-rv32.elf
```

```python
%%file /tmp/gdb_gindex.py
import gdb, json, site, socket, subprocess, time

site.addsitedir("/home/philip/philzook58.github.io/.venv/lib/python3.12/site-packages")
from hypothesis import given, settings, strategies as st

elf = gdb.current_progspace().filename
qemu = subprocess.Popen([
    "qemu-system-riscv32", "-machine", "virt", "-bios", "none",
    "-kernel", elf, "-S", "-gdb", "tcp::1236",
    "-qtest", "tcp:127.0.0.1:1237,server=on,wait=off",
    "-display", "none", "-serial", "none", "-monitor", "none",
], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
qtest = None

try:
    time.sleep(0.1)
    gdb.execute("set suppress-cli-notifications on")
    gdb.execute("set architecture riscv:rv32", to_string=True)
    gdb.execute("target remote :1236", to_string=True)
    gdb.execute("maintenance packet Qqemu.sstep=0x5", to_string=True)  # allow IRQs while stepping
    gdb.execute("set language c", to_string=True)
    qtest = socket.create_connection(("127.0.0.1", 1237))
    runs = []

    def irq_enabled():
        mstatus = int(gdb.parse_and_eval("$mstatus"))
        mie = int(gdb.parse_and_eval("$mie"))
        mip = int(gdb.parse_and_eval("$mip"))
        return mstatus & 8 and mie & 8 and not mip & 8

    def interrupt():
        qtest.sendall(b"writel 0x02000000 1\n")
        assert qtest.recv(64).startswith(b"OK")

    @settings(max_examples=10, deadline=None, derandomize=True)
    @given(st.lists(st.integers(1, 30), min_size=5, max_size=10))
    def test(schedule):
        gdb.execute("monitor system_reset", to_string=True)
        gdb.execute("load", to_string=True)
        stop = gdb.Breakpoint("main_loop", temporary=True, internal=True)
        stop.silent = True
        gdb.execute("continue", to_string=True)
        trace = [int(gdb.parse_and_eval("gIndex"))]
        for n in schedule:
            if irq_enabled():
                interrupt()
            for _ in range(n):
                gdb.execute("stepi", to_string=True)
                value = int(gdb.parse_and_eval("gIndex"))
                if value != trace[-1]:
                    trace.extend([trace[-1], value])
        runs.append(trace)

    test()
    for trace in runs:
        print(json.dumps({
            "vars": ["gIndex"],
            "counterexample": {
                "state": [[i, {"gIndex": value}]
                          for i, value in enumerate(trace, 1)],
                "action": [],
            },
        }))
finally:
    if qtest is not None:
        qtest.close()
    try:
        gdb.execute("disconnect", to_string=True)
    except gdb.error:
        pass
    if qemu.poll() is None:
        qemu.terminate()
    qemu.wait()
```

    Overwriting /tmp/gdb_gindex.py

```python
interrupt_trace_lines = ! gdb-multiarch -q --batch /tmp/gindex-rv32.elf -x /tmp/gdb_gindex.py
interrupt_traces = [json.loads(line) for line in interrupt_trace_lines]
for trace in interrupt_traces:
    print(json.dumps(trace))
```

    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 2}], [4, {"gIndex": 3}], [5, {"gIndex": 4}], [6, {"gIndex": 5}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 2}], [4, {"gIndex": 3}], [5, {"gIndex": 4}], [6, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 2}], [4, {"gIndex": 0}], [5, {"gIndex": 1}], [6, {"gIndex": 2}], [7, {"gIndex": 3}], [8, {"gIndex": 1}], [9, {"gIndex": 2}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 2}], [13, {"gIndex": 3}], [14, {"gIndex": 1}], [15, {"gIndex": 2}], [16, {"gIndex": 1}], [17, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 0}], [4, {"gIndex": 1}], [5, {"gIndex": 2}], [6, {"gIndex": 0}], [7, {"gIndex": 1}], [8, {"gIndex": 0}], [9, {"gIndex": 1}], [10, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 0}], [4, {"gIndex": 1}], [5, {"gIndex": 0}], [6, {"gIndex": 1}], [7, {"gIndex": 2}], [8, {"gIndex": 0}], [9, {"gIndex": 1}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 0}], [13, {"gIndex": 1}], [14, {"gIndex": 0}], [15, {"gIndex": 1}], [16, {"gIndex": 2}], [17, {"gIndex": 0}], [18, {"gIndex": 1}], [19, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 0}], [4, {"gIndex": 1}], [5, {"gIndex": 0}], [6, {"gIndex": 1}], [7, {"gIndex": 2}], [8, {"gIndex": 0}], [9, {"gIndex": 1}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 2}], [13, {"gIndex": 1}], [14, {"gIndex": 0}], [15, {"gIndex": 1}], [16, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 0}], [4, {"gIndex": 1}], [5, {"gIndex": 0}], [6, {"gIndex": 1}], [7, {"gIndex": 0}], [8, {"gIndex": 1}], [9, {"gIndex": 2}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 0}], [13, {"gIndex": 1}], [14, {"gIndex": 2}], [15, {"gIndex": 1}], [16, {"gIndex": 0}], [17, {"gIndex": 1}], [18, {"gIndex": 0}], [19, {"gIndex": 1}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 2}], [4, {"gIndex": 0}], [5, {"gIndex": 1}], [6, {"gIndex": 0}], [7, {"gIndex": 1}], [8, {"gIndex": 0}], [9, {"gIndex": 1}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 0}], [13, {"gIndex": 1}], [14, {"gIndex": 0}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 2}], [4, {"gIndex": 0}], [5, {"gIndex": 1}], [6, {"gIndex": 0}], [7, {"gIndex": 1}], [8, {"gIndex": 0}], [9, {"gIndex": 1}], [10, {"gIndex": 0}], [11, {"gIndex": 1}]], "action": []}}
    {"vars": ["gIndex"], "counterexample": {"state": [[1, {"gIndex": 0}], [2, {"gIndex": 1}], [3, {"gIndex": 0}], [4, {"gIndex": 1}], [5, {"gIndex": 0}], [6, {"gIndex": 1}], [7, {"gIndex": 0}], [8, {"gIndex": 1}], [9, {"gIndex": 2}], [10, {"gIndex": 0}], [11, {"gIndex": 1}], [12, {"gIndex": 0}], [13, {"gIndex": 1}], [14, {"gIndex": 2}], [15, {"gIndex": 0}], [16, {"gIndex": 1}], [17, {"gIndex": 2}]], "action": []}}

```python
for i, trace in enumerate(interrupt_traces):
    tracefile = f"/tmp/gindex_trace_{i}.json"
    Path(tracefile).write_text(json.dumps(trace))
    out = tla.run_tools([
        "tlc2.TLC", "-workers", "1",
        "-loadTrace", "json", tracefile,
        "-config", "/tmp/GIndexAtomic",
        "/tmp/GIndexAtomic.tla",
    ]).decode()
    depth = int(re.search(r"The depth .* is (\d+)\.", out).group(1))
    states = trace["counterexample"]["state"]
    if depth < len(states):
        raise AssertionError(
            f"TLC rejected transition: {states[depth - 1][1]} -> {states[depth][1]}"
        )
print(f"{len(interrupt_traces)} traces passed")
```

    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[97], line 13
         11     states = trace["counterexample"]["state"]
         12     if depth < len(states):
    ---> 13         raise AssertionError(
         14             f"TLC rejected transition: {states[depth - 1][1]} -> {states[depth][1]}"
         15         )
         16 print(f"{len(interrupt_traces)} traces passed")


    AssertionError: TLC rejected transition: {'gIndex': 4} -> {'gIndex': 0}

## Non-atomic spec

```python
%%file /tmp/GIndexNonAtomic.tla
--------------- MODULE GIndexNonAtomic ---------------
EXTENDS Naturals

VARIABLE gIndex, mainpc, gindexlocal, received, processed
vars == <<gIndex, mainpc, gindexlocal, received, processed>>

Init ==
    /\ gIndex = 0
    /\ gindexlocal = 0
    /\ mainpc = "load"
    /\ received = 0
    /\ processed = 0

Load ==
    /\ mainpc = "load"
    /\ gIndex # 0
    /\ mainpc' = "dec"
    /\ gindexlocal' = gIndex - 1
    /\ UNCHANGED <<gIndex, received, processed>>

Dec ==
    /\ mainpc = "dec"
    /\ mainpc' = "load"
    /\ gIndex' = gindexlocal
    /\ processed' = processed + 1
    /\ UNCHANGED <<gindexlocal, received>>

IRQInc ==
    /\ gIndex' = gIndex + 1
    /\ received' = received + 1
    /\ UNCHANGED <<mainpc, gindexlocal, processed>>

Next == Load \/ Dec \/ IRQInc \/ UNCHANGED vars
NoLost == received = processed + gIndex
Bound == /\ gIndex <= 10 /\ gindexlocal <= 10
         /\ received <= 10 /\ processed <= 10
======================================================
```

```python
%%file /tmp/GIndexNonAtomic.cfg
INIT Init
NEXT Next
CONSTRAINT Bound
```

```python
for i, trace in enumerate(interrupt_traces):
    tracefile = f"/tmp/gindex_refined_trace_{i}.json"
    Path(tracefile).write_text(json.dumps(trace))
    out = tla.run_tools([
        "tlc2.TLC", "-workers", "1",
        "-loadTrace", "json", tracefile,
        "-config", "/tmp/GIndexNonAtomic",
        "/tmp/GIndexNonAtomic.tla",
    ]).decode()
    depth = int(re.search(r"The depth .* is (\d+)\.", out).group(1))
    assert depth >= len(trace["counterexample"]["state"]), out
print(f"{len(interrupt_traces)} refined traces passed")
```

```python
%%file /tmp/GIndexNonAtomicCheck.cfg
INIT Init
NEXT Next
CONSTRAINT Bound
INVARIANT NoLost
```

```python
try:
    tla.run_tools([
        "tlc2.TLC", "-workers", "1",
        "-config", "/tmp/GIndexNonAtomicCheck",
        "/tmp/GIndexNonAtomic.tla",
    ])
except RuntimeError as error:
    assert "Invariant NoLost is violated" in str(error)
    print(error)
else:
    raise AssertionError("expected NoLost violation")
```

# factoring

Qemu class

class for specific system. How to detect if interrupts are enabled

Yeah, maybe this is overwrought. But I also want guidance about how not to end up with false negatives.

```
class Tracer
    def __init__(self, mod):
        self.vars = []
        self.traces = []
        self.tla_mod = mod
        for action in mod.actions:
            # find action in file comments
    def 

    def add_var(self, tla_name, gdb_expr):
        assert tla_name in self.tla_mod.vars
    def trace(self):
        event = [gdb.parse_and_eval(gdb_expr) for tla_name, gdb_expr in self.vars]
        self.traces[-1].append(event)
    def new_trace(self):
        assert self.vars == self.tla_mod.vars # we know how to monitor all of them.
        self.traces.append([])
```

Moving more out of the python and into tla is probably good, _if_ we can compare tla specs
lean + gdb mi? or python import lean something? Somewhat arcane achitecture. but maybe.

Try it on hardware debug pi pico
write blog post

qtree - config params?
mtree

Single step qemu?
qmp vs hmp

qtest? <https://www.qemu.org/docs/master/devel/testing/qtest.html>

```python
! echo -e "info mtree\n quit" | qemu-system-riscv32 \
  -machine opentitan \
  -S -display none -monitor stdio
```

    QEMU 8.2.2 monitor - type 'help' for more information
    (qemu) i[K[Din[K[D[Dinf[K[D[D[Dinfo[K[D[D[D[Dinfo [K[D[D[D[D[Dinfo m[K[D[D[D[D[D[Dinfo mt[K[D[D[D[D[D[D[Dinfo mtr[K[D[D[D[D[D[D[D[Dinfo mtre[K[D[D[D[D[D[D[D[D[Dinfo mtree[K
    address-space: cpu-memory-0
    address-space: memory
      0000000000000000-ffffffffffffffff (prio 0, i/o): system
        0000000000008000-000000000000ffff (prio 0, rom): riscv.lowrisc.ibex.rom
        0000000010000000-000000001001ffff (prio 0, ram): riscv.lowrisc.ibex.ram
        0000000020000000-00000000200fffff (prio 0, rom): riscv.lowrisc.ibex.flash
        0000000040000000-00000000400003ff (prio 0, i/o): ibex-uart
        0000000040040000-000000004004003f (prio -1000, i/o): riscv.lowrisc.ibex.gpio
        0000000040050000-0000000040051fff (prio -1000, i/o): riscv.lowrisc.ibex.spi_device
        0000000040080000-000000004008007f (prio -1000, i/o): riscv.lowrisc.ibex.i2c
        00000000400e0000-00000000400e003f (prio -1000, i/o): riscv.lowrisc.ibex.pattgen
        0000000040100000-00000000401003ff (prio 0, i/o): ibex-timer
        0000000040130000-0000000040131fff (prio -1000, i/o): riscv.lowrisc.ibex.otp_ctrl
        0000000040140000-00000000401400ff (prio -1000, i/o): riscv.lowrisc.ibex.lc_ctrl
        0000000040150000-00000000401507ff (prio -1000, i/o): riscv.lowrisc.ibex.alert_handler
        0000000040300000-0000000040300fff (prio 0, i/o): ibex-spi
        0000000040310000-0000000040310fff (prio 0, i/o): ibex-spi
        0000000040320000-0000000040320fff (prio -1000, i/o): riscv.lowrisc.ibex.usbdev
        0000000040400000-000000004040007f (prio -1000, i/o): riscv.lowrisc.ibex.pwrmgr
        0000000040410000-000000004041007f (prio -1000, i/o): riscv.lowrisc.ibex.rstmgr
        0000000040420000-000000004042007f (prio -1000, i/o): riscv.lowrisc.ibex.clkmgr
        0000000040460000-0000000040460fff (prio -1000, i/o): riscv.lowrisc.ibex.pinmux
        0000000040470000-000000004047003f (prio -1000, i/o): riscv.lowrisc.ibex.aon_timer
        0000000040490000-000000004049003f (prio -1000, i/o): riscv.lowrisc.ibex.sensor_ctrl
        0000000041000000-00000000410001ff (prio -1000, i/o): riscv.lowrisc.ibex.flash_ctrl
        0000000041100000-00000000411000ff (prio -1000, i/o): riscv.lowrisc.ibex.aes
        0000000041110000-0000000041110fff (prio -1000, i/o): riscv.lowrisc.ibex.hmac
        0000000041120000-0000000041120fff (prio -1000, i/o): riscv.lowrisc.ibex.kmac
        0000000041130000-000000004113ffff (prio -1000, i/o): riscv.lowrisc.ibex.otbn
        0000000041140000-00000000411400ff (prio -1000, i/o): riscv.lowrisc.ibex.keymgr
        0000000041150000-000000004115007f (prio -1000, i/o): riscv.lowrisc.ibex.csrng
        0000000041160000-00000000411600ff (prio -1000, i/o): riscv.lowrisc.ibex.entropy
        0000000041170000-000000004117007f (prio -1000, i/o): riscv.lowrisc.ibex.edn0
        0000000041180000-000000004118007f (prio -1000, i/o): riscv.lowrisc.ibex.edn1
        00000000411c0000-00000000411c001f (prio -1000, i/o): riscv.lowrisc.ibex.sram_ctrl
        00000000411f0000-00000000411f00ff (prio -1000, i/o): riscv.lowrisc.ibex.ibex_cfg
        0000000048000000-000000004fffffff (prio 0, i/o): riscv.sifive.plic
        0000000080000000-000000008007ffff (prio 0, rom): alias riscv.lowrisc.ibex.flash_virtual @riscv.lowrisc.ibex.flash 0000000000000000-000000000007ffff
    
    address-space: I/O
      0000000000000000-000000000000ffff (prio 0, i/o): io
    
    memory-region: riscv.lowrisc.ibex.flash
      0000000020000000-00000000200fffff (prio 0, rom): riscv.lowrisc.ibex.flash
    
    (qemu)  [K[D q[K[D[D qu[K[D[D[D qui[K[D[D[D[D quit[K

```python

```
