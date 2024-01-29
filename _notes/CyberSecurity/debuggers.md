---
title: Debuggers
layout: post
---


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

# pdb

python debugger
`breakpoint`

# Core Crash Dumps

minidump <https://hacks.mozilla.org/2022/06/everything-is-broken-shipping-rust-minidump-at-mozilla/>
<https://hacks.mozilla.org/2022/06/fuzzing-rust-minidump-for-embarrassment-and-crashes/>

Stack unwindning

snetry crash reporting as a service

<https://github.com/rust-minidump/rust-minidump>
<https://crates.io/crates/minidump-stackwalk>
<https://crates.io/crates/minidump-processor>

core dumps

pwnlib corefile
crashpad <https://chromium.googlesource.com/crashpad/crashpad/> newer
breakpad <https://chromium.googlesource.com/breakpad/breakpad/>

Linux turn on core dumps. ulimit

apport reporter

ECFS Ryan's extended core file snapshotting

# Misc

symbolication - annotating symbols back in

<https://www.timdbg.com/posts/writing-a-debugger-from-scratch-part-7/> debugger from scratch
<https://www.youtube.com/watch?v=QStC084UrgY&ab_channel=TimMisiak> how windbg works

<https://www.youtube.com/@HighVoiceComputing> expert windbg debugging

dynamorio frida are kind of like debuggers. Binary instrumentation

Fault localization

gdb

lldb - fast expression exavliation. llvm debugger.

ptrace - see binary patching

int1
int3

RAD Debugger <https://github.com/EpicGames/raddebugger>

<https://github.com/HyperDbg/HyperDbg> machine architecture assisted debgged
rr - time travel debugging

<https://qira.me/> timeless debugger <https://github.com/geohot/qira>

<https://github.com/x64dbg/x64dbg>
<https://rr-project.org/>
windbg
Time trvael debugging <https://learn.microsoft.com/en-us/windows-hardware/drivers/debuggercmds/time-travel-debugging-overview>

- [pwndbg](https://browserpwndbg.readthedocs.io/en/docs/)
- heap commands. For exminging heap structur

- gef can track malloc and free. That makes sense

- gdb - See notes in C.
- [cemu](https://github.com/hugsy/cemu) an ide of sorts for writing assembly and running it
- [ollydbg]
- [edb](https://github.com/eteran/edb-debugger) an ollydbg for linux. Seems nice. A graphical debugger.
- [x64dbg](https://github.com/x64dbg/x64dbg) windows only
-
