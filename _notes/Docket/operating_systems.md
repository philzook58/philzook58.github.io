---
layout: post
title: Operating Systems
---

- [Linux](#linux)
  - [System Calls](#system-calls)
  - [Resources](#resources)
  - [Kernel](#kernel)
  - [Security](#security)
  - [Tracing](#tracing)
  - [Virtualization](#virtualization)
  - [Concurrency](#concurrency)
  - [Make](#make)
  - [Seccomp](#seccomp)
  - [Git](#git)
  - [Emacs?](#emacs)
  - [Alternate shells](#alternate-shells)
  - [Command Line Tools](#command-line-tools)
  - [docker](#docker)
- [Windows](#windows)
- [RTOS](#rtos)
- [microkernels](#microkernels)
  - [seL4](#sel4)
- [Hypervisors](#hypervisors)
- [Bootloaders](#bootloaders)
- [File System](#file-system)
- [Stuff](#stuff)

See also note on:

- Concurrency

# Linux

[Beej's Guide to Network Programming](https://beej.us/guide/bgnet/html/)
[Linux Kernel Development](https://www.youtube.com/watch?v=598Xe7OsPuU&ab_channel=linuxhint)
[build the smallest possible linux system](https://www.youtube.com/watch?v=Sk9TatW9ino)

Serial port programing <https://www.cmrr.umn.edu/~strupp/serial.html>
<https://en.wikibooks.org/wiki/Serial_Programming/termios> termios

ioctl
fcntl

kernel newbies <https://kernelnewbies.org/>
<https://linux-kernel-labs.github.io/refs/heads/master/index.html> labs

kernel.org. download kernel source. wow it compresses well

Building the kernel.

`make menuconfig`

## System Calls

[The Definitive Guide to Linux System Calls](https://blog.packagecloud.io/the-definitive-guide-to-linux-system-calls/) some nice info on how syscalls happens. Interrupt x80, `syscall` instruction etc. VDSO - v

- `mmap`
- `connect`
- `open`
- `close`
- `read`
- `write`
- `sync`

- `select`
- `poll`

- `fork` - make new process.

- `futex` fast userspace mutex <https://www.collabora.com/news-and-blog/blog/2022/02/08/landing-a-new-syscall-part-what-is-futex/> <https://news.ycombinator.com/item?id=30271902>
[futex tutorial](https://github.com/tchajed/futex-tutorial)

- `epoll`
- `dnotify` / `inotify` - be told when certain events happen

- `ptrace` a parent process can control another process. Gets to peek and poke memory. Control transferred on singals or system calls. Used by debuggers for example. Single step instructions

- [`io_uring`](https://en.wikipedia.org/wiki/Io_uring) I think this is a set of new system calls. Fast io using a ring buffer. liburing library

- `io_ctl` device specific control calls

[Porting OpenBSD pledge() to Linux](https://justine.lol/pledge/)

## Resources

Linux Kernel Labs
<https://linux-kernel-labs.github.io/refs/heads/master/index.html>

<https://training.linuxfoundation.org/training/a-beginners-guide-to-linux-kernel-development-lfd103/>

kernel documentation
<https://www.kernel.org/doc/html/latest/>

Locks

- pthreads

LWN

## Kernel

no libc
small pre-processed fixed size stack ~4kb
no floating point?

processes are tracked
processes own resources
pids. `ps`

## Security

seccomp

LSM linux security module
selinux and apparmor are based on lsm

selinux is externally sandboxing a process. landlock is program developer voluntarily giving up access

ebpf

firejail? <https://firejail.wordpress.com/>

<https://twitter.com/kees_cook> cool links

[landlock](https://landlock.io/) restrict ambient rights, global file system access <https://lwn.net/Articles/859908/>
<https://news.ycombinator.com/item?id=27215563> discussion about landlock, incudes ocmparsion of some other features

openbsd pledge, unveil

[security things in Linux v...](https://outflux.net/blog/archives/category/security/)

[kmsan](https://github.com/google/kmsan) KernelMemorySanitizer, a detector of uses of uninitialized memory in the Linux kernel

## Tracing

Where should this section go?
debugging
ebpf -
<https://thume.ca/2023/12/02/tracing-methods/> <https://x.com/trishume/status/1732173206466003165?s=20>
syscall errors to talk to bpf program
Cannoli, e9patch

<https://github.com/MattPD/cpplinks/blob/master/debugging.tracing.md> C++ debugging tracing
ptrace
perf
strace

PIN
hardware counters

## Virtualization

## Concurrency

libuv
libev
libevent

## Make

[Using Landlock to Sandbox GNU Make](https://justine.lol/make/)
Limitting what make can access? Only should be allowed to access files it depends on explicitly in make rules
pledge and unvil system calls <https://justine.lol/pledge/>

## Seccomp

## Git

Maybe git deserves it's own file
<https://git-scm.com/docs/git-grep>
git-bisect

## Emacs?

???

## Alternate shells

There were those beautiful pictures on that one shell.

<https://charm.sh/> charmbracelet

warp - <https://www.warp.dev/> for mac, linux comin
oh my zsh
fish

## Command Line Tools

awk
jq

<https://www.cyberciti.biz/open-source/command-line-hacks/ag-supercharge-string-search-through-directory-hierarchy/>
<https://github.com/ggreer/the_silver_searcher>
Searching through stuff
"similar to ack but faster" supercharged grep

grep -C 10

gnu parallel

[diffoscope](https://try.diffoscope.org/) recursively diff?

## docker

# Windows

Registry
WSL
powershell

# RTOS

# microkernels

<https://mirage.io/> mirage os

## seL4

Microkernel
Functional correctness
But also binary level verification. Uses gcc but disassemblers result to verify

# Hypervisors

# Bootloaders

Booting is like a whole thing.

UEFI
BIOS basic input output system - loads first sector and runs it. 16 bit code

[UBOOT](https://en.wikipedia.org/wiki/Das_U-Boot)

<https://superuser.com/questions/708196/what-is-difference-between-u-boot-and-bios>

GRUB

POST - power on self test

MBR master boot record. 512 bytes. See sector lisp, sector forth, sector games

bootloader stages  - more an more complex systems

TPM <https://www.sweetwater.com/sweetcare/articles/tpm-and-secure-boot-what-are-they-and-how-do-i-enable-them/>
secure boot
So like malware can really fuck you by manipulating the boot process? I could see that.

Formal methods applied to booting

[Formal Verification of a Modern Boot Loader 2018](https://surface.syr.edu/cgi/viewcontent.cgi?article=1182&context=eecs_techreports) - SABLE. Isabelle
[Towards a verified first-stage bootloader in Coq - 2020](https://dspace.mit.edu/handle/1721.1/127529) - phd dissertation

[SPIN 2009](https://link.springer.com/chapter/10.1007/978-3-540-76650-6_14)
[Verified functional programming of an IoT operating system's bootloader - 2021](https://dl.acm.org/doi/10.1145/3487212.3487347) Low* Riot
[Formally Verifying Security Properties for OpenTitan Boot Code with Uppaal - 2021](https://projekter.aau.dk/projekter/files/422795285/P10__24_.pdf)

[Model checking boot code from AWS data centers- 2020](http://www0.cs.ucl.ac.uk/staff/b.cook/fmsd2020.pdf) - CBMC

# File System

See also databases

Disk sectors.
Disk rotation speed
Disk Seek time

RAID -  Redundant array of inexpensive disks. Copy data to multiple disks, or use error correction. RAID0 just interleaves disks for parallelism
striping - put subsequent blocks on different disks
RAID 1 - mirroring. Just rwwrite the same thing to multiple disks

<https://github.com/klange/toaruos> complete operating system from scratch

Hypervisors - like OS for OSes

<https://twitter.com/Intel80x86/status/1560618407224963072?s=20&t=5ByjIVPCy80__MKWdWW1Aw>
[hypervisor from scratch](https://github.com/SinaKarvandi/Hypervisor-From-Scratch)
[5 Days To Virtualization: A Series On Hypervisor Development](https://revers.engineering/7-days-to-virtualization-a-series-on-hypervisor-development/)

How do programs start?

Syscalls

Memory management

Scheduling - interrupts

# Stuff

<https://www.kernel.org/doc/Documentation/filesystems/proc.txt> proc documentation

```bash
cat /proc/self/mems
cat /proc/self/status


```

<https://osquery.readthedocs.io/en/stable/> query OS info as sqlite virtual table
