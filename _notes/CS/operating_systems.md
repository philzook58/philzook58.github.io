---
layout: post
title: Operating Systems
---

- [Linux](#linux)
  - [System Calls](#system-calls)
  - [Resources](#resources)
  - [Kernel](#kernel)
  - [Security](#security)
  - [Virtualization](#virtualization)
  - [Concurrency](#concurrency)
- [File System](#file-system)
- [docker](#docker)
- [microkernels](#microkernels)
- [seL4](#sel4)
- [Hypervisors](#hypervisors)


See also note on:
- Concurrency

# Linux

[Beej's Guide to Network Programming](https://beej.us/guide/bgnet/html/)
[Linux Kernel Development](https://www.youtube.com/watch?v=598Xe7OsPuU&ab_channel=linuxhint)
[build the smallest possible linux system](https://www.youtube.com/watch?v=Sk9TatW9ino)


Serial port programing https://www.cmrr.umn.edu/~strupp/serial.html
https://en.wikibooks.org/wiki/Serial_Programming/termios termios

ioctl
fcntl

##  System Calls
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
https://linux-kernel-labs.github.io/refs/heads/master/index.html

https://training.linuxfoundation.org/training/a-beginners-guide-to-linux-kernel-development-lfd103/

kernel documentation
https://www.kernel.org/doc/html/latest/

Locks
-  pthreads

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

firejail? https://firejail.wordpress.com/

https://twitter.com/kees_cook cool links

[landlock](https://landlock.io/) restrict ambient rights, global file system access https://lwn.net/Articles/859908/ 
https://news.ycombinator.com/item?id=27215563 discussion about landlock, incudes ocmparsion of some other features

openbsd pledge, unveil

[security things in Linux v...](https://outflux.net/blog/archives/category/security/)

[kmsan](https://github.com/google/kmsan) KernelMemorySanitizer, a detector of uses of uninitialized memory in the Linux kernel
## Virtualization

## Concurrency
libuv
libev
libevent


# File System
Disk sectors.
Disk rotation speed
Disk Seek time

RAID -  Redundant array of inexpensive disks. Copy data to multiple disks, or use error correction. RAID0 just interleaves disks for parallelism
striping - put subsequent blocks on different disks
RAID 1 - mirroring. Just rwwrite the same thing to multiple disks



<https://github.com/klange/toaruos> complete operating system from scratch


Hypervisors - like OS for OSes


https://twitter.com/Intel80x86/status/1560618407224963072?s=20&t=5ByjIVPCy80__MKWdWW1Aw
[hypervisor from scratch](https://github.com/SinaKarvandi/Hypervisor-From-Scratch)
[5 Days To Virtualization: A Series On Hypervisor Development](https://revers.engineering/7-days-to-virtualization-a-series-on-hypervisor-development/)

How do programs start?

Syscalls

Memory management

Scheduling - interrupts


# docker

# microkernels
https://mirage.io/ mirage os


# seL4
Microkernel
Functional correctness
But also binary level verification. Uses gcc but disassemblers result to verify


# Hypervisors
