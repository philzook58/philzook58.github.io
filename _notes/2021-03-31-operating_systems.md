[Operating Systems: Three Easy Pieces](https://pages.cs.wisc.edu/~remzi/OSTEP/)

Serial port programing https://www.cmrr.umn.edu/~strupp/serial.html
https://en.wikibooks.org/wiki/Serial_Programming/termios termios

ioctl
fcntl

[Beej's Guide to Network Programming](https://beej.us/guide/bgnet/html/)

##  System Calls
[The Definitive Guide to Linux System Calls](https://blog.packagecloud.io/the-definitive-guide-to-linux-system-calls/) some nice info on how syscalls happens. Interrupt x80, `syscall` instruction etc. VDSO - v

- `mmap`
- `connect`
- `open`
- `read`
- `write`


## Virtualization

## Concurrency

## File System
Disk sectors.
Disk rotation speed
Disk Seek time

RAID -  Redundant array of inexpensive disks. Copy data to multiple disks, or use error correction. RAID0 just interleaves disks for parallelism
striping - put subsequent blocks on different disks
RAID 1 - mirroring. Just rwwrite the same thing to multiple disks



<https://github.com/klange/toaruos> complete operating system from scratch


Hypervisors - like OS for OSes

How do programs start?

Syscalls

Memory management

Scheduling - interrupts

Locks
-  pthreads



LWN

Linux Kernel Labs
https://linux-kernel-labs.github.io/refs/heads/master/index.html

https://training.linuxfoundation.org/training/a-beginners-guide-to-linux-kernel-development-lfd103/

kernel documentation
https://www.kernel.org/doc/html/latest/