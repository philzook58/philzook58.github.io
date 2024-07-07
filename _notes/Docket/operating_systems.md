---
layout: post
title: Operating Systems
---

- [Linux](#linux)
 	- [Linux Boot](#linux-boot)
 	- [Interrupts](#interrupts)
 	- [Processes](#processes)
  		- [Scheduling](#scheduling)
 	- [Memory](#memory)
 	- [File System](#file-system)
 	- [Init](#init)
  		- [systemd](#systemd)
 	- [Modules](#modules)
 	- [System Calls](#system-calls)
 	- [Resources](#resources)
 	- [Kernel](#kernel)
 	- [Security](#security)
 	- [Seccomp](#seccomp)
 	- [Tracing](#tracing)
  		- [ebpf](#ebpf)
 	- [Virtualization](#virtualization)
 	- [Concurrency](#concurrency)
 	- [Alternate shells](#alternate-shells)
 	- [Command Line Tools](#command-line-tools)
  		- [Make](#make)
  		- [Git](#git)
  		- [Emacs?](#emacs)
 	- [docker](#docker)
- [Windows](#windows)
- [RTOS](#rtos)
 	- [FreeRTOS](#freertos)
- [microkernels](#microkernels)
 	- [seL4](#sel4)
 	- [Unikernel](#unikernel)
- [Hypervisors](#hypervisors)
- [Bootloaders](#bootloaders)
- [File System](#file-system-1)
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
Can git diff to see changes?
Poking around
General setup

currnt config `cat /boot/config-$(uname -r)` Rbuilding a kernel for ubuntu
fakeroot?

hmm. I needed to turn off debian certs

process management
memory management
virtual file system
device drivers
arch

dmesg `man dmesg`
`dmesg -n 5` st level
`dmesg --level=emerg,alert,crit,err,warn`

smbios
smbus

```bash
man sysfs.5
```

procfs
sysfs
debugfs
<https://docs.kernel.org/filesystems/debugfs.html>
<https://lwn.net/Articles/309298/>

```bash
sudo ls /sys/kernel/debug
sudo cat /sys/kernel/debug/dell_laptop/rfkill
```

```
ls /sys/kernel
```

htop. K toggles kernel threads. Kill signals. cpu affinity. l  open file, x file lock, s strace, tree view, space tag process, c tag and children, name search, name filter,
strace is very fun. needs sudo

## Linux Boot

<https://en.wikipedia.org/wiki/Booting_process_of_Linux>
<https://0xax.gitbooks.io/linux-insides/content/Booting/>

bios
real mode <https://en.wikipedia.org/wiki/Real_mode>

bootloader
<https://en.wikipedia.org/wiki/Protected_mode>
grub

acpi <https://en.wikipedia.org/wiki/ACPI> Advanced Configuration and Power Interface
<https://uefi.org/specs/ACPI/6.5/> spec. hmm special registers. AML machine language bytecode
APM is old deprecated method. Many info tables.

<https://en.wikipedia.org/wiki/UEFI>
<https://uefi.org/specs/UEFI/2.10/> spec

kernel parameters. `sysct <https://docs.kernel.org/admin-guide/kernel-parameters.html>

```bash
sysctl -a
```

```bash
ls /boot # some intertestying styuff in here
# System.map kernel symbol table
# vmlinuz is the kernel
# initrd is iniital ram disk
# efi folder. This is where efi partition is mounted
# grub folder. grub.cfg has the grub options in it. x86_64-efi has grub modules
```

initramfs
vmlinux

<https://github.com/torvalds/linux/tree/v6.8-rc4/arch/x86/kernel>
startup_32 <https://github.com/torvalds/linux/blob/master/arch/x86/boot/compressed/head_64.S>
start_kernel
<https://github.com/torvalds/linux/blob/master/init/main.c> generic initialization

<https://github.com/torvalds/linux/tree/master/arch/x86/include/asm> hmm. `<asm.h/..>` stuff is found here

/sbin/init, pid 1 - often systemd. <https://en.wikipedia.org/wiki/Init>

## Interrupts

<https://0xax.gitbooks.io/linux-insides/content/Interrupts/>

<https://en.wikipedia.org/wiki/Programmable_interrupt_controller>

APIC advanced programmable interrupt controller
<https://en.wikipedia.org/wiki/Advanced_Programmable_Interrupt_Controller>

<https://en.wikipedia.org/wiki/Interrupt_descriptor_table>

<https://en.wikipedia.org/wiki/Interrupt_request> Interrupt Request

```bash
cat /proc/interrupts
#watch -n0.1 --no-title cat /proc/interrupts

# IR-IO-APIC   17-fasteoi   idma64.1, i2c_designware.1
# IR-PCI-MSI 32768-edge      i915

```

## Processes

### Scheduling

<https://en.wikipedia.org/wiki/Scheduling_(computing)#Linux>

<https://en.wikipedia.org/wiki/O(n)_scheduler> even older scheduler

<https://en.wikipedia.org/wiki/O(1)_scheduler> old scheduler.

<https://en.wikipedia.org/wiki/Completely_Fair_Scheduler> the SCHED_NORMAL default scheduler

<https://en.wikipedia.org/wiki/Brain_Fuck_Scheduler>

<https://github.com/torvalds/linux/tree/master/kernel/sched> kernel/sched folder

## Memory

<https://en.wikipedia.org/wiki/Global_Descriptor_Table>

tlb

```bash
free
```

available vs free. free is free, available is free + cache
swap. vm.swappiness

## File System

<https://github.com/torvalds/linux/tree/master/fs>

inode <https://en.wikipedia.org/wiki/Inode>

```bash
df # "disk free"
df -a # see everything
df -i /dev/nvme0n1p7 # inodes
ls -i /bin/true # inode of file
# debugfs
du # "disk usage"
ncdu # optionally installable eaiser to read https://dev.yorhel.nl/ncdu netcurses disk usage
```

fsck - file system check <https://en.wikipedia.org/wiki/Fsck>

dd

inode + filesystm idntifies. inode is per filesystem

<https://www.kernel.org/doc/html/latest/filesystems/ext4/index.html> ext4

virtual file system - an abstraction so you can plug in different actual file systems
<https://en.wikipedia.org/wiki/Procfs>
sysfs
devfs
debugfs
tmpfs - /tmp may be backed by ram

<https://en.wikipedia.org/wiki/File_system>
<https://en.wikipedia.org/wiki/Unix_filesystem>
<https://en.wikipedia.org/wiki/Journaling_file_system> journal. physical journal. write entire copy of data. expensive. logical journalling just journal metadata
File systems:
<https://en.wikipedia.org/wiki/Ext4> - extents are contiguous ranges of blocks. 4 can be stored in inode. delayed allocation. <https://en.wikipedia.org/wiki/E2fsprogs> badblacks blkid dumpe2fs e2fsck e4defrag debugfs

copy on write filesystems
<https://en.wikipedia.org/wiki/ZFS>
<https://en.wikipedia.org/wiki/Btrfs>

<https://en.wikipedia.org/wiki/Sync_(Unix)>
fsync

rsync <https://linux.die.net/man/1/rsync> - remote sync

mount

block
superblock

<https://github.com/sysprog21/simplefs> simplefs - a simple file system for Linux

<https://en.wikipedia.org/wiki/Disk_partitioning>

MBR <https://en.wikipedia.org/wiki/Master_boot_record>
bootsector code. 4 partition entries in classic.
<https://en.wikipedia.org/wiki/Cylinder-head-sector> CHS addressing. anyiquated addressing

<https://en.wikipedia.org/wiki/GUID_Partition_Table> GPT. logical block addressing <https://en.wikipedia.org/wiki/Logical_block_addressing>
table header. glonal identifier for partition type. Ok. A pretty simple system

RAID <https://en.wikipedia.org/wiki/RAID>

<https://en.wikipedia.org/wiki/Parallel_ATA> ATAPI IDE
<https://en.wikipedia.org/wiki/Serial_ATA>

logical interface
<https://en.wikipedia.org/wiki/Advanced_Host_Controller_Interface> AHCI
<https://en.wikipedia.org/wiki/NVM_Express>

<https://en.wikipedia.org/wiki/PCI_Express>

<https://en.wikipedia.org/wiki/M.2> is a form factor

what is in `/`
/var
/run
/boot
/sys
/proc
/etc
/dev
/home /root
/mnt
/media
/lost+found
/bin
/sbin
/srv
/swapfile
/usr
/tmp
/lib

## Init

daemon

### systemd

<https://en.wikipedia.org/wiki/Systemd>
units. service and others. mounts
systemctl enable disable start stop
conf files. You can override fields.
udev <https://wiki.archlinux.org/title/Udev>

`journalctl -f`. Lotso f filtering options
journald

## Modules

<https://en.wikipedia.org/wiki/Loadable_kernel_module>

<https://wiki.archlinux.org/title/Kernel_module>

insmod barebones command line to insert a module
modprobe - does depndency lookup
modinfo
lsmod see what's running

```bash
lsmod
modprobe -c
ls /etc/modprobe.d/ # blacklist.conf
ls /lib/modules
```

<https://github.com/torvalds/linux/tree/drivers>
can lookup lots of lsmod stuff in here
<https://docs.kernel.org/driver-api/index.html>

<https://github.com/sysprog21/lkmpg>
<https://sysprog21.github.io/lkmpg/>

```bash
sudo cat /proc/modules
```

```bash
ls /lib/modules/$(uname -r)
```

Hmm. I guess you really do have to buy into the kernel makefile. Fine.

```bash
mkdir /tmp/hellomod
cd /tmp/hellomod
echo "
/* 
 * hello-1.c - The simplest kernel module. 
 */ 
#include <linux/module.h> /* Needed by all modules */ 
#include <linux/printk.h> /* Needed for pr_info() */ 
 
int init_module(void) 
{ 
    pr_info(\"Hello world 1.\n\"); 
 
    /* A non 0 return means init_module failed; module can't be loaded. */ 
    return 0; 
} 
 
void cleanup_module(void) 
{ 
    pr_info(\"Goodbye world 1.\n\"); 
} 
 
MODULE_LICENSE(\"GPL\");
" > hello-1.c

echo "
obj-m += hello-1.o
PWD := \$(CURDIR) 
all:
 make -C /lib/modules/$(uname -r)/build M=\$(PWD) modules

clean:
 make -C /lib/modules/$(uname -r)/build M=\$(PWD) clean
" > Makefile
cat Makefile
make
```

```bash
cd /tmp/hellomod
modinfo hello-1.ko
sudo insmod hello-1.ko
sudo rmmod hello_1
sudo dmesg
```

retpololine

/proc/kallsyms # all symbols kernel knows about inside modules and elsewhere.

## System Calls

<https://github.com/torvalds/linux/tree/master/arch/x86/entry> transitioning syscall code
<https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl>

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

## Seccomp

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

### ebpf

<https://ebpf.io/get-started/>
There's a doucmentary? what <https://www.youtube.com/watch?v=Wb_vD3XZYOA&ab_channel=SpeakeasyProductions>

<https://www.youtube.com/watch?v=J_EehoXLbIU&ab_channel=Computerphile> huh a computerphile. the hype machine is insane

Seccomp filters

ubpf
<https://github.com/iovisor/ubpf>
<https://klyr.github.io/posts/playing_with_ubpf/>

`ubpf_test` `ubpf_plugiin`

```bash
echo "
static int idouble(int a) {
    int temp = 0;
    while(a > 0){
        temp +=  a;
        a--;
        }
        return temp;
}

int bpf_prog(void *ctx) {
        int a = 3;
        a = idouble(a);

        return (a);
}
" > /tmp/hello.c
clang -O2 -target bpf -c /tmp/hello.c -o /tmp/hello.o
/home/philip/Downloads/ubpf/build/bin/ubpf_test /tmp/hello.o
```

<https://www.brendangregg.com/blog/2019-01-01/learn-ebpf-tracing.html>

```bash
#sudo opensnoop-bpfcc # see every open
#sudo execsnoop-bpfcc # see every exec
sudo bitesize-bpfcc #
sudo stackcount-bpfcc # see every stack trace. hmm.
```

execsnoop, opensnoop, ext4slower (or btrfs*, xfs*, zfs*), biolatency, biosnoop, cachestat, tcpconnect, tcpaccept, tcpretrans, runqlat, and profil

<https://github.com/iovisor/bcc>
bcc

```python
from bcc import BPF

BPF(text='int kprobe__sys_clone(void *ctx) { bpf_trace_printk("Hello, World!\\n"); return 0; }').trace_print()
```

<https://blog.quarkslab.com/defeating-ebpf-uprobe-monitoring.html> uprobes

cillium <https://github.com/cilium/ebpf> go library read modify and loadc

## Virtualization

## Concurrency

libuv
libev
libevent

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

### Make

[Using Landlock to Sandbox GNU Make](https://justine.lol/make/)
Limitting what make can access? Only should be allowed to access files it depends on explicitly in make rules
pledge and unvil system calls <https://justine.lol/pledge/>

### Git

Maybe git deserves it's own file
<https://git-scm.com/docs/git-grep>
git-bisect

### Emacs?

???

## docker

# Windows

Registry
WSL
powershell

# RTOS

## FreeRTOS

<https://www.freertos.org/FreeRTOS-quick-start-guide.html>

# microkernels

<https://mirage.io/> mirage os

## seL4

Microkernel
Functional correctness
But also binary level verification. Uses gcc but disassemblers result to verify

## Unikernel

MirageOS

# Hypervisors

# Bootloaders

Booting is like a whole thing.

BIOS basic input output system - loads first sector and runs it. 16 bit code

UEFI <https://en.wikipedia.org/wiki/UEFI> <https://uefi.org/>
<https://github.com/river-li/awesome-uefi-security>
<https://github.com/Kostr/UEFI-Lessons>
<https://github.com/tianocore/edk2>
There's a python for uefi?
/boot/efi/
'System Volume Information' - windows stuff
EFI/Boot   bootx64.efi  fbx64.efi  mmx64.efi
EFI/windows
EFI/dell
EFI/ubuntu BOOTX64.CSV  grub.cfg  grubx64.efi  mmx64.efi - mokmanager. signing bootloader  shimx64.efi
some funky business on secure boot

ACPI - iasl. intel acpi dcompil;er/decompiler

[UBOOT](https://en.wikipedia.org/wiki/Das_U-Boot)

<https://superuser.com/questions/708196/what-is-difference-between-u-boot-and-bios>

GRUB grand unified bootloader

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
<https://github.com/raburton/rboot> boot for esp8266

 opentitan <https://github.com/lowRISC>

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
