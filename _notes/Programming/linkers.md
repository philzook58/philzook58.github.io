---
layout: post
title: Linkers and Loaders
---

- [Sections](#sections)
- [Segments](#segments)
- [Symbol Table](#symbol-table)
- [Relocations](#relocations)
- [Dynamic Linking](#dynamic-linking)
- [Compilation Units](#compilation-units)
- [Link Time Optimization](#link-time-optimization)
- [Linking Formats](#linking-formats)
  - [ELF](#elf)
- [Objcopy](#objcopy)
- [ld](#ld)
  - [Linker scripts](#linker-scripts)
- [DWARF](#dwarf)
- [Resources](#resources)
    - [JT's notes](#jts-notes)


Linking is taking a bunch of library binaries and gluing them together into a new file.

Loading is taking a binary or multiple binaries and loading it into memory so you can run it.

They are related tasks (both are transferring binaries from one place to another and doing some hooking together), but to some degree it is conceptually unfortunate that the concepts run over each other.

# Sections
Sections are for linking.


# Segments
Segments are for loading.
# Symbol Table
A key value mapping

# Relocations
[relocation](https://en.wikipedia.org/wiki/Relocation_(computing))
Relocations are "fixups" to the binary. There is a list of possible ones.
The name comes from relocatable values or something. A memory address you don't currently know. But the mechanism can get used for more things.
Some relocations look for the keys coming in from the symbol table and do something with the corresponding value.


[understanding relocations](https://stac47.github.io/c/relocation/elf/tutorial/2018/03/01/understanding-relocation-elf.html)
# Dynamic Linking
GOT global offset table - table holding global variables
PLT - procedure linkage table - table holding function pointers
got.plt 

DSO - dynamic shared object

[how to write shared libraries](https://www.akkadia.org/drepper/dsohowto.pdf)


[Better understanding Linux secondary dependencies solving with examples](http://www.kaizou.org/2015/01/linux-libraries.html)
[Shared Libraries: Understanding Dynamic Loading](https://amir.rachum.com/blog/2016/09/17/shared-libraries/)


The .dynamic section of the elf file is symbols to look for at runtime.
`readelf -d` and `objdump -T`
If the library file found during the ocmpile process has `.so` it is linked at load time. 

`ldd` lists dynamic dependencies recursively.

For some purposes you really link during program execuction. For example if you're JIT compiling this might be a way to do it. `#include <dlfcn.h>`
- dlopen(libname, flags)
- dlsym(handle, symbolname) looks up symbol name by string
dlmopen

- `LD_LIBRARY_PATH`
- `LD_DEBUG=help cat` This is crazy. This exists?
- `LD_PRELOAD`
`ldconfig`
[`ld.so`](https://man7.org/linux/man-pages/man8/ld.so.8.html)
# Compilation Units
https://en.wikipedia.org/wiki/Single_Compilation_Unit

# Link Time Optimization

# Linking Formats
Some of what makes linking formats so confusing is that they are binary representations of structured data. I am more used to thinking about the data structure and it's serialization more separately. So many of the fields are indices and sizes of other fields. It's also kind of flattened, in a similar way you might flatten to put something into a relational database.

In a curious way, if you are accessing these formats from C, it's actually _easier_ to use them than a textual format. There is no parsing necessary. You memory map in the file and just immediately interpret bytes as their appropriate structs. This does seem fraught with peril to me though.

- elf - linux
- stabs - old?
- PE - windows
- Mach-o - mac
## ELF
`man elf` on your system will give you a whole spiel

[The elf spec](https://refspecs.linuxfoundation.org/elf/elf.pdf)

`#include <elf.h>` will bring in the elf header file from your system. It isn't persay that difficult to parse elf from within C. Everywhere else it sucks.

[tmp.out](https://tmpout.sh/)

<https://github.com/tmpout/awesome-elf>

[pyelftools](https://github.com/eliben/pyelftools/) can read elf from python.

The [Lief](https://lief-project.github.io/) library is useful for manipulating formats

A lot of stuff is powered by 

# Objcopy
Not linking persay. But some useful stuff for manipulating object files

- `redefine-sym` `--redefine-syms` 
- 
# ld
## Linker scripts
[linker scripts for firmware](https://interrupt.memfault.com/blog/how-to-write-linker-scripts-for-firmware)
[linker script guide](https://www.phaedsys.com/principals/emprog/emprogdata/thunderbench-Linker-Script-guide.pdf)
[most throughly commented linker script](https://blog.thea.codes/the-most-thoroughly-commented-linker-script/)
[linker script](https://mcyoung.xyz/2021/06/01/linker-script/)

LMA vs VMA load memoery address vs virtual memory address. Can differe when stored in romvs ram for example



# DWARF
Debug info
unwind tables

[read-dwarf](https://github.com/rems-project/read-dwarf) use dwarf data and Sail / C symbolic execturo to establish bisimulation

[ORC unwind tables in kernel](https://www.kernel.org/doc/html/latest/x86/orc-unwinder.html)

[Reliable and Fast DWARF-Based Stack Unwinding](https://hal.inria.fr/hal-02297690/document)
<https://fzn.fr/projects/frdwarf/>

[dwarf too unreliable, back to frame pointers](https://rwmj.wordpress.com/2023/02/02/fedora-now-has-frame-pointers/) https://news.ycombinator.com/item?id=34632677

[How debuggers work: Part 3 - Debugging information](https://eli.thegreenplace.net/2011/02/07/how-debuggers-work-part-3-debugging-information)

[gimli](https://docs.rs/gimli/latest/gimli/) a rust library for reading and writing dwarf

C++ uses drawf unwind tables to implement exceptions

- `.debug_line` maps addresses to source code lines
- `.debug_info` maps source variables to registers and stack locations
- `.eh_frame` maps address location return address and callee saved registers info. "exception handling"
- 
DWARF encodes using bytecode.
CFA - canonical frame address
FDE - frame description entity
I suppose the dwarf bytecode is kind of a uniform abstraction of the code itself? Only replicating instructions that change frame information?

I don't know what these are
<https://github.com/emersion/libdwarfw>
<https://github.com/emersion/dareog>

[Exploitng the hard working dwarf](https://www.cs.dartmouth.edu/~sergey/battleaxe/hackito_2011_oakley_bratus.pdf)
[video](https://www.youtube.com/watch?v=nLH7ytOTYto&ab_channel=Dartmouth)

[dwarf debug format](https://developer.ibm.com/articles/au-dwarf-debug-format/)
.loc directive outputs into debug_lines table

[pyelftools](https://github.com/eliben/pyelftools/) can read dwarf data

[Introduction to the DWARF Debugging Format](https://dwarfstd.org/doc/Debugging%20using%20DWARF-2012.pdf)

[dwarf standard](https://dwarfstd.org/doc/DWARF5.pdf)

DIE - debugging information entry
.debug_info field
Tons of possible tags


Dwarf expressions are stack machine based. They give the ability to compute values based on machine state.
The mapping of dwarf registers to machine registers is archtecture specific

Each DIE has a tag and attributes

Chapter 4
- `DW_TAG_variable` 
-  `DW_TAG_formal_parameter` function call parameters
-  `DW_TAG_constant`

These have attribtures 
`DW_AT_name` `DW_AT_type` `DW_AT_location` which are the most interesting


You can get line number and column info from dwarf

[gcc flags related to debugging](https://gcc.gnu.org/onlinedocs/gcc/Debugging-Options.html#Debugging-Options)
- `-Og`
# Resources
[packer tutorial](https://github.com/frank2/packer-tutorial)

N. Glew and G. Morrisett. Type-Safe Linking and Modular Assembly Language


[stephen kell - interopability](https://www.humprog.org/~stephen/blog/2022/12/12/#interoperability-c-rich-poor) ld has a plugin interface. Cool linker links

[knit linking language](https://www.cs.utah.edu/flux/papers/knit-osdi00/)

[flux ](http://www.flux.utah.edu/paper/eide-icse02) object files _are_ objects
[statc and dynamic structures follow design patterns](http://www.flux.utah.edu/paper/eide-icse02)

[newspeak](https://gbracha.blogspot.com/2008/02/cutting-out-static.html) cut out static state

[The ABI status of ELF hash tables](https://lwn.net/SubscriberLink/904892/62301a1cdfb55841/)

[redbean](https://news.ycombinator.com/item?id=31764521) justine. Cosmopolitan. APE

ld - linker editor

[oracle linker guide](https://docs.oracle.com/cd/E23824_01/html/819-0690/index.html)

[armlink user guide](https://www.keil.com/support/man/docs/armlink/armlink_deb1353594352617.htm) A different flavor. Some interesting optimization options "veneer" as chunks of linker produced code.

[mold talks about arm thunks for long jumps](https://twitter.com/rui314/status/1497846501740998662?s=20&t=MRs67YjTJIE5glLjgsAcRA)  veneers, risc v does opposite, shrinks long jumps into short jumps. rv5 abi allows this in ways arm doesnt? What does that mean
[veneer](https://www.keil.com/support/man/docs/armlink/armlink_pge1406301797482.htm)
[linker relacation on rv5](https://www.sifive.com/blog/all-aboard-part-3-linker-relaxation-in-riscv-toolchain)


[mold design notes](https://github.com/rui314/mold/blob/main/docs/design.md) very interesting. performance tricks, history of linker features
[The teensy files](https://www.muppetlabs.com/~breadbox/software/tiny/) - writing elf by hand
[On ELF, Part 2](https://kestrelcomputer.github.io/kestrel/2018/02/01/on-elf-2) - a ctrique of elf for being too complex compared to previous formats and for little gain. Counterpoints https://news.ycombinator.com/item?id=29660319
[Assembler and loaders - David Salomon](https://www.davidsalomon.name/assem.advertis/AssemAd.html)

<https://learnxinyminutes.com/docs/ru-ru/linker-ru/>

<https://github.com/AbsInt/CompCert/blob/d194e47a7d494944385ff61c194693f8a67787cb/common/Linking.v> compcert linking file
This file follows "approach A" from the paper
       "Lightweight Verification of Separate Compilation"
    by Kang, Kim, Hur, Dreyer and Vafeiadis, POPL 2016. 
<https://twitter.com/codydroux/status/1456029745175539721?s=20> Cody tweeting about it


 APE - Actually portable executable, Cosmopolitan library
 
<http://hackercurriculum.wikidot.com/elf>
<https://bitlackeys.org/#research>
<https://github.com/elfmaster>
<https://www.amazon.com/Learning-Binary-Analysis-elfmaster-ONeill-ebook/dp/B01891X7V0>

<https://semantic-domain.blogspot.com/2012/11/in-this-post-ill-show-how-to-turn.html?m=1> geometry of interaction stuff. Neel Krinshnasawmi


Dwarf - it's like complicated. But there is a lot in there.


addr2line and other binutils
libdwarf. dwarfdump


<https://twitter.com/stephenrkell/status/1448973963741339650?s=20>
<https://www.humprog.org/~stephen//blog-all.html> - lots of interesting stuff on linkers, elf, other
<https://github.com/stephenrkell/donald/> - his small linker. Uses ocaml?
<https://github.com/rems-project/linksem> - generates ocaml?

ld_preload hacking <http://kev.pulo.com.au/publications/#lca2009_ld_preload>
<http://jvns.ca/blog/2014/11/27/ld-preload-is-super-fun-and-easy/>
<https://rafalcieslak.wordpress.com/2013/04/02/dynamic-linker-tricks-using-ld_preload-to-cheat-inject-features-and-investigate-programs/>
Hmm. So one thing you can do is mock out functions for testing. That's nice



<https://www.cl.cam.ac.uk/~pes20/rems/papers/oopsla-elf-linking-2016.pdf>


<https://web.archive.org/web/20190421205537/http://www.cs.virginia.edu/~dww4s/articles/ld_linux.html> referenced guide on how to write dynamic linker

ryan oneill elfmaster
silvio text segement padding
SCOP padding secure cide oartitioning <http://bitlackeys.org/papers/pocorgtfo20.pdf>
PT_LOAD insertion - "learning linux binary analysis" book. 
reverse text extension techniuqe
github elfmaster - skeski virus, dt
data segment insertion - "learning linux binary analysis"
dt_needed override dt_infect. dynamic segment
.got.plt infection
ymbol string redirection - 
global data in the .got
elf binary control flow hooks, function trampolines, function pointer hooks, breakpoint hnadlerh ook, tls resolver, sigill handler
https://www.youtube.com/watch?v=fCJJnJ84MSE&ab_channel=DEFCONConference
https://commons.wikimedia.org/wiki/File:ELF_Executable_and_Linkable_Format_diagram_by_Ange_Albertini.png

ptrace , injecting a loader

<https://github.com/andrewhalle/byo-linker<> <https://www.reddit.com/r/rust/comments/mdtsk5/build_your_own_linker/>

<https://www.toolchains.net/>
 - the author of gold, Ian Lance Taylor's 20 part Linker posts
<https://lwn.net/Articles/276782/>
V good

Symbols - Types and values?
Relocations - Bits of code that runs in general? Kind of bytecode?

Executable config files -  dhall. Others. Kaitai has executable aspects. if then else, others.

Functional models of linking
```ocaml
type fixups/relocs = Mov | Add | ?

{
    relocs: fixups
    symbols: {name : string ; typ : typ;  value : value}list
    contents: { section : name; contents : string }
}
```

bap's model 

```ocaml
type name = [
  | `tid of tid
  | `addr of addr
  | `symbol of string
] [@@deriving bin_io, compare, sexp]

type exn += Unbound_name of name



module type Code = functor (Machine : Machine) -> sig
  val exec : unit Machine.t
end

type code = (module Code)

(* the same piece of code can be referred via multiple names *)
type refs = {
  term : tid option;
  name : string option;
  addr : addr option;
}

type t = {
  codes : code Int.Map.t;
  alias : refs Int.Map.t;
  terms : int Tid.Map.t;
  names : int String.Map.t;
  addrs : int Addr.Map.t;
}
```


<https://github.com/ocaml/ocaml/blob/trunk/file_formats/cmo_format.mli> This is the ocaml data format of cmo files


### JT's notes

ld has default linker script
`ld --verbose` to see
-T linker script

<https://ftp.gnu.org/old-gnu/Manuals/ld-2.9.1/html_chapter/ld_3.html> (manual)
<https://home.cs.colorado.edu/~main/cs1300/doc/gnu/ld_3.html>

SECTION :
set current address. tell what sections from different files to include.

assignment.

So could I use a linker script to build a computation?
By wiring together input and output cells?



Here's an interesting challenge: linking verification
Verify a relational property that after linking the program still does the same thing.
Requires a model of linking and patching requires fixups
maybe you could have the loader actually do its work and pop in by peeking at /proc/mem
Or maybe ld_preload ?
You'd want a total program verification. In principle the problem is easy?
There is link level modulairty there. So maybe that's good
