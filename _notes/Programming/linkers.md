---
layout: post
title: Linkers
---

# Sections
# Segments
# Symbol Table
# Relocations
# Compilation Units
https://en.wikipedia.org/wiki/Single_Compilation_Unit

# Link Time Optimization

# ELF

# DWARF
Debug info
unwind tables
[Reliable and Fast DWARF-Based Stack Unwinding](https://hal.inria.fr/hal-02297690/document)
<https://fzn.fr/projects/frdwarf/>
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
https://github.com/emersion/libdwarfw
https://github.com/emersion/dareog

[Exploitng the hard working dwarf](https://www.cs.dartmouth.edu/~sergey/battleaxe/hackito_2011_oakley_bratus.pdf)
[video](https://www.youtube.com/watch?v=nLH7ytOTYto&ab_channel=Dartmouth)

[dwarf debug format](https://developer.ibm.com/articles/au-dwarf-debug-format/)
.loc directive outputs into debug_lines table

[Introduction to the DWARF Debugging Format](https://dwarfstd.org/doc/Debugging%20using%20DWARF-2012.pdf)
# Resources
[mold talks about arm thunks for long jumps](https://twitter.com/rui314/status/1497846501740998662?s=20&t=MRs67YjTJIE5glLjgsAcRA)  veneers, risc v does opposite, shrinks long jumps into short jumps. rv5 abi allows this in ways arm doesnt? What does that mean
[veneer](https://www.keil.com/support/man/docs/armlink/armlink_pge1406301797482.htm)
[linker relacation on rv5](https://www.sifive.com/blog/all-aboard-part-3-linker-relaxation-in-riscv-toolchain)


[mold design notes](https://github.com/rui314/mold/blob/main/docs/design.md) very interesting. performance tricks, history of linker features
[The teensy files](https://www.muppetlabs.com/~breadbox/software/tiny/) - writing elf by hand
[On ELF, Part 2](https://kestrelcomputer.github.io/kestrel/2018/02/01/on-elf-2) - a ctrique of elf for being too complex compared to previous formats and for little gain. Counterpoints https://news.ycombinator.com/item?id=29660319
[Assembler and loaders - David Salomon](https://www.davidsalomon.name/assem.advertis/AssemAd.html)

<https://learnxinyminutes.com/docs/ru-ru/linker-ru/>

https://github.com/AbsInt/CompCert/blob/d194e47a7d494944385ff61c194693f8a67787cb/common/Linking.v compcert linking file
This file follows "approach A" from the paper
       "Lightweight Verification of Separate Compilation"
    by Kang, Kim, Hur, Dreyer and Vafeiadis, POPL 2016. 
<https://twitter.com/codydroux/status/1456029745175539721?s=20> Cody tweeting about it


 APE - Actually portable executable, Cosmopolitan library
 
<http://hackercurriculum.wikidot.com/elf>
<https://bitlackeys.org/#research>
<https://github.com/elfmaster>
<https://www.amazon.com/Learning-Binary-Analysis-elfmaster-ONeill-ebook/dp/B01891X7V0>

https://semantic-domain.blogspot.com/2012/11/in-this-post-ill-show-how-to-turn.html?m=1 geometry of interaction stuff. Neel Krinshnasawmi


Dwarf - it's like complicated. But there is a lot in there.


addr2line and other binutils
libdwarf. dwarfdump


https://twitter.com/stephenrkell/status/1448973963741339650?s=20
https://www.humprog.org/~stephen//blog-all.html - lots of interesting stuff on linkers, elf, other
https://github.com/stephenrkell/donald/ - his small linker. Uses ocaml?
https://github.com/rems-project/linksem - generates ocaml?

ld_preload hacking http://kev.pulo.com.au/publications/#lca2009_ld_preload
http://jvns.ca/blog/2014/11/27/ld-preload-is-super-fun-and-easy/
https://rafalcieslak.wordpress.com/2013/04/02/dynamic-linker-tricks-using-ld_preload-to-cheat-inject-features-and-investigate-programs/
Hmm. So one thing you can do is mock out functions for testing. That's nice



https://www.cl.cam.ac.uk/~pes20/rems/papers/oopsla-elf-linking-2016.pdf


https://web.archive.org/web/20190421205537/http://www.cs.virginia.edu/~dww4s/articles/ld_linux.html referenced guide on how to write dynamic linker

ryan oneill elfmaster
silvio text segement padding
SCOP padding secure cide oartitioning http://bitlackeys.org/papers/pocorgtfo20.pdf
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

https://github.com/andrewhalle/byo-linker https://www.reddit.com/r/rust/comments/mdtsk5/build_your_own_linker/

https://www.toolchains.net/
 - the author of gold, Ian Lance Taylor's 20 part Linker posts
https://lwn.net/Articles/276782/
V good

Symbols - Types and values?
Relocations - Bits of code that runs in general? Kind of bytecode?

Executable config files -  dhall. Others. Kaitai has executable aspects. if then else, others.

Functional models of linking

type fixups/relocs = Mov | Add | ?

{
    relocs: fixups
    symbols: {name : string ; typ : typ;  value : value}list
    contents: { section : name; contents : string }
}

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

https://ftp.gnu.org/old-gnu/Manuals/ld-2.9.1/html_chapter/ld_3.html (manual)
https://home.cs.colorado.edu/~main/cs1300/doc/gnu/ld_3.html

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
