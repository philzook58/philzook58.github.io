---
date: 2022-04-22
layout: post
title: "The Almighty DWARF: A Trojan Horse for Program Analysis, Verification, and Recompilation"
tags: binary analysis dwarf
description: DWARF exists, is ubiquitous, and is powerful. It seems like a small step to package more information into it, opening big opportunities for cool PL applications.
---

Table of Contents:
- [High and Low](#high-and-low)
  - [Programs Are Delusions](#programs-are-delusions)
  - [Debugging and DWARF](#debugging-and-dwarf)
  - [Communicating with Decompilers](#communicating-with-decompilers)
  - [VIBES Config files and DWARF](#vibes-config-files-and-dwarf)
- [High-Low Relational Program Analysis](#high-low-relational-program-analysis)
- [Extensions to DWARF](#extensions-to-dwarf)
  - [Program Analyses](#program-analyses)
  - [Verification conditions](#verification-conditions)
  - [DWARF Imp](#dwarf-imp)
  - [DWARF JSON](#dwarf-json)
- [Bits and Bobbles](#bits-and-bobbles)

# High and Low

At work we've been been tinkering away on [VIBES](https://github.com/draperlaboratory/VIBES) for over a year at this point. VIBES is a part of the [DARPA Assured Micropatching](https://www.darpa.mil/program/assured-micropatching) (AMP) program. We've been building a neat [constraint](https://www.minizinc.org/doc-2.6.2/en/index.html) based patching [compiler](https://unison-code.github.io/) that deserves many blog posts of it's own.

Something that has driven me insane with despair during this program is how to talk about the connection between high and low level code in a way precise enough that we can correctly patch in code.

## Programs Are Delusions

In a naive picture of what a compiler does, it looks at programs chunk by chunk and outputs some assembly tha corresponds in a reasonable way to that code. Maybe `foo` goes in `R0`, `bar` goes on the stack, etc. This assignment `:=` becomes a `mov` here, this `+` expression becomes an `add` assembly instruction there.

This is a completely false picture and banish it from your mind.

High level programs are _delusions_. Optimizing compilers make surprisingly few guarantees about what what correspondences must exist between high and low level code. They may inline code, reorder assignments, rematerialize and copy variables, fuse loops. One could say the _goal_ of an optimizing compiler is to mangle code as much as it can to eke out performance. It is a perfectly _antagonistic_ situation if you want to keep good correspondences between high and low. Optimizing compiler writers want to make my life hell and I take it personally.

The main thing compilers try to guarantee is that the high and low level code should have the same [observable behavior](https://en.cppreference.com/w/cpp/language/as_if). This amounts to some memory access, IO and some function calls must actually happen. The entire rest of your code, all those clever loops and bit tricks and such, are essentially functional specs. They are hints at best of what the compiler should output.

This topic is related to that of [concurrency](https://www.philipzucker.com/notes/CS/Concurrency/). In concurrent code, there is a secret window by which other processes see things that were never meant to be seen. At minimum, intermediate states of shared variables become observable. Reads and writes to these variables should no longer be reordered or inlined or done in pieces. In a sense everything done to these variables becomes observable behavior. The was a crisis of sorts when people started realizing that the mechanisms they vaguely felt made sense, didn't actually make sense in concurrent situations. Straightening this out was quite a lot of work (See memory models).

I can't deny however, that despite the compiler only guaranteeing correspondence of high and low at specific points in limited ways, it just so happens that we can usually intuitively see that this region of assembly vaguely corresponds to this region of high level code, and that this high level variable here is stored in that low level variable there. So how is one supposed to proceed when there is clearly an intuitive correspondence that you needmake  precise enough to post hoc patch in code? How do you even describe this correspondence? What is the _schema_ of this correspondence?

Now, it just so happens that our task is not to post hoc patch the original source, but instead decompiled source, output say by Ghidra or Binary Ninja. This task is perhaps a bit easier than the optimizing compiler case. A goal of a decompiler is to keep the correspondence understandable.

## Debugging and DWARF

I've heard it described that one way to think about the concurrency problem is to think of concurrent code as having sort of a debugger level view of the assembly. Debugging is actually a very interesting thing to examine for this problem. Debugging info tries to maintain the connection between high and low data in such away as to be understandable enough to a human operator.

DWARF is a standardized ubiquitous debugging format. It is expressive and open ended. It structured and tree like, kind of like XML or JSON (variables are scoped in subprograms which are scope in compilation units for example). The nodes of the tree are called DIEs (DWARF information entries) and they contain DWARF attributes as children.

DWARF has built in ways to talk about
- Function names, stack frames
- Variables and their locations. Locations can be described in both simple and complex formats.
- Type information
- Source line and column numbers corresponding to addresses (the line table)

I highly invite you to download and skim the table of contents and introduction of the [DWARF standard](https://dwarfstd.org/doc/DWARF5.pdf) and the very good short article [Introduction to the DWARF Debugging Format](https://dwarfstd.org/doc/Debugging%20using%20DWARF-2012.pdf).

As an example of what's in there, take a look at this simple C program. You can see dwarf data by compiling a program with `-g` and using `readelf`. There's a lot to wade through but try grepping for `foo` `x` `y` `z` and see if you can make sense of what you see.

```C
int foo(int x, int y){
    int z = x * y + 42;
    return z;
}
```

```sh
gcc -g -c foo.c
readelf --debug-dump a.out | grep -C 10 foo
```

## Communicating with Decompilers

A difficulty we've faced on the AMP program is how to communicate with between tools that decompile and tools that compile patches. There are `N` tools that decompile and `M` tools that patch. Each one has it's own interfaces and it is outside both the desires and probably people-hours to figure out how to build the `N*M` different interface combinations. I don't want to impose the burden of writing our VIBES config files on others, and also I want the freedom to change the format as I understand more without making people want to kill me.

DWARF has some aspects that make it seem like a partial solution to this problem:

- It is standardized.
- It is language universal. Decompiler output is not really valid C or anything, so this is good.
- It gets in the ballpack of expressing the information we need.
- There is utility in exporting it anyway for other users so they can see their annotated decompilation in gdb. I take that people have made export plugins for [IDA](https://github.com/ALSchwalm/dwarfexport), [Ghidra](https://github.com/cesena/ghidra2dwarf) and [Binary Ninja](https://github.com/immunant/dwarf-writer) as evidence for this. These plugins are all close but no cigar for out purposes AFAIK.

The downsides of DWARF:

- DWARF is not meant for last word precision. It is meant to get human debugging in the ballpark.
- The concepts of high low correspondence is not sufficiently refined even in DWARF.
- DWARF
- DWARF does not express some information we still need like verification conditions. See extension suggestions below.
- The binary format is a pain in the butt for no reason for us. I said DWARF is in essence something like a JSON. I'd suggest we literally export a JSONified DWARF.

## VIBES Config files and DWARF

VIBES works on JSON config files that describe the patches. We've sort of grown this config file as the need has arised to get at th information we need in the most direct way possible. It has not been desirable to spend months pondering what is the most general way to describe the relationship between high and low. In fact, it is my belief that this is not how problems are solved anyway. You solve problems by working at it and seeing what you learn.

Here's an example config json for a [simple patch](https://github.com/draperlaboratory/VIBES/tree/main/resources/exes/arm-null-check).

- A comparative SMTLIB specification for correct patch behavior
- `patch-point` describes the address at which to hijack control flow into our code
- `patch-size` implicitly describe both dead code (the region between `patch-point` and `patch-point + patch-size`) and also where to fallthrough from out patch code.
- `patch-vars` describes what variables can be read from where in the `at-entry` field and where they need to be in the `at-exit` field.

```json
{
  "max-tries": 10,
  "wp-params": {
    "func": "patch_fun",
    "postcond": "(assert
  (implies
    (and (= init_mem_orig init_mem_mod)
         (bvugt init_R0_orig init_SP_orig)
         (= init_R0_orig init_R0_mod))
    (ite (= init_R0_mod #x00000000)
      (= R0_mod #xffffffff)
      (and (= R0_mod R0_orig)
           (= R0_mod
              (concat
                (select init_mem_mod (bvadd init_R0_mod #x00000003))
                (select init_mem_mod (bvadd init_R0_mod #x00000002))
                (select init_mem_mod (bvadd init_R0_mod #x00000001))
                (select init_mem_mod init_R0_mod)))))))"
  },
  "patches": [
    {"patch-name": "null-check",
     "patch-code": "int *x, retval;
                    retval = x ? *x : -1;",
     "patch-point": "0x10468",
     "patch-size": 36,
     "patch-vars": [
       {"name": "x",
        "at-entry": "R0",
        "at-exit": "R0"
       }
     ],
     "extra-constraints": "
       % exclude callee-save registers from the solution
       constraint exclude_reg('R4');
       constraint exclude_reg('R5');
       constraint exclude_reg('R6');
       constraint exclude_reg('R7');
       constraint exclude_reg('R8');
       constraint exclude_reg('R9');
       constraint exclude_reg('R10');
       constraint exclude_reg('R11');
       constraint exclude_reg('SP');
     "
    }
  ]
}
```


I think that we can use already existent DWARF DIEs to approximate or improve these fields.

- `DW_TAG_variable` `DW_TAG_formal_parameter` are two DIEs that describe variables. They have attributes. This is similar to our `patch-vars` field. It is both more and less expressive
- `DW_TAG_label` seems like a reasonable choice to encode both the patch entry and patch exit points. It is very possibly for a patch to have multiple exits (and maybe multiple entries?) so it would be nice for a human to be able to annotate these points in the high level code which we could then read off. 
- `DW_TAG_lexical_block` gives us a way to talk about regions in the high code. We can use this to describe what code we are replacing, i.e. deadcode.
- DWARF type descriptors. We don't yet have the ability to import struct definitions. Now actually, BAP, our underlying framework can already import C headers and decompilers also already export those. So maybe that is a better way to go. But DWARF is an all in one stop for info.


# High-Low Relational Program Analysis

VIBES is a compiler, but an unusual one. Hence we need all traditional program analyses, but with a twist.

Traditional compilers subsequently lower high level code to low, doing analysis and transformations at each stage.
In a certain sense, one could see our task as a vertical slicing of this approach. Suppose a compiler did all stages of analysis and assignment on a subset of the basic blocks in a function. Then what information would the compiler need to compile the remaining blocks such that they remain consistent with the register choices and layout choices already made in the other blocks?

We don't have the whole function available to us. We only have what information the decompilers can export to us. I would suggest that we need any traditional compiler dataflow analysis you can give us at the boundaires of the patch. We can the propagate this information inside of the patch as we see fit.

In the traditional compiler approach, you can consider each IR in isolation for analysis. I suggest this is no longer acceptable and that every analysis should proceed in a deeply high/low relational way, never separating the two. To make a database analogy, I do not think the relational join of a hypothetical `(high_label,low_address)` table with the in isolation produced analyses (liveness,availability,reaching definitions, available expressions) is sufficient to express the full range of possibilities. That schema is wrong. Projecting the information in that way is lossy.

"The" relationship between high variables and low variables is at least multivalued, partial, and address dependent. I suspect that even the very language I am using here leads to false thinking. I don't even think there _is_ a single "correspondence" relationship between high and low variables but instead many.

What about "the" relationship addresses and high level program points? This is also very scattered by the rearrangement of statements of the high level code. This relationship is also partial, multivalued, and does not transfer nicely along the control flow of either.

Here are two tables that might make sense and translate to useful notions for us. 
An available high/low relation says that at this high program position, the high variable can be read at this low level position from this low level location.

Live means that high variables writes at this high label need to be written to these (possibly multiple) low level locations at these low level program addresses.

The two tables tell us how to read incoming variables at patch entry, and what we need to have written at patch exit.

```
.decl live(high_label, high_var, low_address, low_var)
.decl available(high_label, high_var, low_address, low_var)
```

Reaching definitions analysis seems useful in that if a definition in the code we're overwriting reaches the exit points of our patch, we need to replace it's value. If we aren't overwriting a reaching definition, we need to instead _preserve_ values that occur in both available at the beginning of the patch and live at the end of the patch, possibly by spilling.

Basically, we could probably use any analysis you can hand us profitably.

# Extensions to DWARF

## Program Analyses

How could program anlysis like the above be encoded into DWARF? I would claim it's actually pretty close.
Currently DWARF is capable of expressing some kind of location aware relationship between variables in high an low level code.
An extra DWARF flag attribute `DW_AT_live` and `DW_AT_available` in the `DW_TAG_variable` DIE may be sufficient to extend DWARF expressivity to these more precise notions.

It would also be helpful to have flags `DW_AT_precise` to know what information is absolutely trusted and what may be somewhat approximate.

## Verification conditions

DWARF expressions are [shockingly expressive](https://www.youtube.com/watch?v=nLH7ytOTYto). They are described via Turing complete stack machine programs. So this is already a good base to work from.

It is completely possible to interpret common simple DWARF expressions into SMTLIB. This means that it is possible to describe verification asserts and assumes in DWARF. I would suggest two new DIEs `DW_TAG_assert` and `DW_TAG_assume`. I think this is generally pretty interesting.

It would allow for zero cost assert statements in high level languages that are preserved for any subsequent verification you might wish to do. Binaries become "spec-carrying code". Typically, languages insert dynamics checks into code for asserts, and the code is recompiled if you want to turn these off for production. However, with DWARF asserts, if you want to run the binary dynamically in assertion mode, you could run it in GDB, where it places interrupts at any assertion point.

These assert statements could be used for bounds checks, control flow integrity checks, etc, all at no runtime cost when you turn them off.

They would be language agnostic.

Now for our particular use case, we'd also like some extensions to DWARF expressions. We desire the ability to talk about the original and modified program, because our tool CBAT does ocmparative verification. Comparativie verification is nice because it eases the burden of specification on the user and in principle is easier to verify too. All the user has to say is under what conditions should the program do what it used to do, and when should it do something different, instead of specifying what the program does in absolute terms.

We'd desire DWARF expression modifiers `DW_OP_orig` and `DW_OP_mod` to differentiate between R0 in the original and modified program for example.

## DWARF Imp

Another suggestion that I think could aid verification and patching burden is to increase the abilities of DWARF to describe the imperative skeleton of code.
As I mentioned, backing out high code semantic information from the line table is nontrivial work. I don't see why you would store this information in this way if you need it.

There are some language agnostic commonalities you see in many high level languages. These are sketched out in the pedagogocial languages IMP and WHILE you'll see in books and course notes.

A significant burden of binary verification is reconstructing high level control flow expections from the low code.

- `DW_TAG_assign`
- `DW_TAG_while`
- `DW_TAG_for`
- `DW_TAG_switch`
- `DW_TAG_if_then_else`

Now you could argue this is a lot of bloat. Are we not just replicating the entire program again?

No, this information is both more and less than the original code. This information will always be incomplete. A skeleton of some behavior of the original code.

On the other hand, the _relational_ characterization of high level constructs to their intended low level implementation exists _nowhere_ as it stands. It is perhaps kind of implicitly there in the line table but this syntax to semantics leap is basically impossible to make.

## DWARF JSON

DWARF is a pain to read and write in it's low level format. libdwarf is great, but difficult and confusing. A standard human readable format would be awesome. There are a number of projects for reading dwarf into YAML or JSON. There is a desire for this. They are fragmented, in languages du jour, and unmaintained.


# Bits and Bobbles

Thanks to Chris Casinghino, Cody Roux, JT Paasch, Ben Mourad, Ivan Gotovchits, Chloe Fortuna, AMP, and Sergey Bratus. Any ideas herein that are bad I claim as my own.

I'd suggest that somehow the decompiler tools need to enforce or guide people to put patches only in high and low level positions where patches can make sense. If you randomly pick a character or even AST node in high level source, odds are it is not a sufficiently self contained notion to talk about replacing it.

Patches may need to be expanded in size to contain more code than is desired, recompiling code that isn't going to be changed, just so that we can operate at positions where high low correspondences actually exist.
But today we're gonna talk about DWARF.

For more resources on DWARF, see my notes [here](https://www.philipzucker.com/notes/Programming/linkers/#Dwarf)

I have grown accustomed to the SSA style of making writes happen to a unique variable. This is not acceptable as we need to talk about the user facing code and the low level code.

A different mode of creating patches. Watching the patch being made. Edit sequences. Like operation transform of google docs or what have you.

Two projects which certainly have to tackle a concrete notion of the relation between high and low are Compcert and sel4.
<https://www.cs.cmu.edu/~15811/papers/compcert-journal.pdf> I should more deeply understand what is going on here, but I suspect it doesn't work for our use case. Bisimulation over observable behavior is a trap.

Look more into prior work on recompilation



