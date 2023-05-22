title: Compiling Micropatch program fragments with gcc



In the context of the VIBES project, we have been building a compiler that is supposed to take high level code (C-like. It's funny how context dependent what "high level" means) and compiles it to assembly that can be patched in place 

1. This is the dual problem to inline assembly. Inline assembly is inserting little chunks of assembly into some bulk C code. 


It is in general a confusing problem to consider how to work with program fragments / open programs. What I mean by "fragment", "open", or "program" is vague and you may consider your environement of choice. 
Open lambda terms for example are lambda terms that have some variables unbound. The trick is in some manner or another have a notion of context or environment that refers to the variables. These dealings are subtle.

Another place where "open programs" may be considered is that of linking and seperate compilation.


If I take the code `x = y + 4;` and put it in a C file and call `gcc`, it has no idea what to do with that.

1. Full function compiling
2. Full state saving and then a function call
3. 

The relationship of hgh level code and low level code is intentionally nebulous because we want to allow compilr writers the freedom to achieve optimizations. In olden times, perhaps each chunk of C would translate quite straightforwardly to a chunk of assembly, but this is not guaranteed.

There are some things that must happen however.
It is at least unusual for the program to not obey the application binary interface (ABI), in particular I'm referring to the function calling conventions. Inlining can perhaps be seen as breaking the ABI.


1. `-O0` or `-Og` makes it better
2. Observable effects have to happen, like printing. Although honestly, I'm not going to be that surprised if my prints occur out of order because of some buffering issue.

A whole separate issue is finding space aka code caves in which to place code. It is often the case that micropatching is attempting to add code where there was none before.

1. Find some code to blast
2. Recompile or optimize existing code.
3. 
