SMTPP - A pre-processor for SMTlib2

Smtlib2 is the standardized query and logical language for SMT solvers. It is supposed to be an automatically generated representation, but I actually rather like it even written manually. It has a lisp-y prenex flavor.
It does however not have the full set of features

The interesting angle here is that we can start with raw smtlib2 and work backwards, slowly adding more sugar on top of it. Because of this approach, the full spectrum of stmlib2 constructs will be available and never obscured.

- Use programmatic bindings
- Use an already existing lisp macro system
- Roll my own
- What about Rosette?
- What about Why3 and Boogie?




There is a question if it makes sense to allow user defined macros written in the lisp-like syntax itself. It probably does, but that increases the scope of this project to building an entire language.


Parsing options:
- Using Sexplib, which is a standardized s-expression parsing library in Ocaml gets us a lot of distance for free. It is not smtlib2 compliant however, particularly in regards to quoting literals. Down the line, if this project grows we'd need to fix this. Perhaps we can have kludges patching this up.
- Dolmen & Smtlib cruanes - The projects can not parse things that are not compliant smtlib2. It is both a positive and a negative that the representation they produce is more structured thn just lists of atoms.

What kinds of things might we want?
- A programmatic looking syntax for weakest precondition
- Expansion to horn clauses.
- Type inference (hard as a macro)
- Bounded quantification that can be expanded
- Bounded unrolling / recursion. 
- Defunctionalization


Reusing lisp
(define spec (read (open-input-string "(foo bar)")))
We can then pattern match through it to find `define-macro` definitions.
And then there are usable definable macros. If I want to do so in ocaml I'll have a gimped bad lisp.
We need to write the traversing macro pass, but it shouldn't be too hard?
Use biwa scheme
Need some funky eval magic.



- Using ocaml - upside javascript story is better. Better compiling to binary. Doesn't need full scheme runtime to work. I'm more familiar with it. More palatable to vibes. I'd have to write
- using scheme / CL. user defined macros. just kind of feels right. Actually parse |#123| closer to correctly.

