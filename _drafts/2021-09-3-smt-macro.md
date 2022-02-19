
Macros for SMTLib: MicroDafny




SMTPP - A pre-processor for SMTlib2

Smtlib2 is the standardized query and logical language for SMT solvers. It has a lisp-y prenex flavor. Here's an example from <https://www.philipzucker.com/z3-rise4fun/>

```lisp
(declare-fun f (Int) Int)
(declare-fun a () Int) ; a is a constant
(declare-const b Int) ; syntax sugar for (declare-fun b () Int)
(assert (> a 20))
(assert (> b a))
(assert (= (f 10) 1))
(check-sat)
(get-model)
```

It is supposed to be an automatically generated representation, but I actually rather like it even written manually. It does however have some rough edges. The lisp-y character naturally brings one to ask, can we smooth those edges using macros? Lisps have a natural way of reifying their own syntax as a data structure and processing it. You can use this to simple synonyms, make constructs that reduce boilerplate, or make new control flow operations. This can easily be integrated with many other tools if we write the preprocessor as a standalone binary that just outputs the expanded smtlib. Then you can just pipe the output of a tool into the preprocessor before piping it into your smt solver of choice.


As an example of this idea, I wrote a very minimal version of a dafny-esque language. This is still missing a lot of features of dafny (like all the hard parts)

Many things you might think have to be macros can actually be written using other constructos of smtlib, in particular the `define-fun` capability. My understanding is that smt solvers treat these essentially as macros anyhow. Other things that could be interesting as smtlib macros
- less verbose type annotation requirements
- bitvector mode to use operators like `+` instead of `bvadd`
- a `calc` macro
- structured proofs. deftheorem. define-axiom. define-schema. + calc mode possibly. This is simiilar to hilbert style proofs.
- Auto defunctionalization / Combinatorization to support higher order functions (use smtlib3 syntax? <http://smtlib.cs.uiowa.edu/version3.shtml> )
- A refinement type checker
- symbolic differentiation operator
- Presolve calls to other solvers
- Collecting up extra facts to assert (like interval constraints on every use of `cosine` etc)
- Macro expanded bounded quantification
- Idea: Analgous to intervals or complex numbers, do extended reals <https://en.wikipedia.org/wiki/Extended_real_number_line> Using Reals + ADTs. Interesting because algerbaic operations become partial. Do as smt macro? P
- Partial functions. If I want to use z3 systematically with partial functions what do I do. I guess Maybe values. At which point, perhaps monadic sugar becomes desirable `let*`. I guess I should look at other places macro sugar was nice.  Automatic deriving.  Alternative: Collect up "VC" somehow. (value, is_junk). Monadic discipline is still nice. It's kind of like Either R R, where Left means value good, Right means it is junk. [(value, is_junk)] is interesting. WWell, is there a point? This should be an if then else chain, with a final.
 junk value.
- list comprehensions?
- Auto derive "gassed" versions of functions
- Datalog - rules2chc already is kind of like this.
- egglog using z3 triggers


The interesting angle here is that we can start with raw smtlib2 and work backwards, slowly adding more sugar on top of it. Because of this approach, the full spectrum of stmlib2 constructs will be available and never obscured.

- Use programmatic bindings
- Use an already existing lisp macro system
- Roll my own
- What about Rosette?
- What about Why3 and Boogie?

The advantage of this approach is that it is very thin layer. Other smtlib++ languages like Boogie, Why3, etc are much heavier and have their own syntax. They are not nearly as universally accepted also. Smtlib is a langua franca.



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
- Something TLA+ like. Verify invariants
- Ivy?


Reusing lisp
(define spec (read (open-input-string "(foo bar)")))
We can then pattern match through it to find `define-macro` definitions.
And then there are usable definable macros. If I want to do so in ocaml I'll have a gimped bad lisp.
We need to write the traversing macro pass, but it shouldn't be too hard?
Use biwa scheme
Need some funky eval magic.



- Using ocaml - upside javascript story is better. Better compiling to binary. Doesn't need full scheme runtime to work. I'm more familiar with it. More palatable to vibes. I'd have to write
- using scheme / CL. user defined macros. just kind of feels right. Actually parse |#123| closer to correctly.


On the difference between sets and lets:
Set scopes to the end of time, let has a scope when it ends. That's about it. This is perhaps why it is so easy to use `let` to simulate `set` in the weakest precondition formulation. `let` has connotation of peristence, expressions. `set` has connotations of mutation and destruction.


Ghost code and noninterference. Metaocaml and interference.



You know I'm still unhygienic because of smtlib allows includes

Houdini huh.



