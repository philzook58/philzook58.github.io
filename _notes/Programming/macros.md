---
title: Macros
---

Syntax vs datum.
Syntax usually needs source locations tagged for good error reporting at minimum. String-> String or unannotated Sexp->Sexp are not going to be able to 

CPP macros are string to string. Preprocessor style. They do annotate original source locations though.


[bindings as sets of scopes(https://www.cs.utah.edu/plt/scope-sets/) ["Let's Build a Hygienic Macro Expander" by Matthew Flatt](https://www.youtube.com/watch?v=Or_yKiI3Ha4&feature=emb_title&ab_channel=StrangeLoopConference)
syntax objects 

Hmm. macros are close to term rewriting. Quoting is a way of talking about syntax and meaning... Hmm.
egglog macros expander if hygienic needs this stuff...
We often want to switch between term and semantics views. Stepping out of the 
binding table.
scope vs context
a set of scopes is perhaps like an eclass of scopes
metatheoryjl possibly had thoughts on this. generatedfunctions etc
https://pl.ewi.tudelft.nl/research/projects/scope-graphs/ scope graphs a theory of name rtesolution

https://github.blog/2021-12-09-introducing-stack-graphs/ https://docs.rs/stack-graphs/0.10.1/stack_graphs/
Stack graphs at github for resoling references.
This is an interesting dataflow/datalog feeling problem actually
He mentions that dataflow is intertwined
https://www.youtube.com/watch?v=l2R1PTGcwrE&ab_channel=StrangeLoopConference incrmenetal zero-config code nave
partial path concat... proof? groupoid?
tree sitter has patterns and rules and now graph construction?
This does

[Macros in Lean4](https://www.youtube.com/watch?v=n1Pd0GeHsAY&ab_channel=Racket)

Macros like rust. Languages that aren't uniform like lisp 

Honu 

[paper describing different generative programming systems]
["micros"](https://twitter.com/ShriramKMurthi/status/1507398991033606189?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)

- [Hygienic Macros](https://en.wikipedia.org/wiki/Hygienic_macro)
- [Beautiful Racket explainer](https://beautifulracket.com/explainer/hygiene.html)
- [Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages](https://arxiv.org/abs/2001.10490) [video](https://www.youtube.com/watch?v=34jZTv0Gla8&ab_channel=IJCAR-FSCD2020)
- Fellison course hisotry of programming languages [hygienic](http://mballantyne.net/hopl-hygiene.pdf) [regular macros](https://felleisen.org/matthias/7480-s21/4.pdf)
- Let over lambda
- [reddit macro links](https://www.reddit.com/r/scheme/comments/3chowf/collection_of_links_about_scheme_macros/)
- [fear of macros](https://www.greghendershott.com/fear-of-macros/)
- [advanced scheme techniques](http://people.csail.mit.edu/jhbrown/scheme/macroslides04.pdf)
- [petrofsky  An Advanced Syntax-Rules Primer for the Mildly Insane](http://www.eighty-twenty.org/~tonyg/Darcs/macromod/doc/reference/petrofsky/petrofsky-advanced-syntax-rules-primer-for-the-mildly-insane.txt)
- [scheme bibiliography](https://github.com/schemedoc/bibliography/blob/master/page3.md)


[A Third Perspective on Hygiene](https://blog.brownplt.org/2017/06/20/scope-inference-hygiene.html)


See also: Partial Evaluation.

Raw macros work on syntax. Hygienic macros pay more attention to scope. They attach scope identification data to the syntax tree.

dynamic scope and lexical scope
Without macros, the scope of binding forms is straightoforward. With macros, 

sets of scopes - Flatt. Does this lattice maybe have something 

Syntax objects in racket - More than just s-expressions. Annotated with source locations but also scope.

syntax-rules
Syntax-case


What about gensymming?

## Examples


