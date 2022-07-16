---
title: Macros
---

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


