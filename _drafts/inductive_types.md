
So last time I blasted in a definition of peano addition to knuckledragger as an axiom. This is fine, but probably not the best.

It is totally fine for fooling around to add new axioms to expediate getting to whatever meat you want to get to. I recall it being a revelation when I saw Cody do that in Coq, that I didn't need to start from inductive datatypes and build a whole world, one can just posit new axioms.

However, it is nice to have the option to instead use more controlled or opinionated interfaces to add axioms.

When you define an inductive datatype in Coq or lean, it says that the system has defined a couple of primitives and helpers for you.

Inductive datatypes by design allow for admitting induction principles.

Since Z3 has support for inductive data types, it seems nice to piggy back on this mechanism

A classic thing to do is create a conservative extension to a theory. This adds new constants and function symbols to the signature, but no new theorems involving only old constants are provable.
See the metamath book section 4.4 <https://us.metamath.org/downloads/metamath.pdf>
<https://en.wikipedia.org/wiki/Conservative_extension>
[FOM: Conservative Extension](https://cs.nyu.edu/pipermail/fom/1998-October/002306.html)

When you intermix inductive datatypes and first class functions things get dicey for some reason. There are certain positivity restrictions to keep things sound.
Mutually recursive datatypes is also a fiddly area.
<https://en.wikipedia.org/wiki/Induction-induction>
<https://en.wikipedia.org/wiki/Induction-recursion>
<https://proofassistants.stackexchange.com/questions/926/what-are-well-founded-inductive-types>

<http://adam.chlipala.net/papers/PhoasICFP08/> HOAS is fiddly
<https://cstheory.stackexchange.com/questions/22157/w-types-vs-inductive-types>
<https://mathoverflow.net/questions/402435/why-are-w-types-called-w> W types fit into this discussion somewhere <https://ncatlab.org/nlab/show/W-type>
