---
layout: post
title: Agda / Idris
---

[Certainty by Construction Maguire book](https://sandymaguire.me/blog/certainty-by-construction/)

Stump Agda book

<https://twitter.com/agdakx/status/1577952310243872769?s=20&t=UJrepWvNkFpXFRNY8yoWDA> agda2hs blog post jasper

Martin Escardo
[Introduction to Univalent Foundations of Mathematics with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)

[agda wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php)

[Agda manual](https://agda.readthedocs.io/en/latest/)

[Programming Language Foundations in Agda](https://plfa.github.io/)

```
apt-get install agda agda-mode agda-stdlib
```

```bash
echo 'module hello-world where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

main : IO ⊤
main = putStrLn "Hello world!"

' > /tmp/hello-world.agda
cd /tmp # Why do I have to do this? Me dunno.
agda --compile /tmp/hello-world.agda
./hello-world
```

```bash
agda --help
```

[The hott game](https://thehottgameguide.readthedocs.io/en/latest/index.html)
[Cubical Agda: a cold Introduction](https://nextjournal.com/agdacubicold/intro)
<https://leanpub.com/certainty-by-construction> sandy maguire book

<https://dl.acm.org/doi/abs/10.1145/3437992.3439922>  Formalizing category theory in Agda

<https://link.springer.com/chapter/10.1007/978-3-030-33636-3_10>  
System F in Agda, for Fun and Profit

<https://yangzhixuan.github.io/pdf/free.pdf> Algebraic Effects Meet Hoare Logic in Cubical Agda - Kidney, Yang, Wu

<https://dl.acm.org/doi/abs/10.1145/3607861> Timely Computation Conal Elliot

<https://cris.vub.be/ws/portalfiles/portal/66013205/TyDeAbstract.pdf> Shallowly Embedding Type Theories as Presheaf Models in Agda

<https://arxiv.org/abs/2306.15375> Frex: dependently-typed algebraic simplification

<https://github.com/JacquesCarette/PureBaggery>

<https://github.com/pigworker/CS410-17> cs 410 mcbride

<https://github.com/jsiek/abstract-binding-trees> agda abstract bnding trees siek

## Well Typed Syntax

<https://dl.acm.org/doi/pdf/10.1145/3498715> Formal Metatheory of Second-Order Abstract Syntax

<https://arxiv.org/abs/1804.00119> Generic Description of Well-Scoped, Well-Typed Syntaxes Erdi

<https://link.springer.com/article/10.1007/s10817-011-9219-0>  2012 benton et al Strongly Typed Term Representations in Coq

 Altenkirch and Reus [1999] Monadic presentations of lambda terms using generalized inductive types <https://link.springer.com/chapter/10.1007/3-540-48168-0_32>

 Richard S. Bird and Ross Paterson. 1999. de Bruijn notation as a nested datatype

 Allais, Atkey, Chapman, McBride, and McKinna [2021] <https://www.cambridge.org/core/journals/journal-of-functional-programming/article/type-and-scopesafe-universe-of-syntaxes-with-binding-their-semantics-and-proofs/8A0865F34313BA65F4FE46D4522B4568>
<https://dl.acm.org/doi/10.1145/3236785> A type and scope safe universe of syntaxes with binding: their semantics and proofs

 <http://strictlypositive.org/ren-sub.pdf> 2005 mcbride Type-Preserving Renaming and Substitution

<https://www.youtube.com/watch?v=imz9UkdQBdI&ab_channel=LFCSSeminar> horsten Altenkirch: How to define type theories?

mcbride thinning and substitution <https://www.youtube.com/watch?v=ahwCXcYHkXQ&t=1853s&ab_channel=ConorMcBride>

<https://docs.idris-lang.org/en/latest/tutorial/interp.html> well typed interpeter example idris

<https://lean-lang.org/lean4/doc/examples/interp.lean.html> well typed interpreter lean

<https://richarde.dev/papers/2018/stitch/stitch.pdf> Stitch: The Sound Type-Indexed Type Checker (Functional Pearl) - eisenberg

<https://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html> An algerbaic approahc to typchecking and elaboration - bob atkey

<https://arxiv.org/abs/2310.13413> Scoped and Typed Staging by Evaluation . two level type theory embedded in agda allais. <https://gallais.github.io/publis.html> all sorts of great stuff

# Idris

Eh, they're similar enough. Wow. Idris. Takes me back

[Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/pdf/2104.00480.pdf)

<https://gallais.github.io/teaching> idris 2 course <https://gallais.github.io/pdf/splv23_gallais_lecture_notes.pdf>
<https://arxiv.org/abs/2310.13441> Seamless, Correct, and Generic Programming over Serialised Data

<https://github.com/stefan-hoeck/idris2-tutorial>

```bash
echo '--re
module Main

main : IO ()
main = putStrLn "Hello world"

x : Int
x = 94

foo : String
foo = "Sausage machine"

--bar : Char
--bar = 

quux : Bool
quux = False

data Tree = Leaf | Node Tree Bits8 Tree
sum : Tree -> Nat
sum t = case t of
    Leaf => 0
    Node l b r =>
        let m = sum l
            n = sum r
        in (m + cast b + n)

q : Nat
q = S Z
y = [1,2,3]

-- import Data.Vect
data Vect : Nat -> Type -> Type where
    VNil : Vect Z a
    VCons : a -> Vect n a -> Vect (S n) a
' > /tmp/test.idr
cd /tmp
idris2 -c  test.idr


```

<https://github.com/stefan-hoeck/aoc23/tree/main/src> advent of code 2023

```bash
echo "
--re idris2


main : IO ()
main = printLn 42

" > /tmp/test.idr
cd /tmp
idris2  -x main test.idr
```

Use pack? <https://github.com/stefan-hoeck/idris2-pack>

Zanzi
<https://zanzix.github.io/posts/bcc.html> Lambda Calculus And Bicartesian Closed Categories
<https://gist.github.com/zanzix>
Second Order Algebraic Theories <https://gist.github.com/zanzix/df5eb62079d4bc3a56306a1de4f276cd> "two theories"
kappa and zeta calculus <https://gist.github.com/zanzix/0e113d5aef1c7e0a985328fac35fa032>

Typed Syntax. Thinnings
telescope

Relative monads <https://stringdiagram.com/2023/05/28/relative-monads/>

Quantitative type theory
0 1 omega
algebraic paths
optics
open games

<https://github.com/Jademaster/TheCategoryMachine/tree/main>

<https://gist.github.com/Jademaster/755ec0d389c41e8a681f8bdd27be8e76>  Grothendieckconstruction.idr

<https://gist.github.com/Jademaster/df24f8d2640c066ddbe427e98547d35e> freesemiring.idr

<https://www.cis.upenn.edu/~sweirich/papers/yorgey-thesis.pdf> brent yorgey theis COMBINATORIAL SPECIES AND
LABELLED STRUCTURES

<https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html> phil freeman. Stack safe traversal via dissections
<https://github.com/PureFunctor/purescript-ssrs>

<https://github.com/adamgundry/type-inference/blob/master/src/Milner/Zipper.lhs> zipperized algorithm W <https://types.pl/@pigworker/111375156578265560> more n phd thesis

<https://www.researchgate.net/profile/Peter-Dybjer/publication/226035566_Inductive_families/links/0f317532159fcea814000000/Inductive-families.pdf> dybjer inductive families

<https://github.com/jfdm/velo-lang> <https://arxiv.org/abs/2301.12852> type theory as a language workbench
