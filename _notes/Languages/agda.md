---
layout: post
title: Agda
---


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

[The hott game](https://thehottgameguide.readthedocs.io/en/latest/index.html)
[Cubical Agda: a cold Introduction](https://nextjournal.com/agdacubicold/intro)
