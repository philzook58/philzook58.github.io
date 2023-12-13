---
author: philzook58
comments: true
date: 2018-03-27 18:24:16+00:00
layout: post
link: https://www.philipzucker.com/?p=1026
published: false
slug: Haskell FFI
title: Haskell FFI
wordpress_id: 1026
---

The landscape of FFI is rather confusing

Basically you can do it all manually.

hsc2hs is a part of ghc

c2hs  - does more for you. Auto makes a lot of foregin C-type info. Enums, structs and stuff.



http://blog.ezyang.com/2010/06/the-haskell-preprocessor-hierarchy/

inline-c is useful and easy enough if you are calling functions that take standard types or Arrays of them.

inline-c is sort of meant for run and gun type scenarios.



Example using inline-c to bind to the NAG library (a C numerical library)

https://github.com/fpco/inline-c-nag



Basically, The easiest thing is to use Vecs and use the C style where you pass in a pointer for the modified variablle.

You can make muttable Vecs easily on the haskell side and then hand them in using C-inline.


