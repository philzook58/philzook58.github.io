---
author: philzook58
comments: true
date: 2018-03-06 20:12:17+00:00
layout: post
link: https://www.philipzucker.com/?p=1005
published: false
slug: Haskell Generics
title: Haskell Generics
wordpress_id: 1005
---

https://www.stackbuilders.com/tutorials/haskell/generics/

Generics are functor level programming.

You want to build up types using Functor composition, products and sums. :+: and :*:

The Const Functor and Identity Functor are important.

Many (all?) Algebraic data types can be converted to a stack of this form

V1 is a Void Functor. That's interesting

U2 is a Const Unit a basicallt



Less familiar are Rec0 and Par0



https://hackage.haskell.org/package/base-4.10.1.0/docs/GHC-Generics.html

You can inspect the Rep using :kind! in GHCi

The Rep is itself a functor


