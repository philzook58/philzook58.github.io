---
author: philzook58
comments: true
date: 2016-08-30 01:32:08+00:00
layout: post
link: https://www.philipzucker.com/?p=498
published: false
slug: Some Physics and Haskell
title: Some Physics and Haskell
wordpress_id: 498
---

The random walk using applicatives

step = [(.5, \n->n+1),(.5, \n->n-1) ]

initial = [(1.,0)]

data Probability [( Float,a)]

instance Functor

instance Applicative Probability

solution = iterate (<*> step) initial

The Legendre Transform

First we define how to invert a function

f :: x->y

inversewithguess f initguess = \y ->

and derivatives
