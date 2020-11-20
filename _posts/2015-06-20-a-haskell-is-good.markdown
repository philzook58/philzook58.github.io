---
author: philzook58
comments: true
date: 2015-06-20 21:17:12+00:00
layout: post
link: https://www.philipzucker.com/a-haskell-is-good/
slug: a-haskell-is-good
title: A Haskell is Good?
wordpress_id: 23
tags:
- functional programming
---

I am a beginner in functional programming.

Over the past couple weeks, I've been revisiting Haskell. As I've brought it up in conversation, I've been asked a couple times what to define what functional programming even is when I've brought it up. Honestly, I do not yet know how to express it in words. But I think I know how it feels. A very gooey statement to make about a typically precise field.

I've been asked if passing in callback functions as arguments is functional programming. I think it is an aspect but that it doesn't gets to the heart of the matter.

A couple things without poisoning my impression by reading the definition from wikipedia:



	
  * Functions are like, really important

	
  * Ordinary programs are like a very explicit list of instructions for the machine. Functional programming doesn't feel like that.

	
  * If you're mind wants to explode, maybe it's functional programming

	
  * Seems Mathy. In that abstract proofy math kind of way. You build programs kind of like how you'd build a proof. Take axioms and tie them together with minimal lemmas and theorems into more complex programs. Also, the goals are mathy. You try to program things as general as possible, a task aided by focussing on the function.

	
  * Recursion is not required but it's got the flavor.

	
  * While most programming languages have functional bits and some functional paradigms in them now, the only one's that really have the taste are the pure ones, Lisp, Scheme, Haskell, etc. The languages that have the alternatives to the functional style basically end up programming kind of the same.


Stuff I've heard but don't really get:

	
  * Lazy Evaluation: Stuff doesn't evaluate until it needs to and then it only evaluates as much as it needs. If you've got a thing that builds a list of 1000, but then you only ask for the first 3 elements, it'll only build the list when you ask for those elements and then also only those three. I think that's what's going down.

	
  * The type system is F'ed up.

	
  * How I could ever conceive of the weirdly clever things they do.

	
  * That functional programming is actually good. The boiler plate of wiring thing to thing is 99% of what programs are, and the algorithm is a minimal component. I am disbelieving but hopeful that functional programming could alleviate that.


Updates as I understand more.
