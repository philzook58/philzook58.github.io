---
author: philzook58
comments: true
date: 2015-09-11 19:06:44+00:00
layout: post
link: https://www.philipzucker.com/random-potentials-and-qft-i/
slug: random-potentials-and-qft-i
title: Random Potentials and QFT I
wordpress_id: 154
---

There is a remarkable mathematical similarity between systems with random potentials and interacting quantum systems (QFT). I think that systems with random potentials are conceptually more straightforward.

The problem often is that you want to take the average value with respect to the distribution of possible potentials. The choice where you place this averaging (integration with respect to the probability distribution) and you can make smart approximations by placing this averaging where it shouldn't go.

Let us suppose we have a system with $latex H=H_0+V$ where H is an ordinary hamiltonian for a single particle and V is a random non time varying (for simplicity) potential background.

Solving the system with a given instance of V is no big deal. Put it in a computer. It's doable basically.

The trouble is averaging over all the V.

The mother of all questions in quantum mechanics (or mechanics in general) is how to time evolve a system.

The hiccup we run into is the simple fact that

$latex \overline{e^{-iHt}} \ne e^{-i\bar{H}t}$

Try expanding the exponentials to see.

$latex 1-i \overline{H}t-\overline{HH}t^2/2! +..\ne 1-i\overline{H}t-\bar{H}\bar{H}t^2/2! + ..$

The problem starts with that second term. On the left side we have the correlations of V. On the right side we never have any correlations.

What are we to do? The right side is easily computed. The average value of V is the only thing that shows up (and it would probably be a reasonable convention to set that equal to 0 and put any bias it has into $latex H_0$). The left side is a hairy mess. Naively, we would have to solve the parametized by V eigenvalue problem in closed form, then average that answer with respect to to distribution of V, basically an impossible task.

So what are we to do?

Well, what we can do is start working on moments. Then we can do better and better.

Even if your initial $latex \psi $ is set, after any evolution $latex \psi $ becomes a random variable inheriting it's randomness from the randomness of V. That means we can ask about its average values (a bad idea or at least you should know what you're asking. The phase of wavefunctions is a fragile and sometimes irrelevant thing, when you average over it you may get 0. Again the classic misconception that the summed average object has to be the same  as characteristic example of the object. The sum of 1 and -1 is 0, and 0 is neither 1 nor is it -1. Pedantic and yet obtuse? You're welcome.).

Sooooo. We can form $latex \psi \psi $ and evolve that.

$latex (e^{-iHt}\otimes e^{-iHt})( \psi\otimes\psi) $

I assume you can totally see where I'm going with this. Because I see it only hazily. But I know there is something here.

How does this connect to QFT?


