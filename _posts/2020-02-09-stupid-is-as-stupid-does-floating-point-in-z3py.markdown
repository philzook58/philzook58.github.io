---
author: philzook58
comments: true
date: 2020-02-09 05:44:21+00:00
layout: post
link: https://www.philipzucker.com/stupid-is-as-stupid-does-floating-point-in-z3py/
slug: stupid-is-as-stupid-does-floating-point-in-z3py
title: 'Stupid is as Stupid Does: Floating Point in Z3Py'
wordpress_id: 2653
categories:
- Formal Methods
tags:
- python
- smt
- z3py
---




Floating points are nice and all. You can get pretty far pretending they are actually numbers. But they don't obey some mathematical properties that feel pretty obvious. A classic to glance through is "What Every Computer Scientist Should Know About Floating-Point Arithmetic" [https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html)







We can check some properties with z3py. Here are a couple simple properties that succeed for mathematical integers and reals, but fail for floating point 





[gist https://gist.github.com/philzook58/3632e1cd323171c69875c811c9b7a34c#file-numbery-py]





I recently saw on twitter a reference to a Sylvie Boldo paper [https://hal.archives-ouvertes.fr/hal-01148409/](https://hal.archives-ouvertes.fr/hal-01148409/) "Stupid is as Stupid Does: Taking the Square Root of the Square of a Floating-Point Number".








https://twitter.com/fatlimey/status/1225496023553978369?s=20








In it, she uses FlocQ and Coq to prove a somewhat surprising result that the naive formula $latex \sqrt{x^2} = |x|$ actually is correct for the right rounding mode of floating point, something I wouldn't have guessed.







Z3 confirms for `Float16`. I can't get `Float32` to come back after even a day on a fairly beefy computer. If I use `FPSort(ebits,sbits)` rather than a standard size, it just comes back unknown, so i can't really see where the cutoff size is. This does not bode well for checking properties of floating point in z3 in general. I think a brute force for loop check of 32 bit float properties is feasible. I might even be pretty fast. To some degree, if z3 is taking forever to find a counterexample, I wonder to what to degree the property is probably true.







If anyone has suggestions, I'm all ears.





[gist https://gist.github.com/philzook58/3632e1cd323171c69875c811c9b7a34c#file-stupid-py]

