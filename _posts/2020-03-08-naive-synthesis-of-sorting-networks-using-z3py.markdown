---
author: philzook58
comments: true
date: 2020-03-08 19:52:23+00:00
layout: post
link: https://www.philipzucker.com/naive-synthesis-of-sorting-networks-using-z3py/
slug: naive-synthesis-of-sorting-networks-using-z3py
title: Naive Synthesis of Sorting Networks using Z3Py
wordpress_id: 2691
categories:
- Formal Methods
- Optimization
tags:
- z3py
---




As a simple extension of [verifying the sorting networks from before](http://www.philipzucker.com/stupid-z3py-tricks-verifying-sorting-networks-off-of-wikipedia/), we can synthesize optimally small sorting networks. The "program" of the sorting network is specified by a list of tuples of the elements we wish to compare and swap in order. We just generate all possible sequences of comparison operations and ask z3 to try verifying. If z3 says it verifies, we're done.







Here are some definitions for running the thing





[gist https://gist.github.com/philzook58/1755ce5bbacd197e549a1e7ae407813f#file-prelude-py]





and here is a simple generating thing for all possible pairs.





[gist https://gist.github.com/philzook58/1755ce5bbacd197e549a1e7ae407813f#file-synthesize-py]





As is, this is astoundingly slow. Truly truly abysmally slow. The combinatorics of really naively search through this space is abysmal. I doubt you're going to get more than a network of size 6 out of this as is.







Some possible optimizations: early pruning of bad networks with testing, avoiding ever looking at obviously bad networks. Maybe a randomized search might be faster if one doesn't care about optimality. We could also ask z3 to produce networks.







For more on program synthesis, check out[ ](https://github.com/nadia-polikarpova)Nadia Polikarpova's sick course here.







[https://github.com/nadia-polikarpova/cse291-program-synthesis](https://github.com/nadia-polikarpova/cse291-program-synthesis)



