---
author: philzook58
comments: true
date: 2019-12-24 23:33:24+00:00
layout: post
link: https://www.philipzucker.com/stupid-z3py-tricks-verifying-sorting-networks-off-of-wikipedia/
slug: stupid-z3py-tricks-verifying-sorting-networks-off-of-wikipedia
title: 'Stupid Z3Py Tricks: Verifying Sorting Networks off of Wikipedia'
wordpress_id: 2592
categories:
- Formal Methods
tags:
- python
- z3
---




[Sorting networks](https://en.wikipedia.org/wiki/Sorting_network) are a circuit flavored take on sorting. Although you can build circuits for any size input, any particular circuit works for a fixed sized input. They are like an unrolling of the loops or recursion of more familiar sorting algorithms. They come up also in the context of parallel and gpu sorting  








Here's an interesting thing. We can go to Wikipedia and get a little python snippet for the comparison order of a [Batcher odd-even mergesort](https://en.wikipedia.org/wiki/Batcher_odd%E2%80%93even_mergesort). Kind of a confusing algorithm. Why does it even work? Is it even right? It's written in some kind of funky, indexful generator style.





![](http://philzucker2.nfshost.com/wp-content/uploads/2019/12/Batcher_Odd-Even_Mergesort_for_eight_inputs.svg_-1024x829.png)Source: Wikipedia



[gist https://gist.github.com/philzook58/4aa17037bcb9b1ee57f4afdf87f7f3fd#file-batcher-py]





Well we can confirm this relatively straightforwardly using z3 by replacing the implementation of compare_and_swap with its z3 equivalent. We then ask z3 .





[gist https://gist.github.com/philzook58/4aa17037bcb9b1ee57f4afdf87f7f3fd#file-verify-py]





This comes back unsat, hence there are no inputs or executions that do not come back sorted. If I delete some elements from pair_to_compare, it comes back sat, showing that it doesn't always sort.







The trick here is that the circuit is fixed size, so we have no need for induction, one of the main things z3 is rather finicky at. 







It's somewhat interesting to note that the output of odd_even_merge is a sequence of instructions, we can think of this as interpreting a very small 1 instruction programming language.







We can also confirm similarly a simple odd-even bubblesort and other similar algorithms.





[gist https://gist.github.com/philzook58/4aa17037bcb9b1ee57f4afdf87f7f3fd#file-bubble-py]





Q: What about using uninterpreted sorts rather than integers? Integers is pretty convincing to me.







same_elems is slightly weaker than a permutation predicate. Wasn't super obvious to me the best way to do a permutation predicate in z3. Would I want to internalize the array? 







Edit: Upon further thought, actually the sort IS a nice predicate for permutation. How do we compute if two things are permutations of each other? By sorting them and forcing a zipped equality. Alternatively count the number of each element (a piece of bucket sort).  Since this sort is done by composing swaps, it is somewhat intrinsically a permutation







As a bummer though, I think randomized testing on arrays would be equally or perhaps more convincing of the correctness of the algorithm. Oh well.



