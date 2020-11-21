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






```
from z3 import *

def compare_and_swap_z3(x,y):
    x1, y1 = FreshInt(), FreshInt()
    c = If(x <= y, And(x1 == x, y1 == y) , And(x1 == y, y1 == x) )
    return x1, y1, c
    
# predicates of interest
def sorted_list(x): # list is sorted
    return And([x <= y for x,y in zip(x , x[1:])])
def in_list(x,a): # x is in the list of a
    return Or([x == y for y in a])
def sub_list(a, b): # all elements of a appear in b
    return And([in_list(x,a) for x in b ])
def same_elems(a,b): # a contains the same elements as b
    return And(sub_list(a,b), sub_list(b,a))

def verify_network(pairs_to_compare, N):
    s = Solver()

    a = [Int(f"x_{i}") for i in range(N)] #build initial array in z3 variables

    #a_orig = a.copy() # keep around copy for correctness predicate
    for i,j in pairs_to_compare:
       x = a[i]
       y = a[j]
       x1, y1, c = compare_and_swap_z3(x,y) 
       a[i] = x1
       a[j] = y1
       s.add(c)

    #s.add(Not(And(sorted_list(a), same_elems(a_orig,a))))
    s.add(Not(sorted_list(a)))
    if s.check() == unsat:
        print("proved")
        return True
    else:
        return False
N = 8
verify_network(list(oddeven_merge_sort(N)), N)
```






and here is a simple generating thing for all possible pairs.






```
def all_swaps(m): # all pairs of integers from 0 to m-1
    return [ [(i, j)] for i in range(m) for j in range(i+1, m) ]
    
# All list of length n on swaps on m wires 
def all_networks(m, n): 
   if n == 0:
     return []
   elif n == 1:
     return all_swaps(m)
   else:
     return [ c + swap for c in all_networks(m,n-1) for swap in all_swaps(m)]


def synthesize(N):
    for n in range(N**2): # we can definitely do it in N*2 gates.
       print(f"trying network size: {n}")
       for pairs_to_compare in all_networks(N,n):   
           if verify_network(pairs_to_compare, N):
               return pairs_to_compare


synthesize(4)
```






As is, this is astoundingly slow. Truly truly abysmally slow. The combinatorics of really naively search through this space is abysmal. I doubt you're going to get more than a network of size 6 out of this as is.







Some possible optimizations: early pruning of bad networks with testing, avoiding ever looking at obviously bad networks. Maybe a randomized search might be faster if one doesn't care about optimality. We could also ask z3 to produce networks.







For more on program synthesis, check out[ ](https://github.com/nadia-polikarpova)Nadia Polikarpova's sick course here.







[https://github.com/nadia-polikarpova/cse291-program-synthesis](https://github.com/nadia-polikarpova/cse291-program-synthesis)



