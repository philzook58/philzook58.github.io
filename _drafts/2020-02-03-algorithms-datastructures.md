I feel like most algorithms and data structures are os ordinary they are kind of boring?


Sparse Sets - knuth - bitvectors + 
Bitvectors  http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.681.8766&rep=rep1&type=pdf
ullmann bitvector algos for binary constraint and subgraph iso.

Books:
CLRS


Sorting algorithms
Hash tables
Dynamic programming
Tries
Graph algorithsm - shortest path, spanning tree

https://news.ycombinator.com/item?id=26590234#26592091 hash table in C. some interesting commments too
linear search - an assoc list but he kept it in an array
http://burtleburtle.net/bob/hash/doobs.html - hashing from z3 source code
https://craftinginterpreters.com/hash-tables.html

lkinear probing vs linked list in hash table. 

concurrent hash map


What this?
https://branchfree.org/2019/02/25/paper-parsing-gigabytes-of-json-per-second/
https://news.ycombinator.com/item?id=24069530
roaring bitmaps
simdjson
judy arrays
People are mentioned warming up the branch predictors on purpose somehow
Branchless programming

https://algorithmica.org/en/eytzinger https://news.ycombinator.com/item?id=26695694
Interesting. Cache-oblivious binary search. Uses the "Heap" ordering or what have you
Plus a branchless comparator?
I think also a big point is 
How do you even know when cache something is a problem. How do you use feedback and self correct?
How do you organize tight loops? "smart" ways of keeping structure.


microbenchmarking
performance counters - cache misses, TLB ht/miss, mispredicted branches
nanobench https://arxiv.org/pdf/1911.03282.pdf
VTune, perf, PAPI, libpfc,

What every programmer should know abouyt memory
https://people.freebsd.org/~lstewart/articles/cpumemory.pdf

modern microprcessor 90 minute guide
http://www.lighterra.com/papers/modernmicroprocessors/


https://en.wikipedia.org/wiki/Program_optimization
Bentley Writing Efficient Program
