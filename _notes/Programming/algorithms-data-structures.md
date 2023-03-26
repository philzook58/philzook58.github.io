
See also:
- Performance
- Any domain that uses algorithms

[List of algorithms](https://en.wikipedia.org/wiki/List_of_algorithms)
[List of Data structures](https://en.wikipedia.org/wiki/List_of_data_structures)


[distibuted algoryhtms course](https://www.youtube.com/playlist?list=PL2RY7P3JxZN8g9hFCasNqzuDhZbIbAj54)
[Algorithms for Competitive Programming](https://cp-algorithms.com/)

# Functional Data Structures
Okasaki

# Hash 
[fibonacci hashing](https://probablydance.com/2018/06/16/fibonacci-hashing-the-optimization-that-the-world-forgot-or-a-better-alternative-to-integer-modulo/) fibonacci method is not good hash, but good way to map big into to smaller int

https://databasearchitects.blogspot.com/2020/01/all-hash-table-sizes-you-will-ever-need.html what are useful sizes to pick for your hash table. Magic numbers for modding by primes

## Linear Probing


https://en.wikipedia.org/wiki/Double_hashing Double Hashing. Use second hash function as offset multiplier
## Perfect Hashing
https://en.wikipedia.org/wiki/Perfect_hash_function
Perfect hashing is without collisions. If you know the key space ahead of time, can you construct a perfect hash function?

Minimal perfect hash function - bijective mapping

https://www.gnu.org/software/gperf/ - small sets ~1000.


## Cuckoo Hashing


# Tries

Hash array mapped tries https://hackage.haskell.org/package/unordered-containers-0.2.19.1/docs/Data-HashMap-Strict.html
https://en.wikipedia.org/wiki/Hash_array_mapped_trie
https://worace.works/2016/05/24/hash-array-mapped-tries/
I think the basic idea is to use a trie as a mapping of the hash table rather than an array.
[bagwell paper](https://lampwww.epfl.ch/papers/idealhashtrees.pdf)


Patricia tries

## Suffix Tries
[ben langmead videos](https://www.youtube.com/playlist?list=PL2mpR0RYFQsDFNyRsTNcWkFTHTkxWREeb)

Put all suffixed of a string into a trie.
You can compress edges.
Then you can represent the annotations on the compressed edges by reference to positions in original string.

substring query - a prefix of a suffix is a substring


Suffix links


### suffix array
sorted list of suffixes
```python
# possibly bad O(m^2)
def suffix_array(s):
    return sorted(range(len(s)), key=lambda n: s[n:])
```
things that share a prefix will be consecutive

BUild by building suffix trie, then getting suffix array

Two efficient algorithms for linar time suffix array construction SA-IS https://ieeexplore.ieee.org/document/5582081
# Minimal Acyclic Finite State Automaton
DAWG
https://en.wikipedia.org/wiki/Deterministic_acyclic_finite_state_automaton

Trie but share common leaves. Related to egraph?
Finite set of strings very compactly represented.
Acyclic means automata is way more structured than usual

[incremental construction paper](https://aclanthology.org/J00-1002.pdf)
http://stevehanov.ca/blog/index.php?id=115
https://docs.rs/fst/latest/fst/raw/struct.Fst.html#bibliography
Finite State transducer. What is this term getting at?

# Strings
https://en.wikipedia.org/wiki/String-searching_algorithm
https://www.geeksforgeeks.org/algorithms-gq/pattern-searching/
Aho-corasick
KMP - partial evaluation
Z algorithm
robin karp
boyer moore https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string-search_algorithm
https://en.wikipedia.org/wiki/Two-way_string-matching_algorithm

# Graph


# Geometry


