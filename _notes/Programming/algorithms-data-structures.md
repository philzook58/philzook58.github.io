
See also:
- Performance
- Any domain that uses algorithms

[List of algorithms](https://en.wikipedia.org/wiki/List_of_algorithms)
[List of Data structures](https://en.wikipedia.org/wiki/List_of_data_structures)


[distibuted algoryhtms course](https://www.youtube.com/playlist?list=PL2RY7P3JxZN8g9hFCasNqzuDhZbIbAj54)

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