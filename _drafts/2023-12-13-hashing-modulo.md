
We can also consider the semidecidable equality case.

sets = absorptive monoid
multisets = commutative monoid
lists = monoid
tree

Lattice data structures.
Multisets of incomparable elements, we ought to be able to tune between having a total order and a partial order.
The more total the order is, the better we can do.
Equality
partially ordered <https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html>
total ordered

Maybe a set of chains of some kind

Hash cons modulo theories
Hash Cons modulo symmetry

There is material on how to perform hashing in terms of how to take a range of integers and deterministically map it in a scrambled way into a smaller range. By the nature of functions, if two objects map to different hashes they must not be equal. `f(x) != f(y) -> x != y` no matter what the definition of `f` is. We cannot conclude anything if two objects map to the same value (a hash collision) and a further test must be made.

There are some interesting questions that come up when you want to hash data structures or mathematical objects. How do you take these things to an integer in the first place?

The simplest case is hashing of tuples and ordered trees (like typical ASTs). This doesn't seem that bad.

But in other data structures there are representational redundancies or equations that might hold. How do you hash these things that have a notion of equality beyond that of structural equality?

A common example is typical dictionary data structures like red-black trees. The order you put keys into these trees changes their exact balancing. To put this in more mathematical terms, how do we make hashes for finite maps. A related question is how do we make hashes for sets?

There are alternative formulations of sets. Tries are one example, for example patricia tries. These data structures are canonical for the set or map they represent and hence you can use regular tree hashing techinques.

If you have a normalization procedure that can

Another example which really inspired this post is the question of how to hash a tree that has a notion of alpha equivalence (where names of variables don't really matter). Examples of these things are lambda binders, summation symbol indices, the dummy variable name for an integral, etc. [Hashing Modulo Alpha-Equivalence](https://arxiv.org/abs/2105.02856) presents a scheme for doing this.

Lambda syntax requires variables to also be scoped. This may be a separate concern.

de Bruijn indices is famously a canonical representation of closed lambda terms. Why is this not a solution to the problem?

It is useful to consider invariants of the equivalence class of structures. One invariant is the tree derived by replacing every variable with the same marker. An invariant from `("foo", ("var", 0), ("var", 1))` is `("foo", "marker", "marker")`
Another invariant is the number of variables, the set of counts of variables, or the confusion size.
The variable breadcrumb trick in co de Bruijn notation is very clever. A set of multicontexts. There is redundant information here.

These are all special cases of graph hashing. That is not to say that you want to reach for the big hammer of graph hashing, since it might be very difficult to do.

Hashing and Hash consing are related but distinct concerns. Hash consing is also called interning in some contexts. See for example [`sys.intern`](https://docs.python.org/3/library/sys.html#sys.intern) in the python standard library.

If you only use interned data, you can replace structural equality `==` with physical equality `is`, since every equal thing is literally the same object in memory. This is much faster, especially when you consider structural equality may require traversing some big tree.

egraphs in a sense are an answer to how can you hash modulo an equational theory with no good properties. It keeps refining and fixing up your hash dynamically

False positive and false negatives

Definitely equal,
Definitely not equal,

Structural equality
Physical equality

Big integers, arbitrarily large integers often

# Canonization

One technique to
Binary search trees
Tries
Patricia trie in souffle

Hashing Sets

Hashing graphs

Homomorphisms and hash functions

Fingerprinting and invariants.

Fast paths
Structural Equality.

Hash Consing

Replacing varables with generaic var. Does this represent a tree of all equal variables or tree of all different

Unique Enumeration

Variable maps

```python


```

Resources:

- Handbook of automated reasoning
- Vector fingerprint eprover paper
- Hash cons modulo alpha, criticism by paul.
- Richard O-Keefe paper
- Python hashing of frozensets

```python

_mytable = {}
interned_ids = set()

def intern(x):
    if isinstance(x,tuple):
        #x = tuple( intern(y) for y in x )
        key = tuple(id(y) if id(y) in interned_ids else id(intern(y)) for y in x) # don't recursively intern
    elif isinstance(x,str) or isinstance(x,int):
        key = x
    else:
        assert False, f"not internable {x}"
    x1 = _mytable.get(key)
    if x1 is not None:
        return x1
    else:
        _mytable[key] = x
        interned_ids.add(id(x))
        return x

def fast_equals(x,y): #"fast"
    x = intern(x)
    y = intern(y)
    return x is y
    
print(intern( (1,2,(3,4)) ) is intern( (1,2,(3,4)) ))
print(id(intern((1,2,3))))
print(_mytable)
```
