---
date: 2024-03-25
title: Finite Set Theory in Python
---

[Set theory](https://en.wikipedia.org/wiki/Set_theory) is interesting.

It's a really cool thing that it builds up a ton of structure from such basic seeming components.

An interesting python builtin data structure I learned of only recently is `frozenset`. Because `frozenset` is immutable, it makes sense to hash it and use it as keys. This makes it easy to build sets of sets, which is the bread and butter of axiomatic set theory.

I highly recommend Naive Set Theory by Halmos.

Set theory is a pile of axioms about what kinds of sets exist and operations you can perform on them. I can't strongly enforce an interface in python, but if you can construct a set using my already defined operators, it doesn't require a new axiom. Anywhere I have to use a `frozenset` constructor, I am making some kind of new primitive construction.

It has a characteristic flavor of encoding more familiar mathematical objects like natural numbers in terms of sets.

A simple first axiom is

## Axiom: The Empty Set Exists

```python
emp = frozenset([])
print(emp)
```

    frozenset()

## The Axiom of Extension
<https://en.wikipedia.org/wiki/Axiom_of_extensionality>

This axiom says that two sets with the same contents are equal.

This is built in to the definition of `==` for `frozenset`.

We could allow other python values into our sets as "[ur-elements](https://en.wikipedia.org/wiki/Urelement)". This is the main way we use sets typically in python.

```python
emp == frozenset([])
```

    True

It is interesting to muse that there is a sense in which these two things are not equal. They do actually have distinct memory addresses and can be distinguished. This is sometimes called [physical equality](https://stackoverflow.com/questions/69608285/ocaml-physical-and-structural-equality#:~:text=One%20way%20to%20think%20of,values%20are%20structurally%20the%20same.). Our metasystem of python can kind of look behind the veil.

```python
emp is frozenset([])
```

    False

## The axiom schema of specification
<https://en.wikipedia.org/wiki/Axiom_schema_of_specification>

This is a super powerful set construction principle.

From any set, we can form another set by cutting out the pieces that satisfy a logical formula. Given a set $A$, we can take all the pieces
$$ \{ x : A | P(x) \}$$

We have a close analog using python comprehensions. I can package it up into a little function `specify` that takes in the set and the predicate, or perhaps we'll just say we're allowed to use comprehension.

```python
from typing import Callable, Any
def specify(A : frozenset[Any], P : Callable[Any, bool]) -> frozenset[Any]:
    return frozenset([x for x in A if P(x)])
```

With specification, we can defined the derived notion of intersection of two sets. It is a set of all the elements of X that are also in Y.

```python
def intersect(X,Y):
    return specify(X, lambda x: x in Y)
    # equivalently specify(Y, lambda y: y in X)
    # or simpler looking python definitions that don't make the definitional nature self evident
    #frozenset([z for z in x if z in y])
    #x & y
```

The [unrestricted comprehension](https://en.wikipedia.org/wiki/Frege%27s_theorem#Overview) principle doesn't require an $A$. Somehow it magically grabs all things that obey $P$. It is difficult to see how such a  thing could be contructed in python and indeed Frege's original formulation of unrestricted comprehension is inconsistent as show by Russell with his [famous paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox)

## The Axiom of Pairing
<https://en.wikipedia.org/wiki/Axiom_of_pairing>

For any two sets there exists another set they both belong to.

In other words we can construct unordered pairs.

```python
def upair(x,y):
    return frozenset([x,y])
```

By handing `upair` the same set, we can also make singleton sets. This is useful for starting to build sets of sets and is used for encodings of natural numbers and ordered pairs. You can see we don't refer to `frozenset` so this so `singleton` is a derived notion

```python
def singleton(x):
    return upair(x,x)

print(f"{singleton(emp)=}")
print(f"{singleton(singleton(emp))=}")
```

    singleton(emp)=frozenset({frozenset()})
    singleton(singleton(emp))=frozenset({frozenset({frozenset()})})

## Axiom of Unions
<https://en.wikipedia.org/wiki/Axiom_of_union>

For any collection of sets there exists a set that contains all the elements that belong to at least one set of the given collection.

$$ \bigcup C $$

```python
def bigunion(C):
    return frozenset([x for X in C for x in X])

print(f"{bigunion(emp)==emp=}")
```

    bigunion(emp)==emp=True

We can now derive the more familiar union operation.

```python

def union(x,y):
    return bigunion(upair(x,y)) # x | y

```

## Checking some properties

A poor man's theorem prover is quickcheck, in python's case [hypothesis](https://hypothesis.readthedocs.io/en/latest/). We can sanity check some properties

```python
# a collection of frozensets for testing. The iterated closure of the empty set under upair and bigunion operations
testsets = set([emp])
for i in range(3):
    testsets.update([upair(x,y) for x in testsets for y in testsets])
    testsets.update([bigunion(x) for x in testsets])
testsets
```

    {frozenset(),
     frozenset({frozenset({frozenset({frozenset()})})}),
     frozenset({frozenset({frozenset()}), frozenset({frozenset({frozenset()})})}),
     frozenset({frozenset({frozenset(), frozenset({frozenset()})})}),
     frozenset({frozenset({frozenset({frozenset()})}),
                frozenset({frozenset(), frozenset({frozenset()})})}),
     frozenset({frozenset({frozenset()}),
                frozenset({frozenset(), frozenset({frozenset()})})}),
     frozenset({frozenset()}),
     frozenset({frozenset({frozenset()})}),
     frozenset({frozenset(), frozenset({frozenset({frozenset()})})}),
     frozenset({frozenset(), frozenset({frozenset()})}),
     frozenset({frozenset(), frozenset({frozenset(), frozenset({frozenset()})})})}

```python
# commutativty of union
assert all(union(x,y) == union(y,x) for x in testsets for y in testsets)
# associativity of union
assert all(union(x,union(y,z)) == union(union(x,y),z) for x in testsets for y in testsets for z in testsets)
# idempotence of union
assert all(union(x,x) == x for x in testsets)

#commutation of intersection
assert all(intersect(x,y) == intersect(y,x) for x in testsets for y in testsets)
#associativity of intersection
assert all(intersect(x,intersect(y,z)) == intersect(intersect(x,y),z) for x in testsets for y in testsets for z in testsets)
#idempotence of intersection
assert all(intersect(x,x) == x for x in testsets)

#distributivity of intersection over union
assert all(intersect(x,union(y,z)) == union(intersect(x,y),intersect(x,z)) for x in testsets for y in testsets for z in testsets)
#distributivity of union over intersection
assert all(union(x,intersect(y,z)) == intersect(union(x,y),union(x,z)) for x in testsets for y in testsets for z in testsets)
```

## Axiom of Powers
<https://en.wikipedia.org/wiki/Axiom_of_power_set>

The powerset axiom let's you build a set of all subsets. There is a useful recipe <https://docs.python.org/3/library/itertools.html#itertools-recipes> that we can crib from itertools.

```python
import itertools
def power(s):
    return frozenset(itertools.chain.from_iterable(map(frozenset, itertools.combinations(s, r)) for r in range(len(s)+1)))

power(singleton(singleton(emp)))
```

    frozenset({frozenset(), frozenset({frozenset({frozenset()})})})

## Ordered pairs

Ordered pairs are readily available in python. It is mildly insane to encode them in terms of sets. This is what set theory does though.

The construction of the cartesian product of two sets is quite painful.

```python
def pair(x,y):
    return upair(singleton(x), upair(x,y))
    #return hashset([hashset([x]), hashset([x,y])])

def cartesian(A,B):
    C = power(power(union(A,B)))
    return specify(C, lambda x: any(x == pair(a,b) for a in A for b in B))

```

```python

# some projection operations. Do I need A and B?
def fst(z, A, B):
    return bigunion(specify(A, lambda a: singleton(a) in z))

def snd(z, A, B):
    return bigunion(specify(B, lambda b: any(z == pair(a,b) for a in A)))



assert(all(fst(pair(a,b), A, B) == a for A in testsets for B in testsets for a in A for b in B))
assert(all(snd(pair(a,b), A, B) == b for A in testsets for B in testsets for a in A for b in B))




```

# Relations, Functions, Dicts

So set theory can encode functions and relations as sets of ordered pairs. The natural python encoding of a finite function is a dict.

```python
def from_dict(d):
    return frozenset([pair(k, v) for k,v in d.items()])

```

## Numbers

There are multiple ways of encoding numbers. The relatively standard way is to encode 0 as `emp`  and then a successor function as c

```python

zero = emp
def succ(x):
    return union(x, singleton(x))
    #return eats(x, x)

one = succ(emp)
two = succ(one)
three = succ(two)
print(f"{one=}")
print(f"{two=}")
print(f"{three=}")


from functools import cache
@cache
def from_int(n):
    assert n >= 0
    if n == 0:
        return emp
    return succ(from_int(n-1))

from_int(3)
```

    one=frozenset({frozenset()})
    two=frozenset({frozenset(), frozenset({frozenset()})})
    three=frozenset({frozenset(), frozenset({frozenset(), frozenset({frozenset()})}), frozenset({frozenset()})})





    frozenset({frozenset(),
               frozenset({frozenset()}),
               frozenset({frozenset(), frozenset({frozenset()})})})

# Bits and Bobbles

We're just starting to get into interesting stuff. But that's exactly where the post gets harder to write. Each of these deserves of day of thought and a post of its own.

## The Axiom of Choice
<https://en.wikipedia.org/wiki/Axiom_of_choice>

Families are functions into sets.

The axiom of choice. Much blood has been spilled.

It in uncontroversial in our setting and I think a theorem, not an axiom

```python
def choice(Xi):
    return frozenset([pair(fst(x), snd(x).elems[0]) for x in Xi])
```

## Hashconsing and Universes

By using hash consing, we can give an arbitrary total ordering to each set as we build it, the order given by it's `id` identifiers. This ordering will not be stable between different runs.
In this way we can use the method of taking a sorted deduplicated tuple as being a canonical representative of it's set. Hashing this tuple in the usual way works fine.
Another approach is to consider using a hash combination function that respects the properties of the set datastructure. In other words the hash combination function is something like a homomorphism from sets to integers. An example might be `xor`, which is associative and commutative, just like set union.

Iterators perhaps can have the feel of classes? They are set like in some respects. Axiom schema of replacement. The ability to capture a growing universe might be useful. It feels a bit like the nonstandard reals. As soon as we discuss a particular time stamp of universes, it become an ordinary set and the universe of discourse is one step bigger.

<https://en.wikipedia.org/wiki/Von_Neumann_universe>
<https://en.wikipedia.org/wiki/Constructible_universe>

It would be interesting to replace `testsets` above with the expanding universe.

```python
from dataclasses import dataclass
from typing import Iterable
univ = {}
@dataclass(frozen=True)
class HashSet(): # do not use this constructor
    elems: tuple["HashSet", ...] # names. elem, mem, items   
    def __lt__(self, other) -> bool:
        return self.elems < other.elems
    def __hash__(self) -> int:
        return hash(id(self))
    def __eq__(self, other) -> bool: # fast equality via pointer equality
        return self is other
    def __iter__(self): # essentially enables a comprehension/separation operation
        return iter(self.elems)
    def __len__(self):
        return len(self.elems)
    def __repr__(self): # pretty printing
        return "{" + ",".join(map(repr, self.elems)) + "}"

# hmm. Could I use functools cache here? But maybe then it's hard to get the univ later
def hashset(x : Iterable[HashSet]) -> HashSet:
    """Smart constructor returns literally the same object if the same input is given."""
    x = tuple(sorted(set(x)))
    if x in univ:
        return univ[x]
    else:
        y = HashSet(x)
        univ[x] = y
        return y
    


# When we make the same hashset twice, they should be the same
x = hashset([])
y = hashset([])
print(f"{hashset([x]) is hashset([y, y])=}")



def reify() -> HashSet:
    return hashset(univ.values())
```

    hashset([x]) is hashset([y, y])=True

## Infinite Sets

Can we include infinite sets? In some sense perhaps. I believe we can basically attach some ordinals. There are certain questions that won't be computable. `[from_int(i) for i integers()] in omega` is true, but python won't ever return true.

Can we talk about induction?

Well foundedness. We can write a recursor.

def recurse(f):
    raise Exception("not well founded")

Non well founded sets like Graham's thing
Aczel
We can make loopy set structures if we take iterators / lazy data structures as our sets.

The laziness allows the set to be deep (infinite depth to set) or wide (infinite card set)

## Other Stuff

Hereditarily Finite Sets
Paulson <https://lawrencecpaulson.github.io/2022/02/23/Hereditarily_Finite.html> . Paulson's blog rules. <https://arxiv.org/abs/2104.14260>  <https://doi.org/10.4064/DM422-0-1> Świerczkowski. Useful alternative to peano arithmethmetic and godel encoding

We are making a very constructive perspective on set theory. It'd be interesting to do a follow up post on python variations of computability, constructivity. I don't feel confident I know enough to write cogently.

I've been using `any` and `all` without much comment, but these are natural analogs for bounded quantifiers. RCA0 is kind of pythony.

The system is missing the ability the talk about the hypothetical. A little bit of crazy talk, but maybe one way of doing this is using promises/futures. If a value is never forced, then it's contents do not matter. This is similar to inferring forall polymorphism or when a prolog query returns an unbound metavariable.

As shownn here we can't really prover theorems about hypothetical sets. We can only compute a canononical form of concrete sets and wave our hands that union is associative and so on. We need to have more tricks. Applicative python a la acl2 <https://www.philipzucker.com/applicative_python/> ?

set logic programming
CLP(Set)

<https://www.clpset.unipr.it/>
`{log}` "setlog"
JSetL

[set unification](https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/set-unification/2B789EB32DCF9F77021DBE26FC691032)
[Sets and constraint logic programming](https://dl.acm.org/doi/10.1145/365151.365169)

G Rossi
A Dovier
E Pontelli

herditraryl hybrid finite sets. Finite sets of finite sets + terms

[Set Constraints in Logic Programming](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=ea756dcfc1db14307899a5b7d33b82fefbdc74c0)
[Set constraints and logic programming - kozen](https://www.cs.cornell.edu/~kozen/Papers/sclp.pdf) CLP(SC)
Herbrand atom ~ singleton set
Aiken

Relation to boolean equation systems?

Kuper - Logic programming with sets

Non well founded sets

The concept of a set within a set is a bit unfamiliar from a programming perspective. This rarely comes up?
Typical set data structures require an ability to totally order or hash its elements. The subset relationship is almost a canonical example of a partial order.  Hashing of sets is interesting.

There is of course an empty set.

Comprehension is allowed. We obviously need to perform comprehension over a known set, so it is separation

axiom of choice. We don't really need the axiom of choice since we don't have infinite things

The TPTP set theory is very intriguing as a target of knuckledragger
<https://lawrencecpaulson.github.io/2022/02/02/Formalising_Math_Set_theory.html>
Art Quaife. Automated Deduction in von Neumann–Bernays–Gödel Set Theory. Journal of Automated Reasoning 8:1 (1992), 119–120. <https://rdcu.be/cJtDU>

Union is a new primitive operation. Anything that needs to touch the `elems` field is peeking under the curtains. Whereas intersection is a derived operation because it can use comprehension. Is this true? Ehhhh. Kind of we have an ambient theory of lists and tuples. We can convert to them using a comprehension. Are lists, tuples, generators kind of like "classes"? They are HashSet like.

```python

def pred(z : Hashset) -> Hashset:
    return max(z.x, key=len)

pred(three) == two

# the value of memoization

def plus(x: HashSet, y : HashSet):
    if x == emp:
        return y
    return hashset([plus(x,y) for x in x.x])

@cache
def plus(x:HashSet, y : HashSet):
    if x == emp:
        return y
    return hashset([plus(x,y) for x in x.x])



print(f"{from_int(3) == three=}")
from_int(4)


power(power(emp))

wrap2 = hashset([hashset([emp])])

def closure(s : HashSet) -> HashSet:
    return reduce(union, [closure(x) for x in s])
    #pass #return hashset([ power(closure(x)) for x in s ])

def natlabel(s:HashSet) -> int:
    return sum(2**natlabel(x) for x in s)

natlabel(emp)
natlabel(one)
natlabel(wrap2)
natlabel(two)
natlabel(three)

def to_dict(z):
    return {fst(x):snd(x) for x in z}
def domain(z):
    return hashset([fst(x) for x in z])
def codomain(z):
    return hashset([snd(x) for x in z])


def fst(z):
    return bigunion(bigunion(specify(z, lambda a: a != bigunion(z))))

def snd(z):
    return bigunion(bigunion(specify(z, lambda a: a != singleton(fst(z)))))

snd(pair(singleton(emp),emp))

#one = hashset([emp])
def eats(x,y): # aka add
    #return hashset((y,) + x.elems)


#more intuitive and performant verions using python pattern matching.
def fst(z):
    x,y = z.x
    if len(x) == 1:
        return x
    else:
        return y

def snd(z):
    x,y = z.x
    if len(y) == 1:
        x,y = y,x
    return y - x

```

```python
%%file /tmp/set.tptp
cnf(emp_exist, axiom, ~elem(X,emp)).
fof(extension, axiom, (![X] : (elem(X,A) <=> elem(X,B)))) <=> A = B).
fof(power, )



```
