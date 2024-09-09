---
title: String Knuth Bendix
date: 2024-09-09
---

I've become entranced by all the [varieties](https://cstheory.stackexchange.com/questions/12326/unification-and-gaussian-elimination) of the knuth bendix completion algorithm as of late.

Knuth Bendix completion is a kind of equational reasoning algorithm. Given some generators of an equivalence relation like `X + 0 = X` it converts them into a "good" rewriting system like `X + 0 -> X`.

Knuth Bendix does not have to be over terms. It can be over other things that have a notion of overlapping and ordering, graphs, strings, multisets, polynomials, etc. There are ways perhaps of modelling these things as terms, which is a unifying, but there can be computational and mental overhead in doing so.

Strings are in particular an interesting example and actually the original thing [Knuth and Bendix](https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/knuth-bendix.pdf) were considering (I think).

When we say strings, we mean the same thing as sequences. There isn't anything intrinsically textual about what we're doing.

Having said that, it is neat that you can use the commonly available string manipulation libraries to achieve string rewriting needs. String rewriting is the analog of repeatedly applying find/replace rules.

Try it out on colab: <https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2024-09-09-string_knuth.ipynb>

```python
def rewrite(s : str, R : list[tuple[str,str]]) -> str:
    """Fully reduce s by rewrite rules R"""
    s0 = ""
    while s0 != s:
        s0 = s
        for lhs,rhs in R:
            s = s.replace(lhs,rhs)
    return s

assert rewrite("aaabbbaa", [("aa", "a")]) == "abbba" # remove duplicate a
assert rewrite("aaabbbaa", [("aa", "a"), ("bb", "b")]) == "aba" # remove duplicates
assert rewrite("aaabbbaa", [("aa", "a"), ("bb", "b"), ("ba", "ab")]) == "ab" # bubble sort 

```

But actually for my purposes, I don't want to be restricted to just sequences of characters, so I need to rebuild some functionality we had with python strings using python tuples.

# Rewriting Tuples

In order to do matching, I need to know when one tuple is a subsequence of another.

```python
def subseq(s,t):
    """Return index when s is a subsequence of t, None otherwise"""
    for i in range(len(t) - len(s) + 1):
        if s == t[i:i+len(s)]:
            return i
    return None
assert subseq((2,2), (1,1,1,2,2)) == 3
assert subseq((2,2), (1,1,1,2,2,2)) == 3
assert subseq((), (1,2,3)) == 0
assert subseq((3,4), (4,5,3)) is None
assert subseq((3,4), (4,5,3,4)) == 2
```

Next, we need to reimplement the `replace` functionality of a single replacement rule.

```python
def replace(s, lhs, rhs):
    """"""
    i = subseq(lhs, s)
    if i is not None:
        return s[:i] + rhs + s[i+len(lhs):]
    else:
        return s

assert replace((1,2,3,4), (2,3), (5,6)) == (1,5,6,4)
assert replace((1,2,3,4), (2,3), (5,6,7)) == (1,5,6,7,4)
assert replace((1,2,3,4), (2,3), (5,6,7,8)) == (1,5,6,7,8,4)
assert replace((1,1), (4,4), (2,2)) == (1,1)
```

Finally we can fully reduce tuples now

```python
def rewrite(s, R, exclude=-1):
    # exclude is useful for simplifying a rule
    while True:
        s0 = s
        for i,(lhs,rhs) in enumerate(R):
            if i != exclude:
                s = replace(s,lhs,rhs)
        if s == s0:
            return s

assert rewrite((1,2,3,4), [((2,3), (5,6)), ((5,6), (7,8))]) == (1,7,8,4)
assert rewrite((1,1,1,1,1,1), [((1,1), ())]) == ()
assert rewrite((1,1,1,1,2,1), [((1,1), ())]) == (2,1)
```

# Knuth Bendix

So we've implemented running our string rewrite system. Nice.

The next piece I need is to implement our term ordering. The concept of a term ordering I think is the key point of term rewriting that is both nearly trivial in some sense but also not at all obvious.

A key property that is very useful in a rewriting system (or any algorithm) is termination. When we want to talk mathematically about termination, we talk about well founded relations. <https://en.wikipedia.org/wiki/Well-founded_relation> Well founded transition relations are the ones that are guaranteed to terminate.

Orderings are also binary relations and we can cook up all sorts of ways of ordering things based on different intuitions and needs. If we choose an ordering that is well founded, then when the right hand sides of our rewrites are "smaller" than our left hand sides, our rewrite system is guaranteed to terminate.

Actually implementing the typical orderings (LPO, RPO, KBO) for terms is quite confusing. The basics string orderings are more straightforward.

We want short strings, so we can order by length. To tie break, we can use the build in lex ordering. This is called the shortlex ordering.

```python
def shortlex(s,t):
    """ order by length, then tie break by contents lex"""
    if len(s) < len(t):
        return t,s
    elif len(s) > len(t):
        return s,t
    elif s < t:
        return t,s
    elif s > t:
        return s,t
    else:
        assert False
```

Here's things that are a bit trickier. In Knuth Bendix we need to find all non trivial overlaps of left hand sides in rules. These are the possible sources of non-confluence aka the rule order mattering.

```python

def overlaps(s,t):
    """critical pairs https://en.wikipedia.org/wiki/Critical_pair_(term_rewriting)"""
    # make len(t) >= len(s)
    if len(t) < len(s):
        s,t = t,s
    if subseq(s,t) is not None:
        yield t
    # iterate over possible overlap sizes 1 to the len(s) at edges
    for osize in range(1,len(s)):
        if t[-osize:] == s[:osize]:
            yield t + s[osize:]
        if s[-osize:] == t[:osize]:
            yield s + t[osize:]

assert set(overlaps((1,2), (2,3))) == {(1,2,3)}
assert set(overlaps((1,2), (3,2))) == set()
assert set(overlaps((1,2), (2,1))) == {(1,2,1), (2,1,2)}
assert set(overlaps((1,2), (1,2))) == {(1,2)}
assert set(overlaps((2,2), (2,2,3))) == {(2,2,3), (2,2,2,3)}
assert set(overlaps((), (1,2))) == {(1,2)} # Hmm. Kind of a weird edge case
```

Given all these pieces, knuth bendix is a pretty simple almost brute force way of inferring equations and rules turning a set of equations into a good set of rules.

In a big loop we

1. For each pair of rules, we try to find a critical pair and add this to E
2. Reduce all equations in E with respect to R to remove redundancy
3. Orient equations in E to make them rewrite rules in R

```python
def deduce(R):
    """deduce all possible critical pairs from R"""
    for i, (lhs,rhs) in enumerate(R):
        for j in range(i):
            lhs1,rhs1 = R[j]
            for o in overlaps(lhs1,lhs):
                x,y = rewrite(o, [(lhs1, rhs1)]), rewrite(o, [(lhs, rhs)])
                if x != y:
                    yield x,y

def KB(E):
    E = E.copy()
    R = []
    done = False
    while not done:
        done = True
        E.extend(deduce(R))
        while E:
            lhs, rhs = E.pop()
            lhs, rhs = rewrite(lhs,R), rewrite(rhs,R)
            if lhs != rhs:
                done = False
                lhs, rhs = shortlex(lhs,rhs)
                R.append((lhs, rhs))

    return R
```

Here's a nice example from <https://haskellformaths.blogspot.com/2010/05/string-rewriting-and-knuth-bendix.html> .

![](https://blogger.googleusercontent.com/img/b/R29vZ2xl/AVvXsEjXLtSpN3WX0ZQr_HhiXMvJuS5gmRzufJk36492TLrFr_dkyTBYIJA46ROYoVQZkmkIlrWNpJxLQP8w6T2dUu00g-6eXDxEK52yyA8AkXqvNNigY14YuVOVcVhEVBRtorgZUnOLllCW9AO1/s400/squaresyms.GIF)

`a` and `b` generate rotations and flips of a square. These equations aren't normalizing though as is. We can run them through Knuth Bendix to get a normalizing set of rules.

A nice trick is to encode the inverse as a negative. These are opaque identitifiers and I have done nothin special in KB for accounting for inverses, but it is nice from a python syntax perspective.

```python
e = 0
a = 1 # a is rottate square
b = 2 # b is flip square horizontally.
E = [
    ((-a, a), ()), # inverse -b * b = 1
    ((-b,b), ()), # inverse -a * a = 1
    ((a,a,a,a), ()), # a^4 = 1
    ((b,b), ()), # b^2 = 1
    ((a,a,a,b), (b,a)) #a^3 b = ba  
]
print(E)
print(KB(E))

```

    [((-1, 1), ()), ((-2, 2), ()), ((1, 1, 1, 1), ()), ((2, 2), ()), ((1, 1, 1, 2), (2, 1))]
    [((1, 1, 1, 2), (2, 1)), ((2, 2), ()), ((1, 1, 1, 1), ()), ((-2, 2), ()), ((-1, 1), ()), ((1, 1, 1), (-1,)), ((1, 1, 2), (-1, 2, 1)), ((2,), (-2,)), ((1, -2, 1), (-2,)), ((-1, -2, 1, 1), (1, -2)), ((-1, -2, 1), (-2, 1, 1)), ((-2, 1, -2), (-1,)), ((-2, 1, 1, -2), (-1, -1)), ((1, -1), (-2, -2)), ((-2, -2), ()), ((-1, -2), (-2, 1)), ((1, -2), (-2, -1)), ((1, 1), (-1, -1)), ((-1, -1, -1), (1,))]

It's a big pile. Here is a post processing to simplify the redundancies in the rules. A more efficient knuth bendix, like Huet's algorithm, would do this as it goes. The simplification of the left hand side of rules is a bit tricky. I'm not particularly sure I did it right here.

```python
def simplify(R):
    Rnew = []
    E = []
    for i, (lhs,rhs) in enumerate(R):
        # lhs = reduce(Rnew)
        lhs1 = rewrite(lhs, R, exclude=i) # L-simplify. nebulous correctness. I might be playing it both ways here. I keep around the old R even though I should have moved it to E?
        rhs1 = rewrite(rhs, R) # R-simplify
        if lhs1 == lhs:
            Rnew.append((lhs,rhs1))
        elif lhs1 != rhs1:
            E.append((lhs1, rhs1))
    return E,Rnew

R = KB(E)
E,R = simplify(R)
R
```

    [((-1, 1), ()),
     ((2,), (-2,)),
     ((1, -1), ()),
     ((-2, -2), ()),
     ((-1, -2), (-2, 1)),
     ((1, -2), (-2, -1)),
     ((1, 1), (-1, -1)),
     ((-1, -1, -1), (1,))]

We've deduced that $b^{-1} = b$ for the flips.

Just to confirm I haven't lost completeness, I can derive all of the original axioms using my new simplified system R.

```python
E = [
    ((-a, a), ()), # inverse -b * b = 1
    ((-b,b), ()), # inverse -a * a = 1
    ((a,a,a,a), ()), # a^4 = 1
    ((b,b), ()), # b^2 = 1
    ((a,a,a,b), (b,a)) #a^3 b = ba  
]
for x,y in E:
    print(rewrite(x, R), rewrite(y, R))
```

    () ()
    () ()
    () ()
    () ()
    (-2, 1) (-2, 1)

# Bits and Bobbles

Note that GAP already ships a string knuth bendix. This is accessible from python via sage <https://www.sagemath.org/>

```python
#https://doc.sagemath.org/html/en/reference/groups/sage/groups/finitely_presented.html
from sage.all import *
F = FreeGroup(3)
x0,x1,x2 = F.gens()
G = F / [x0**2, x1 * x0]
G
F([1])
F.gap()
G.relations()
k = G.rewriting_system()
k.make_confluent()
k
G.simplification_isomorphism()
```

Where I'm going with my next post is to tie in string rewriting to an egraph giving a "seqeunce egraph". The "characters" of the string are ground terms. Because this egraph embeds string rewriting, it isn't guaranteed to terminate.

I want this because programs often have sequence of instructions. Instrinsic associativity in the style of <https://www.philipzucker.com/linear_grobner_egraph/> seems useful.

<https://github.com/sympy/sympy/blob/master/sympy/combinatorics/rewritingsystem.py> hmm also here

<https://github.com/gap-packages/kbmag>

- <https://www.sciencedirect.com/science/article/pii/S1567832610001025> efficiency issues of kbmag - swan <https://www.cs.stir.ac.uk/~kjt/techreps/pdf/TR197.pdf> Augmenting Metaheuristics with Rewriting Systems
- <https://maffsa.sourceforge.net/old_manpages/maf.html> MAF
- rkbp

Useful books:

- Epstein book Word Processing in Groups
- Handbook of computational group theory
- Charles Sims book - Computation with Finitely Presented Groups
- Term Rewriting and All That

<https://community.wolfram.com/groups/-/m/t/3217387>   Monoids, string-rewriting, confluence, and the Knuth-Bendix Algorithm - Mathematica

<https://haskellformaths.blogspot.com/2010/05/string-rewriting-and-knuth-bendix.html>

The automata anlge is really intriguing, becayse I'd hope I could use off the shelf high perf stuff to achieve the rewriting. Maybe BurntSushi?

Word processing in groups
automatic groups <https://en.wikipedia.org/wiki/Automatic_group>
word acceptor. Is this for partiality? the valid stings = {w | accept(w)} ?
Could have automata that identifies strings that correspond to particular elements
wa=v is the same asa recognizer a=i(w)v

What's the deal with the automata stuff

Twee sorting.
If we specialize commutiativyt, a very bad rule, to the individual guys, it becopmes sorting rules

This rewrite system will sort.

Computational group theory. Orbits. Caleb's graph hashing. Cayley Graph. Nauty

Free monoid
I can totalize the groupoid of paths into path fragment sequences?
Use string KB a la grobner egraphs. String

![](https://blogger.googleusercontent.com/img/b/R29vZ2xl/AVvXsEjXLtSpN3WX0ZQr_HhiXMvJuS5gmRzufJk36492TLrFr_dkyTBYIJA46ROYoVQZkmkIlrWNpJxLQP8w6T2dUu00g-6eXDxEK52yyA8AkXqvNNigY14YuVOVcVhEVBRtorgZUnOLllCW9AO1/s400/squaresyms.GIF)

shortlex

<https://math.stackexchange.com/questions/684066/knuth-bendix-completion-algorithm-word-problem>

<https://docs.gap-system.org/pkg/kbmag/doc/manual.pdf>

Strings are nice mathematically because they bake in an associative operation of concatenation, which we use to model other associative operations like group multiplication. Most typical algebraic thingies have associativity, and cutting out associativty computationally by brute force is awful. We often bake in associativty into our notation by just forgetting to bother with parenthesis, which makes proofs incvolving associativity so trivial as to be beneath notice.

Strings can also represent paths.

- Strings can be modelled as terms. The string `xyz` in a left string context `A` and a right string context `B`, `AxyzB`, can be modelled in a couple different way: `x(y(z(B)))` or `cons(x,cons(y,cons(z,cons(B)))` or reversedly `z(y(x(A)))`. It's interesting that we tend to make the string contexts A & B implicit, whereas the upper term context is usually implicit but the lower child context is not implicit and instead represented by variables. Food for thought.

- It is to my knowledge difficult to shallowly embed term rewriting into string rewriting. It is possible to embed because string rewriting is turing complete, so the brute force solutions is build a turing machine into string rewriting, then write a program to do term rewriting on that turing machine. Yuck.
- Ground term rewriting is trivially embeddable into string rewriting. Just flatten / pretty print the term. The difference here is that term rewriting supports (multiple) variables, which is tough in strings. When we look at critical pairs, in ground terms the ONLY way to have non trivial overlap is for on term to be a subterm of the other. There are no interesting partial overlaps.

String knuth bendix is much simpler than term knuth bendix because the notion of overlap and reduction is so much simpler. You don't need to go into some side discussion of unification and narrowing, which are topics into their own right.

A Interesting trick to if I need bulk rewriting, perhaps concat a special symbol in between my different strings I want reduced `"$".join(string_db).replace()`

Regular lexicographic order is not well founded b > ab > aab > aaab > ...

<https://www.philipzucker.com/ground_kbo/>

Charles Sim book has heuristics, suggestions about indexing
Automata for indexing?

Hyperscan. Burntsushi. Geoff langdale
Can their tricks be applied or are those tricks about regex?

A way of generating all the normal forms is mentioned for this finite group. Enumerate all strings formed by appending the generators to something else that was a normal form.

```python

def nfs(gens, R):
    nf = [()]
    seen = 0
    while seen < len(nf):
        s = nf[seen]
        seen += 1
        for g in gens:
            t = (g,) + s
            t1 = rewrite(t, R)
            if t == t1:
                nf.append(t)
    return nf

nfs([1,2], KB(E))
```

    [(), (1,)]

```python
def subseq(s,t):
    for i in range(len(t) - len(s)):
        if s == t[i:i+len(s)]:
            return i
    return None

def overlaps(s,t):
    if len(t) < len(s):
        s,t = t,s
    # t is bigger than s
    #overlap_size == 0
    #for i in range(len(t) - len(s)):
    #    if s == t[i:i+len(s)]:
    if subseq(s,t) is not None:
        yield t
    for osize in range(1,min(len(s), len(t)) + 1):
        if t[-osize:] == s[:osize]:
            yield t + s[osize:]
        if s[-osize:] == t[:osize]:
            yield s + t[osize:]

list(overlaps( (2,2,2,1,2), (1,2,2) ))



        

```

    [(1, 2, 2, 2, 2, 1, 2), (2, 2, 2, 1, 2, 2), (1, 2, 2, 2, 1, 2)]

proofs.
don't delete anything. Keep the active simplified set though.
R = [] # write only
explain = []
Rmin = {} # simmplified ids or tuples without exaplain

R = [((lhs,rhs),explain)]
Rmin = {(lhs,rhs)} ...  {lhs:rhs}  (?)

A trie / prefix trie seems useful.

preallocate numpy (?) for numba jit?
np.zeros((N, M))

```python
def huet(E,R):
    R = set()
    unmarked = []
    while len(E) > 0 or len(unmarked) > 0:
        while E:
            (lhs,rhs) = E.pop()
            lhs,rhs = rewrite(lhs, R), rewrite(rhs, R)
            if lhs == rhs:
                continue
            lhs,rhs = shortlex(lhs,rhs)
            Rnew = [(lhs,rhs)]
            unmarked.append((lhs,rhs))
            for (g,d) in R:
                g1 = replace(g, (lhs,rhs))
                if g1 == g:
                    d = rewrite(d, R)
                    Rnew.append((g,d))
                else:
                    E.append((g1,d))
            R = Rnew
        if unmarked:
            (lhs,rhs) = unmarked.pop()
            for (g,d) in R:
                for o in overlaps(g,lhs):
                    x = rewrite(o, R)
                    y = rewrite(o, [(lhs,rhs)])
                    if x != y:
                        E.append((x,y))

```

Knuth bendix can be made more goal driven. We don't persay need to fully ocmplete the system if we just want to prove some particular equality.

Similarly, we can early stop knuth bendix is all we want is a simplified term. It isn't obvious if we can show that a term is globally maximally simplified until KB finishes though.

```python
def KBgoal(E, goal):
    """
    goal driven KB. 
    """
    gl, gr = goal
    while len(E) > 0:
        if gl == gr:
            # We can do early stopping given a particular goal.
            return True
        E,R = KB1(E, R)
        gl, gr = reduce(gl, R), reduce(gr, R)
    return False

# could also do binary combinations as goals. and / or / not  of = !=
```

to be even more goal driven, we should generate critical pairs coming from the goal terms first. This is a bit (exactly?) like set of support. mark new rules as "tainted" by a goal term. This is interesting in the simplifcation driven context also. If we insist on a particular hyperesolution / UR resolution total grounding, we get egraph saturation.

The only thing we need to make egraph saturation complwete is throw in a KB step on the rules every once in a while.

```python

def overlaps(s,t):
    if len(s) > len(t):
        s,t = t,s
    for i in range(1, min(len(s), len(t)) + 1):
        if s[-i:] == t[:i]:
            yield i
    for i in range(len(t) - len(s)):
        if s == t[i:i+len(s)]:
            return i
        
        """
        for i, (lhs,rhs) in enumerate(R):
            for j in range(i):
                lhs1,rhs1 = R[j]
                for o in overlaps(lhs1,lhs):
                    E.append((reduce(o, [(lhs1, rhs1)]), reduce(o, [(lhs, rhs)])))
        """
```

```python
e = 0
a = 1 # a is rottate square
b = 2 # b is flip square horizontally.
E = [
    ((-a, a), ()), # inverse -b * b = 1
    ((-b,b), ()), # inverse -a * a = 1
    #((e,a), (a,)),
    #((e,b), (b,)),
    #((e,-a), (-a,)),
    #((e,-b), (-b,)),
    ((a,a,a,a), ()),
    ((b,b), ()),
    ((a,a,a,b), (b,a))
]
print(E)
print(KB(E))

```

# Old notes String rewriting systems

[Semi-Thue systems](https://en.wikipedia.org/wiki/Semi-Thue_system)
[Word problem](https://en.wikipedia.org/wiki/Word_problem_(mathematics))
Monoid presentation

converting to term rewriting system fff ---> f(f(f(X)))

Term Rewriting using linux command line tools

The string search and manipulation tools are very powerful and efficient. They compile queries like grep into simple machines and such I think.

There's a big difference between ground and non ground terms. They appear subtly different when latexed, but the are way different beats
Ground terms equation proving can be done through the e graph efficiently.

Ground term rewriting seems to be identical to string rewriting. Just layout serially a traversal of the term.

The implicit prefix and suffix are the context of the term

```python

rules = [
  ("aa", "b"),
  ("b", "c")
]

def run_rules(s,rules):
  old_s = None
  while s != old_s:
    old_s = s
    for lhs,rhs in rules:
      s = s.replace(lhs,rhs)
  return s

print(run_rules("ababaaaaccaaa", rules))

def naive_completion(rules):  
  old_rules = None
  while rules != old_rules:
    old_rules = rules.copy()
    for (lhs,rhs) in old_rules:
        a = run_rules(lhs, rules)
        b = run_rules(rhs, rules)
        if a == b:
          break
        if a < b:
          rules.add((b,a))
        if a > b:
          rules.add((a,b))
  return rules

# an incomplete reduction routine?
# Triangular rewrite rules in some sense.
# Is this right at all? This is like a chunk of Huet's. I think just moving R -> E might be ok even if not one of listed rules. No, if I could do that ths move + simplfy would give me a more powerful R-simplify.
# I might be weakening my rules. That's not so bad imo.
def reduce_rules(E):  
  # worklist style
  R = set()
  # Sort E so smallest last probably. Most reduction power.
  E = sorted(E, key=lambda k: len(k[0]), reverse=True)
  while len(E) > 0:
    (a,b) = E.pop()
    a = run_rules(a, R) # simplify
    b = run_rules(b, R)
    print(a,b)
    if a == b: #delete
      continue
    if (len(b), b) > (len(a), a): # len then lex ordering
      R.add((b,a))
    if (len(a), a) > (len(b), b):
      R.add((a,b))
  return R



rules = {
  ("aaa", "a"),
  ("aaa", "c")
}

print(naive_completion(rules))


rules = [
  ("ffa", "a"),
  ("fa", "a")
]

print(run_rules("ffffffffffffa", rules))

print(reduce_rules(rules))

rules = [
  ("12+", "21+"), # an application of comm
  ("23+1+", "2+31+") # an application of assoc
]
# I am really going to want a notion of indirection or compression here.
# Intern strings

class RPN():
  def __init__(self, s):
    self.s = str(s)
  def __add__(self,b):
    return RPN(self.s + b.s + "+")
  def __repr__(self):
    return self.s

b0 = RPN(0)
b1 = RPN(1)
b2 = RPN(2)
b3 = RPN(3)


E = [
  (b1 + b0, b0 + b1),
  (b0 + b1, b1),
  (b1 + b2, b3),
  (b2, b1 + b1) 
]
E = [
  ("10+", "01+"),
  ("01+", "1"),
  ("12+", "3"),
  ("2", "11+"),
  ("00+", "0"),
  ("00+1+1+1+", "3"),
]

print(reduce_rules(E))
E = reduce_rules(E)
print(run_rules("00+1+0+1+0+2+",E))

E = [( str(i) + str(j) + "+" , str(i + j)) for i in range(4) for j in range(10) if i + j <= 9]
print(E)
print(reduce_rules(E))
print(run_rules("00+1+0+1+0+2+",E))

```

Ropes

We can of course compile a rule set to do better than this. In some sense every string represents a possibly infinite class of strings posible by running rules in reverse

String rewriting systems are a bit easier to think about and find good stock library functionality for.

string rewriting is unary term rewriting. A variable string pattern "aaaXbbbb" is a curious object from that perspective. While simple, it is a higher order pattern. `a(a(a(X(b(b(b(Y)))))))`. You can also finitize a bit. `foo(a)` can be made an atomic character. Or you can partially normalize a term rewriting system to string rewriting form

String orderings
Lexicographic comparison
Length
shortlex - first length, then lex
symbol counts

```python
def critical_pairs(a,b):
  assert len(a) > 0 and len(b) > 0
  if len(b) <= len(a):
    a,b = b,a # a is shorter
  cps = []
  if b.find(a) != -1: # b contains a
   cps.append(b)
  for n in range(1,len(a)): # check if overlapping concat is possible
    if b[-n:] == a[:n]:
      cps.append(b + a[n:])
    if b[:n] == a[-n:]:
      cps.append(a + b[n:])
  return cps

print(critical_pairs("aba", "ac"))
print(critical_pairs("aba", "ca"))
print(critical_pairs("abab", "ba"))
  
'''
def reduce_rules(rules): # a very simple reduction, reducing rhs, and removing duplicate rules
  rules1 = set()
  for (lhs,rhs) in rules:
    rhs = run_rules(rhs,rules)
    rules1.add((lhs,rhs))
  return rules1
'''

  #run_rules
  #reduce_rules
```

Building a suffix tree might be a good way to find critical pairs.

Lempel Ziv / Lzw is the analog of hash consing? Some kind of string compression is. That's fun.

<http://haskellformaths.blogspot.com/2010/05/string-rewriting-and-knuth-bendix.html>

It seems like named pattern string rewriting and variable term rewriting might be close enough

You could imagine

((x + 0) + 0 + 0) laid out as + + + x 0 0 0. and the found ground rewite rule + x 0 -> x being applied iteratively.

Labelling shifts:
f(g(a), b) ->   f +0 g +1 a -1 b -0

the pattern
f(?x)  -> ?x
 becoming
 f +0 <x> -0 -> <x>
 f +1 <x> -1 -> <x>
 f +2 <x> -2 -> <x>
and so on to some upper limit
We could occasionally renormalize maybe if there are no +n -n pairs remaining.
then shuffle all the above ones down.
Ok but what about something that increases the depth
x -> f(x)
... hmmm.

And if we number from the bottom?

f +2 <X> -2 -> <X>

and
<X> -> ??? Well a raw pattern is pretty shitty
f(x) -> f(f(x)) becomes
f +n <X> -n -> f +(n+1) f +n <x>
Yeah. Numbering from the bottom is better. We don't have to

f(stuff,stuff)
f +n <X> -n +n <Y> -n

even without enumerating
plus +<n1> <X> -<n1> +<n2> <Y> -<n2>

Oooh. We have to enumerate every combo of possible subterm depths.

Hmm. This adjust levels

<http://matt.might.net/articles/sculpting-text/>

A unique terminator for the subexpression is the point.
f +2 (^ -2)* -2

could have a counter per symbol. per symbol depth.
f1 ( yadayada) \f1

fa1 <X> fb1 <Y> fc1

huh. What about the CPP? Won't that basically work?

This is horribly inefficent because it'll expand out huge terms.
And big backtracking jumps. Or rather big seeks while it tries to find the next spot to go to. The next argument of f.

For ground term rewriting it seems actually reasonable and faster than having indirections. We can't have sharing though. That is a bummer.Maybe with zip.
Unless our goal is simplifcation.

using the rule

We could try to use the e-matching strategy where we iteratively instantiate fixed ground rewrite rules into the sed file itself?

Instead of using parenthesis, one could use numbered enter level exit level. And then bound the number of levels.
Each term rewriting becomes a string rewriting (with named regex holes ) replicated by the number of supported levels.

using sed on itself we might be able to implement knuth bendix

One could compile into a human unreadable huffman encoded like thing

<https://superuser.com/questions/1366825/how-to-recursively-replace-characters-with-sed> looping in sed
You can gnu parallel into chunks
grep is much faster. If terms are rare, maybe find using grep first?

Suffix trees can store every subterm of ground term with efficient query.

<https://spencermortensen.com/articles/serialize-a-binary-tree-in-minimal-space/> an interesting perspective on tree serialization
catalan numbers. We know size of tree if we give elements.
<https://www.educative.io/edpresso/what-is-morris-traversal> woah. Bizarre. It mutates the true as it goes down it and store
Kind of reminscent of dancing links in a way

f 20 90 190 yada yada yada could desribe links to the approprate spots.
This would be the analog of flatterms.

There is something like encoding lambda terms with de bruijn. vs unique signifiers.
If we could encode the unique signifiers in a way such that they never collide.

There is something to that we're kind of converting to rpn.
<https://github.com/GillesArcas/numsed>
<https://github.com/shinh/sedlisp>
