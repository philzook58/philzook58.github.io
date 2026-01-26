---
title: "Term Ordering Etudes: Ground Lexicographic Path Ordering"
date: 2026-01-26
---

[Term orderings](https://en.wikipedia.org/wiki/Rewrite_order) are a concept that is both obvious and bizarre.

On the one hand, of course when we are rewriting terms to make better expressions, we are trying to make "simpler" or "better" ones. Or we are seeking normal forms by a process that has to stop because there is a lower bound on how simple a term can get. When we tease this concept out, yea, there is some kind of [well founded](https://en.wikipedia.org/wiki/Well-founded_relation) ordering on terms, an objective function perhaps, we are trying to maximize or minimize. Well founded is roughly (exactly?) a mathematical definition of what it means to be terminating.

On the other hand, the addition of variables and the constraints of playing nicely with rewriting and substitution are more complex than one might hope. Variables + good substitution also _require_ the ordering become partial and that the commutativity axiom `X + Y = Y + X` cannot be ordered, because some demon could always find a way to pick `X` and `Y` to defeat your ordering choice. Partial orderings are more confusing than total orderings. Not unbearably so, but more.

I think it is very conceptually important to simplify to the non-variable case first. The definitions simplify and become closer to obvious

Knuth Bendix ordering (KBO) is ordering by (weighted) size with a recursive tie breaking
<https://www.philipzucker.com/ground_kbo/> . This is an obvious idea.

Polynomial orderings I think may be the most intuitive, but I've actually spent the least time with them

Lexicographic path ordering (LPO) has eluded me.

Here I have implemented a ground version of it with some property tests. I think seeing some bulk output gives me better intuition for what it is doing.

# Ground LPO

Here is a simple term datatype with a symbol `f` applied to arguments `args

```python
from dataclasses import dataclass, field
import functools

@dataclass(frozen=True)
class App():
    f : str
    args : tuple["App", ...] = ()
    def __repr__(self):
        if self.args:
            return f"{self.f}({', '.join(repr(a) for a in self.args)})"
        else:
            return self.f
    
    def __le__(t : "App", s : "App") -> bool:
        return t == s or t < s
        
    def __lt__(t : "App", s : "App") -> bool:
        if t == s:
            return False
        cond1 = any(a >= s for a in t.args)
        cond2 = any(t <= b for b in s.args)
        assert not (cond1 and cond2) # sanity checking. Early return would be a bit more performant
        if cond1:
            return False
        elif cond2:
            return True
        else:
            # note we do not need chkargs because cond2 already takes care of it
            if (t.f, len(t.args)) > (s.f, len(s.args)): # different arity f are different symbols really. f/2 != f/3
                return False
            elif (t.f, len(t.args)) < (s.f, len(s.args)):
                return True
            else:
                for a,b in zip(t.args, s.args):
                    if a != b:
                        return a < b
                else:
                    raise ValueError("Unreachable")
        
x = App("x")
y = App("y")
h = lambda x: App("h", (x,))
f = lambda a,b: App("f", (a,b))
g = lambda a,b: App("g", (a,b))

assert x < h(x)
assert h(x) > x
assert x < y
assert h(x) < h(y)

```

LPO is defined nearly by brute force to make sure that if one of your subterms is larger than `t`, you must be larger than `t`. `cond1` and `cond2` deal with this case symmetrically. If neither is true, then we need some tie breaking system. We can tie break just on the current top symbol, and if that fails then on the children lexicographically.

The above is written to use python comparisons, but we can also write it in the form where it returns a comparison. Which form is clearer is a matter of taste.

```python
from enum import Enum
class Order(Enum):
    LT = -1
    EQ = 0
    GT = 1

def ground_lpo(t : App, s : App):
    if t == s:
        return Order.EQ
    cond1 = any(ground_lpo(a, s) in [Order.GT, Order.EQ] for a in t.args)
    cond2 = any(ground_lpo(t, b) in [Order.LT, Order.EQ] for b in s.args)
    assert not (cond1 and cond2)
    if cond1:
        return Order.GT
    elif cond2:
        return Order.LT
    else:
    # note we do not need chkargs because cond2 already takes care of it
        if (t.f, len(t.args)) > (s.f, len(s.args)):
            return Order.GT
        elif (t.f, len(t.args)) < (s.f, len(s.args)):
            return Order.LT
        else:
            for a,b in zip(t.args, s.args):
                res = ground_lpo(a,b)
                if res != Order.EQ:
                    return res
            else:
                raise ValueError("Unreachable")
```

# Examining an enumeration

I think examining this enumeration gave me a nice intuition for what this ordering is doing.

Note that this enumeration is not enumerating the "next" term in the total order, it's just enumerating some random terms. There sometimes isn't a "next" term. An arbitrary number of `f` applications is still better than a single `g`. This is like the situation in the ordinals <https://en.wikipedia.org/wiki/Ordinal_number> , or more simply a pair of Nats. There is no particular thing that is "one less" than `(1,0)`. `(0,9999999)` is still less than `(1,0)` by lex ordering.

The ordering should really have `...` in some positions

```
[a,
 b,
 f(a),
 f(b),
 f(f(a)),
 f(f(b)),
 f(f(f(a))),
 f(f(f(b))),
 f(f(f(f(a)))),
 f(f(f(f(b)))),
 ... # an arbitrary number of f
 g(a),
 f(g(a)),
 f(f(g(a))),
 f(f(f(g(a)))),
 ... # an abirtrary number of f
 g(b), 
and so on
```

This intuition is that the ordering wants the arguments to the "worse" symbols to decrease, and it willing to pay a very large cost in terms of the other symbols to do so.

There is an intuition that the symbol ordering can be thought of as a definition or call graph ordering in the case of functional programming. We can define `*` recursively in terms of `+` and `*`. When we unfold the definition of `*`, we gain many many `+` nodes, but this is ok, because we've reduced the argument to `*`. Likewise for worse things like ackermann functions. Probably symbols that are "constructor like" like `cons` should go very low in symbol ordering, and the symbol ordering of functions should roughly follow the definition ordering.

Another way of looking at this is that the ordering kind of like pushing "bad" symbols deeper inside the term and raising "good" symbols higher up in the term.

```python
terms = set([App("a"), App("b")])
for i in range(4):
    newterms = set()
    newterms |= {App("f", (t1,)) for t1 in terms}
    newterms |= {App("g", (t1,)) for t1 in terms}
    newterms |= {App("h", (t1,)) for t1 in terms}
    terms |= newterms

terms1= list(terms)
terms1.sort()
terms1
```

    [a,
     b,
     f(a),
     f(b),
     f(f(a)),
     f(f(b)),
     f(f(f(a))),
     f(f(f(b))),
     f(f(f(f(a)))),
     f(f(f(f(b)))),
     g(a),
     f(g(a)),
     f(f(g(a))),
     f(f(f(g(a)))),
     g(b),
     f(g(b)),
     f(f(g(b))),
     f(f(f(g(b)))),
     g(f(a)),
     f(g(f(a))),
     f(f(g(f(a)))),
     g(f(b)),
     f(g(f(b))),
     f(f(g(f(b)))),
     g(f(f(a))),
     f(g(f(f(a)))),
     g(f(f(b))),
     f(g(f(f(b)))),
     g(f(f(f(a)))),
     g(f(f(f(b)))),
     g(g(a)),
     f(g(g(a))),
     f(f(g(g(a)))),
     g(f(g(a))),
     f(g(f(g(a)))),
     g(f(f(g(a)))),
     g(g(b)),
     f(g(g(b))),
     f(f(g(g(b)))),
     g(f(g(b))),
     f(g(f(g(b)))),
     g(f(f(g(b)))),
     g(g(f(a))),
     f(g(g(f(a)))),
     g(f(g(f(a)))),
     g(g(f(b))),
     f(g(g(f(b)))),
     g(f(g(f(b)))),
     g(g(f(f(a)))),
     g(g(f(f(b)))),
     g(g(g(a))),
     f(g(g(g(a)))),
     g(f(g(g(a)))),
     g(g(f(g(a)))),
     g(g(g(b))),
     f(g(g(g(b)))),
     g(f(g(g(b)))),
     g(g(f(g(b)))),
     g(g(g(f(a)))),
     g(g(g(f(b)))),
     g(g(g(g(a)))),
     g(g(g(g(b)))),
     h(a),
     f(h(a)),
     f(f(h(a))),
     f(f(f(h(a)))),
     g(h(a)),
     f(g(h(a))),
     f(f(g(h(a)))),
     g(f(h(a))),
     f(g(f(h(a)))),
     g(f(f(h(a)))),
     g(g(h(a))),
     f(g(g(h(a)))),
     g(f(g(h(a)))),
     g(g(f(h(a)))),
     g(g(g(h(a)))),
     h(b),
     f(h(b)),
     f(f(h(b))),
     f(f(f(h(b)))),
     g(h(b)),
     f(g(h(b))),
     f(f(g(h(b)))),
     g(f(h(b))),
     f(g(f(h(b)))),
     g(f(f(h(b)))),
     g(g(h(b))),
     f(g(g(h(b)))),
     g(f(g(h(b)))),
     g(g(f(h(b)))),
     g(g(g(h(b)))),
     h(f(a)),
     f(h(f(a))),
     f(f(h(f(a)))),
     g(h(f(a))),
     f(g(h(f(a)))),
     g(f(h(f(a)))),
     g(g(h(f(a)))),
     h(f(b)),
     f(h(f(b))),
     f(f(h(f(b)))),
     g(h(f(b))),
     f(g(h(f(b)))),
     g(f(h(f(b)))),
     g(g(h(f(b)))),
     h(f(f(a))),
     f(h(f(f(a)))),
     g(h(f(f(a)))),
     h(f(f(b))),
     f(h(f(f(b)))),
     g(h(f(f(b)))),
     h(f(f(f(a)))),
     h(f(f(f(b)))),
     h(g(a)),
     f(h(g(a))),
     f(f(h(g(a)))),
     g(h(g(a))),
     f(g(h(g(a)))),
     g(f(h(g(a)))),
     g(g(h(g(a)))),
     h(f(g(a))),
     f(h(f(g(a)))),
     g(h(f(g(a)))),
     h(f(f(g(a)))),
     h(g(b)),
     f(h(g(b))),
     f(f(h(g(b)))),
     g(h(g(b))),
     f(g(h(g(b)))),
     g(f(h(g(b)))),
     g(g(h(g(b)))),
     h(f(g(b))),
     f(h(f(g(b)))),
     g(h(f(g(b)))),
     h(f(f(g(b)))),
     h(g(f(a))),
     f(h(g(f(a)))),
     g(h(g(f(a)))),
     h(f(g(f(a)))),
     h(g(f(b))),
     f(h(g(f(b)))),
     g(h(g(f(b)))),
     h(f(g(f(b)))),
     h(g(f(f(a)))),
     h(g(f(f(b)))),
     h(g(g(a))),
     f(h(g(g(a)))),
     g(h(g(g(a)))),
     h(f(g(g(a)))),
     h(g(f(g(a)))),
     h(g(g(b))),
     f(h(g(g(b)))),
     g(h(g(g(b)))),
     h(f(g(g(b)))),
     h(g(f(g(b)))),
     h(g(g(f(a)))),
     h(g(g(f(b)))),
     h(g(g(g(a)))),
     h(g(g(g(b)))),
     h(h(a)),
     f(h(h(a))),
     f(f(h(h(a)))),
     g(h(h(a))),
     f(g(h(h(a)))),
     g(f(h(h(a)))),
     g(g(h(h(a)))),
     h(f(h(a))),
     f(h(f(h(a)))),
     g(h(f(h(a)))),
     h(f(f(h(a)))),
     h(g(h(a))),
     f(h(g(h(a)))),
     g(h(g(h(a)))),
     h(f(g(h(a)))),
     h(g(f(h(a)))),
     h(g(g(h(a)))),
     h(h(b)),
     f(h(h(b))),
     f(f(h(h(b)))),
     g(h(h(b))),
     f(g(h(h(b)))),
     g(f(h(h(b)))),
     g(g(h(h(b)))),
     h(f(h(b))),
     f(h(f(h(b)))),
     g(h(f(h(b)))),
     h(f(f(h(b)))),
     h(g(h(b))),
     f(h(g(h(b)))),
     g(h(g(h(b)))),
     h(f(g(h(b)))),
     h(g(f(h(b)))),
     h(g(g(h(b)))),
     h(h(f(a))),
     f(h(h(f(a)))),
     g(h(h(f(a)))),
     h(f(h(f(a)))),
     h(g(h(f(a)))),
     h(h(f(b))),
     f(h(h(f(b)))),
     g(h(h(f(b)))),
     h(f(h(f(b)))),
     h(g(h(f(b)))),
     h(h(f(f(a)))),
     h(h(f(f(b)))),
     h(h(g(a))),
     f(h(h(g(a)))),
     g(h(h(g(a)))),
     h(f(h(g(a)))),
     h(g(h(g(a)))),
     h(h(f(g(a)))),
     h(h(g(b))),
     f(h(h(g(b)))),
     g(h(h(g(b)))),
     h(f(h(g(b)))),
     h(g(h(g(b)))),
     h(h(f(g(b)))),
     h(h(g(f(a)))),
     h(h(g(f(b)))),
     h(h(g(g(a)))),
     h(h(g(g(b)))),
     h(h(h(a))),
     f(h(h(h(a)))),
     g(h(h(h(a)))),
     h(f(h(h(a)))),
     h(g(h(h(a)))),
     h(h(f(h(a)))),
     h(h(g(h(a)))),
     h(h(h(b))),
     f(h(h(h(b)))),
     g(h(h(h(b)))),
     h(f(h(h(b)))),
     h(g(h(h(b)))),
     h(h(f(h(b)))),
     h(h(g(h(b)))),
     h(h(h(f(a)))),
     h(h(h(f(b)))),
     h(h(h(g(a)))),
     h(h(h(g(b)))),
     h(h(h(h(a)))),
     h(h(h(h(b))))]

# Property Based Testing

We can use property based testing to confirm some properties. Hypothesis is a nice python library for this.

The following is a random generator of terms.

```python
from hypothesis import given, strategies as st
apps = st.recursive(
    st.builds(App, st.sampled_from(["a","b","c"])),
    lambda children: st.lists(children, min_size=2,max_size=2).flatmap( lambda c:
        st.sampled_from(["f","g"]).map( lambda f:
         App(f, tuple(c)))))

for i in range(3):
    print(apps.example())
```

    g(b, f(f(b, a), b))
    f(f(g(f(b, b), f(c, c)), g(a, a)), f(c, c))
    b

Here we can compare our two versions

```python
@given(t=apps, s=apps)
def test_lt_ground_lpo(t,s):
    assert (t < s) == (ground_lpo(t,s) == Order.LT)
    assert (t > s) == (ground_lpo(t,s) == Order.GT)
    assert (t == s) == (ground_lpo(t,s) == Order.EQ)

test_lt_ground_lpo()
```

This is what a incorrect property looks like:

```python
@given(t=apps, s=apps)
def test_all_lt(t,s):
    assert ground_lpo(t,s) == Order.LT
test_all_lt()
```

    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    Cell In[26], line 4
          1 @given(t=apps, s=apps)
          2 def test_all_lt(t,s):
          3     assert ground_lpo(t,s) == Order.LT
    ----> 4 test_all_lt()


    Cell In[26], line 2, in test_all_lt()
          1 @given(t=apps, s=apps)
    ----> 2 def test_all_lt(t,s):
          3     assert ground_lpo(t,s) == Order.LT
          4 test_all_lt()


        [... skipping hidden 1 frame]


    Cell In[26], line 3, in test_all_lt(t, s)
          1 @given(t=apps, s=apps)
          2 def test_all_lt(t,s):
    ----> 3     assert ground_lpo(t,s) == Order.LT


    AssertionError: 

    Falsifying example: test_all_lt(
        t=App(f='a', args=()),
        s=App(f='a', args=()),
    )

Test that flipping the arguments flips the result to the order.

```python
@given(apps, apps)
def test_anti(t,s):
    res1 = ground_lpo(t,s)
    res2 = ground_lpo(s,t)
    assert res1 == Order(-res2.value)
test_anti()
```

It should obviously be reflexive. It's nice to check

```python
@given(apps, apps)
def test_ground_refl(t,s):
    res1 = ground_lpo(t,s)
    assert (t == s) == (res1 == Order.EQ)
test_ground_refl()
```

Test that it is transitive

```python
@given(apps, apps, apps)
def test_ground_trans(t,s,u):
    res1 = ground_lpo(t,s)
    res2 = ground_lpo(s,u)
    res3 = ground_lpo(t,u)
    if res1 == Order.LT and res2 == Order.LT:
        assert res3 == Order.LT
    elif res1 == Order.GT and res2 == Order.GT:
        assert res3 == Order.GT
test_ground_trans()
```

It is monotonic inside of terms / has a congruence property

```python
@given(apps, apps, apps)
def test_cong(t,s,q):
    res1 = ground_lpo(t,s)
    res2 = ground_lpo(App("f", (q,t)), App("f", (q,s)))
    assert res1 == res2
test_cong()
```

# Bits and Bobbles

I wrote about LPO previously here <https://www.philipzucker.com/term_ordering/>

Look at the chapter 4.5 in harrison's automated reasoning for lexicographic path ordering.

I have implemented LPO nearly maximally inefficiently. It should perhaps be memoized. For more info read
<https://www.worldscientific.com/doi/abs/10.1142/S0218213006002564?srsltid=AfmBOorEE7mKBvTxtZ5xZ_sBmWKvO3l09YYstQYCresacZ9-dWJIICeT>  THINGS TO KNOW WHEN IMPLEMENTING LPO - BERND LÖCHNER

<https://en.wikipedia.org/wiki/Path_ordering_(term_rewriting)>

<https://www.cs.unm.edu/~mccune/prover9/manual/2009-02A/term-order.html>

I quite like the description of LPO in here <https://research.vu.nl/ws/portalfiles/portal/266879340/A_Lambda_Free_Higher_Order_Recursive_Path_Order.pdf>

I found the description in term rewriting and all that to be pretty puzzling.

<https://arxiv.org/abs/2505.22181> Term Ordering Diagrams. Term orderings are an expensive part of vampire.

Would extracting a least LPO term from an egraph be interesting? I think because it is monotonic, this should still be in Poly time. KBO is roughly what standard extraction is using.

Can LPO orient typed SKI combinators where every `app_T` is a different symbol? This would show terminationg of STLC evaluation.

I think to property based check well foundedness, I might need to write a function that generates a lesser term if there is one, perhaps given a seed. Well foundedness has some nested quantifier structure or something.

<https://courses.grainger.illinois.edu/cs576/sp2017/readings/18-mar-9/rubio-ac-rpo-long.pdf> ac rpo
ac kbo

ACRPO as a step towards Miller completion.
It's interesting in it's own right also though.

<https://www.arxiv.org/abs/2510.18452> Term Orders for Optimistic Lambda-Superposition

Harrison - LPO / RPO is getting a reduction order by fiat
Blanchette -  <https://research.vu.nl/ws/portalfiles/portal/266879340/A_Lambda_Free_Higher_Order_Recursive_Path_Order.pdf>
<https://events.model.in.tum.de/mod23/blanchette/Lecture3-Lambda-Superposition.pdf>

"LPO essentially performs a lexicographic comparison while ensuring the subterm property (i.e., the property that a
term is larger than its proper subterms)."

"""
Definition 5. Let <= be a well-founded total order on Σ, and let >>f ⊆ (T ∗)2 be
a family of relations indexed by > ⊆ T 2 and by f ∈ Σ and satisfying properties
X1–X6. The induced recursive path order >fo on first-order Σ-terms is defined
inductively so that t >fo s if any of the following conditions is met, where t = g ¯t:
F1. t ≥fo s for some term t ∈ ¯t;
F2. s = f (¯s), g  f, and chkargs(t, ¯s);
F3. s = f(¯s), f = g, ¯t >>ffo ¯s, and chkargs(t, ¯s).
The auxiliary predicate chkargs(t, ¯s) is true if and only if t >fo s for all terms s ∈ ¯s.
The inductive definition is legitimate by the monotonicity of >>f (property X1).
RPO is a compromise between two design goals. On the one hand, rules F2
and F3, which form the core of the order, attempt to perform a comparison of
two terms by first looking at their heads, proceeding recursively to break ties.
On the other hand, rule F1 ensures that terms are larger than their proper
subterms and, transitively, larger than terms smaller than these. The chkargs
predicate prevents the application of F2 and F3 when F1 is applicable in the
other direction, ensuring irreflexivity.
The more recent literature defines RPO somewhat differently: Precision is
improved by replacing recursive calls to ≥fo with a nonstrict quasiorder fo and
by exploiting a generalized multiset extension [14,33]. These extensions are useful
but require substantial duplication in the definitions and the
"""

Why do macros terminate?
KBO with weights is good enough for foo(X) = bar(bar(bar(X))), but not good enough for foo(X) = bar(bar(bar(X,X))) (well, I guess it might orient it the other way)

Anything that writes to subterms terminates. Yeah. But kbo works for that.

The call graph

In AC, if we reify every term with a new constant, we end up fully expanding all the AC equivalent terms. The goal was to not do this.

rewrite relations
reduction orderings if stable under

Hmm. closed under contextual embedding and closed under subterm are distinct notions

For rational rewriting, the subterm relationship is not well founded or even an order. But contextual embedding could be a consistent order. Interesting.

subterms are a good opening question because a subterm ought to be smaller than the entire term. What does it even mean to be simplifcation ordering. contains the subterm realtions

<https://en.wikipedia.org/wiki/Rewrite_order>

<https://www.cs.ru.nl/~cynthiakop/research_publications_en.html> cynthia kop
carsten fuhs

<https://titan.dcs.bbk.ac.uk/~carsten/papers/FSCD2025-innermost-dps-lcstrs.pdf> An Innermost DP Framework for Constrained
Higher-Order Rewriting

What about specializing LPO to string f(f(f(x)))
x,y,z is obvious

f(f(x)) , g(x)
f(x) g(x)

x = x
f(x) > x
g(x) > x
f(x) > g(x)
x >? g(x) No
f(x) <? x No

f > g
f(x) > g(x)

x > y
f(x) > f(y)
x >? f(y)
x <? y  No

f(x) > y

We kind of ask for all possible pairs of subterms whether they can be compared
subterms(t), subterms(s)

if is_const(x) :
    use const order

f(t) = g(s)

Can g(s) be a subterm of t and also f(t) a subterm of s. No. But why.

sub_s, sub_t = subterms(s), subterms(t)

All the comparisons have to go the wrong way

LPO kind of likes pushing symbols downwards.
We can grow a lot to pay for a swap.

It doesn't push stuff down so much as it vastly prefers having big symbols receiving smaller subterms
You can pay for reducing the argument to the biggest symbol by adding nearly anything else made out of smaller symbols above that term
it does make sense to think of lpo ordering as being related to call graph
acrpo is some kind of language with ac matching?

For strings, it would

In strings, substrings on the right are much worse than substrings on the left.

Look again at original desrhiwitz paper.
<https://www.sciencedirect.com/science/article/pii/0304397582900263> Orderings for term Rewrite systems
Dershowtiz and jouannaod <https://www.sciencedirect.com/science/chapter/edited-volume/abs/pii/B9780444880741500111>

Extracting an rpo least term? Does this fix shachar's issue?
Efficient extraction may require monotonicity (compositionality) and well founded ness. subterm property?

I think kind of LPO compares by saying "the argument to the worst symbol is decreasing"

ac
ab

What is it I don't understand about my presentation of Miller.
The connection back to lambda

Transfer my open_binder and close into arip
I'm not an umber i'm a free variable has a scoped notion of name.
I guess de bruijn levels does make a kind of sense from that perspective.

```python
from hypothesis import given, strategies as st

strs = st.text(alphabet=["a", "b", "c", "d"], max_size=12)
strs.example()

from enum import Enum
class Order(Enum):
    LT = -1
    EQ = 0
    GT = 1

def str_lpo(s, t):
    if s == t:
        return Order.EQ
    elif s == "":
        return Order.LT
    elif t == "":
        return Order.GT
    cond1 = str_lpo(s[1:], t) in [Order.GT, Order.EQ]
    cond2 = str_lpo(s, t[1:]) in [Order.LT, Order.EQ]
    assert not (cond1 and cond2), "Something is awry"
    if cond1:
        return Order.GT
    elif cond2:
        return Order.LT
    else:
        if s[0] < t[0]:
            return Order.LT
        elif s[0] > t[0]:
            return Order.GT
        else:
            return str_lpo(s[1:], t[1:])

@given(strs,strs)
def test_is_integer(a,b):
    #print(f"called with {a,b}")
    str_lpo(a,b)

@given(strs,strs)
def test_symm(a,b):
    #print(f"called with {a,b}")
    res1 = str_lpo(a,b)
    res2 = str_lpo(b,a)
    assert res1 == Order(-res2.value)

@given(strs,strs)
def test_refl(a,b):
    #print(f"called with {a,b}")
    res1 = str_lpo(a,b)
    assert (a == b) == (res1 == Order.EQ)

@given(strs,strs,strs)
def test_trans(a,b,c):
    #print(f"called with {a,b,c}")
    res1 = str_lpo(a,b)
    res2 = str_lpo(b,c)
    res3 = str_lpo(a,c)
    if res1 == Order.LT and res2 == Order.LT:
        assert res3 == Order.LT
    elif res1 == Order.GT and res2 == Order.GT:
        assert res3 == Order.GT

# test_wellfounded?
test_trans()

```

    ---------------------------------------------------------------------------

    DeadlineExceeded                          Traceback (most recent call last)

    Cell In[12], line 62
         60     elif res1 == Order.GT and res2 == Order.GT:
         61         assert res3 == Order.GT
    ---> 62 test_trans()


    Cell In[12], line 53, in test_trans()
         49     res1 = str_lpo(a,b)
         50     assert (a == b) == (res1 == Order.EQ)
         52 @given(strs,strs,strs)
    ---> 53 def test_trans(a,b,c):
         54     #print(f"called with {a,b,c}")
         55     res1 = str_lpo(a,b)
         56     res2 = str_lpo(b,c)


        [... skipping hidden 1 frame]


    File ~/philzook58.github.io/.venv/lib/python3.12/site-packages/hypothesis/core.py:920, in StateForActualGivenExecution.execute_once.<locals>.test(*args, **kwargs)
        918         current_deadline = (current_deadline // 4) * 5
        919     if runtime >= current_deadline.total_seconds():
    --> 920         raise DeadlineExceeded(
        921             datetime.timedelta(seconds=runtime), self.settings.deadline
        922         )
        923 return result


    DeadlineExceeded: Test took 264.33ms, which exceeds the deadline of 200.00ms

    Falsifying example: test_trans(
        a='',
        b='aaaaaaaaaaa',
        c='aaaaaaaaaab',
    )

```python
def ground_string_lpo(s, t):
    ground_string_lpo(s[1:], t)
    ground_string_lpo(s, t[1:])
    if s[0] == t[0]:
        return ground_string_lpo(s[1:], t[1:]) # I'm not sure this tie break can be possible?

```

```python
from dataclasses import dataclass, field
import functools

@dataclass(frozen=True)
class App():
    f : str
    args : tuple["App", ...] = ()
    def __repr__(self):
        if self.args:
            return f"{self.f}({', '.join(repr(a) for a in self.args)})"
        else:
            return self.f


apps = st.recursive(
    st.builds(App, st.sampled_from(["a","b","c"])),
    lambda children: st.lists(children, min_size=2,max_size=2).flatmap( lambda c:
        st.sampled_from(["f","g"]).map( lambda f:
         App(f, tuple(c)))))
apps.example()

@functools.cache
def ground_lpo(t : App, s : App):
    if t == s:
        return Order.EQ
    cond1 = any(ground_lpo(a, s) in [Order.GT, Order.EQ] for a in t.args)
    cond2 = any(ground_lpo(t, b) in [Order.LT, Order.EQ] for b in s.args)
    assert not (cond1 and cond2)
    if cond1:
        return Order.GT
    elif cond2:
        return Order.LT
    else:
        if (t.f, len(t.args)) > (s.f, len(s.args)):
            return Order.GT
        elif (t.f, len(t.args)) < (s.f, len(s.args)):
            return Order.LT
        else:
            for a,b in zip(t.args, s.args):
                res = ground_lpo(a,b)
                if res != Order.EQ:
                    return res
            else:
                raise ValueError("Unreachable")

@given(apps, apps)
def test_ground_lpo(t,s):
    print(s,t)
    res1 = ground_lpo(t,s)
    res2 = ground_lpo(s,t)
    assert res1 == Order(-res2.value)

@given(apps, apps)
def test_ground_refl(t,s):
    res1 = ground_lpo(t,s)
    assert (t == s) == (res1 == Order.EQ)
@given(apps, apps, apps)
def test_ground_trans(t,s,u):
    res1 = ground_lpo(t,s)
    res2 = ground_lpo(s,u)
    res3 = ground_lpo(t,u)
    if res1 == Order.LT and res2 == Order.LT:
        assert res3 == Order.LT
    elif res1 == Order.GT and res2 == Order.GT:
        assert res3 == Order.GT

for i in range(10):
    test_ground_lpo()
    test_ground_refl()
    test_ground_trans()

```

    a a
    a f(a, a)
    f(f(c, b), f(f(b, a), g(b, a))) f(f(f(a, b), g(b, f(c, b))), f(f(b, g(b, b)), f(b, a)))
    a f(f(a, a), a)
    g(b, b) g(f(g(f(b, b), f(b, a)), f(c, f(c, c))), f(f(a, g(g(b, a), f(b, b))), g(g(a, b), g(c, b))))
    a f(a, a)
    f(f(g(b, g(b, a)), c), g(c, f(a, b))) f(a, a)
    a f(a, a)
    f(c, b) g(g(b, b), c)
    a f(b, a)
    g(b, c) f(b, c)
    f(b, c) f(b, c)
    g(b, f(g(b, a), g(b, f(b, b)))) g(a, c)
    g(b, f(g(b, a), g(f(b, b), f(b, b)))) g(a, c)
    g(f(g(b, a), g(f(b, b), f(b, b))), f(g(b, a), g(f(b, b), f(b, b)))) g(a, c)
    g(f(g(b, a), g(b, a)), f(g(b, a), g(f(b, b), f(b, b)))) g(a, c)
    f(f(g(b, a), g(f(b, b), f(b, b))), g(g(b, a), g(f(b, b), f(b, b)))) g(a, c)
    f(f(g(b, a), g(f(b, b), f(b, b))), g(g(f(b, b), f(b, b)), g(f(b, b), f(b, b)))) g(a, c)
    f(g(g(b, a), f(g(b, b), b)), g(b, a)) g(a, c)
    g(f(a, c), f(g(a, c), a)) c
    g(f(a, c), f(g(a, c), c)) c
    g(f(a, c), f(g(a, c), c)) g(f(a, c), f(g(a, c), c))
    g(f(a, c), f(g(a, c), c)) g(f(a, c), f(g(c, c), c))
    g(f(a, c), f(g(a, c), c)) g(f(a, c), f(a, c))
    g(f(g(a, c), c), f(g(a, c), c)) g(f(a, c), f(a, c))
    g(f(g(a, c), c), f(c, c)) g(f(a, c), f(a, c))
    g(f(b, a), c) g(f(c, a), f(f(g(c, a), b), f(a, b)))
    g(f(b, a), c) g(f(c, a), f(f(a, b), f(a, b)))
    g(f(b, a), c) g(f(f(a, b), f(a, b)), f(f(a, b), f(a, b)))
    g(f(b, a), c) g(f(b, a), c)
    g(f(b, a), c) g(f(a, a), c)
    g(f(b, a), c) g(f(b, a), a)
    g(f(f(g(a, c), c), g(a, c)), a) f(g(b, g(f(c, b), g(f(b, a), f(c, b)))), g(f(b, a), f(b, c)))
    g(f(f(g(a, c), c), g(a, c)), a) f(g(b, g(f(c, b), g(f(c, b), f(c, b)))), g(f(b, a), f(b, c)))
    f(g(b, g(f(c, b), g(f(c, b), f(c, b)))), g(f(b, a), f(b, c))) f(g(b, g(f(c, b), g(f(c, b), f(c, b)))), g(f(b, a), f(b, c)))
    f(g(b, g(f(c, b), g(f(c, b), f(c, b)))), g(f(b, a), f(b, c))) f(g(b, b), g(f(b, a), f(b, c)))
    f(g(b, b), g(f(b, a), f(b, c))) f(g(b, b), g(f(b, a), f(b, c)))
    g(f(b, a), f(b, c)) f(g(b, b), g(f(b, a), f(b, c)))
    g(f(f(c, b), g(b, a)), f(f(a, b), f(f(b, f(a, c)), g(g(c, c), a)))) g(a, a)
    g(f(f(c, b), g(b, a)), f(f(a, b), f(f(b, f(a, b)), g(g(c, c), a)))) g(a, a)
    f(f(f(c, b), g(b, a)), f(f(a, b), f(f(b, g(b, c)), g(b, a)))) g(a, a)
    f(f(f(c, b), f(c, b)), f(f(a, b), f(f(b, g(b, c)), g(b, a)))) g(a, a)
    f(f(f(c, b), f(c, b)), f(f(a, b), f(a, b))) g(a, a)
    g(a, a) g(a, a)
    g(a, a) g(a, b)
    g(c, a) g(c, c)
    g(c, c) g(c, c)
    g(c, c) g(c, c)
    g(f(a, a), c) f(a, c)
    g(f(a, a), c) g(f(a, a), c)
    g(b, f(f(b, b), c)) f(g(a, g(b, a)), f(g(c, c), b))
    g(b, f(f(b, b), c)) f(g(a, g(b, a)), g(a, g(b, a)))
    g(b, f(f(b, b), c)) f(g(a, g(b, a)), g(a, g(b, b)))
    g(b, f(f(b, b), c)) f(g(a, g(b, a)), g(b, g(b, b)))
    g(b, f(c, c)) f(g(a, g(b, a)), g(b, g(b, b)))
    g(b, f(c, c)) f(g(a, g(b, a)), g(b, g(b, a)))
    g(b, f(c, c)) f(g(b, g(b, a)), g(b, g(b, a)))
    g(g(a, b), g(a, a)) f(g(f(f(b, f(c, b)), f(f(c, c), f(b, g(a, b)))), g(b, c)), g(b, c))
    g(b, c) g(f(f(f(b, f(c, b)), f(f(c, c), f(b, g(a, b)))), c), g(a, c))
    g(b, c) g(b, c)
    g(c, c) g(b, c)
    g(c, c) g(c, c)
    g(f(b, c), b) g(f(g(g(g(a, c), a), g(c, b)), f(a, b)), f(f(g(a, c), f(a, b)), g(f(g(a, c), a), b)))
    f(b, b) f(f(g(g(g(a, c), a), g(c, b)), f(a, b)), g(f(g(a, c), f(c, b)), g(a, a)))
    f(b, b) f(f(g(g(g(a, c), a), g(c, b)), f(a, b)), g(f(g(a, b), f(c, b)), g(a, a)))
    f(b, b) f(f(g(g(g(b, c), a), g(c, b)), f(a, b)), g(f(g(a, b), f(c, b)), g(a, a)))
    f(b, b) f(f(g(g(g(b, c), a), g(c, b)), f(g(c, b), b)), g(f(g(a, b), f(c, b)), g(a, a)))
    f(b, b) f(f(g(g(g(b, c), g(b, c)), g(c, b)), f(g(c, b), b)), g(f(g(a, b), f(c, b)), g(a, a)))
    f(b, b) f(f(g(g(g(b, c), g(b, c)), g(c, b)), f(g(c, b), b)), g(g(g(g(b, c), g(b, c)), g(c, b)), f(g(c, b), b)))
    f(g(b, f(f(c, b), b)), b) g(f(a, g(a, a)), c)
    f(g(b, f(f(a, g(a, a)), c)), b) g(f(a, g(a, a)), c)
    f(g(b, f(f(a, g(a, a)), c)), b) f(g(b, f(f(a, g(a, a)), c)), b)
    f(f(b, f(a, b)), f(a, a)) f(g(b, f(f(a, g(a, a)), c)), b)
    f(f(b, f(a, b)), f(a, a)) f(g(b, b), b)
    f(f(b, f(a, b)), f(a, a)) f(g(b, f(a, b)), b)
    f(f(b, f(a, b)), f(a, a)) f(g(b, f(b, b)), b)
    f(c, c) g(a, a)
    f(c, c) f(c, c)
    f(c, c) f(c, b)
    f(c, c) f(b, b)
    f(b, a) f(f(f(a, b), g(b, c)), f(g(f(c, a), c), c))
    f(b, a) f(b, a)
    b f(b, a)
    b b
    a b
    b g(b, b)
    g(b, b) g(b, b)
    g(a, f(a, b)) g(f(g(b, c), c), g(f(c, b), g(a, a)))
    f(c, a) g(f(g(b, c), c), g(f(c, b), f(a, a)))
    f(c, b) f(f(b, b), f(a, c))
    f(f(b, b), f(a, c)) f(f(b, b), f(a, c))
    f(f(g(a, a), c), g(g(c, c), g(a, b))) g(b, c)
    f(f(c, c), g(g(c, c), g(a, b))) g(b, c)
    f(g(g(c, c), g(a, b)), g(g(c, c), g(a, b))) g(b, c)
    f(g(g(c, c), g(a, b)), g(g(c, c), g(a, b))) f(g(g(c, c), g(a, b)), g(g(c, c), g(a, b)))
    f(g(g(c, c), g(a, b)), g(g(a, b), g(a, b))) f(g(g(c, c), g(a, b)), g(g(c, c), g(a, b)))
    f(g(g(c, c), g(a, b)), g(g(a, b), g(a, b))) f(g(g(c, c), g(a, b)), g(g(a, c), g(a, b)))
    f(g(g(c, c), g(a, b)), g(g(a, b), g(a, b))) f(g(g(c, c), g(a, b)), g(g(a, b), g(a, b)))
    c f(a, g(g(c, b), f(a, a)))
    c f(a, g(g(c, b), f(a, c)))
    a a
    a f(a, a)
    g(g(f(b, a), f(g(c, c), c)), g(f(b, b), f(a, f(b, a)))) g(f(g(a, c), g(c, c)), f(b, b))
    a b
    g(a, g(a, c)) b
    a f(a, a)
    f(g(b, a), g(f(a, c), f(g(b, b), f(a, c)))) g(f(g(a, c), g(b, a)), f(c, f(c, a)))
    a f(f(a, a), a)
    f(g(b, g(b, b)), g(f(a, a), g(b, c))) f(f(c, f(c, b)), g(f(g(a, a), g(a, c)), g(b, a)))
    a f(a, a)
    g(g(b, b), g(c, f(a, b))) g(g(f(g(c, c), b), c), g(g(c, a), f(b, f(c, a))))
    g(g(b, b), g(c, f(a, b))) g(g(b, b), g(c, f(a, b)))
    g(g(b, b), g(c, f(a, b))) g(g(b, b), g(c, f(a, a)))
    g(g(b, b), g(c, f(a, a))) g(g(b, b), g(c, f(a, a)))
    g(b, b) f(b, f(a, g(g(b, b), b)))
    a f(a, b)
    f(a, b) f(a, b)
    f(a, b) f(a, a)
    f(a, a) f(a, a)
    a f(a, a)
    a g(f(a, f(a, c)), b)
    g(f(a, f(a, c)), b) g(f(a, f(a, c)), b)
    g(b, b) g(f(a, f(a, c)), b)
    f(f(a, b), g(a, b)) g(f(a, f(a, c)), b)
    f(f(a, b), f(a, f(a, c))) g(f(a, f(a, c)), b)
    f(f(a, b), f(a, f(a, c))) f(f(a, b), f(a, f(a, c)))
    f(f(f(a, c), b), f(a, f(a, c))) f(f(a, b), f(a, f(a, c)))
    g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(a, a))))), f(f(b, a), f(c, b))) b
    g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(a, a))))), f(f(b, a), f(c, b))) g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(a, a))))), f(f(b, a), f(c, b)))
    g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b))) g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(a, a))))), f(f(b, a), f(c, b)))
    g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b))) g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b)))
    g(g(c, g(f(f(f(b, c), g(c, c)), f(a, b)), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b))) g(g(c, g(f(a, g(f(a, a), f(b, c))), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b)))
    g(g(c, g(f(a, g(f(a, a), f(b, c))), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b))) g(g(c, g(f(a, g(f(a, a), f(b, c))), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b)))
    g(f(c, g(f(a, g(f(a, a), f(b, c))), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b))) g(g(c, g(f(a, g(f(a, a), f(b, c))), f(a, g(f(a, a), f(b, c))))), f(f(b, a), f(c, b)))
    f(g(b, g(a, b)), f(g(c, c), a)) f(g(g(c, a), c), a)
    f(g(g(c, a), c), f(g(c, c), a)) f(g(g(c, a), c), a)
    f(g(b, c), a) f(g(g(c, a), c), a)
    f(g(b, c), a) f(g(g(c, a), c), g(g(c, a), c))
    f(g(g(c, a), c), g(g(c, a), c)) f(g(g(c, a), c), g(g(c, a), c))
    f(g(g(c, a), c), g(g(c, a), c)) f(g(g(c, a), c), g(g(c, a), g(c, a)))
    f(g(g(c, a), c), g(g(c, a), g(c, a))) f(g(g(c, a), c), g(g(c, a), g(c, a)))
    g(a, f(g(f(a, b), c), f(f(b, b), c))) c
    g(a, f(f(f(b, b), c), f(f(b, b), c))) c
    g(a, a) c
    f(a, a) c
    f(a, a) f(a, a)
    g(g(f(f(a, c), f(b, b)), g(c, a)), b) f(f(a, b), c)
    f(f(a, b), c) f(f(a, b), c)
    f(f(a, b), f(a, a)) f(f(a, b), c)
    f(f(a, b), c) f(c, c)
    f(g(a, c), a) f(c, c)
    f(g(a, c), a) f(a, c)
    g(g(c, f(a, g(c, b))), f(f(a, a), g(f(c, b), f(c, b)))) f(c, g(b, c))
    g(g(c, f(a, g(c, b))), f(f(a, a), g(f(c, b), f(c, b)))) f(c, g(b, b))
    g(g(c, f(a, g(c, b))), f(f(a, a), f(a, a))) f(c, g(b, b))
    f(c, g(b, b)) f(c, g(b, b))
    f(c, g(b, b)) f(c, g(b, b))
    f(c, c) f(c, g(b, b))
    f(c, g(b, b)) f(c, g(b, b))
    f(f(g(f(a, f(c, b)), b), g(c, g(b, c))), g(g(b, c), g(a, b))) g(f(b, b), f(f(g(b, b), b), f(f(b, b), g(a, a))))
    f(f(g(f(a, f(c, b)), b), g(f(a, f(c, b)), b)), g(g(b, c), g(a, b))) g(f(b, b), f(f(g(b, b), b), f(f(b, b), g(a, a))))
    f(f(g(f(a, f(c, b)), b), g(f(a, f(b, b)), b)), g(g(b, c), g(a, b))) g(f(b, b), f(f(g(b, b), b), f(f(b, b), g(a, a))))
    f(f(g(f(a, g(b, c)), b), g(f(a, f(b, b)), b)), g(g(b, c), g(a, b))) g(f(b, b), f(f(g(b, b), b), f(f(b, b), g(a, a))))
    f(f(g(f(a, g(b, c)), b), g(f(a, f(b, b)), b)), f(g(b, b), b)) g(f(b, b), f(f(g(b, b), b), f(f(b, b), g(a, a))))
    f(f(g(f(a, g(b, c)), b), g(f(a, f(b, b)), b)), f(g(b, b), b)) g(f(b, b), f(f(g(b, b), b), b))
    f(f(g(f(g(b, b), b), b), g(f(a, f(b, b)), b)), f(g(b, b), b)) g(f(b, b), f(f(g(b, b), b), b))
    c f(f(f(b, f(b, b)), c), f(c, c))
    c f(f(f(b, f(b, b)), c), f(b, c))
    f(f(f(b, f(b, b)), c), f(b, c)) f(f(f(b, f(b, b)), c), f(b, c))
    f(f(c, c), f(b, c)) f(f(f(b, f(b, b)), c), f(b, c))
    f(f(c, c), f(b, c)) f(f(c, c), f(b, c))
    g(g(f(a, g(c, b)), f(a, a)), g(f(a, c), g(b, c))) g(g(b, b), g(b, a))
    g(g(f(a, g(c, b)), f(a, a)), g(f(a, c), g(b, c))) g(g(b, a), g(b, a))
    g(g(f(a, g(c, b)), f(a, a)), g(f(a, c), g(b, c))) g(g(b, g(c, b)), g(b, a))
    g(g(f(a, g(c, b)), f(a, g(c, b))), g(f(a, c), g(b, c))) g(g(b, g(c, b)), g(b, a))
    g(g(f(b, g(c, b)), f(a, g(c, b))), g(f(a, c), g(b, c))) g(g(b, g(c, b)), g(b, a))
    g(g(f(b, g(c, b)), f(a, g(a, c))), g(f(a, c), g(b, c))) g(g(b, g(c, b)), g(b, a))
    g(g(f(b, g(c, b)), f(b, g(c, b))), g(f(a, c), g(b, c))) g(g(b, g(c, b)), g(b, a))
    g(f(b, g(c, a)), f(g(b, b), f(c, c))) f(f(c, a), g(f(a, a), g(a, b)))
    g(f(b, g(c, a)), f(g(b, b), g(b, b))) f(f(c, a), g(f(a, a), g(a, b)))
    g(f(b, g(b, a)), f(g(b, b), g(b, b))) f(f(c, a), g(f(a, a), g(a, b)))
    g(f(b, g(b, a)), f(g(b, b), g(b, b))) f(f(c, a), g(f(b, a), g(a, b)))
    g(f(c, a), f(g(b, b), g(b, b))) f(f(c, a), g(f(b, a), g(a, b)))
    g(f(c, a), f(g(b, b), g(b, b))) f(f(c, c), g(f(b, a), g(a, b)))
    g(f(c, a), f(g(b, b), g(b, b))) f(f(c, c), g(g(a, b), g(a, b)))
    f(g(g(a, b), f(a, c)), b) g(f(c, g(f(b, b), c)), g(a, b))
    f(g(g(a, b), f(a, c)), b) g(f(c, g(f(b, b), f(b, b))), g(a, b))
    f(g(g(a, b), f(a, c)), b) g(f(c, c), g(a, b))
    f(g(g(a, b), f(a, c)), b) g(f(b, c), g(a, b))
    f(g(g(a, b), f(a, c)), b) g(g(g(a, b), f(a, c)), b)
    f(g(g(a, b), f(a, c)), b) g(g(g(a, b), f(b, c)), b)
    f(g(g(a, b), f(a, c)), b) g(g(g(a, b), f(a, b)), b)
    g(a, b) a
    g(a, b) g(a, b)
    g(b, b) g(a, b)
    g(b, b) f(a, b)
    g(b, b) f(b, b)
    g(b, b) g(b, b)
    f(b, b) g(b, b)
    g(g(b, c), f(f(a, b), f(a, a))) g(a, f(g(c, a), g(g(c, c), f(b, a))))
    a a
    a f(a, a)
    g(g(b, b), g(f(g(c, b), a), a)) f(g(b, c), b)
    a f(a, a)
    g(f(c, g(c, a)), f(b, c)) f(g(b, c), g(b, a))
    a c
    g(f(c, c), g(b, a)) c
    a b
    f(g(a, b), g(c, a)) b
    a f(a, a)
    f(f(b, a), c) f(f(g(b, c), g(a, b)), f(a, c))
    f(f(b, a), c) f(f(a, c), f(a, c))
    f(b, a) f(f(a, c), f(a, c))
    f(a, a) f(f(a, c), f(a, c))
    f(a, a) f(a, a)
    g(f(g(a, c), a), f(f(b, a), f(f(b, a), f(g(b, a), b)))) b
    g(f(g(b, c), a), f(f(b, a), f(f(b, a), f(g(b, a), b)))) b
    g(f(f(b, a), f(f(b, a), f(g(b, a), b))), f(f(b, a), f(f(b, a), f(g(b, a), b)))) b
    g(f(f(b, a), f(f(b, a), f(g(b, a), b))), f(f(b, a), f(f(b, a), f(g(b, a), b)))) g(f(f(b, a), f(f(b, a), f(g(b, a), b))), f(f(b, a), f(f(b, a), f(g(b, a), b))))
    f(f(g(c, a), c), g(b, b)) g(f(f(a, a), b), g(f(c, c), g(b, c)))
    f(f(g(c, a), c), g(b, b)) g(f(b, b), g(f(c, c), g(b, c)))
    f(f(g(c, a), c), g(b, b)) g(f(b, b), g(f(g(c, a), c), g(b, b)))
    g(g(f(c, b), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c)))), g(g(g(a, b), f(c, a)), g(c, b))) f(g(a, c), a)
    g(g(f(c, b), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c)))), g(f(c, b), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c))))) f(g(a, c), a)
    g(g(f(b, c), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c)))), g(f(c, b), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c))))) f(g(a, c), a)
    g(g(f(b, c), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c)))), g(f(b, c), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c))))) f(g(a, c), a)
    g(g(f(b, c), f(g(f(a, f(b, c)), f(b, c)), g(f(a, f(b, c)), f(b, c)))), g(f(b, c), f(f(f(g(a, c), f(c, a)), c), g(f(a, f(b, c)), f(b, c))))) f(g(a, c), a)
    f(f(f(b, c), f(g(f(a, f(b, c)), f(b, c)), g(a, b))), a) f(g(a, c), a)
    f(f(f(b, c), f(g(f(a, f(b, c)), f(b, c)), g(a, b))), a) f(a, f(b, c))
    g(g(c, g(a, c)), g(a, b)) g(a, b)
    g(g(c, g(a, c)), g(c, g(a, c))) g(a, b)
    g(g(c, g(a, c)), g(c, g(a, c))) g(g(c, g(a, c)), g(c, g(a, c)))
    a f(g(c, f(b, f(c, a))), b)
    a f(g(f(b, f(c, a)), f(b, f(c, a))), b)
    a f(b, b)
    f(g(a, c), g(a, c)) b
    b b
    b a
    g(b, b) f(f(f(a, a), f(b, a)), g(b, c))
    g(b, b) f(f(f(a, b), f(b, a)), g(b, c))
    g(a, b) f(f(f(a, b), f(b, a)), g(b, c))
    g(a, b) f(f(f(b, a), f(b, a)), g(b, c))
    g(a, b) g(a, b)
    g(a, b) g(b, b)
    g(a, b) g(b, a)
    f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, a)), c)) g(f(b, f(a, b)), g(g(a, c), g(c, a)))
    f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, a)), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, a)), c))
    f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, a)), c))
    f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c))
    f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(a, b), c))
    f(g(f(f(a, b), f(b, g(a, a))), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(a, b), c))
    f(g(f(f(a, b), f(b, g(a, a))), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), c)) f(g(f(g(c, a), f(a, b)), f(g(a, c), g(a, a))), f(f(f(a, b), f(b, g(a, a))), f(g(a, c), g(a, a))))
    g(b, b) g(c, c)
    g(b, b) g(c, a)
    g(b, a) g(c, a)
    g(c, a) g(c, a)
    g(c, c) g(c, a)
    g(c, a) g(c, c)
    g(c, a) g(a, a)
    f(f(b, g(f(c, a), f(a, a))), f(f(b, b), c)) g(f(f(c, b), f(b, a)), g(g(b, b), a))
    f(f(g(f(c, a), f(a, a)), g(f(c, a), f(a, a))), f(f(b, b), c)) g(f(f(c, b), f(b, a)), g(g(b, b), a))
    f(f(g(f(c, a), f(a, a)), g(f(c, a), f(a, a))), f(f(b, b), c)) g(f(f(c, b), f(b, a)), f(f(c, b), f(b, a)))
    f(f(g(f(c, a), f(a, a)), g(f(c, a), f(a, a))), f(g(f(c, a), f(a, a)), g(f(c, a), f(a, a)))) g(f(f(c, b), f(b, a)), f(f(c, b), f(b, a)))
    g(f(f(c, b), f(b, a)), f(f(c, b), f(b, a))) g(f(f(c, b), f(b, a)), f(f(c, b), f(b, a)))
    g(f(f(c, b), f(b, a)), f(f(c, b), f(c, b))) g(f(f(c, b), f(b, a)), f(f(c, b), f(b, a)))
    g(f(f(c, b), f(b, a)), f(f(c, b), f(c, b))) g(f(f(c, b), f(b, a)), f(f(c, b), f(c, b)))
    f(f(a, a), a) f(a, c)
    f(f(a, c), a) f(a, c)
    f(f(a, c), a) f(f(a, c), a)
    f(f(a, c), a) f(f(a, c), f(a, c))
    f(a, c) f(f(a, c), f(c, a))
    f(a, c) f(f(a, a), f(c, a))
    f(a, c) f(f(a, a), f(a, a))
    c f(f(c, b), f(b, c))
    c c
    f(g(c, b), a) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, f(b, c)), g(g(a, c), g(a, c)))), f(b, b)))
    f(g(c, b), a) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c)))), f(b, b)))
    f(g(c, b), a) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c)))), f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c))))))
    f(g(c, b), a) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c)))), f(g(c, a), f(g(a, g(a, c)), g(g(a, c), g(a, c))))))
    f(g(c, b), g(c, b)) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c)))), f(g(c, a), f(g(a, g(a, c)), g(g(a, c), g(a, c))))))
    f(g(c, b), g(c, b)) g(g(f(b, g(b, c)), b), f(f(g(c, a), f(g(a, g(b, c)), g(g(a, c), g(a, c)))), f(g(c, a), g(c, a))))
    g(b, b) f(c, a)
    b f(c, a)
    b f(c, b)
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) g(g(g(g(c, b), c), f(c, c)), g(f(b, a), g(g(a, b), a)))
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) g(g(g(g(c, b), a), f(c, c)), g(f(b, a), g(g(a, b), a)))
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) g(g(g(g(c, b), a), f(c, c)), g(f(b, a), g(g(a, b), b)))
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) g(g(g(g(c, b), a), f(c, c)), g(f(b, a), g(g(b, a), b)))
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) f(f(c, g(a, b)), g(f(f(b, b), c), c))
    f(f(c, c), g(f(f(b, b), c), c)) f(f(c, g(a, b)), g(f(f(b, b), c), c))
    f(f(c, g(a, b)), g(f(f(b, b), c), c)) f(f(c, g(a, b)), g(f(f(a, b), c), c))
    f(g(a, a), f(f(c, b), b)) f(b, a)
    f(g(b, a), f(f(c, b), b)) f(b, a)
    f(f(c, b), f(f(c, b), b)) f(b, a)
    f(f(c, b), f(f(c, b), f(c, b))) f(b, a)
    f(f(c, b), f(f(c, b), f(c, b))) f(c, a)
    f(f(f(c, b), f(c, b)), f(f(c, b), f(c, b))) f(c, a)
    g(g(b, b), f(a, b)) g(c, g(a, c))
    g(g(b, b), f(a, b)) g(b, g(a, c))
    g(g(b, b), f(a, a)) g(b, g(a, c))
    a a
    a f(a, a)
    g(f(b, f(b, f(c, b))), f(g(a, c), a)) f(f(f(b, a), g(c, a)), f(a, f(a, a)))
    a f(a, a)
    g(g(g(c, a), g(c, b)), g(g(b, c), g(c, b))) f(g(a, b), g(a, c))
    a f(a, a)
    a f(g(f(c, a), b), g(f(g(c, b), f(b, c)), g(g(a, c), g(c, c))))
    a f(c, a)
    g(a, a) f(c, g(a, a))
    a f(b, a)
    g(g(a, b), g(b, c)) f(b, g(f(c, a), g(g(b, a), g(a, b))))
    g(g(a, b), g(b, c)) f(g(f(c, a), g(g(b, a), g(a, b))), g(f(c, a), g(g(b, a), g(a, b))))
    g(g(a, b), g(b, c)) f(g(f(c, a), g(g(b, a), g(a, b))), g(f(c, b), g(g(b, a), g(a, b))))
    g(g(a, b), g(b, c)) f(g(f(c, b), g(g(b, a), g(a, b))), g(f(c, b), g(g(b, a), g(a, b))))
    g(g(b, a), g(a, b)) f(f(g(g(b, a), g(a, b)), f(a, c)), b)
    a f(g(g(f(b, b), g(b, a)), g(b, a)), f(b, a))
    a f(g(g(f(b, b), g(b, a)), g(f(b, b), g(b, a))), f(b, a))
    f(g(c, a), f(g(a, b), c)) f(f(c, b), f(b, b))
    f(g(c, a), f(g(b, b), c)) f(f(c, b), f(b, b))
    f(g(c, c), f(g(b, b), c)) f(f(c, b), f(b, b))
    f(g(c, c), f(g(b, b), c)) f(g(c, c), f(g(b, b), c))
    f(g(c, b), f(g(b, b), c)) f(g(c, c), f(g(b, b), c))
    f(b, a) g(g(c, c), b)
    a f(g(a, a), g(c, a))
    f(b, a) c
    f(b, a) f(b, a)
    f(b, a) f(a, a)
    f(b, a) f(b, b)
    g(b, a) f(b, a)
    g(b, a) f(b, b)
    g(b, a) g(b, a)
    f(g(a, f(g(b, c), g(a, b))), g(a, b)) g(c, f(f(g(f(c, a), f(a, a)), f(b, b)), f(g(a, c), f(b, f(b, b)))))
    a f(c, g(g(g(f(a, a), g(b, c)), b), b))
    a f(c, g(g(g(f(a, a), g(b, c)), b), g(g(f(a, a), g(b, c)), b)))
    f(c, g(g(g(f(a, a), g(b, c)), b), g(g(f(a, a), g(b, c)), b))) f(c, g(g(g(f(a, a), g(b, c)), b), g(g(f(a, a), g(b, c)), b)))
    f(c, g(g(g(f(b, c), g(b, c)), b), g(g(f(a, a), g(b, c)), b))) f(c, g(g(g(f(a, a), g(b, c)), b), g(g(f(a, a), g(b, c)), b)))
    f(f(c, a), g(f(b, c), g(b, c))) f(c, g(g(g(f(a, a), g(b, c)), b), g(g(f(a, a), g(b, c)), b)))
    a f(c, g(a, c))
    f(b, b) f(f(a, a), g(f(c, c), f(b, b)))
    f(b, b) f(g(f(c, c), f(b, b)), g(f(c, c), f(b, b)))
    f(b, b) f(g(f(b, b), f(b, b)), g(f(c, c), f(b, b)))
    f(g(f(c, c), f(b, b)), g(f(c, c), f(b, b))) f(g(f(c, c), f(b, b)), g(f(c, c), f(b, b)))
    f(b, b) f(b, c)
    f(b, c) f(b, c)
    f(b, c) f(c, c)
    f(a, c) g(f(a, g(c, a)), g(c, a))
    f(a, c) g(f(f(a, b), b), g(c, a))
    a f(f(f(a, b), b), a)
    a f(a, a)
    f(a, a) f(a, a)
    g(b, b) g(f(b, c), g(b, a))
    g(f(b, c), g(b, a)) g(f(b, c), g(b, a))
    g(f(b, c), g(b, a)) g(f(b, a), g(b, a))
    g(f(b, a), g(b, a)) g(f(b, a), g(b, a))
    g(f(f(b, b), c), f(g(c, a), g(c, c))) g(a, b)
    c f(a, a)
    c f(a, c)
    c f(c, c)
    c c
    a f(b, c)
    f(g(c, f(b, c)), f(c, b)) f(g(c, b), g(f(c, b), a))
    f(g(c, f(a, c)), f(c, b)) f(g(c, b), g(f(c, b), a))
    f(f(c, b), f(c, b)) f(g(c, b), g(f(c, b), a))
    f(f(c, b), f(c, b)) f(f(c, b), f(c, b))
    f(c, b) f(f(c, b), f(c, b))
    f(c, b) f(c, b)
    f(b, b) f(c, b)
    f(g(a, f(b, a)), c) f(g(f(b, c), a), f(f(b, b), f(c, g(a, b))))
    f(g(a, f(b, a)), c) f(g(a, f(b, a)), c)
    f(f(a, b), b) f(g(a, f(b, a)), c)
    f(f(a, a), b) f(g(a, f(b, a)), c)
    f(a, a) f(f(a, f(a, a)), b)
    f(a, a) f(b, b)
    f(a, b) f(b, b)
    f(f(g(a, a), f(a, a)), g(c, g(f(c, b), c))) f(g(b, c), g(g(a, a), g(g(c, c), c)))
    f(f(g(a, a), f(a, a)), g(c, g(f(a, a), c))) f(g(b, c), g(g(a, a), g(g(c, c), c)))
    f(f(g(a, a), f(a, a)), g(c, g(f(a, a), c))) f(g(a, c), g(g(a, a), g(g(c, c), c)))
    f(f(g(a, a), f(a, a)), g(c, g(f(a, a), c))) f(g(c, g(f(a, a), c)), g(g(a, a), g(g(c, c), c)))
    f(f(g(a, a), f(a, a)), g(c, g(f(a, a), c))) f(g(c, g(f(a, a), c)), g(g(a, a), g(a, a)))
    f(f(g(a, a), f(a, a)), f(g(a, a), f(a, a))) f(g(c, g(f(a, a), c)), g(g(a, a), g(a, a)))
    f(f(g(a, a), f(a, a)), f(g(a, a), f(a, a))) f(g(c, g(g(a, a), c)), g(g(a, a), g(a, a)))
    g(c, a) g(g(c, b), f(b, a))
    g(c, f(b, a)) g(g(c, b), f(b, a))
    g(g(c, b), f(b, a)) g(g(c, b), f(b, a))
    b f(c, g(b, b))
    b b
    a f(c, g(f(a, a), f(f(b, a), f(a, a))))
    a f(c, g(f(a, a), f(f(b, a), f(a, b))))
    a f(g(f(a, a), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b))))
    a f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b))))
    f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b)))) f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b))))
    f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(a, a), f(a, b)))) f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b))))
    f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(a, b), f(a, b)))) f(g(f(f(b, a), f(a, b)), f(f(b, a), f(a, b))), g(f(a, a), f(f(b, a), f(a, b))))
    g(g(b, f(c, f(b, a))), b) g(c, b)
    g(g(b, f(c, f(c, b))), b) g(c, b)
    g(g(b, f(c, f(c, c))), b) g(c, b)
    g(b, b) g(c, b)
    g(c, b) g(c, b)
    g(b, b) g(c, b)
    g(a, b) f(c, c)
    a a
    a f(a, a)
    g(f(b, f(c, b)), f(a, f(c, c))) f(c, g(b, b))
    a f(a, a)
    f(g(b, f(g(b, a), b)), a) g(g(f(g(c, b), b), g(b, f(a, c))), f(b, b))
    a b
    f(g(a, c), a) b
    a f(a, a)
    f(g(c, c), g(b, b)) g(g(c, b), c)
    a f(a, a)
    g(c, a) g(c, b)
    g(c, b) g(c, b)
    g(c, b) g(c, c)
    f(a, a) g(c, a)
    g(c, a) g(c, a)
    c f(a, b)
    c c
    g(b, a) f(g(g(f(a, c), f(c, a)), f(f(a, c), c)), f(c, g(a, a)))
    g(b, a) f(g(g(f(a, c), f(c, a)), f(f(a, c), f(c, a))), f(c, g(a, a)))
    g(b, a) g(b, a)
    g(a, a) g(b, a)
    g(a, a) g(a, a)
    c f(f(f(a, c), g(a, c)), a)
    a f(g(b, c), a)
    a f(g(b, c), g(b, c))
    f(g(b, c), g(b, c)) f(g(b, c), g(b, c))
    f(g(b, c), g(b, c)) f(g(c, c), g(b, c))
    f(g(c, c), g(b, c)) f(g(c, c), g(b, c))
    b f(f(f(g(a, c), f(f(a, b), a)), b), a)
    b f(f(f(g(a, c), f(f(a, c), a)), b), a)
    b f(f(f(f(f(a, c), a), f(f(a, c), a)), b), a)
    b f(f(f(f(a, a), f(f(a, c), a)), b), a)
    b f(f(f(f(a, a), f(f(a, c), b)), b), a)
    b f(f(f(f(a, b), f(f(a, c), b)), b), a)
    f(a, c) f(a, f(a, b))
    f(g(f(g(b, a), g(c, c)), f(b, c)), f(g(g(b, a), f(c, b)), f(f(b, a), a))) g(g(a, c), g(f(c, c), g(f(a, c), f(b, a))))
    f(g(a, c), g(f(c, c), g(f(a, c), f(b, a)))) g(g(a, c), g(f(c, c), g(f(a, c), f(b, a))))
    f(g(a, a), g(f(c, c), g(f(a, c), f(b, a)))) g(g(a, c), g(f(c, c), g(f(a, c), f(b, a))))
    g(g(a, c), g(f(c, c), g(f(a, c), f(b, a)))) g(g(a, c), g(f(c, c), g(f(a, c), f(b, a))))
    g(g(f(a, c), f(b, a)), g(f(c, c), g(f(a, c), f(b, a)))) g(g(a, c), g(f(c, c), g(f(a, c), f(b, a))))
    g(g(f(a, c), f(b, a)), g(f(c, c), g(f(a, c), f(b, a)))) g(g(a, c), g(f(c, c), f(c, c)))
    g(g(f(a, c), f(b, a)), g(f(c, c), g(f(a, c), f(b, c)))) g(g(a, c), g(f(c, c), f(c, c)))
    g(g(c, a), f(a, b)) f(a, c)
    g(f(a, b), f(a, b)) f(a, c)
    g(f(a, b), f(a, b)) f(a, a)
    g(f(b, b), f(a, b)) f(a, a)
    g(f(b, b), f(a, b)) g(f(b, b), f(a, b))
    g(f(a, b), f(a, b)) g(f(b, b), f(a, b))
    f(f(a, b), f(a, a)) g(f(b, b), f(a, b))
    f(c, b) f(g(a, g(b, b)), f(f(a, c), c))
    f(c, b) f(g(a, g(b, b)), f(f(a, c), a))
    f(c, b) f(g(a, g(a, b)), f(f(a, c), a))
    f(c, b) f(f(f(a, c), a), f(f(a, c), a))
    f(c, b) f(f(f(a, c), a), f(f(a, a), a))
    f(c, a) f(f(f(a, c), a), f(f(a, a), a))
    f(c, a) f(c, a)
    g(f(a, b), g(f(c, b), a)) f(b, b)
    g(f(a, b), g(f(b, b), a)) f(b, b)
    g(f(a, b), f(f(b, b), a)) f(b, b)
    f(b, b) f(b, b)
    g(a, a) f(f(c, f(c, c)), f(c, a))
    g(a, c) f(f(c, f(c, c)), f(c, a))
    a f(f(c, f(c, c)), f(a, a))
    f(f(c, f(c, c)), f(a, a)) f(f(c, f(c, c)), f(a, a))
    f(f(c, f(c, c)), f(a, a)) f(f(c, c), f(a, a))
    f(f(a, f(c, c)), f(a, a)) f(f(c, c), f(a, a))
    f(f(c, c), f(a, a)) f(f(c, c), f(a, a))
    g(g(a, g(c, a)), g(a, c)) f(b, a)
    b f(f(b, c), b)
    b f(f(c, c), b)
    b f(b, b)
    f(b, b) f(b, b)
    f(a, g(b, f(b, a))) b
    f(a, a) b
    a f(b, a)
    f(b, a) f(b, a)
    f(a, a) f(b, a)
    f(b, a) f(b, b)
    f(a, a) f(b, b)
    f(b, b) f(g(b, b), c)
    f(b, b) g(g(b, b), c)
    g(g(b, b), c) g(g(b, b), c)
    g(b, b) g(g(b, b), c)
    g(b, b) g(g(b, b), b)
    g(b, b) g(g(b, b), g(b, b))
    g(g(b, b), g(b, b)) g(g(b, b), g(b, b))
    c f(f(f(c, f(b, b)), f(b, a)), b)
    g(f(g(a, a), g(a, a)), c) b
    g(f(g(a, a), g(a, a)), a) b
    b b
    b a
    f(f(f(a, b), b), a) a
    f(f(f(a, b), b), b) a
    f(f(f(a, b), f(a, b)), b) a
    g(a, f(c, b)) g(f(g(f(a, a), b), g(a, b)), g(a, f(b, a)))
    g(a, f(c, b)) g(f(g(f(b, a), b), g(a, b)), g(a, f(b, a)))
    g(a, f(c, b)) g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, b)))
    g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, b))) g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, b)))
    g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, b))) g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, a)))
    g(f(g(f(b, a), b), g(f(b, a), b)), f(g(f(b, a), b), g(a, b))) g(f(g(f(b, a), b), g(a, b)), f(g(f(b, a), b), g(a, a)))
    a a
    a f(a, a)
    g(b, b) f(f(b, g(a, b)), f(g(f(b, b), f(a, c)), f(c, a)))
    a f(a, a)
    g(g(c, a), c) f(b, b)
    a b
    g(g(b, a), f(f(b, c), f(b, b))) b
    a f(a, a)
    g(f(b, f(c, f(b, c))), g(f(f(c, c), a), g(c, b))) f(f(f(a, f(a, c)), f(c, c)), f(f(b, f(c, c)), f(c, g(a, c))))
    a f(a, a)
    f(g(g(f(a, c), g(b, a)), g(b, g(c, b))), g(g(f(a, a), b), g(g(a, c), b))) f(c, g(c, a))
    f(c, g(c, a)) f(c, g(c, a))
    f(c, g(c, a)) f(c, g(c, c))
    f(g(c, a), g(b, b)) g(g(b, c), g(a, g(c, f(b, b))))
    f(g(b, b), g(b, b)) g(g(b, c), g(a, g(c, f(b, b))))
    g(a, b) g(f(a, a), g(c, f(b, b)))
    g(a, b) g(a, b)
    g(a, b) g(b, b)
    g(b, b) g(b, b)
    g(b, b) c
    g(b, b) g(b, b)
    c f(g(f(c, b), g(f(a, a), a)), f(b, c))
    c f(g(f(a, a), g(f(a, a), a)), f(b, c))
    c f(f(b, c), f(b, c))
    f(f(b, c), f(b, c)) f(f(b, c), f(b, c))
    f(f(c, a), f(a, c)) f(f(b, c), f(b, c))
    f(f(b, c), f(b, a)) f(f(b, c), f(b, c))
    g(a, a) f(f(b, c), b)
    g(g(f(b, c), c), f(c, c)) g(g(g(c, b), g(g(c, a), c)), f(f(f(g(a, c), f(f(b, a), a)), f(f(a, c), f(b, b))), f(f(c, g(b, a)), g(c, c))))
    b g(g(g(c, b), g(g(c, a), c)), f(f(f(g(a, c), f(f(b, a), a)), f(f(a, c), f(b, b))), g(a, b)))
    g(a, b) f(g(g(c, b), g(g(c, a), c)), f(g(f(g(a, c), f(f(b, a), a)), g(a, a)), f(b, b)))
    g(a, b) g(a, b)
    g(b, b) g(a, b)
    g(b, b) g(b, a)
    g(b, a) g(b, a)
    f(c, c) f(f(a, a), g(f(c, a), g(f(b, b), b)))
    g(a, a) g(f(a, a), g(f(c, a), c))
    a g(f(a, a), g(f(c, a), c))
    g(f(a, a), g(f(c, a), c)) g(f(a, a), g(f(c, a), c))
    b g(f(a, a), g(f(c, a), c))
    b g(f(a, a), g(c, c))
    b g(f(a, c), g(c, c))
    f(f(f(f(b, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))) f(g(g(b, c), b), a)
    f(f(f(f(b, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))) f(g(f(f(f(b, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))), a)
    f(f(f(f(b, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))) f(g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))), a)
    f(f(f(f(b, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))) f(g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))), g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))))
    f(f(a, c), f(a, b)) f(g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(a, c), f(a, b)), g(f(a, a), b))), f(f(f(f(c, b), a), g(b, a)), g(b, f(a, c))))
    f(f(a, c), f(a, b)) f(g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(c, b), g(b, a)), g(b, f(a, c)))), f(f(f(f(c, b), a), g(b, a)), g(b, f(a, c))))
    f(f(a, c), f(a, b)) f(g(f(f(f(c, b), g(b, a)), g(b, f(a, c))), f(f(f(c, b), g(b, a)), g(b, f(a, c)))), f(f(g(f(c, b), g(a, a)), b), g(b, f(a, c))))
    f(b, b) a
    g(b, f(b, b)) g(f(b, f(c, c)), f(f(c, a), f(c, b)))
    g(b, b) g(f(b, f(c, c)), f(f(c, a), f(c, b)))
    f(c, a) f(f(b, c), a)
    f(f(b, c), a) f(f(b, c), a)
    f(f(b, a), a) f(f(b, c), a)
    f(f(b, a), a) f(f(b, a), a)
    f(f(b, a), a) f(a, a)
    f(a, g(b, a)) a
    g(a, g(b, a)) a
    g(f(g(c, f(a, a)), f(c, c)), f(g(f(f(a, a), g(c, f(c, b))), c), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) f(g(b, a), g(c, g(a, a)))
    g(f(g(c, f(a, a)), f(c, c)), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) f(g(b, a), g(c, g(a, a)))
    g(f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) f(g(b, a), g(c, g(a, a)))
    g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) f(g(b, a), g(c, g(a, a)))
    g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))))
    g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a))))) g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(g(c, c), g(a, a)), f(g(c, c), g(a, a)))))
    g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(g(c, c), g(a, a)), f(g(c, c), g(a, a))))) g(f(g(f(f(a, a), g(c, g(a, a))), f(f(a, a), g(c, f(c, b)))), g(f(b, f(b, b)), f(g(c, c), g(a, a)))), f(g(f(f(a, a), g(c, f(c, b))), f(f(a, a), g(c, f(c, b)))), g(f(g(c, c), g(a, a)), f(g(c, c), g(a, a)))))
    a g(f(b, a), c)
    a g(f(b, a), f(b, a))
    a g(g(b, a), b)
    a g(a, g(a, c))
    a g(g(a, c), g(a, c))
    g(g(a, c), b) g(f(c, a), g(c, g(b, b)))
    g(g(a, b), b) g(f(c, a), g(c, g(b, b)))
    g(g(a, b), b) g(f(c, a), g(c, c))
    g(g(a, b), g(a, b)) g(f(c, a), g(c, c))
    g(f(c, a), g(c, c)) g(f(c, a), g(c, c))
    g(f(c, a), g(c, c)) g(f(c, a), g(c, a))
    g(f(c, a), g(c, a)) g(f(c, a), g(c, a))
    c g(b, a)
    b g(b, a)
    g(b, a) g(b, a)
    g(a, b) f(c, a)
    g(a, b) f(b, a)
    f(b, a) f(b, a)
    b f(b, a)
    b b
    f(f(f(b, a), f(f(b, c), f(c, b))), f(b, a)) g(g(c, b), f(a, b))
    f(f(f(b, a), f(f(c, c), f(c, b))), f(b, a)) g(g(c, b), f(a, b))
    g(g(c, b), f(a, b)) g(g(c, b), f(a, b))
    g(g(a, b), f(a, b)) g(g(c, b), f(a, b))
    g(b, a) g(f(b, g(b, a)), f(a, b))
    g(b, a) g(f(g(b, a), g(b, a)), f(a, b))
    g(f(g(b, a), g(b, a)), f(a, b)) g(f(g(b, a), g(b, a)), f(a, b))
    a f(g(a, b), g(c, a))
    f(g(g(c, c), f(c, b)), g(g(f(a, a), b), c)) g(f(f(a, b), b), a)
    f(g(g(c, c), f(c, b)), g(g(b, b), c)) g(f(f(a, b), b), a)
    f(g(g(c, c), f(c, b)), g(g(b, b), c)) f(g(g(c, c), f(c, b)), g(g(b, b), c))
    f(g(g(c, c), f(c, b)), g(g(c, b), c)) f(g(g(c, c), f(c, b)), g(g(b, b), c))
    f(g(g(c, c), f(c, b)), g(g(c, b), c)) f(g(c, b), g(g(b, b), c))
    f(g(g(c, c), f(c, b)), g(g(c, b), b)) f(g(c, b), g(g(b, b), c))
    a a
    a f(a, a)
    f(g(b, b), g(c, c)) f(a, a)
    a f(a, a)
    f(f(f(f(c, b), f(c, b)), g(g(a, g(b, b)), g(c, a))), f(a, b)) g(g(b, f(f(b, a), a)), g(g(c, a), f(a, a)))
    a f(a, a)
    g(g(a, c), b) f(a, f(c, a))
    a f(f(a, a), a)
    f(f(b, b), a) g(f(f(a, b), g(a, f(a, c))), g(b, c))
    a f(f(f(a, a), a), a)
    g(g(f(b, b), a), f(f(b, c), g(b, b))) g(f(f(c, b), f(a, b)), g(g(f(a, a), g(a, b)), f(a, b)))
    g(g(f(b, b), a), f(f(b, c), g(b, b))) g(f(f(c, b), f(a, b)), f(f(c, b), f(a, b)))
    g(g(f(b, b), a), g(f(b, b), a)) g(f(f(c, b), f(a, b)), f(f(c, b), f(a, b)))
    g(g(f(b, b), a), g(f(b, b), f(b, b))) g(f(f(c, b), f(a, b)), f(f(c, b), f(a, b)))
    g(g(f(b, b), f(b, b)), g(f(b, b), f(b, b))) g(f(f(c, b), f(a, b)), f(f(c, b), f(a, b)))
    g(g(f(b, b), f(b, b)), g(f(b, b), f(b, b))) g(g(f(b, b), f(b, b)), g(f(b, b), f(b, b)))
    f(g(f(b, c), f(b, g(c, c))), g(c, a)) g(c, a)
    f(g(f(b, c), f(b, g(c, c))), g(f(b, c), f(b, g(c, c)))) g(c, a)
    g(c, a) g(c, a)
    g(c, a) g(a, a)
    g(a, a) g(a, a)
    f(f(f(c, b), f(b, b)), f(f(b, c), g(a, b))) b
    f(f(f(b, b), f(b, b)), f(f(b, c), g(a, b))) b
    f(f(f(b, b), f(b, b)), f(f(b, b), g(a, b))) b
    f(f(f(b, b), f(b, b)), f(f(b, b), g(a, b))) f(f(f(b, b), f(b, b)), f(f(b, b), g(a, b)))
    f(f(f(b, b), f(b, b)), f(f(b, b), g(a, b))) f(f(f(b, b), f(b, b)), f(f(b, b), f(b, b)))
    f(f(f(b, b), f(b, b)), f(f(b, b), f(b, b))) f(f(f(b, b), f(b, b)), f(f(b, b), f(b, b)))
    f(f(f(b, b), f(b, b)), f(f(b, b), f(b, b))) f(f(f(b, b), g(b, b)), f(f(b, b), f(b, b)))
    f(b, f(g(a, c), c)) f(b, g(f(c, c), b))
    f(b, g(f(c, c), b)) f(b, g(f(c, c), b))
    f(b, g(f(c, c), b)) f(g(f(c, c), b), g(f(c, c), b))
    f(b, f(a, a)) b
    b b
    a b
    b a
    f(g(a, c), f(c, b)) g(g(f(b, b), c), g(b, f(c, b)))
    g(g(f(b, b), c), g(b, f(c, b))) g(g(f(b, b), c), g(b, f(c, b)))
    g(g(f(b, b), c), g(b, f(c, b))) g(g(b, c), g(b, f(c, b)))
    g(g(g(a, a), c), g(b, f(c, b))) g(g(b, c), g(b, f(c, b)))
    g(g(g(a, a), b), g(b, f(c, b))) g(g(b, c), g(b, f(c, b)))
    g(g(g(a, a), b), g(b, f(c, b))) g(g(g(a, a), b), g(b, f(c, b)))
    f(b, f(b, f(c, b))) g(b, g(c, f(c, c)))
    f(b, a) f(b, g(c, f(c, c)))
    f(b, g(c, f(c, c))) f(b, g(c, f(c, c)))
    f(b, g(b, f(c, c))) f(b, g(c, f(c, c)))
    f(g(c, f(c, c)), g(c, f(c, c))) f(b, g(c, f(c, c)))
    f(g(c, f(c, c)), g(c, f(c, c))) f(g(c, f(c, c)), g(c, f(c, c)))
    f(b, a) f(f(c, g(a, c)), g(b, f(c, a)))
    f(g(g(a, a), f(c, a)), c) g(f(a, a), b)
    b f(f(b, c), a)
    a f(f(b, c), a)
    a f(f(b, b), a)
    g(a, g(g(a, c), g(b, g(a, c)))) a
    g(a, g(g(b, g(a, c)), g(b, g(a, c)))) a
    g(a, f(g(b, g(a, c)), f(b, g(a, b)))) a
    g(a, f(g(b, g(a, c)), f(b, g(a, a)))) a
    g(a, f(g(b, g(a, c)), f(b, g(a, a)))) g(a, f(g(b, g(a, c)), f(b, g(a, a))))
    g(a, f(g(b, g(a, c)), f(b, g(b, a)))) g(a, f(g(b, g(a, c)), f(b, g(a, a))))
    g(a, f(g(b, g(a, c)), f(b, g(a, a)))) g(a, f(g(b, g(a, c)), g(b, g(a, c))))
    f(a, b) g(a, c)
    f(a, b) f(a, b)
    f(a, b) f(b, b)
    f(b, b) f(b, b)
    f(f(a, a), f(c, g(c, a))) g(g(c, c), f(f(f(a, c), b), f(f(a, b), b)))
    f(f(a, a), f(c, g(c, a))) g(g(c, c), f(f(f(a, c), b), f(f(a, b), f(a, b))))
    f(f(a, a), f(c, g(c, a))) g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, b))))
    g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, b)))) g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, b))))
    g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, c)))) g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, b))))
    g(g(a, c), f(f(f(a, a), b), f(f(a, b), f(a, c)))) g(g(c, c), f(f(f(a, a), b), f(f(a, b), f(a, b))))
    g(c, c) f(c, c)
    g(c, c) g(c, c)
    g(g(a, g(c, c)), g(f(a, b), b)) f(f(b, f(c, b)), f(a, c))
    g(g(a, g(c, c)), g(f(a, a), b)) f(f(b, f(c, b)), f(a, c))
    f(f(a, f(c, f(b, a))), a) f(f(b, f(c, b)), f(a, c))
    f(f(b, f(c, b)), f(a, c)) f(f(b, f(c, b)), f(a, c))
    f(f(b, f(c, b)), f(c, c)) f(f(b, f(c, b)), f(a, c))
    f(f(b, f(c, b)), f(a, c)) f(g(a, b), f(g(a, a), c))
    f(f(b, f(c, b)), f(b, c)) f(g(a, b), f(g(a, a), c))
    b g(g(g(a, f(g(b, b), g(b, a))), a), f(g(a, a), a))
    b g(g(g(a, a), a), f(g(a, a), a))
    g(g(g(a, a), a), f(g(a, a), a)) g(g(g(a, a), a), f(g(a, a), a))
    g(g(g(a, a), a), f(g(a, a), a)) g(g(g(a, a), a), g(g(a, a), a))
    g(g(g(a, a), a), f(a, a)) g(g(g(a, a), a), g(g(a, a), a))
    g(g(g(a, a), a), g(g(a, a), a)) g(g(g(a, a), a), g(g(a, a), a))
    b f(g(g(a, a), a), g(g(a, a), a))
    g(b, f(f(c, b), c)) f(c, a)
    g(b, f(f(c, b), c)) g(b, f(f(c, b), c))
    g(b, f(f(c, b), b)) g(b, f(f(c, b), c))
    g(b, f(c, b)) g(b, f(f(c, b), c))
    g(b, f(f(c, b), c)) g(b, f(c, c))
    g(b, f(f(c, b), b)) g(b, f(f(c, b), b))
    g(b, f(f(c, b), b)) g(b, f(f(c, b), f(c, b)))
    f(f(f(b, c), b), g(f(c, a), g(g(b, c), g(c, b)))) g(b, a)
    f(f(f(b, c), b), g(f(c, a), g(g(b, c), g(c, b)))) f(f(f(b, c), b), g(f(c, a), g(g(b, c), g(c, b))))
    f(f(f(b, c), b), g(f(c, a), g(g(b, c), g(c, b)))) f(f(f(b, c), b), g(f(a, a), g(g(b, c), g(c, b))))
    f(f(f(b, c), b), g(f(a, a), g(g(b, c), g(c, b)))) f(f(f(b, c), b), g(f(a, a), g(g(b, c), g(c, b))))
    f(f(f(b, c), b), g(f(a, a), g(f(b, c), b))) f(f(f(b, c), b), g(f(a, a), g(g(b, c), g(c, b))))
    f(f(f(b, c), b), g(f(a, a), g(g(b, c), g(c, b)))) f(f(f(b, c), b), g(f(a, a), g(f(b, c), b)))
    f(g(f(a, a), g(g(b, c), g(c, b))), g(f(a, a), g(g(b, c), g(c, b)))) f(f(f(b, c), b), g(f(a, a), g(f(b, c), b)))
    a g(f(g(a, a), g(b, b)), c)
    a a
    a f(a, a)
    f(g(g(b, f(a, b)), a), g(a, f(b, b))) g(c, a)
    a f(a, a)
    f(g(c, c), a) f(f(f(a, c), b), g(f(f(c, a), b), g(b, a)))
    a f(a, a)
    f(g(g(a, b), f(a, b)), f(f(b, g(c, a)), b)) g(g(c, a), g(c, b))
    a f(a, a)
    g(g(g(c, f(a, b)), a), g(g(g(a, c), g(b, a)), b)) f(f(c, b), g(b, b))
    a f(c, a)
    f(f(c, a), g(g(b, a), f(f(c, b), f(a, a)))) f(c, g(f(g(b, c), a), f(g(c, a), a)))
    f(f(c, a), g(g(b, a), f(b, a))) f(c, g(f(g(b, c), a), f(g(c, a), a)))
    f(f(c, a), g(g(b, a), f(b, a))) f(g(f(g(b, c), a), f(g(c, a), a)), g(f(g(b, c), a), f(g(c, a), a)))
    f(f(c, a), g(g(b, a), f(b, a))) f(g(f(g(b, c), a), f(g(c, a), a)), g(f(g(c, c), a), f(g(c, a), a)))
    g(g(b, a), f(b, a)) f(g(f(g(b, c), a), f(g(c, a), a)), f(f(g(c, c), a), f(g(c, a), g(b, a))))
    g(g(b, a), f(b, a)) f(g(f(g(b, c), a), f(g(c, a), a)), f(f(g(c, c), c), f(g(c, a), g(b, a))))
    f(g(f(g(b, c), a), f(g(c, a), a)), f(f(g(c, c), c), f(g(c, a), g(b, a)))) f(g(f(g(b, c), a), f(g(c, a), a)), f(f(g(c, c), c), f(g(c, a), g(b, a))))
    a c
    g(f(b, c), f(f(b, f(a, c)), a)) g(f(g(f(c, b), g(b, c)), g(a, b)), g(f(f(f(c, a), f(b, b)), f(c, a)), f(f(b, a), a)))
    g(f(b, c), f(f(b, f(a, c)), a)) g(f(g(f(c, b), g(b, c)), g(a, b)), f(g(f(c, b), g(b, c)), g(a, b)))
    g(f(b, c), f(f(f(a, c), f(a, c)), a)) g(f(g(f(c, b), g(b, c)), g(a, b)), f(g(f(c, b), g(b, c)), g(a, b)))
    g(f(b, c), f(f(f(a, c), f(a, c)), a)) g(f(b, c), f(f(f(a, c), f(a, c)), a))
    a f(f(b, c), g(a, b))
    a g(g(b, a), b)
    g(g(b, a), b) g(g(b, a), b)
    f(g(a, c), f(c, a)) f(c, c)
    f(g(a, c), f(c, a)) f(g(a, c), f(c, a))
    c g(f(c, a), a)
    c c
    f(a, b) a
    f(a, a) a
    g(f(a, c), f(a, b)) g(c, a)
    f(a, c) f(a, b)
    f(a, c) f(a, c)
    b f(a, c)
    a f(a, c)
    f(f(f(c, a), c), f(a, c)) g(b, b)
    f(f(f(c, b), c), f(a, c)) g(b, b)
    f(f(f(c, b), c), f(f(c, b), c)) g(b, b)
    g(b, b) g(b, b)
    g(g(g(g(a, a), g(f(a, a), c)), g(g(c, c), f(b, f(a, c)))), f(f(b, a), f(f(f(b, c), f(a, c)), g(c, a)))) g(g(b, b), g(g(b, a), f(b, f(g(b, a), g(a, a)))))
    g(g(g(g(a, a), g(f(a, a), c)), g(g(c, c), f(b, f(a, c)))), f(f(b, a), f(f(g(c, c), f(a, c)), g(c, a)))) g(g(b, b), g(g(b, a), f(b, f(g(b, a), g(a, a)))))
    g(g(g(g(a, a), g(f(a, a), c)), g(g(c, c), f(b, f(a, c)))), f(f(b, a), f(f(g(c, c), f(a, c)), g(c, a)))) g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a)))))
    g(g(f(b, a), f(f(g(c, c), f(a, c)), g(c, a))), f(f(b, a), f(f(g(c, c), f(a, c)), g(c, a)))) g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a)))))
    g(g(f(b, f(b, f(g(a, a), g(a, a)))), f(f(g(c, c), f(a, c)), g(c, a))), f(f(b, a), f(f(g(c, c), f(a, c)), g(c, a)))) g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a)))))
    g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a))))) g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a)))))
    g(g(b, b), g(g(b, a), f(b, f(g(a, a), g(a, a))))) g(g(b, b), g(g(b, a), f(a, f(g(a, a), g(a, a)))))
    f(a, g(g(g(a, a), a), g(b, a))) g(g(f(a, b), f(c, c)), g(g(c, b), b))
    f(a, g(g(g(a, a), g(a, a)), g(b, a))) g(g(f(a, b), f(c, c)), g(g(c, b), b))
    f(a, g(g(g(a, a), g(a, a)), g(b, a))) f(a, g(g(g(a, a), g(a, a)), g(b, a)))
    g(b, a) g(a, g(g(f(a, b), b), a))
    g(b, a) g(a, g(g(f(a, a), b), a))
    g(b, a) g(a, g(a, a))
    b f(a, g(a, f(b, c)))
    f(b, a) f(g(a, c), f(a, c))
    f(b, a) f(g(c, c), f(a, c))
    f(b, a) f(g(c, b), f(a, c))
    f(b, a) f(b, a)
    f(b, b) f(b, a)
    f(b, g(a, c)) g(b, f(f(g(a, a), c), g(f(a, b), f(c, a))))
    f(a, g(a, c)) g(b, f(f(g(a, a), c), g(f(a, b), f(c, a))))
    f(a, g(a, c)) g(b, f(f(g(a, a), c), g(f(a, b), f(a, b))))
    f(a, g(a, c)) g(f(f(g(a, a), c), g(f(a, b), f(a, b))), f(f(g(a, a), c), g(f(a, b), f(a, b))))
    f(a, f(a, b)) g(f(f(g(a, a), c), g(f(a, b), f(a, b))), f(f(g(a, a), c), g(f(a, b), f(a, b))))
    f(a, f(a, b)) g(f(g(f(a, b), f(a, b)), g(f(a, b), f(a, b))), f(f(g(a, a), c), g(f(a, b), f(a, b))))
    f(a, f(a, b)) g(f(g(f(a, b), f(a, a)), g(f(a, b), f(a, b))), f(f(g(a, a), c), g(f(a, b), f(a, b))))
    a f(g(a, a), g(b, c))
    f(a, a) f(g(a, a), b)
    f(a, a) f(g(a, b), b)
    f(g(a, a), b) f(g(a, a), b)
    a f(g(a, a), b)
    f(g(a, b), b) f(g(a, a), b)
    f(g(a, b), b) f(g(a, b), b)
    b f(a, g(c, c))
    b f(a, g(a, c))
    a f(a, g(a, c))
    g(g(g(a, c), g(g(a, a), c)), b) f(a, f(g(c, b), f(f(b, c), f(a, b))))
    g(g(g(a, c), g(f(b, c), f(a, b))), b) f(a, f(g(c, b), f(f(b, c), f(a, b))))
    g(g(g(a, c), g(f(b, c), f(a, b))), b) f(a, f(g(c, b), f(f(b, b), f(a, b))))
    g(g(g(a, c), g(f(b, c), f(b, b))), b) f(a, f(g(c, b), f(f(b, b), f(a, b))))
    g(g(g(a, c), g(f(b, c), f(b, b))), b) f(a, a)
    g(g(g(a, c), g(f(b, c), f(b, b))), b) g(g(g(a, c), g(f(b, c), f(b, b))), b)
    g(g(g(a, c), g(f(b, c), f(b, b))), b) g(g(g(a, c), g(f(b, c), f(c, b))), b)
    g(g(b, c), f(f(a, a), f(c, a))) g(a, f(c, a))
    g(g(b, c), g(b, c)) g(a, f(c, a))
    g(g(b, c), g(b, c)) g(c, f(c, a))
    g(g(b, c), g(b, c)) g(c, f(c, c))
    g(c, f(c, c)) g(c, f(c, c))
    f(c, g(a, c)) g(c, f(c, c))
    f(g(a, c), a) f(f(b, b), f(g(a, b), c))
    f(a, a) f(f(b, b), f(g(a, b), c))
    f(a, a) f(f(b, b), f(g(b, b), c))
    f(a, a) f(f(a, b), f(g(b, b), c))
    f(a, a) f(a, a)
    f(g(g(b, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, a)), g(f(g(g(c, a), a), g(b, f(a, b))), a))
    f(g(g(b, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, a)), f(f(a, c), g(b, a)))
    f(g(g(b, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, c)), f(f(a, c), g(b, a)))
    f(g(g(b, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, c)), f(g(g(b, b), f(a, b)), g(c, c)))
    f(g(f(a, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, c)), f(g(g(b, b), f(a, b)), g(c, c)))
    f(g(f(a, b), f(a, b)), g(c, c)) g(f(f(a, c), g(b, c)), f(g(f(a, b), f(a, b)), g(c, c)))
    a a
    a f(a, a)
    g(b, f(b, f(b, b))) f(c, c)
    a f(a, a)
    g(f(c, b), g(b, a)) f(g(f(b, c), b), f(c, g(g(b, c), c)))
    a f(a, a)
    f(a, b) f(b, a)
    a f(f(a, a), a)
    f(f(b, g(f(b, b), a)), b) f(g(c, c), f(a, b))
    a f(b, c)
    f(g(b, b), a) g(b, c)
    f(g(b, b), a) f(g(b, b), a)
    f(g(b, a), a) f(g(b, b), a)
    g(b, a) f(f(b, a), f(a, a))
    g(b, a) g(b, a)
    f(g(g(g(c, c), c), f(g(c, b), g(a, a))), g(g(c, b), g(a, c))) f(f(c, b), g(b, b))
    f(g(g(g(c, c), c), f(g(c, b), g(a, b))), g(g(c, b), g(a, c))) f(f(c, b), g(b, b))
    f(g(g(g(c, c), c), f(g(c, b), g(a, b))), g(g(g(c, c), c), f(g(c, b), g(a, b)))) f(f(c, b), g(b, b))
    f(g(g(g(c, c), c), f(g(c, b), g(a, b))), g(g(g(c, c), c), f(g(c, c), g(a, b)))) f(f(c, b), g(b, b))
    f(f(c, b), g(b, b)) f(f(c, b), g(b, b))
    g(b, b) f(g(f(f(c, b), f(a, a)), g(f(f(b, c), a), g(c, b))), c)
    g(b, b) g(b, b)
    g(f(c, b), a) c
    g(f(c, c), a) c
    g(f(c, c), c) c
    g(f(c, c), c) a
    g(b, f(b, b)) g(g(b, b), f(b, b))
    g(b, f(b, b)) g(f(b, b), f(b, b))
    b g(f(a, b), f(a, c))
    f(a, c) f(f(b, a), b)
    f(a, c) f(f(b, c), b)
    f(b, c) f(f(b, c), b)
    f(c, c) g(g(g(a, c), c), g(c, g(a, a)))
    f(b, a) f(g(g(a, c), c), f(c, f(a, c)))
    f(b, a) f(g(g(a, c), c), g(g(a, c), c))
    f(b, a) f(b, a)
    f(b, a) f(b, b)
    f(b, b) f(b, b)
    f(c, g(b, a)) g(b, c)
    f(c, g(b, a)) g(c, c)
    f(c, c) g(c, c)
    f(c, c) f(c, c)
    f(c, a) f(c, c)
    f(c, a) f(a, c)
    f(a, c) f(a, c)
    f(a, g(g(c, b), c)) g(g(c, b), g(b, b))
    f(a, g(c, c)) g(g(c, b), g(b, b))
    f(a, g(c, c)) g(f(c, b), g(b, b))
    f(a, g(c, c)) g(f(c, b), g(c, b))
    f(a, g(c, c)) f(a, g(c, c))
    f(a, g(c, c)) f(c, g(c, c))
    f(a, f(c, a)) f(c, g(c, c))
    f(a, g(g(b, b), f(c, f(c, c)))) g(g(f(f(c, a), g(c, c)), b), a)
    f(a, g(g(b, b), f(c, f(c, c)))) g(g(g(b, b), f(c, f(c, c))), a)
    f(a, g(g(b, b), f(c, f(c, c)))) g(g(g(b, b), f(c, f(c, c))), b)
    f(a, a) g(g(g(b, b), f(c, f(c, c))), b)
    g(g(g(b, b), f(c, f(c, c))), b) g(g(g(b, b), f(c, f(c, c))), b)
    g(g(g(b, b), f(c, f(c, c))), b) g(g(g(b, b), f(c, f(b, b))), b)
    f(g(c, c), b) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), g(a, b))))
    f(g(c, c), b) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), c)))
    f(g(c, c), b) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), a)))
    g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), a))) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), a)))
    g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), c))) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), a)))
    g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), c))) g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(f(g(a, c), c), f(g(a, c), a)))
    g(g(f(f(g(a, c), c), f(a, f(a, a))), f(g(b, a), c)), f(g(b, a), f(g(a, c), c))) g(g(f(f(g(a, c), a), f(a, f(a, a))), f(g(b, a), c)), f(f(g(a, c), c), f(g(a, c), a)))
    g(g(b, g(a, c)), g(b, b)) f(f(b, b), f(g(a, b), g(a, b)))
    g(g(b, g(a, c)), g(b, b)) f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b)))
    g(g(a, g(a, c)), g(b, b)) f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b)))
    g(g(a, g(a, c)), g(a, g(a, c))) f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b)))
    f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b))) f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b)))
    f(f(g(a, b), g(a, b)), f(g(a, b), g(a, b))) f(f(f(a, b), g(a, b)), f(g(a, b), g(a, b)))
    f(f(f(a, b), g(a, b)), f(g(a, b), g(a, b))) f(f(f(a, b), g(a, b)), f(g(a, b), g(a, b)))
    g(f(a, a), f(a, c)) f(b, c)
    g(f(a, a), f(a, a)) f(b, c)
    g(f(a, a), f(a, a)) g(f(a, a), f(a, a))
    f(f(a, a), f(a, a)) g(f(a, a), f(a, a))
    g(g(c, c), g(g(c, a), c)) b
    g(g(c, c), g(g(c, b), c)) b
    g(g(c, c), g(c, c)) b
    g(g(c, c), g(c, c)) g(g(c, c), g(c, c))
    g(g(c, c), g(c, c)) g(c, g(f(a, a), c))
    g(c, g(f(a, a), c)) g(c, g(f(a, a), c))
    g(c, g(f(a, a), b)) g(c, g(f(a, a), c))
    f(a, a) g(a, g(b, a))
    f(a, a) f(a, a)
    f(a, a) f(a, a)
    a f(a, a)
    f(g(b, b), f(g(a, b), b)) f(b, f(c, b))
    g(a, b) f(b, f(c, b))
    f(c, b) f(b, f(c, b))
    f(c, b) f(b, f(c, c))
    f(c, b) f(b, f(b, b))
    f(b, b) f(b, f(b, b))
    g(a, b) f(b, f(b, b))
    g(g(b, b), g(c, a)) g(a, c)
    g(g(c, a), g(c, a)) g(a, c)
    f(g(a, f(c, c)), f(b, a)) g(g(a, c), f(b, f(a, c)))
    f(g(a, f(c, c)), f(b, a)) f(g(a, f(c, c)), f(b, a))
    f(g(a, f(c, c)), g(a, f(c, c))) f(g(a, f(c, c)), f(b, a))
    f(c, c) f(g(a, f(c, c)), f(f(a, a), c))
    a a
    a f(a, a)
    g(b, c) g(f(g(c, c), c), a)
    a f(a, a)
    f(b, g(g(a, g(c, b)), f(g(c, a), g(b, c)))) f(f(a, c), f(g(b, f(a, a)), f(b, g(a, c))))
    a f(f(a, a), a)
    f(g(f(b, c), b), g(b, a)) f(f(c, f(c, c)), f(c, c))
    a f(a, a)
    f(g(b, c), g(a, a)) g(f(g(b, b), f(g(b, a), g(c, b))), f(f(c, c), c))
    a f(f(f(a, a), a), a)
    g(f(a, a), b) f(f(g(a, a), g(b, c)), f(a, g(c, b)))
    g(f(a, a), b) f(f(g(a, a), g(b, c)), f(a, g(c, c)))
    g(a, b) f(f(g(a, a), g(b, c)), f(a, g(c, c)))
    g(a, b) f(f(g(a, a), g(b, c)), f(a, b))
    g(a, b) f(f(g(a, a), g(b, c)), f(b, b))
    f(f(g(a, a), g(b, c)), f(b, b)) f(f(g(a, a), g(b, c)), f(b, b))
    f(f(b, g(b, c)), f(b, b)) f(f(g(a, a), g(b, c)), f(b, b))
    f(f(b, b), f(c, b)) f(c, g(f(c, g(c, a)), g(b, a)))
    f(f(b, b), f(c, b)) f(f(b, b), f(c, b))
    f(f(b, b), f(c, b)) f(f(b, b), f(b, b))
    f(f(b, b), f(c, b)) f(f(b, b), f(b, b))
    b f(f(b, b), f(g(a, f(a, a)), f(b, a)))
    b b
    a g(b, g(g(a, c), f(g(c, f(c, a)), g(b, a))))
    a g(b, g(g(a, c), f(g(c, f(c, a)), c)))
    a g(b, g(g(a, c), f(g(c, c), c)))
    a g(c, g(g(a, c), f(g(c, c), c)))
    a g(g(g(a, c), f(g(c, c), c)), g(g(a, c), f(g(c, c), c)))
    a g(g(g(a, c), f(g(c, c), g(c, c))), g(g(a, c), f(g(c, c), c)))
    a g(g(g(a, c), f(g(c, c), c)), g(g(a, c), g(g(c, c), c)))
    a f(f(c, a), g(c, g(a, a)))
    a f(f(a, a), g(c, g(a, a)))
    f(g(f(b, f(c, b)), c), a) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(c, a))), f(a, c))
    f(g(f(b, f(c, b)), c), a) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c))
    g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c)) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c))
    g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c)) g(f(g(g(a, c), f(g(b, g(a, c)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c))
    g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c)) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, b)))), f(a, c))
    g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c)) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, a), f(g(b, g(a, a)), f(c, b)))), f(a, c))
    g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, c), f(g(b, g(a, a)), f(c, c)))), f(a, c)) g(f(g(g(a, c), f(g(b, g(a, a)), f(c, c))), f(g(a, a), f(g(b, g(a, a)), f(c, c)))), f(a, c))
    f(f(a, a), g(f(a, a), g(b, c))) g(c, c)
    f(f(a, a), g(f(a, a), g(a, a))) g(c, c)
    f(g(f(a, a), g(a, a)), g(f(a, a), g(a, a))) g(c, c)
    g(c, c) g(c, c)
    g(b, c) g(c, c)
    g(b, c) g(b, c)
    c g(g(g(c, c), c), f(g(b, a), g(g(c, a), b)))
    g(g(g(c, c), c), f(g(b, a), g(g(c, a), b))) g(g(g(c, c), c), f(g(b, a), g(g(c, a), b)))
    g(g(a, c), b) f(g(g(c, c), c), g(g(b, a), f(g(c, a), f(a, b))))
    g(g(a, c), b) f(g(g(c, c), c), g(g(b, a), f(g(a, c), b)))
    f(a, b) f(g(g(c, c), c), f(g(b, a), b))
    f(a, b) f(g(g(c, c), c), g(g(c, c), c))
    f(a, b) f(a, b)
    g(g(a, c), f(b, c)) a
    g(g(a, c), f(b, b)) a
    g(g(a, c), f(b, b)) g(g(a, c), f(b, b))
    g(f(a, c), f(b, b)) g(g(a, c), f(b, b))
    g(f(b, b), f(b, b)) g(g(a, c), f(b, b))
    f(f(b, b), g(g(a, c), a)) g(g(a, c), f(b, b))
    g(g(f(b, g(f(b, a), b)), g(a, c)), f(c, b)) g(f(c, a), b)
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b)) g(f(c, a), b)
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b)) g(f(b, a), b)
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b)) g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b))
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), a))), f(c, b)) g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b))
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), a))), f(c, a)) g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), b))), f(c, b))
    g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), a))), f(c, a)) g(g(f(b, g(f(b, a), b)), f(b, g(f(b, a), a))), f(c, a))
    a f(g(g(f(b, c), c), f(g(a, c), a)), g(f(b, b), g(g(c, c), f(a, b))))
    a f(g(g(f(b, c), a), f(g(a, c), a)), g(f(b, b), g(g(c, c), f(a, b))))
    a f(g(g(g(c, c), f(a, b)), f(g(a, c), a)), g(f(b, b), g(g(c, c), f(a, b))))
    a f(g(g(g(c, c), f(a, b)), f(g(a, c), a)), g(f(b, b), g(a, c)))
    a f(g(g(g(a, b), f(a, b)), f(g(a, c), a)), g(f(b, b), g(a, c)))
    a f(g(g(g(a, b), f(a, b)), f(g(g(a, b), c), a)), g(f(b, b), g(a, c)))
    f(a, a) f(f(g(g(a, b), f(a, b)), f(g(g(a, b), c), b)), b)
    a f(b, f(a, f(c, a)))
    a f(b, f(a, f(c, b)))
    a f(b, b)
    f(b, b) f(b, b)
    g(g(g(b, f(c, a)), a), c) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(f(b, b), g(b, b)), f(a, c)) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(f(b, b), c), f(a, c)) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(f(b, b), c), f(c, c)) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(a, g(b, b)), f(a, c)) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(f(b, b), g(b, b)), f(f(b, b), c)) f(g(f(b, b), g(b, b)), f(a, c))
    f(g(f(b, b), g(b, b)), f(f(b, b), c)) f(f(f(b, b), c), f(a, c))
    f(g(f(a, c), g(b, c)), g(a, f(b, c))) g(b, f(b, f(a, a)))
    g(b, f(b, f(a, a))) g(b, f(b, f(a, a)))
    g(b, f(b, f(a, a))) g(b, f(f(a, a), f(a, a)))
    g(b, f(f(a, a), f(a, a))) g(b, f(f(a, a), f(a, a)))
    b f(b, g(f(a, a), f(a, a)))
    f(b, g(f(a, a), f(a, a))) f(b, g(f(a, a), f(a, a)))
    a g(b, f(g(a, a), a))
    g(f(b, g(a, a)), f(f(b, c), g(f(c, c), b))) f(f(f(g(c, b), g(f(a, b), c)), f(c, c)), f(g(c, b), c))
    g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b))) f(f(f(g(c, b), g(f(a, b), c)), f(c, c)), f(g(c, b), c))
    g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b))) f(f(b, g(a, a)), f(f(b, c), g(f(a, b), b)))
    g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b))) f(f(b, g(a, a)), f(b, g(a, a)))
    g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b))) g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b)))
    g(f(b, g(a, a)), f(f(b, c), g(f(a, b), b))) g(f(b, g(b, a)), f(f(b, c), g(f(a, b), b)))
    g(f(b, g(a, a)), f(f(a, b), b)) g(f(b, g(b, a)), f(f(b, c), g(f(a, b), b)))
    f(c, g(c, a)) f(g(f(a, c), a), f(c, c))
    f(g(f(a, c), a), f(c, c)) f(g(f(a, c), a), f(c, c))
    c g(g(f(c, a), b), f(a, a))

```python
terms = set([App("a"), App("b"), App("c")])
for i in range(2):
    newterms = set()
    newterms |= {App("f", (t1, t2)) for t1 in terms for t2 in terms}
    newterms |= {App("g", (t1, t2)) for t1 in terms for t2 in terms}
    #deltaterms = newterms - terms
    terms |= newterms

ts = {(t1,t2) : ground_lpo(t1, t2) for t1 in terms for t2 in terms}
```

<https://stackoverflow.com/questions/32752739/how-does-the-functools-cmp-to-key-function-work>
Huh. Ok, that makes sense. I thought maybe there was something crazier and cache-y going on. Maintaing a tree or something

```python
from functools import cmp_to_key
terms = set([App("a"), App("b")])
for i in range(4):
    newterms = set()
    newterms |= {App("f", (t1,)) for t1 in terms}
    newterms |= {App("g", (t1,)) for t1 in terms}
    newterms |= {App("h", (t1,)) for t1 in terms}
    #newterms |= {App("f", (t1, t2)) for t1 in terms for t2 in terms}
    #newterms |= {App("g", (t1, t2)) for t1 in terms for t2 in terms}
    #deltaterms = newterms - terms
    terms |= newterms

terms1= list(terms)
terms1.sort(key=cmp_to_key(lambda x,y: ground_lpo(x,y).value))
terms1
```

    [a,
     b,
     f(a),
     f(b),
     f(f(a)),
     f(f(b)),
     f(f(f(a))),
     f(f(f(b))),
     f(f(f(f(a)))),
     f(f(f(f(b)))),
     g(a),
     f(g(a)),
     f(f(g(a))),
     f(f(f(g(a)))),
     g(b),
     f(g(b)),
     f(f(g(b))),
     f(f(f(g(b)))),
     g(f(a)),
     f(g(f(a))),
     f(f(g(f(a)))),
     g(f(b)),
     f(g(f(b))),
     f(f(g(f(b)))),
     g(f(f(a))),
     f(g(f(f(a)))),
     g(f(f(b))),
     f(g(f(f(b)))),
     g(f(f(f(a)))),
     g(f(f(f(b)))),
     g(g(a)),
     f(g(g(a))),
     f(f(g(g(a)))),
     g(f(g(a))),
     f(g(f(g(a)))),
     g(f(f(g(a)))),
     g(g(b)),
     f(g(g(b))),
     f(f(g(g(b)))),
     g(f(g(b))),
     f(g(f(g(b)))),
     g(f(f(g(b)))),
     g(g(f(a))),
     f(g(g(f(a)))),
     g(f(g(f(a)))),
     g(g(f(b))),
     f(g(g(f(b)))),
     g(f(g(f(b)))),
     g(g(f(f(a)))),
     g(g(f(f(b)))),
     g(g(g(a))),
     f(g(g(g(a)))),
     g(f(g(g(a)))),
     g(g(f(g(a)))),
     g(g(g(b))),
     f(g(g(g(b)))),
     g(f(g(g(b)))),
     g(g(f(g(b)))),
     g(g(g(f(a)))),
     g(g(g(f(b)))),
     g(g(g(g(a)))),
     g(g(g(g(b)))),
     h(a),
     f(h(a)),
     f(f(h(a))),
     f(f(f(h(a)))),
     g(h(a)),
     f(g(h(a))),
     f(f(g(h(a)))),
     g(f(h(a))),
     f(g(f(h(a)))),
     g(f(f(h(a)))),
     g(g(h(a))),
     f(g(g(h(a)))),
     g(f(g(h(a)))),
     g(g(f(h(a)))),
     g(g(g(h(a)))),
     h(b),
     f(h(b)),
     f(f(h(b))),
     f(f(f(h(b)))),
     g(h(b)),
     f(g(h(b))),
     f(f(g(h(b)))),
     g(f(h(b))),
     f(g(f(h(b)))),
     g(f(f(h(b)))),
     g(g(h(b))),
     f(g(g(h(b)))),
     g(f(g(h(b)))),
     g(g(f(h(b)))),
     g(g(g(h(b)))),
     h(f(a)),
     f(h(f(a))),
     f(f(h(f(a)))),
     g(h(f(a))),
     f(g(h(f(a)))),
     g(f(h(f(a)))),
     g(g(h(f(a)))),
     h(f(b)),
     f(h(f(b))),
     f(f(h(f(b)))),
     g(h(f(b))),
     f(g(h(f(b)))),
     g(f(h(f(b)))),
     g(g(h(f(b)))),
     h(f(f(a))),
     f(h(f(f(a)))),
     g(h(f(f(a)))),
     h(f(f(b))),
     f(h(f(f(b)))),
     g(h(f(f(b)))),
     h(f(f(f(a)))),
     h(f(f(f(b)))),
     h(g(a)),
     f(h(g(a))),
     f(f(h(g(a)))),
     g(h(g(a))),
     f(g(h(g(a)))),
     g(f(h(g(a)))),
     g(g(h(g(a)))),
     h(f(g(a))),
     f(h(f(g(a)))),
     g(h(f(g(a)))),
     h(f(f(g(a)))),
     h(g(b)),
     f(h(g(b))),
     f(f(h(g(b)))),
     g(h(g(b))),
     f(g(h(g(b)))),
     g(f(h(g(b)))),
     g(g(h(g(b)))),
     h(f(g(b))),
     f(h(f(g(b)))),
     g(h(f(g(b)))),
     h(f(f(g(b)))),
     h(g(f(a))),
     f(h(g(f(a)))),
     g(h(g(f(a)))),
     h(f(g(f(a)))),
     h(g(f(b))),
     f(h(g(f(b)))),
     g(h(g(f(b)))),
     h(f(g(f(b)))),
     h(g(f(f(a)))),
     h(g(f(f(b)))),
     h(g(g(a))),
     f(h(g(g(a)))),
     g(h(g(g(a)))),
     h(f(g(g(a)))),
     h(g(f(g(a)))),
     h(g(g(b))),
     f(h(g(g(b)))),
     g(h(g(g(b)))),
     h(f(g(g(b)))),
     h(g(f(g(b)))),
     h(g(g(f(a)))),
     h(g(g(f(b)))),
     h(g(g(g(a)))),
     h(g(g(g(b)))),
     h(h(a)),
     f(h(h(a))),
     f(f(h(h(a)))),
     g(h(h(a))),
     f(g(h(h(a)))),
     g(f(h(h(a)))),
     g(g(h(h(a)))),
     h(f(h(a))),
     f(h(f(h(a)))),
     g(h(f(h(a)))),
     h(f(f(h(a)))),
     h(g(h(a))),
     f(h(g(h(a)))),
     g(h(g(h(a)))),
     h(f(g(h(a)))),
     h(g(f(h(a)))),
     h(g(g(h(a)))),
     h(h(b)),
     f(h(h(b))),
     f(f(h(h(b)))),
     g(h(h(b))),
     f(g(h(h(b)))),
     g(f(h(h(b)))),
     g(g(h(h(b)))),
     h(f(h(b))),
     f(h(f(h(b)))),
     g(h(f(h(b)))),
     h(f(f(h(b)))),
     h(g(h(b))),
     f(h(g(h(b)))),
     g(h(g(h(b)))),
     h(f(g(h(b)))),
     h(g(f(h(b)))),
     h(g(g(h(b)))),
     h(h(f(a))),
     f(h(h(f(a)))),
     g(h(h(f(a)))),
     h(f(h(f(a)))),
     h(g(h(f(a)))),
     h(h(f(b))),
     f(h(h(f(b)))),
     g(h(h(f(b)))),
     h(f(h(f(b)))),
     h(g(h(f(b)))),
     h(h(f(f(a)))),
     h(h(f(f(b)))),
     h(h(g(a))),
     f(h(h(g(a)))),
     g(h(h(g(a)))),
     h(f(h(g(a)))),
     h(g(h(g(a)))),
     h(h(f(g(a)))),
     h(h(g(b))),
     f(h(h(g(b)))),
     g(h(h(g(b)))),
     h(f(h(g(b)))),
     h(g(h(g(b)))),
     h(h(f(g(b)))),
     h(h(g(f(a)))),
     h(h(g(f(b)))),
     h(h(g(g(a)))),
     h(h(g(g(b)))),
     h(h(h(a))),
     f(h(h(h(a)))),
     g(h(h(h(a)))),
     h(f(h(h(a)))),
     h(g(h(h(a)))),
     h(h(f(h(a)))),
     h(h(g(h(a)))),
     h(h(h(b))),
     f(h(h(h(b)))),
     g(h(h(h(b)))),
     h(f(h(h(b)))),
     h(g(h(h(b)))),
     h(h(f(h(b)))),
     h(h(g(h(b)))),
     h(h(h(f(a)))),
     h(h(h(f(b)))),
     h(h(h(g(a)))),
     h(h(h(g(b)))),
     h(h(h(h(a)))),
     h(h(h(h(b))))]

```python
from functools import cmp_to_key
terms = set([App("a"), App("b")])
for i in range(2):
    newterms = set()
    newterms |= {App("f", (t1, t2)) for t1 in terms for t2 in terms}
    newterms |= {App("g", (t1, t2)) for t1 in terms for t2 in terms}
    #deltaterms = newterms - terms
    terms |= newterms

terms1= list(terms)
terms1.sort(key=cmp_to_key(lambda x,y: ground_lpo(x,y).value))
terms1
```

    [a,
     b,
     f(a, a),
     f(a, b),
     f(a, f(a, a)),
     f(a, f(a, b)),
     f(b, a),
     f(a, f(b, a)),
     f(b, b),
     f(a, f(b, b)),
     f(b, f(a, a)),
     f(b, f(a, b)),
     f(b, f(b, a)),
     f(b, f(b, b)),
     f(f(a, a), a),
     f(f(a, a), b),
     f(f(a, a), f(a, a)),
     f(f(a, a), f(a, b)),
     f(f(a, a), f(b, a)),
     f(f(a, a), f(b, b)),
     f(f(a, b), a),
     f(f(a, b), b),
     f(f(a, b), f(a, a)),
     f(f(a, b), f(a, b)),
     f(f(a, b), f(b, a)),
     f(f(a, b), f(b, b)),
     f(f(b, a), a),
     f(f(b, a), b),
     f(f(b, a), f(a, a)),
     f(f(b, a), f(a, b)),
     f(f(b, a), f(b, a)),
     f(f(b, a), f(b, b)),
     f(f(b, b), a),
     f(f(b, b), b),
     f(f(b, b), f(a, a)),
     f(f(b, b), f(a, b)),
     f(f(b, b), f(b, a)),
     f(f(b, b), f(b, b)),
     g(a, a),
     f(a, g(a, a)),
     f(b, g(a, a)),
     f(f(a, a), g(a, a)),
     f(f(a, b), g(a, a)),
     f(f(b, a), g(a, a)),
     f(f(b, b), g(a, a)),
     f(g(a, a), a),
     f(g(a, a), b),
     f(g(a, a), f(a, a)),
     f(g(a, a), f(a, b)),
     f(g(a, a), f(b, a)),
     f(g(a, a), f(b, b)),
     f(g(a, a), g(a, a)),
     g(a, b),
     f(a, g(a, b)),
     f(b, g(a, b)),
     f(f(a, a), g(a, b)),
     f(f(a, b), g(a, b)),
     f(f(b, a), g(a, b)),
     f(f(b, b), g(a, b)),
     f(g(a, a), g(a, b)),
     f(g(a, b), a),
     f(g(a, b), b),
     f(g(a, b), f(a, a)),
     f(g(a, b), f(a, b)),
     f(g(a, b), f(b, a)),
     f(g(a, b), f(b, b)),
     f(g(a, b), g(a, a)),
     f(g(a, b), g(a, b)),
     g(a, f(a, a)),
     g(a, f(a, b)),
     g(a, f(b, a)),
     g(a, f(b, b)),
     g(a, g(a, a)),
     g(a, g(a, b)),
     g(b, a),
     f(a, g(b, a)),
     f(b, g(b, a)),
     f(f(a, a), g(b, a)),
     f(f(a, b), g(b, a)),
     f(f(b, a), g(b, a)),
     f(f(b, b), g(b, a)),
     f(g(a, a), g(b, a)),
     f(g(a, b), g(b, a)),
     f(g(b, a), a),
     f(g(b, a), b),
     f(g(b, a), f(a, a)),
     f(g(b, a), f(a, b)),
     f(g(b, a), f(b, a)),
     f(g(b, a), f(b, b)),
     f(g(b, a), g(a, a)),
     f(g(b, a), g(a, b)),
     f(g(b, a), g(b, a)),
     g(a, g(b, a)),
     g(b, b),
     f(a, g(b, b)),
     f(b, g(b, b)),
     f(f(a, a), g(b, b)),
     f(f(a, b), g(b, b)),
     f(f(b, a), g(b, b)),
     f(f(b, b), g(b, b)),
     f(g(a, a), g(b, b)),
     f(g(a, b), g(b, b)),
     f(g(b, a), g(b, b)),
     f(g(b, b), a),
     f(g(b, b), b),
     f(g(b, b), f(a, a)),
     f(g(b, b), f(a, b)),
     f(g(b, b), f(b, a)),
     f(g(b, b), f(b, b)),
     f(g(b, b), g(a, a)),
     f(g(b, b), g(a, b)),
     f(g(b, b), g(b, a)),
     f(g(b, b), g(b, b)),
     g(a, g(b, b)),
     g(b, f(a, a)),
     g(b, f(a, b)),
     g(b, f(b, a)),
     g(b, f(b, b)),
     g(b, g(a, a)),
     g(b, g(a, b)),
     g(b, g(b, a)),
     g(b, g(b, b)),
     g(f(a, a), a),
     g(f(a, a), b),
     g(f(a, a), f(a, a)),
     g(f(a, a), f(a, b)),
     g(f(a, a), f(b, a)),
     g(f(a, a), f(b, b)),
     g(f(a, a), g(a, a)),
     g(f(a, a), g(a, b)),
     g(f(a, a), g(b, a)),
     g(f(a, a), g(b, b)),
     g(f(a, b), a),
     g(f(a, b), b),
     g(f(a, b), f(a, a)),
     g(f(a, b), f(a, b)),
     g(f(a, b), f(b, a)),
     g(f(a, b), f(b, b)),
     g(f(a, b), g(a, a)),
     g(f(a, b), g(a, b)),
     g(f(a, b), g(b, a)),
     g(f(a, b), g(b, b)),
     g(f(b, a), a),
     g(f(b, a), b),
     g(f(b, a), f(a, a)),
     g(f(b, a), f(a, b)),
     g(f(b, a), f(b, a)),
     g(f(b, a), f(b, b)),
     g(f(b, a), g(a, a)),
     g(f(b, a), g(a, b)),
     g(f(b, a), g(b, a)),
     g(f(b, a), g(b, b)),
     g(f(b, b), a),
     g(f(b, b), b),
     g(f(b, b), f(a, a)),
     g(f(b, b), f(a, b)),
     g(f(b, b), f(b, a)),
     g(f(b, b), f(b, b)),
     g(f(b, b), g(a, a)),
     g(f(b, b), g(a, b)),
     g(f(b, b), g(b, a)),
     g(f(b, b), g(b, b)),
     g(g(a, a), a),
     g(g(a, a), b),
     g(g(a, a), f(a, a)),
     g(g(a, a), f(a, b)),
     g(g(a, a), f(b, a)),
     g(g(a, a), f(b, b)),
     g(g(a, a), g(a, a)),
     g(g(a, a), g(a, b)),
     g(g(a, a), g(b, a)),
     g(g(a, a), g(b, b)),
     g(g(a, b), a),
     g(g(a, b), b),
     g(g(a, b), f(a, a)),
     g(g(a, b), f(a, b)),
     g(g(a, b), f(b, a)),
     g(g(a, b), f(b, b)),
     g(g(a, b), g(a, a)),
     g(g(a, b), g(a, b)),
     g(g(a, b), g(b, a)),
     g(g(a, b), g(b, b)),
     g(g(b, a), a),
     g(g(b, a), b),
     g(g(b, a), f(a, a)),
     g(g(b, a), f(a, b)),
     g(g(b, a), f(b, a)),
     g(g(b, a), f(b, b)),
     g(g(b, a), g(a, a)),
     g(g(b, a), g(a, b)),
     g(g(b, a), g(b, a)),
     g(g(b, a), g(b, b)),
     g(g(b, b), a),
     g(g(b, b), b),
     g(g(b, b), f(a, a)),
     g(g(b, b), f(a, b)),
     g(g(b, b), f(b, a)),
     g(g(b, b), f(b, b)),
     g(g(b, b), g(a, a)),
     g(g(b, b), g(a, b)),
     g(g(b, b), g(b, a)),
     g(g(b, b), g(b, b))]

```python
"a" < "b"
```

    True

right it's a total ordering

```python
from collections import defaultdict
import copy
def size(t: App) -> int:
    return 1 + sum(size(a) for a in t.args)
#{(a,b) for (a,b),k in ts.items() if k == Order.LT and size(b) > size(a) and }
#{(a,b) for (a,b),k in ts.items() for (b1,c),k1 in ts.items() if k == Order.LT and k1 == Order.LT and }
neighb = defaultdict(set)
for (a,b),k in ts.items():
    #print(a,b)
    if k == Order.LT:
        #print(a,b)
        neighb[a].add(b)
#print(neighb)
for i in range(4):
    print(sum(len(bs) for bs in neighb.values()))
    newneighb = {a : {b for b in bs} for a,bs in neighb.items()}
    for a, bs in neighb.items():
        for b in bs:
            cs = newneighb.get(b, set())
            if cs is not None:
                newneighb[a] -= cs
    neighb = newneighb
neighb
```

    391170
    884
    884
    884





    {f(g(b, c), a): {f(g(b, c), b)},
     g(f(c, a), f(c, a)): {g(f(c, a), f(c, b))},
     f(g(a, c), g(a, a)): {f(g(a, c), g(a, b))},
     g(g(b, c), g(c, a)): {g(g(b, c), g(c, b))},
     g(f(a, c), g(a, a)): {g(f(a, c), g(a, b))},
     g(f(b, b), g(a, a)): {g(f(b, b), g(a, b))},
     f(f(b, b), f(b, a)): {f(f(b, b), f(b, b))},
     f(f(b, c), f(b, b)): {f(f(b, c), f(b, c))},
     f(f(a, b), f(a, a)): {f(f(a, b), f(a, b))},
     f(f(c, a), g(b, c)): {f(f(c, b), g(b, c))},
     g(g(c, b), g(c, a)): {g(g(c, b), g(c, b))},
     f(g(b, a), g(b, a)): {g(a, g(b, a))},
     g(a, f(a, c)): {g(a, f(b, a))},
     g(c, g(b, a)): {g(c, g(b, b))},
     g(b, g(c, b)): {g(c, c)},
     g(g(c, c), g(c, b)): {g(g(c, c), g(c, c))},
     g(b, f(c, c)): {g(b, g(a, a))},
     f(f(c, b), g(c, c)): {f(f(c, c), g(c, c))},
     f(g(c, c), f(b, c)): {f(g(c, c), f(c, a))},
     f(g(b, c), f(c, b)): {f(g(b, c), f(c, c))},
     g(g(b, b), g(b, a)): {g(g(b, b), g(b, b))},
     g(g(c, c), f(c, c)): {g(g(c, c), g(a, a))},
     f(f(b, c), f(b, a)): {f(f(b, c), f(b, b))},
     f(f(c, b), g(a, c)): {f(f(c, c), g(a, c))},
     g(f(a, b), g(b, c)): {g(f(a, b), g(c, a))},
     f(g(c, b), f(c, b)): {f(g(c, b), f(c, c))},
     g(f(c, c), f(c, a)): {g(f(c, c), f(c, b))},
     f(f(a, c), g(b, c)): {f(f(b, a), g(b, c))},
     g(g(c, a), g(b, c)): {g(g(c, a), g(c, a))},
     f(f(a, a), f(c, a)): {f(f(a, a), f(c, b))},
     f(f(c, a), g(c, c)): {f(f(c, b), g(c, c))},
     f(f(a, c), f(c, a)): {f(f(a, c), f(c, b))},
     f(f(a, a), g(c, b)): {f(f(a, b), g(c, b))},
     g(g(c, a), f(c, a)): {g(g(c, a), f(c, b))},
     g(c, g(c, a)): {g(c, g(c, b))},
     f(f(b, a), g(b, b)): {f(f(b, b), g(b, b))},
     f(f(c, a), g(a, c)): {f(f(c, b), g(a, c))},
     g(g(a, a), g(c, a)): {g(g(a, a), g(c, b))},
     g(b, f(a, b)): {g(b, f(a, c))},
     f(f(c, b), g(a, b)): {f(f(c, c), g(a, b))},
     g(g(a, c), g(c, a)): {g(g(a, c), g(c, b))},
     g(g(b, b), g(c, a)): {g(g(b, b), g(c, b))},
     g(f(c, a), f(b, b)): {g(f(c, a), f(b, c))},
     f(g(c, b), c): {f(g(c, b), f(a, a))},
     f(f(a, b), b): {f(f(a, b), c)},
     g(f(a, b), g(c, c)): {g(f(a, c), a)},
     f(b, g(b, a)): {f(c, g(b, a))},
     g(f(b, a), g(b, a)): {g(f(b, a), g(b, b))},
     g(g(c, c), f(a, a)): {g(g(c, c), f(a, b))},
     g(g(b, c), f(a, b)): {g(g(b, c), f(a, c))},
     g(g(b, c), f(a, c)): {g(g(b, c), f(b, a))},
     f(f(a, c), g(c, c)): {f(f(b, a), g(c, c))},
     f(g(c, c), g(b, a)): {f(g(c, c), g(b, b))},
     g(g(c, a), g(c, c)): {g(g(c, b), a)},
     g(f(a, b), g(a, c)): {g(f(a, b), g(b, a))},
     f(f(a, a), g(a, c)): {f(f(a, b), g(a, c))},
     f(f(a, b), f(b, c)): {f(f(a, b), f(c, a))},
     g(g(b, a), f(b, c)): {g(g(b, a), f(c, a))},
     f(f(c, a), g(a, b)): {f(f(c, b), g(a, b))},
     f(f(a, c), g(a, c)): {f(f(b, a), g(a, c))},
     f(f(c, b), c): {f(f(c, b), f(a, a))},
     g(g(c, a), g(a, c)): {g(g(c, a), g(b, a))},
     f(f(c, c), g(a, c)): {f(g(a, a), g(a, c))},
     g(c, f(a, c)): {g(c, f(b, a))},
     f(f(b, c), f(b, c)): {f(f(b, c), f(c, a))},
     g(g(a, a), f(a, c)): {g(g(a, a), f(b, a))},
     f(a, a): {f(a, b)},
     f(f(c, a), f(a, a)): {f(f(c, a), f(a, b))},
     g(a, g(c, a)): {g(b, g(c, a))},
     g(g(a, c), f(a, c)): {g(g(a, c), f(b, a))},
     f(f(c, a), c): {f(f(c, a), f(a, a))},
     f(f(a, a), f(b, b)): {f(f(a, a), f(b, c))},
     f(g(a, b), g(c, b)): {f(g(a, c), g(c, b))},
     g(f(a, b), g(a, b)): {g(f(a, b), g(a, c))},
     g(f(b, a), g(c, a)): {g(f(b, a), g(c, b))},
     f(g(c, c), g(c, a)): {f(g(c, c), g(c, b))},
     f(f(a, c), f(b, b)): {f(f(a, c), f(b, c))},
     f(g(a, b), f(c, c)): {f(g(a, b), g(a, a))},
     f(f(b, b), g(a, b)): {f(f(b, c), g(a, b))},
     f(f(b, b), f(b, b)): {f(f(b, b), f(b, c))},
     g(g(a, a), g(a, a)): {g(g(a, a), g(a, b))},
     f(f(b, c), f(c, c)): {f(f(c, a), a)},
     f(g(a, b), b): {f(g(a, b), c)},
     g(g(b, c), a): {g(g(b, c), b)},
     f(b, a): {f(a, f(b, a))},
     f(g(a, b), f(a, c)): {f(g(a, b), f(b, a))},
     g(f(b, b), f(b, a)): {g(f(b, b), f(b, b))},
     g(f(b, c), f(b, b)): {g(f(b, c), f(b, c))},
     g(c, f(a, b)): {g(c, f(a, c))},
     f(g(b, c), g(b, c)): {g(a, g(b, c))},
     g(f(a, b), f(a, a)): {g(f(a, b), f(a, b))},
     g(f(c, a), g(b, c)): {g(f(c, a), g(c, a))},
     f(a, f(c, b)): {f(b, f(c, b))},
     g(g(b, a), g(b, a)): {g(g(b, a), g(b, b))},
     g(f(a, b), c): {g(f(a, b), f(a, a))},
     f(f(a, c), f(a, a)): {f(f(a, c), f(a, b))},
     f(f(b, b), c): {f(f(b, b), f(a, a))},
     f(f(c, c), f(a, a)): {f(f(c, c), f(a, b))},
     f(f(c, b), b): {f(f(c, b), c)},
     g(f(c, b), g(c, c)): {g(f(c, c), a)},
     g(g(c, c), f(b, c)): {g(g(c, c), f(c, a))},
     g(g(b, c), f(c, b)): {g(g(b, c), f(c, c))},
     f(b, f(c, b)): {f(c, c)},
     g(f(b, c), f(b, a)): {g(f(b, c), f(b, b))},
     f(g(a, a), g(b, c)): {f(g(a, b), g(b, c))},
     g(f(c, b), g(a, c)): {g(f(c, b), g(b, a))},
     f(a, g(b, b)): {f(b, g(b, b))},
     g(f(a, a), g(b, c)): {g(f(a, a), g(c, a))},
     g(g(c, b), f(c, b)): {g(g(c, b), f(c, c))},
     f(g(a, c), g(b, c)): {f(g(b, a), g(b, c))},
     f(g(a, b), f(a, a)): {f(g(a, b), f(a, b))},
     g(f(a, c), g(b, c)): {g(f(a, c), g(c, a))},
     g(f(a, a), f(c, a)): {g(f(a, a), f(c, b))},
     f(f(b, c), f(a, a)): {f(f(b, c), f(a, b))},
     f(g(b, c), g(c, c)): {f(g(c, a), g(c, c))},
     g(f(c, a), g(c, c)): {g(f(c, b), a)},
     g(f(a, c), f(c, a)): {g(f(a, c), f(c, b))},
     f(g(a, b), a): {f(g(a, b), b)},
     f(b, g(b, b)): {f(c, g(b, b))},
     f(g(c, b), f(b, a)): {f(g(c, b), f(b, b))},
     g(f(b, a), g(b, b)): {g(f(b, a), g(b, c))},
     f(f(c, a), f(b, c)): {f(f(c, a), f(c, a))},
     g(f(c, a), g(a, c)): {g(f(c, a), g(b, a))},
     f(c, g(b, c)): {f(f(a, a), g(b, c))},
     f(g(c, c), g(b, b)): {f(g(c, c), g(b, c))},
     f(g(c, c), b): {f(g(c, c), c)},
     g(a, f(a, b)): {g(a, f(a, c))},
     f(g(c, b), g(a, b)): {f(g(c, b), g(a, c))},
     g(f(c, b), g(a, b)): {g(f(c, b), g(a, c))},
     f(g(b, a), g(c, a)): {f(g(b, b), g(c, a))},
     f(g(b, b), g(b, c)): {f(g(b, c), a)},
     g(f(a, b), b): {g(f(a, b), c)},
     g(b, g(b, a)): {g(b, g(b, b))},
     f(g(a, c), g(c, c)): {f(g(b, a), g(c, c))},
     f(f(a, b), g(c, b)): {f(f(a, c), g(c, b))},
     f(g(b, b), f(c, a)): {f(g(b, b), f(c, b))},
     g(f(a, c), g(c, c)): {g(f(b, a), a)},
     g(f(a, a), g(a, c)): {g(f(a, a), g(b, a))},
     g(f(a, b), f(b, c)): {g(f(a, b), f(c, a))},
     f(f(a, a), f(b, c)): {f(f(a, a), f(c, a))},
     f(f(a, b), f(c, c)): {f(f(a, c), a)},
     f(f(c, c), b): {f(f(c, c), c)},
     f(g(c, a), g(c, b)): {f(g(c, b), a)},
     g(f(c, a), g(a, b)): {g(f(c, a), g(a, c))},
     g(f(a, c), g(a, c)): {g(f(a, c), g(b, a))},
     g(f(c, b), c): {g(f(c, b), f(a, a))},
     f(f(a, c), f(b, c)): {f(f(a, c), f(c, a))},
     f(g(c, a), f(c, c)): {f(g(c, a), g(a, a))},
     f(f(b, a), g(a, a)): {f(f(b, b), g(a, a))},
     f(f(b, b), f(c, a)): {f(f(b, b), f(c, b))},
     f(c, f(c, b)): {f(c, f(c, c))},
     f(f(c, c), f(b, c)): {f(f(c, c), f(c, a))},
     f(g(c, a), b): {f(g(c, a), c)},
     g(f(c, c), g(a, c)): {g(f(c, c), g(b, a))},
     f(g(c, b), g(a, a)): {f(g(c, b), g(a, b))},
     g(f(b, c), f(b, c)): {g(f(b, c), f(c, a))},
     g(a, a): {f(a, g(a, a))},
     f(g(b, c), c): {f(g(b, c), f(a, a))},
     f(g(a, a), f(b, b)): {f(g(a, a), f(b, c))},
     g(f(c, a), c): {g(f(c, a), f(a, a))},
     g(f(a, a), f(b, b)): {g(f(a, a), f(b, c))},
     g(g(a, b), g(c, b)): {g(g(a, b), g(c, c))},
     f(a, g(b, c)): {f(b, g(b, c))},
     f(g(a, b), f(b, c)): {f(g(a, b), f(c, a))},
     g(f(a, c), f(b, b)): {g(f(a, c), f(b, c))},
     f(g(a, c), g(a, b)): {f(g(a, c), g(a, c))},
     f(f(b, a), g(b, c)): {f(f(b, b), g(b, c))},
     g(f(b, b), f(b, b)): {g(f(b, b), f(b, c))},
     g(g(a, b), f(c, c)): {g(g(a, b), g(a, a))},
     g(f(b, b), g(a, b)): {g(f(b, b), g(a, c))},
     g(g(a, b), b): {g(g(a, b), c)},
     f(f(a, b), f(a, b)): {f(f(a, b), f(a, c))},
     f(f(b, a), f(c, a)): {f(f(b, a), f(c, b))},
     g(b, a): {f(a, g(b, a))},
     g(g(c, a), f(b, a)): {g(g(c, a), f(b, b))},
     f(g(b, a), g(b, b)): {f(g(b, b), a)},
     g(a, f(c, b)): {g(a, f(c, c))},
     f(f(b, b), g(a, c)): {f(f(b, c), g(a, c))},
     f(g(a, a), c): {f(g(a, a), f(a, a))},
     g(g(c, a), g(a, b)): {g(g(c, a), g(a, c))},
     f(g(c, a), f(a, a)): {f(g(c, a), f(a, b))},
     f(g(a, c), c): {f(g(a, c), f(a, a))},
     g(f(b, b), c): {g(f(b, b), f(a, a))},
     f(f(c, b), f(b, c)): {f(f(c, b), f(c, a))},
     g(f(c, c), f(a, a)): {g(f(c, c), f(a, b))},
     f(f(a, a), f(a, a)): {f(f(a, a), f(a, b))},
     f(a, g(c, c)): {f(b, g(c, c))},
     f(f(b, a), g(c, c)): {f(f(b, b), g(c, c))},
     f(g(b, a), g(a, a)): {f(g(b, a), g(a, b))},
     f(f(c, b), g(c, b)): {f(f(c, c), g(c, b))},
     f(b, g(c, a)): {f(c, g(c, a))},
     g(g(a, a), g(b, c)): {g(g(a, a), g(c, a))},
     g(a, g(b, b)): {g(b, c)},
     f(f(c, b), f(c, c)): {f(f(c, c), a)},
     g(g(a, c), g(b, c)): {g(g(a, c), g(c, a))},
     g(g(a, b), f(a, a)): {g(g(a, b), f(a, b))},
     g(f(b, c), f(a, a)): {g(f(b, c), f(a, b))},
     f(g(a, b), g(b, a)): {f(g(a, c), g(b, a))},
     g(f(c, b), f(b, b)): {g(f(c, b), f(b, c))},
     f(g(a, b), f(a, b)): {f(g(a, b), f(a, c))},
     f(f(c, a), g(c, b)): {f(f(c, b), g(c, b))},
     g(b, g(b, b)): {g(b, g(b, c))},
     f(f(c, a), f(c, c)): {f(f(c, b), a)},
     g(c, g(b, c)): {g(c, g(c, a))},
     g(g(c, c), g(b, b)): {g(g(c, c), g(b, c))},
     g(g(c, c), b): {g(g(c, c), c)},
     g(g(b, a), g(c, a)): {g(g(b, a), g(c, b))},
     g(g(b, b), g(b, c)): {g(g(b, b), g(c, a))},
     g(f(c, b), f(b, a)): {g(f(c, b), f(b, b))},
     f(a, g(a, a)): {f(b, g(a, a))},
     f(f(c, b), f(a, b)): {f(f(c, b), f(a, c))},
     g(g(a, c), g(c, c)): {g(g(b, a), a)},
     g(f(a, b), g(c, b)): {g(f(a, b), g(c, c))},
     f(b, f(a, c)): {f(b, f(b, a))},
     f(g(c, c), f(a, c)): {f(g(c, c), f(b, a))},
     f(g(c, c), f(a, b)): {f(g(c, c), f(a, c))},
     f(f(a, c), g(c, b)): {f(f(b, a), g(c, b))},
     f(f(b, b), g(c, b)): {f(f(b, c), g(c, b))},
     f(f(c, b), f(a, a)): {f(f(c, b), f(a, b))},
     g(f(a, a), f(b, c)): {g(f(a, a), f(c, a))},
     g(f(a, b), f(c, c)): {g(f(a, b), g(a, a))},
     f(g(a, a), f(c, a)): {f(g(a, a), f(c, b))},
     g(f(c, c), b): {g(f(c, c), c)},
     f(f(a, a), b): {f(f(a, a), c)},
     g(g(c, a), g(c, b)): {g(g(c, a), g(c, c))},
     f(g(c, a), f(b, c)): {f(g(c, a), f(c, a))},
     f(f(a, c), f(c, c)): {f(f(b, a), a)},
     f(g(b, c), f(b, a)): {f(g(b, c), f(b, b))},
     f(f(c, c), g(c, b)): {f(g(a, a), g(c, b))},
     g(g(c, a), f(c, c)): {g(g(c, a), g(a, a))},
     f(f(a, c), b): {f(f(a, c), c)},
     g(f(b, a), g(a, a)): {g(f(b, a), g(a, b))},
     g(f(b, b), f(c, a)): {g(f(b, b), f(c, b))},
     g(c, f(c, b)): {g(c, f(c, c))},
     g(f(c, c), f(b, c)): {g(f(c, c), f(c, a))},
     g(f(c, a), f(b, a)): {g(f(c, a), f(b, b))},
     f(f(c, c), f(c, c)): {g(a, a)},
     f(g(b, c), g(a, b)): {f(g(b, c), g(a, c))},
     g(g(c, a), b): {g(g(c, a), c)},
     g(g(c, b), g(a, a)): {g(g(c, b), g(a, b))},
     g(g(b, b), f(c, b)): {g(g(b, b), f(c, c))},
     f(f(c, c), f(a, c)): {f(f(c, c), f(b, a))},
     g(g(a, a), f(b, b)): {g(g(a, a), f(b, c))},
     f(c, g(c, c)): {f(f(a, a), g(c, c))},
     f(f(b, c), g(c, b)): {f(f(c, a), g(c, b))},
     g(g(a, b), f(b, c)): {g(g(a, b), f(c, a))},
     f(g(a, a), g(c, c)): {f(g(a, b), g(c, c))},
     g(f(b, a), g(b, c)): {g(f(b, a), g(c, a))},
     f(g(a, a), f(b, a)): {f(g(a, a), f(b, b))},
     f(g(b, b), g(c, c)): {f(g(b, c), g(c, c))},
     f(f(b, b), b): {f(f(b, b), c)},
     g(f(a, b), f(a, b)): {g(f(a, b), f(a, c))},
     f(g(a, c), f(b, a)): {f(g(a, c), f(b, b))},
     g(f(a, c), f(b, a)): {g(f(a, c), f(b, b))},
     f(g(a, a), g(a, b)): {f(g(a, b), a)},
     b: {c},
     f(f(b, c), f(a, c)): {f(f(b, c), f(b, a))},
     f(g(c, c), a): {f(g(c, c), b)},
     g(g(b, a), g(b, b)): {g(g(b, a), g(b, c))},
     g(f(a, c), g(a, b)): {g(f(a, c), g(a, c))},
     g(f(b, b), g(a, c)): {g(f(b, b), g(b, a))},
     f(f(a, b), g(b, a)): {f(f(a, c), g(b, a))},
     g(g(a, a), c): {g(g(a, a), f(a, a))},
     f(f(c, c), f(a, b)): {f(f(c, c), f(a, c))},
     g(g(b, a), f(a, c)): {g(g(b, a), f(b, a))},
     g(g(c, a), f(a, a)): {g(g(c, a), f(a, b))},
     g(g(a, c), c): {g(g(a, c), f(a, a))},
     g(f(c, b), f(b, c)): {g(f(c, b), f(c, a))},
     f(g(c, a), g(b, a)): {f(g(c, a), g(b, b))},
     f(c, f(b, a)): {f(c, f(b, b))},
     f(g(c, b), f(c, a)): {f(g(c, b), f(c, b))},
     g(f(a, a), f(a, a)): {g(f(a, a), f(a, b))},
     f(g(a, b), g(b, b)): {f(g(a, c), g(b, b))},
     f(f(b, c), b): {f(f(b, c), c)},
     g(f(b, a), f(c, b)): {g(f(b, a), f(c, c))},
     g(f(b, a), g(c, c)): {g(f(b, b), a)},
     f(g(b, b), f(b, a)): {f(g(b, b), f(b, b))},
     g(f(c, b), g(c, b)): {g(f(c, b), g(c, c))},
     g(b, g(c, a)): {g(c, b)},
     f(g(c, c), f(c, b)): {f(g(c, c), f(c, c))},
     f(f(b, c), f(a, b)): {f(f(b, c), f(a, c))},
     f(c, g(a, a)): {f(f(a, a), g(a, a))},
     g(f(c, b), f(c, c)): {g(f(c, b), g(a, a))},
     f(g(b, b), g(a, b)): {f(g(b, b), g(a, c))},
     g(g(a, b), g(b, a)): {g(g(a, b), g(b, b))},
     f(g(b, b), g(a, a)): {f(g(b, b), g(a, b))},
     g(g(a, b), f(a, b)): {g(g(a, b), f(a, c))},
     f(g(c, b), g(c, c)): {f(g(c, c), a)},
     g(f(c, a), g(c, b)): {g(f(c, a), g(c, c))},
     g(f(c, a), f(c, c)): {g(f(c, a), g(a, a))},
     f(g(c, b), g(a, c)): {f(g(c, b), g(b, a))},
     f(g(b, b), c): {f(g(b, b), f(a, a))},
     f(f(a, b), a): {f(f(a, b), b)},
     g(g(b, a), a): {g(g(b, a), b)},
     f(g(b, a), g(b, c)): {f(g(b, b), g(b, c))},
     g(a, g(a, a)): {g(a, g(a, b))},
     f(a, f(b, a)): {f(b, b)},
     f(g(a, c), f(c, a)): {f(g(a, c), f(c, b))},
     f(g(a, a), g(c, b)): {f(g(a, b), g(c, b))},
     g(b, f(a, c)): {g(b, f(b, a))},
     f(f(b, a), f(b, a)): {f(f(b, a), f(b, b))},
     f(g(b, c), f(b, b)): {f(g(b, c), f(b, c))},
     g(g(c, c), f(a, c)): {g(g(c, c), f(b, a))},
     g(g(c, c), f(a, b)): {g(g(c, c), f(a, c))},
     g(f(a, c), g(c, b)): {g(f(a, c), g(c, c))},
     g(f(b, b), g(c, b)): {g(f(b, b), g(c, c))},
     g(f(c, b), f(a, a)): {g(f(c, b), f(a, b))},
     f(f(b, a), g(a, b)): {f(f(b, b), g(a, b))},
     g(g(a, a), f(c, a)): {g(g(a, a), f(c, b))},
     f(f(c, b), g(b, a)): {f(f(c, c), g(b, a))},
     g(f(a, a), b): {g(f(a, a), c)},
     g(g(c, a), f(b, c)): {g(g(c, a), f(c, a))},
     f(f(a, b), f(c, b)): {f(f(a, b), f(c, c))},
     f(g(c, b), f(b, b)): {f(g(c, b), f(b, c))},
     g(f(a, c), f(c, c)): {g(f(a, c), g(a, a))},
     g(g(b, c), f(b, a)): {g(g(b, c), f(b, b))},
     g(f(c, c), g(c, b)): {g(f(c, c), g(c, c))},
     g(f(a, c), b): {g(f(a, c), c)},
     f(g(a, b), g(c, a)): {f(g(a, c), g(c, a))},
     g(f(c, c), f(c, c)): {g(f(c, c), g(a, a))},
     g(g(b, c), g(a, b)): {g(g(b, c), g(a, c))},
     f(f(a, a), f(c, c)): {f(f(a, b), a)},
     f(g(b, a), f(c, b)): {f(g(b, a), f(c, c))},
     f(g(b, a), g(c, c)): {f(g(b, b), g(c, c))},
     f(f(c, a), g(b, a)): {f(f(c, b), g(b, a))},
     f(f(b, a), c): {f(f(b, a), f(a, a))},
     f(f(a, a), f(a, c)): {f(f(a, a), f(b, a))},
     f(g(c, b), f(a, a)): {f(g(c, b), f(a, b))},
     g(c, g(c, c)): {g(f(a, a), a)},
     g(f(b, c), g(c, b)): {g(f(b, c), g(c, c))},
     f(f(c, a), f(a, b)): {f(f(c, a), f(a, c))},
     f(f(a, b), g(b, b)): {f(f(a, c), g(b, b))},
     g(g(a, a), g(c, c)): {g(g(a, b), a)},
     g(g(a, a), f(b, a)): {g(g(a, a), f(b, b))},
     g(g(b, b), g(c, c)): {g(g(b, c), a)},
     g(f(b, b), b): {g(f(b, b), c)},
     f(f(c, b), g(c, a)): {f(f(c, c), g(c, a))},
     g(g(a, c), f(b, a)): {g(g(a, c), f(b, b))},
     g(g(a, a), g(a, b)): {g(g(a, a), g(a, c))},
     g(g(c, c), a): {g(g(c, c), b)},
     f(b, g(b, c)): {f(c, g(b, c))},
     f(c, f(b, b)): {f(c, f(b, c))},
     g(f(a, b), g(b, a)): {g(f(a, b), g(b, b))},
     g(g(b, c), g(a, a)): {g(g(b, c), g(a, b))},
     f(f(b, b), f(c, c)): {f(f(b, c), a)},
     g(f(c, c), f(a, b)): {g(f(c, c), f(a, c))},
     g(g(c, b), g(b, c)): {g(g(c, b), g(c, a))},
     f(f(a, a), f(a, b)): {f(f(a, a), f(a, c))},
     f(f(a, c), g(b, a)): {f(f(b, a), g(b, a))},
     f(g(a, c), f(b, b)): {f(g(a, c), f(b, c))},
     f(g(b, b), f(b, b)): {f(g(b, b), f(b, c))},
     g(c, f(b, a)): {g(c, f(b, b))},
     f(f(a, c), f(a, b)): {f(f(a, c), f(a, c))},
     f(f(b, b), f(a, b)): {f(f(b, b), f(a, c))},
     g(g(c, b), f(c, a)): {g(g(c, b), f(c, b))},
     f(f(c, c), g(b, a)): {f(g(a, a), g(b, a))},
     g(g(a, b), g(b, b)): {g(g(a, b), g(b, c))},
     g(f(b, c), b): {g(f(b, c), c)},
     g(g(b, b), f(b, a)): {g(g(b, b), f(b, b))},
     g(g(c, c), f(c, b)): {g(g(c, c), f(c, c))},
     g(f(b, c), f(a, b)): {g(f(b, c), f(a, c))},
     g(c, g(a, a)): {g(c, g(a, b))},
     f(f(c, a), a): {f(f(c, a), b)},
     g(g(b, b), g(a, b)): {g(g(b, b), g(a, c))},
     f(b, f(c, a)): {f(c, b)},
     g(g(a, c), g(a, a)): {g(g(a, c), g(a, b))},
     g(g(b, b), g(a, a)): {g(g(b, b), g(a, b))},
     g(g(c, b), g(c, c)): {g(g(c, c), a)},
     f(g(b, c), f(c, a)): {f(g(b, c), f(c, b))},
     f(f(b, b), f(a, a)): {f(f(b, b), f(a, b))},
     g(g(c, b), g(a, c)): {g(g(c, b), g(b, a))},
     g(g(b, b), c): {g(g(b, b), f(a, a))},
     f(g(c, b), f(b, c)): {f(g(c, b), f(c, a))},
     f(g(a, b), g(a, a)): {f(g(a, b), g(a, b))},
     f(a, f(b, b)): {f(b, c)},
     g(f(a, b), a): {g(f(a, b), b)},
     f(f(b, a), f(b, b)): {f(f(b, a), f(b, c))},
     f(f(c, b), g(b, b)): {f(f(c, c), g(b, b))},
     f(f(a, c), a): {f(f(a, c), b)},
     f(f(b, b), a): {f(f(b, b), b)},
     g(g(b, a), g(b, c)): {g(g(b, a), g(c, a))},
     f(g(c, a), g(c, a)): {g(a, g(c, a))},
     g(a, f(b, a)): {g(a, f(b, b))},
     g(g(a, c), f(c, a)): {g(g(a, c), f(c, b))},
     f(f(c, c), a): {f(f(c, c), b)},
     c: {f(a, a)},
     g(f(b, a), f(b, a)): {g(f(b, a), f(b, b))},
     g(g(b, c), f(b, b)): {g(g(b, c), f(b, c))},
     f(b, g(a, b)): {f(c, g(a, b))},
     g(f(b, a), g(a, b)): {g(f(b, a), g(a, c))},
     f(a, c): {f(a, f(a, a))},
     g(g(c, b), f(b, b)): {g(g(c, b), f(b, c))},
     f(f(c, a), g(b, b)): {f(f(c, b), g(b, b))},
     f(f(c, a), b): {f(f(c, a), c)},
     f(f(a, b), g(c, a)): {f(f(a, c), g(c, a))},
     g(f(a, a), g(c, b)): {g(f(a, a), g(c, c))},
     f(g(b, c), g(a, c)): {f(g(b, c), g(b, a))},
     f(f(b, c), a): {f(f(b, c), b)},
     g(g(a, b), g(c, a)): {g(g(a, b), g(c, b))},
     g(f(a, a), f(c, c)): {g(f(a, a), g(a, a))},
     f(f(c, c), f(c, b)): {f(f(c, c), f(c, c))},
     g(g(b, a), f(c, b)): {g(g(b, a), f(c, c))},
     g(g(b, a), g(c, c)): {g(g(b, b), a)},
     f(b, c): {f(a, f(b, c))},
     g(f(b, a), c): {g(f(b, a), f(a, a))},
     f(c, f(c, a)): {f(c, f(c, b))},
     g(g(c, b), f(a, a)): {g(g(c, b), f(a, b))},
     g(f(c, a), f(a, b)): {g(f(c, a), f(a, c))},
     g(g(c, b), c): {g(g(c, b), f(a, a))},
     g(f(a, b), g(b, b)): {g(f(a, b), g(b, c))},
     f(g(a, c), f(b, c)): {f(g(a, c), f(c, a))},
     f(g(b, b), f(b, c)): {f(g(b, b), f(c, a))},
     f(g(a, b), f(c, b)): {f(g(a, b), f(c, c))},
     f(f(b, b), g(b, b)): {f(f(b, c), g(b, b))},
     g(g(c, c), g(b, a)): {g(g(c, c), g(b, b))},
     f(f(b, c), f(c, b)): {f(f(b, c), f(c, c))},
     f(g(a, a), g(a, c)): {f(g(a, b), g(a, c))},
     f(f(c, c), g(b, b)): {f(g(a, a), g(b, b))},
     f(g(a, c), g(a, c)): {g(a, f(a, a))},
     g(c, f(b, b)): {g(c, f(b, c))},
     f(f(b, b), f(b, c)): {f(f(b, b), f(c, a))},
     g(f(b, b), f(c, c)): {g(f(b, b), g(a, a))},
     f(f(a, b), f(a, c)): {f(f(a, b), f(b, a))},
     f(g(c, a), g(b, b)): {f(g(c, a), g(b, c))},
     g(f(a, a), f(a, b)): {g(f(a, a), f(a, c))},
     g(g(a, c), f(b, b)): {g(g(a, c), f(b, c))},
     g(g(b, b), f(b, b)): {g(g(b, b), f(b, c))},
     g(f(a, c), f(a, b)): {g(f(a, c), f(a, c))},
     f(g(c, a), f(a, c)): {f(g(c, a), f(b, a))},
     f(g(c, a), f(a, b)): {f(g(c, a), f(a, c))},
     g(f(b, b), f(a, b)): {g(f(b, b), f(a, c))},
     g(f(c, c), g(b, a)): {g(f(c, c), g(b, b))},
     a: {b},
     f(c, g(a, c)): {f(f(a, a), g(a, c))},
     f(c, g(a, b)): {f(f(a, a), g(a, b))},
     f(f(a, a), g(b, a)): {f(f(a, b), g(b, a))},
     f(f(b, c), g(b, b)): {f(f(c, a), g(b, b))},
     g(f(c, a), f(a, a)): {g(f(c, a), f(a, b))},
     f(f(a, b), g(a, a)): {f(f(a, c), g(a, a))},
     f(g(b, a), f(b, a)): {f(g(b, a), f(b, b))},
     g(g(c, c), g(c, a)): {g(g(c, c), g(c, b))},
     f(g(b, b), g(a, c)): {f(g(b, b), g(b, a))},
     g(f(c, a), a): {g(f(c, a), b)},
     f(g(b, a), g(a, b)): {f(g(b, a), g(a, c))},
     f(f(b, a), f(b, c)): {f(f(b, a), f(c, a))},
     g(f(b, c), f(c, c)): {g(f(b, c), g(a, a))},
     f(a, f(c, a)): {f(b, f(c, a))},
     g(g(a, b), f(a, c)): {g(g(a, b), f(b, a))},
     f(c, f(a, a)): {f(c, f(a, b))},
     g(g(b, c), g(b, c)): {g(g(b, c), g(c, a))},
     f(c, c): {f(a, f(c, c))},
     f(g(a, a), f(a, a)): {f(g(a, a), f(a, b))},
     f(f(b, a), g(c, b)): {f(f(b, b), g(c, b))},
     f(g(a, c), f(a, a)): {f(g(a, c), f(a, b))},
     f(g(b, b), f(a, a)): {f(g(b, b), f(a, b))},
     f(g(c, b), g(c, b)): {g(a, g(c, b))},
     g(g(b, c), f(c, a)): {g(g(b, c), f(c, b))},
     g(f(a, c), f(a, a)): {g(f(a, c), f(a, b))},
     g(f(b, b), f(a, a)): {g(f(b, b), f(a, b))},
     f(g(b, a), c): {f(g(b, a), f(a, a))},
     f(f(b, b), g(b, a)): {f(f(b, c), g(b, a))},
     g(g(c, b), f(b, c)): {g(g(c, b), f(c, a))},
     f(g(c, b), f(c, c)): {f(g(c, b), g(a, a))},
     g(a, f(b, b)): {g(a, f(b, c))},
     g(f(b, a), f(b, b)): {g(f(b, a), f(b, c))},
     f(f(c, a), g(c, a)): {f(f(c, b), g(c, a))},
     f(g(c, b), b): {f(g(c, b), c)},
     g(f(c, b), g(b, b)): {g(f(c, b), g(b, c))},
     f(g(c, a), a): {f(g(c, a), b)},
     g(f(a, c), a): {g(f(a, c), b)},
     g(f(c, b), b): {g(f(c, b), c)},
     g(g(c, a), g(c, a)): {g(g(c, a), g(c, b))},
     g(b, f(c, b)): {g(b, f(c, c))},
     g(f(c, c), a): {g(f(c, c), b)},
     f(f(a, a), a): {f(f(a, a), b)},
     f(a, g(a, c)): {f(b, g(a, c))},
     f(a, g(a, b)): {f(b, g(a, b))},
     f(f(b, a), g(a, c)): {f(f(b, b), g(a, c))},
     g(g(b, c), g(c, c)): {g(g(c, a), a)},
     g(a, c): {f(a, g(a, c))},
     g(f(c, a), g(b, b)): {g(f(c, a), g(b, c))},
     g(f(c, a), b): {g(f(c, a), c)},
     f(b, g(c, c)): {f(c, g(c, c))},
     f(f(c, b), f(a, c)): {f(f(c, b), f(b, a))},
     f(f(b, c), g(b, a)): {f(f(c, a), g(b, a))},
     g(f(a, b), g(c, a)): {g(f(a, b), g(c, b))},
     g(g(a, b), a): {g(g(a, b), b)},
     f(g(c, a), f(c, b)): {f(g(c, a), f(c, c))},
     g(g(b, c), g(a, c)): {g(g(b, c), g(b, a))},
     f(g(c, c), f(b, a)): {f(g(c, c), f(b, b))},
     g(f(b, c), a): {g(f(b, c), b)},
     g(g(c, b), f(b, a)): {g(g(c, b), f(b, b))},
     f(f(b, b), g(c, a)): {f(f(b, c), g(c, a))},
     g(f(c, a), f(b, c)): {g(f(c, a), f(c, a))},
     f(g(a, b), g(b, c)): {f(g(a, c), g(b, c))},
     g(f(c, c), f(c, b)): {g(f(c, c), f(c, c))},
     f(f(b, a), f(a, a)): {f(f(b, a), f(a, b))},
     f(f(a, a), f(c, b)): {f(f(a, a), f(c, c))},
     f(f(c, c), g(c, a)): {f(g(a, a), g(c, a))},
     g(g(c, b), g(a, b)): {g(g(c, b), g(a, c))},
     g(c, f(c, a)): {g(c, f(c, b))},
     f(f(c, a), f(a, c)): {f(f(c, a), f(b, a))},
     f(g(a, a), b): {f(g(a, a), c)},
     g(g(a, c), f(b, c)): {g(g(a, c), f(c, a))},
     f(g(a, c), b): {f(g(a, c), c)},
     g(g(b, b), f(c, a)): {g(g(b, b), f(c, b))},
     g(g(a, b), f(c, b)): {g(g(a, b), f(c, c))},
     g(f(b, c), f(c, b)): {g(f(b, c), f(c, c))},
     g(g(a, a), g(a, c)): {g(g(a, a), g(b, a))},
     f(g(a, a), f(b, c)): {f(g(a, a), f(c, a))},
     f(f(b, c), g(c, a)): {f(f(c, a), g(c, a))},
     g(f(c, c), g(b, b)): {g(f(c, c), g(b, c))},
     g(g(a, c), g(a, c)): {g(g(a, c), g(b, a))},
     f(f(a, a), g(b, b)): {f(f(a, b), g(b, b))},
     g(f(a, c), f(b, c)): {g(f(a, c), f(c, a))},
     g(f(b, b), f(b, c)): {g(f(b, b), f(c, a))},
     f(b, g(a, a)): {f(c, g(a, a))},
     f(f(a, c), g(b, b)): {f(f(b, a), g(b, b))},
     f(g(a, b), g(c, c)): {f(g(a, c), g(c, c))},
     f(f(c, b), a): {f(f(c, b), b)},
     g(f(a, b), f(a, c)): {g(f(a, b), f(b, a))},
     g(g(c, a), g(b, b)): {g(g(c, a), g(b, c))},
     f(g(c, c), g(a, a)): {f(g(c, c), g(a, b))},
     f(g(b, a), f(b, b)): {f(g(b, a), f(b, c))},
     f(f(a, c), f(a, c)): {f(f(a, c), f(b, a))},
     f(f(b, b), f(a, c)): {f(f(b, b), f(b, a))},
     g(g(c, a), f(a, c)): {g(g(c, a), f(b, a))},
     g(g(c, a), f(a, b)): {g(g(c, a), f(a, c))},
     g(c, g(a, c)): {g(c, g(b, a))},
     g(c, g(a, b)): {g(c, g(a, c))},
     g(f(a, a), g(b, a)): {g(f(a, a), g(b, b))},
     g(f(b, c), g(b, b)): {g(f(b, c), g(b, c))},
     g(g(b, c), c): {g(g(b, c), f(a, a))},
     g(g(b, a), f(b, a)): {g(g(b, a), f(b, b))},
     f(a, g(c, b)): {f(b, g(c, b))},
     g(a, g(b, c)): {g(b, f(a, a))},
     g(g(a, c), g(a, b)): {g(g(a, c), g(a, c))},
     g(g(b, b), g(a, c)): {g(g(b, b), g(b, a))},
     g(g(b, a), g(a, b)): {g(g(b, a), g(a, c))},
     g(a, f(c, a)): {g(a, f(c, b))},
     f(f(c, b), f(c, b)): {f(f(c, b), f(c, c))},
     f(f(c, c), g(a, a)): {f(g(a, a), a)},
     g(f(b, a), f(c, a)): {g(f(b, a), f(c, b))},
     g(c, c): {f(a, g(c, c))},
     g(g(a, a), f(a, a)): {g(g(a, a), f(a, b))},
     g(f(b, a), g(c, b)): {g(f(b, a), g(c, c))},
     g(g(a, c), f(a, a)): {g(g(a, c), f(a, b))},
     g(g(b, b), f(a, a)): {g(g(b, b), f(a, b))},
     g(g(c, b), g(c, b)): {g(g(c, b), g(c, c))},
     g(g(b, a), c): {g(g(b, a), f(a, a))},
     g(f(b, b), g(b, a)): {g(f(b, b), g(b, b))},
     g(g(c, b), f(c, c)): {g(g(c, b), g(a, a))},
     f(f(b, c), g(a, a)): {f(f(c, a), g(a, a))},
     g(f(c, a), g(c, a)): {g(f(c, a), g(c, b))},
     g(g(c, b), b): {g(g(c, b), c)},
     f(f(a, b), g(b, c)): {f(f(a, c), g(b, c))},
     g(g(c, a), a): {g(g(c, a), b)},
     g(a, g(c, c)): {g(b, g(c, c))},
     g(g(b, a), g(a, a)): {g(g(b, a), g(a, b))},
     f(g(a, b), c): {f(g(a, b), f(a, a))},
     g(f(a, a), a): {g(f(a, a), b)},
     g(a, g(a, c)): {g(b, a)},
     g(a, g(a, b)): {g(a, g(a, c))},
     g(f(b, a), g(a, c)): {g(f(b, a), g(b, a))},
     g(b, g(c, c)): {g(c, f(a, a))},
     g(f(c, b), f(a, c)): {g(f(c, b), f(b, a))},
     g(f(b, c), g(b, a)): {g(f(b, c), g(b, b))},
     f(g(a, a), g(c, a)): {f(g(a, b), g(c, a))},
     f(g(b, c), g(c, b)): {f(g(c, a), g(c, b))},
     g(g(c, a), f(c, b)): {g(g(c, a), f(c, c))},
     f(g(b, c), f(c, c)): {f(g(b, c), g(a, a))},
     g(f(b, b), g(c, a)): {g(f(b, b), g(c, b))},
     g(g(a, b), g(b, c)): {g(g(a, b), g(c, a))},
     f(g(b, c), b): {f(g(b, c), c)},
     g(f(b, a), f(a, a)): {g(f(b, a), f(a, b))},
     f(f(a, b), g(c, c)): {f(f(a, c), g(c, c))},
     g(f(a, a), f(c, b)): {g(f(a, a), f(c, c))},
     g(f(c, c), g(c, a)): {g(f(c, c), g(c, b))},
     f(f(a, a), g(c, a)): {f(f(a, b), g(c, a))},
     f(g(b, c), f(a, b)): {f(g(b, c), f(a, c))},
     f(b, f(b, b)): {f(b, f(b, c))},
     g(f(c, a), f(a, c)): {g(f(c, a), f(b, a))},
     f(g(c, b), g(b, a)): {f(g(c, b), g(b, b))},
     g(g(a, a), b): {g(g(a, a), c)},
     f(f(a, c), g(c, a)): {f(f(b, a), g(c, a))},
     f(c, g(c, b)): {f(f(a, a), g(c, b))},
     f(g(c, b), f(a, b)): {f(g(c, b), f(a, c))},
     g(f(c, b), f(a, b)): {g(f(c, b), f(a, c))},
     g(g(a, c), b): {g(g(a, c), c)},
     f(g(b, a), f(c, a)): {f(g(b, a), f(c, b))},
     g(g(a, a), f(b, c)): {g(g(a, a), f(c, a))},
     f(g(a, c), g(c, b)): {f(g(b, a), g(c, b))},
     f(g(b, b), g(c, b)): {f(g(b, c), g(c, b))},
     f(g(a, a), f(c, c)): {f(g(a, a), g(a, a))},
     g(f(b, c), g(c, a)): {g(f(b, c), g(c, b))},
     g(f(a, a), g(b, b)): {g(f(a, a), g(b, c))},
     f(g(a, c), f(c, c)): {f(g(a, c), g(a, a))},
     f(g(a, a), f(a, c)): {f(g(a, a), f(b, a))},
     g(b, g(a, a)): {g(b, g(a, b))},
     f(b, f(b, a)): {f(b, f(b, b))},
     g(f(a, c), g(b, b)): {g(f(a, c), g(b, c))},
     g(g(a, b), g(c, c)): {g(g(a, c), a)},
     g(f(c, b), a): {g(f(c, b), b)},
     g(g(c, c), g(a, a)): {g(g(c, c), g(a, b))},
     f(g(a, c), f(a, c)): {f(g(a, c), f(b, a))},
     g(g(b, a), f(b, b)): {g(g(b, a), f(b, c))},
     g(f(a, c), f(a, c)): {g(f(a, c), f(b, a))},
     f(f(a, b), g(a, b)): {f(f(a, c), g(a, b))},
     g(f(b, b), f(a, c)): {g(f(b, b), f(b, a))},
     f(g(b, c), f(a, a)): {f(g(b, c), f(a, b))},
     g(f(c, c), f(a, c)): {g(f(c, c), f(b, a))},
     g(a, g(c, b)): {g(b, g(c, b))},
     f(c, b): {f(a, f(c, b))},
     f(g(b, a), g(a, c)): {f(g(b, a), g(b, a))},
     f(c, f(a, b)): {f(c, f(a, c))},
     g(f(c, b), f(c, b)): {g(f(c, b), f(c, c))},
     f(g(c, b), a): {f(g(c, b), b)},
     f(g(b, b), b): {f(g(b, b), c)},
     g(f(c, c), g(a, a)): {g(f(c, c), g(a, b))},
     f(f(a, b), c): {f(f(a, b), f(a, a))},
     f(f(a, a), g(a, a)): {f(f(a, b), g(a, a))},
     f(g(a, c), f(a, b)): {f(g(a, c), f(a, c))},
     f(g(b, b), f(a, b)): {f(g(b, b), f(a, c))},
     g(f(b, c), f(a, c)): {g(f(b, c), f(b, a))},
     f(g(c, c), g(b, c)): {f(g(c, c), g(c, a))},
     f(g(b, a), f(a, a)): {f(g(b, a), f(a, b))},
     g(g(c, a), g(b, a)): {g(g(c, a), g(b, b))},
     f(g(a, b), f(b, a)): {f(g(a, b), f(b, b))},
     g(f(b, c), g(a, a)): {g(f(b, c), g(a, b))},
     f(g(c, c), f(c, a)): {f(g(c, c), f(c, b))},
     f(f(a, a), g(b, c)): {f(f(a, b), g(b, c))},
     f(g(a, b), g(a, b)): {g(a, c)},
     g(g(a, b), c): {g(g(a, b), f(a, a))},
     f(f(c, c), g(b, c)): {f(g(a, a), g(b, c))},
     f(a, f(c, c)): {f(b, f(c, c))},
     f(a, b): {f(a, c)},
     f(f(b, a), b): {f(f(b, a), c)},
     g(g(b, c), g(c, b)): {g(g(b, c), g(c, c))},
     f(a, f(a, b)): {f(a, f(a, c))},
     f(g(c, c), g(c, c)): {g(a, g(c, c))},
     f(g(c, b), g(b, b)): {f(g(c, b), g(b, c))},
     f(g(b, c), f(b, c)): {f(g(b, c), f(c, a))},
     g(g(b, c), f(c, c)): {g(g(b, c), g(a, a))},
     f(b, g(a, c)): {f(c, g(a, c))},
     g(g(b, c), b): {g(g(b, c), c)},
     f(g(c, c), g(a, c)): {f(g(c, c), g(b, a))},
     f(f(c, a), f(c, b)): {f(f(c, a), f(c, c))},
     g(f(a, a), g(c, a)): {g(f(a, a), g(c, b))},
     g(b, f(b, b)): {g(b, f(b, c))},
     g(g(c, b), g(b, a)): {g(g(c, b), g(b, b))},
     g(f(a, c), g(c, a)): {g(f(a, c), g(c, b))},
     g(c, g(c, b)): {g(c, g(c, c))},
     g(g(c, b), f(a, b)): {g(g(c, b), f(a, c))},
     f(f(c, c), g(c, c)): {f(g(a, a), g(c, c))},
     g(g(b, a), f(c, a)): {g(g(b, a), f(c, b))},
     g(g(a, a), g(c, b)): {g(g(a, a), g(c, c))},
     g(g(a, c), g(c, b)): {g(g(a, c), g(c, c))},
     g(g(b, b), g(c, b)): {g(g(b, b), g(c, c))},
     g(g(a, a), f(c, c)): {g(g(a, a), g(a, a))},
     f(a, f(a, a)): {f(a, f(a, b))},
     g(f(c, b), g(b, a)): {g(f(c, b), g(b, b))},
     g(g(a, c), f(c, c)): {g(g(a, c), g(a, a))},
     f(g(c, c), g(a, b)): {f(g(c, c), g(a, c))},
     g(f(a, b), f(c, b)): {g(f(a, b), f(c, c))},
     g(b, f(b, a)): {g(b, f(b, b))},
     f(f(a, c), f(c, b)): {f(f(a, c), f(c, c))},
     f(f(b, b), f(c, b)): {f(f(b, b), f(c, c))},
     f(f(b, c), f(c, a)): {f(f(b, c), f(c, b))},
     g(g(b, c), f(a, a)): {g(g(b, c), f(a, b))},
     f(b, f(a, a)): {f(b, f(a, b))},
     f(c, f(b, c)): {f(c, f(c, a))},
     f(g(b, c), g(b, a)): {f(g(b, c), g(b, b))},
     g(f(c, a), g(b, a)): {g(f(c, a), g(b, b))},
     f(f(a, b), f(b, a)): {f(f(a, b), f(b, b))},
     g(f(a, a), f(a, c)): {g(f(a, a), f(b, a))},
     g(c, b): {f(a, g(c, b))},
     f(g(c, c), c): {f(g(c, c), f(a, a))},
     f(f(c, c), g(a, b)): {f(g(a, a), g(a, b))},
     g(g(b, a), g(a, c)): {g(g(b, a), g(b, a))},
     f(g(c, a), f(b, a)): {f(g(c, a), f(b, b))},
     g(g(c, b), a): {g(g(c, b), b)},
     g(g(b, b), b): {g(g(b, b), c)},
     g(f(c, b), g(c, a)): {g(f(c, b), g(c, b))},
     f(c, f(c, c)): {f(f(a, a), a)},
     f(g(c, a), g(a, b)): {f(g(c, a), g(a, c))},
     g(f(a, a), g(a, a)): {g(f(a, a), g(a, b))},
     g(g(a, c), f(a, b)): {g(g(a, c), f(a, c))},
     g(g(b, b), f(a, b)): {g(g(b, b), f(a, c))},
     f(g(a, b), f(b, b)): {f(g(a, b), f(b, c))},
     g(b, g(b, c)): {g(c, a)},
     f(g(a, a), g(b, a)): {f(g(a, b), g(b, a))},
     f(g(b, b), f(c, c)): {f(g(b, b), g(a, a))},
     f(f(b, c), g(a, b)): {f(f(c, a), g(a, b))},
     g(g(c, c), g(b, c)): {g(g(c, c), g(c, a))},
     g(g(b, a), f(a, a)): {g(g(b, a), f(a, b))},
     f(f(c, c), c): {f(f(c, c), f(a, a))},
     f(g(a, a), f(a, b)): {f(g(a, a), f(a, c))},
     f(g(a, c), g(b, a)): {f(g(b, a), a)},
     g(f(a, c), g(b, a)): {g(f(a, c), g(b, b))},
     g(g(a, b), f(b, a)): {g(g(a, b), f(b, b))},
     g(g(c, c), f(c, a)): {g(g(c, c), f(c, b))},
     f(g(b, b), f(a, c)): {f(g(b, b), f(b, a))},
     f(g(c, a), c): {f(g(c, a), f(a, a))},
     g(g(a, b), g(a, b)): {g(g(a, b), g(a, c))},
     f(f(c, b), f(b, b)): {f(f(c, b), f(b, c))},
     f(f(b, c), c): {f(f(b, c), f(a, a))},
     f(a, f(b, c)): {f(b, f(a, a))},
     f(g(c, a), g(a, a)): {f(g(c, a), g(a, b))},
     g(f(c, c), g(b, c)): {g(f(c, c), g(c, a))},
     g(a, f(c, c)): {g(a, g(a, a))},
     g(a, b): {f(a, g(a, b))},
     g(b, f(c, a)): {g(b, f(c, b))},
     f(b, b): {f(a, f(b, b))},
     g(f(b, a), b): {g(f(b, a), c)},
     g(g(c, b), g(b, b)): {g(g(c, b), g(b, c))},
     g(g(b, c), f(b, c)): {g(g(b, c), f(c, a))},
     g(b, g(a, c)): {g(b, g(b, a))},
     f(b, f(b, c)): {f(c, a)},
     f(c, a): {f(a, f(c, a))},
     f(f(b, a), f(c, c)): {f(f(b, b), a)},
     g(g(c, c), g(a, c)): {g(g(c, c), g(b, a))},
     f(f(a, b), f(c, a)): {f(f(a, b), f(c, b))},
     f(f(c, b), f(b, a)): {f(f(c, b), f(b, b))},
     f(g(a, a), a): {f(g(a, a), b)},
     g(g(a, b), g(a, a)): {g(g(a, b), g(a, b))},
     g(f(c, a), f(c, b)): {g(f(c, a), f(c, c))},
     f(g(a, c), a): {f(g(a, c), b)},
     f(f(b, a), f(a, c)): {f(f(b, a), f(b, a))},
     f(g(b, b), a): {f(g(b, b), b)},
     g(f(b, b), a): {g(f(b, b), b)},
     f(g(c, c), f(b, b)): {f(g(c, c), f(b, c))},
     f(g(c, b), f(a, c)): {f(g(c, b), f(b, a))},
     g(f(c, c), g(c, c)): {g(g(a, a), a)},
     f(f(b, b), g(b, c)): {f(f(b, c), g(b, c))},
     f(f(a, a), g(c, c)): {f(f(a, b), g(c, c))},
     f(f(c, a), f(b, a)): {f(f(c, a), f(b, b))},
     g(b, g(a, b)): {g(b, g(a, c))},
     g(a, f(a, a)): {g(a, f(a, b))},
     f(g(b, c), g(b, b)): {f(g(b, c), g(b, c))},
     f(g(a, a), f(c, b)): {f(g(a, a), f(c, c))},
     f(a, g(b, a)): {f(b, g(b, a))},
     g(g(c, c), g(a, b)): {g(g(c, c), g(a, c))},
     f(g(a, c), f(c, b)): {f(g(a, c), f(c, c))},
     f(g(b, b), f(c, b)): {f(g(b, b), f(c, c))},
     f(f(c, c), f(b, b)): {f(f(c, c), f(b, c))},
     g(f(a, c), f(c, b)): {g(f(a, c), f(c, c))},
     g(f(b, b), f(c, b)): {g(f(b, b), f(c, c))},
     f(f(b, a), f(a, b)): {f(f(b, a), f(a, c))},
     g(f(b, c), f(c, a)): {g(f(b, c), f(c, b))},
     f(f(b, c), g(b, c)): {f(f(c, a), g(b, c))},
     g(b, f(a, a)): {g(b, f(a, b))},
     g(c, f(b, c)): {g(c, f(c, a))},
     f(f(c, b), g(a, a)): {f(f(c, c), g(a, a))},
     f(g(c, a), f(b, b)): {f(g(c, a), f(b, c))},
     g(g(b, c), g(b, a)): {g(g(b, c), g(b, b))},
     g(b, c): {f(a, g(b, c))},
     g(f(a, b), f(b, a)): {g(f(a, b), f(b, b))},
     f(g(a, b), f(c, a)): {f(g(a, b), f(c, b))},
     f(f(a, a), f(b, a)): {f(f(a, a), f(b, b))},
     f(c, g(b, b)): {f(f(a, a), g(b, b))},
     f(g(b, a), g(c, b)): {f(g(b, b), g(c, b))},
     g(g(c, c), c): {g(g(c, c), f(a, a))},
     f(f(b, b), g(c, c)): {f(f(b, c), g(c, c))},
     g(f(c, c), g(a, b)): {g(f(c, c), g(a, c))},
     f(g(a, a), g(b, b)): {f(g(a, b), g(b, b))},
     f(f(a, c), f(b, a)): {f(f(a, c), f(b, b))},
     f(f(b, a), a): {f(f(b, a), b)},
     g(g(b, b), f(b, c)): {g(g(b, b), f(c, a))},
     f(f(a, a), g(a, b)): {f(f(a, b), g(a, b))},
     f(g(b, a), f(c, c)): {f(g(b, a), g(a, a))},
     f(g(a, c), g(b, b)): {f(g(b, a), g(b, b))},
     f(g(b, b), g(b, b)): {g(a, g(b, b))},
     g(f(b, b), g(b, b)): {g(f(b, b), g(b, c))},
     f(g(b, a), b): {f(g(b, a), c)},
     f(f(a, c), g(a, b)): {f(f(b, a), g(a, b))},
     f(f(c, c), f(b, a)): {f(f(c, c), f(b, b))},
     g(c, f(c, c)): {g(c, g(a, a))},
     f(f(a, b), f(b, b)): {f(f(a, b), f(b, c))},
     f(g(b, a), f(a, c)): {f(g(b, a), f(b, a))},
     f(g(b, a), f(a, b)): {f(g(b, a), f(a, c))},
     f(f(c, b), g(b, c)): {f(f(c, c), g(b, c))},
     f(f(c, a), g(a, a)): {f(f(c, b), g(a, a))},
     g(g(a, b), f(b, b)): {g(g(a, b), f(b, c))},
     g(g(a, a), g(b, a)): {g(g(a, a), g(b, b))},
     g(g(b, b), f(c, c)): {g(g(b, b), g(a, a))},
     g(f(b, c), g(a, b)): {g(f(b, c), g(a, c))},
     f(f(c, b), f(c, a)): {f(f(c, b), f(c, b))},
     g(f(c, c), c): {g(f(c, c), f(a, a))},
     g(g(a, a), f(a, b)): {g(g(a, a), f(a, c))},
     g(g(a, c), g(b, a)): {g(g(a, c), g(b, b))},
     f(f(a, a), c): {f(f(a, a), f(a, a))},
     f(f(b, c), g(c, c)): {f(f(c, a), g(c, c))},
     f(f(b, a), f(c, b)): {f(f(b, a), f(c, c))},
     g(g(b, b), f(a, c)): {g(g(b, b), f(b, a))},
     f(f(a, c), c): {f(f(a, c), f(a, a))},
     g(g(c, a), c): {g(g(c, a), f(a, a))},
     f(g(a, b), g(a, c)): {f(g(a, c), a)},
     f(f(b, c), g(a, c)): {f(f(c, a), g(a, c))},
     g(f(a, b), g(a, a)): {g(f(a, b), g(a, b))},
     f(f(c, a), f(c, a)): {f(f(c, a), f(c, b))},
     f(g(b, c), g(c, a)): {f(g(c, a), a)},
     f(f(a, c), g(a, a)): {f(f(b, a), g(a, a))},
     f(f(b, b), g(a, a)): {f(f(b, c), g(a, a))},
     g(f(b, c), c): {g(f(b, c), f(a, a))},
     g(a, f(b, c)): {g(a, f(c, a))},
     g(g(c, a), g(a, a)): {g(g(c, a), g(a, b))},
     g(f(b, a), f(b, c)): {g(f(b, a), f(c, a))},
     g(b, b): {f(a, g(b, b))},
     f(g(c, b), g(c, a)): {f(g(c, b), g(c, b))},
     f(a, f(a, c)): {f(b, a)},
     g(c, f(a, a)): {g(c, f(a, b))},
     f(c, g(b, a)): {f(f(a, a), g(b, a))},
     f(g(b, a), a): {f(g(b, a), b)},
     f(b, g(c, b)): {f(c, g(c, b))},
     f(g(c, c), g(c, b)): {f(g(c, c), g(c, c))},
     g(b, f(b, c)): {g(b, f(c, a))},
     g(c, a): {f(a, g(c, a))},
     f(b, f(c, c)): {f(c, f(a, a))},
     g(f(b, a), f(c, c)): {g(f(b, a), g(a, a))},
     g(f(a, b), f(c, a)): {g(f(a, b), f(c, b))},
     f(g(b, b), g(b, a)): {f(g(b, b), g(b, b))},
     f(g(c, c), f(c, c)): {f(g(c, c), g(a, a))},
     g(g(a, a), a): {g(g(a, a), b)},
     g(g(a, c), a): {g(g(a, c), b)},
     g(f(b, a), f(a, c)): {g(f(b, a), f(b, a))},
     g(g(b, b), a): {g(g(b, b), b)},
     g(g(c, c), f(b, b)): {g(g(c, c), f(b, c))},
     g(g(c, b), f(a, c)): {g(g(c, b), f(b, a))},
     f(f(c, c), f(c, a)): {f(f(c, c), f(c, b))},
     g(f(b, b), g(b, c)): {g(f(b, b), g(c, a))},
     f(g(c, a), g(b, c)): {f(g(c, a), g(c, a))},
     g(f(a, a), g(c, c)): {g(f(a, b), a)},
     f(g(c, a), f(c, a)): {f(g(c, a), f(c, b))},
     g(g(b, c), g(b, b)): {g(g(b, c), g(b, c))},
     f(c, g(c, a)): {f(f(a, a), g(c, a))},
     g(g(a, a), f(c, b)): {g(g(a, a), f(c, c))},
     g(a, g(b, a)): {g(b, b)},
     g(g(a, c), f(c, b)): {g(g(a, c), f(c, c))},
     g(f(c, c), f(b, b)): {g(f(c, c), f(b, c))},
     f(b, f(a, b)): {f(b, f(a, c))},
     g(f(b, a), f(a, b)): {g(f(b, a), f(a, c))},
     f(g(a, c), g(c, a)): {f(g(b, a), g(c, a))},
     f(g(b, b), g(c, a)): {f(g(b, c), g(c, a))},
     g(g(c, c), f(b, a)): {g(g(c, c), f(b, b))},
     f(f(c, a), f(b, b)): {f(f(c, a), f(b, c))},
     g(f(b, c), g(b, c)): {g(f(b, c), g(c, a))},
     g(f(c, b), g(a, a)): {g(f(c, b), g(a, b))},
     g(g(c, a), f(b, b)): {g(g(c, a), f(b, c))},
     f(f(b, a), g(b, a)): {f(f(b, b), g(b, a))},
     f(g(c, c), f(a, a)): {f(g(c, c), f(a, b))},
     f(g(b, c), f(a, c)): {f(g(b, c), f(b, a))},
     g(g(a, b), f(c, a)): {g(g(a, b), f(c, b))},
     g(f(a, a), f(b, a)): {g(f(a, a), f(b, b))},
     g(c, g(b, b)): {g(c, g(b, c))},
     g(g(b, a), g(c, b)): {g(g(b, a), g(c, c))},
     f(g(c, a), g(c, c)): {f(g(c, b), g(c, c))},
     g(f(b, b), g(c, c)): {g(f(b, c), a)},
     g(g(a, a), g(b, b)): {g(g(a, a), g(b, c))},
     f(f(a, b), g(a, c)): {f(f(a, c), g(a, c))},
     f(g(b, a), f(b, c)): {f(g(b, a), f(c, a))},
     g(f(b, a), a): {g(f(b, a), b)},
     g(f(a, a), g(a, b)): {g(f(a, a), g(a, c))},
     g(g(b, a), f(c, c)): {g(g(b, a), g(a, a))},
     g(g(a, c), g(b, b)): {g(g(a, c), g(b, c))},
     g(g(b, b), g(b, b)): {g(g(b, b), g(b, c))},
     g(g(b, a), b): {g(g(b, a), c)},
     g(f(c, c), f(b, a)): {g(f(c, c), f(b, b))},
     f(g(c, a), g(a, c)): {f(g(c, a), g(b, a))},
     f(g(b, c), g(a, a)): {f(g(b, c), g(a, b))},
     g(f(a, b), f(b, b)): {g(f(a, b), f(b, c))},
     f(g(c, b), g(b, c)): {f(g(c, b), g(c, a))},
     g(f(c, a), g(a, a)): {g(f(c, a), g(a, b))},
     g(g(b, a), f(a, b)): {g(g(b, a), f(a, c))},
     g(f(c, b), g(b, c)): {g(f(c, b), g(c, a))},
     f(c, f(a, c)): {f(c, f(b, a))},
     g(f(c, b), f(c, a)): {g(f(c, b), f(c, b))},
     g(f(a, a), c): {g(f(a, a), f(a, a))},
     g(f(b, c), g(c, c)): {g(f(c, a), a)},
     f(a, g(c, a)): {f(b, g(c, a))},
     f(f(b, a), g(c, a)): {f(f(b, b), g(c, a))},
     g(f(a, c), c): {g(f(a, c), f(a, a))},
     g(g(a, b), g(a, c)): {g(g(a, b), g(b, a))},
     g(f(b, c), g(a, c)): {g(f(b, c), g(b, a))},
     f(g(a, a), g(a, a)): {g(a, b)}}

Hmm. How can I do a reasonable check for well foundedness?
Search for loops
But also just veering off into infinity

```python
from dataclasses import dataclass, field


@dataclass(frozen=True)
def App():
    f : str
    args : tuple["App", ...] = ()

def is_subterm(s, t):


class Order(Enum):
    LT = -1
    EQ = 0
    GT = 1

def chkargs(t, s):
    return all(ground_lpo(t, a) == Order.GT for a in s.args)

def ground_lpo(t : App, s : App):
    if t == s:
        return Order.EQ
    cond1 = any(ground_lpo(a, s) == Order.GT or Order.EQ for a in t.args)
    cond2 = any(ground_lpo(t, b) == Order.LT or Order.EQ for b in s.args)
    assert not (cond1 and cond2)
    if cond1:
        return Order.GT
    elif cond2:
        return Order.LT
    else:
        if (t.f, len(t.args)) > (s.f, len(s.args)):
            return Order.GT
        elif (t.f, len(t.args)) > (s.f, len(s.args)):
            return Order.LT
        else:
            

    if any(ground_lpo(a, s) == Order.GT or Order.EQ for a in t.args): # subterm or compatibility of contexts?
        return Order.GT
    elif any(ground_lpo(t, b) == Order.LT or Order.EQ for b in s.args):
        # Interleave the two directions of asking lpo?
        # Having or Order.Eq is strangely symmettric. But only one side can be a subterm of the other
        # This implies chkargs passes
        return Order.LT
    # all of the subterms of t are less than s, and all the subterms of s are greater than t?
    # It is impossible for both of these branches to come back True? That is not obvious.
    # fuzz it?
    else:
        if t.f > s.f:
            return Order.GT
        elif t.f < s.f:
            return Order.LT
        else:
            for (a,b) in zip(t.args, s.args):
                res = ground_lpo(a,b)
                if res != Order.EQ:
                    return res
            else:
                raise ValueError("Unreachable")
    if s == t:
        return Order.EQ
    elif is_subterm(t, s): # This is not what the definition says.
        return Order.GT
    
    
a = App("a")
b = App("b")
c = App("c")
d = App("d")
f = lambda x,y: App("f", (x,y))
g = lambda x,y: App("g", (x,y))
h = lambda x: App("h", (x,))
    



```
