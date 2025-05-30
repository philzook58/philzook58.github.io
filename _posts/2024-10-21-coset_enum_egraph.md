---
title: "Coset Enumeration using Equality Saturation"
date: 2024-10-21
---

As I was digging into [computational group theory](https://en.wikipedia.org/wiki/Computational_group_theory) for [string Knuth Bendix completion](https://www.philipzucker.com/string_knuth/) goodness I noted that coset enumeration aka [Todd-Coxeter](https://en.wikipedia.org/wiki/Todd%E2%80%93Coxeter_algorithm), one of the mainstay algorithms of computational group theory, mechanically looks quite a bit like equality saturation. This is interesting in its own right but also as a source of controlled benchmarks for equality saturation systems.

[Groups](https://en.wikipedia.org/wiki/Group_theory) are a particular algebraic structure for describing things with symmetry. Symmetries are changes that somehow leave something alone. Familiar examples include rotations and [permutations](https://en.wikipedia.org/wiki/Permutation_group). You can compose these things and invert them.

A [subgroup](https://en.wikipedia.org/wiki/Subgroup) of a group is a set of group operations that are closed under the operations. 2D rotations are a subgroup of 3D rotations, or the even permutations are a subgroup of the permutations.

You can define multiplying against a set of group elements as mapping the multiplication over all the elements of the set. When you do this to a subgroup, those are the cosets of that subgroup <https://en.wikipedia.org/wiki/Coset> . Because group multiplication is invertible, this group action is doesn't compress these sets and you can use the subgroup to tile/partition the entire group with cosets. In this way we can decompose and study groups. It's a bit abstract.

# Finitely Presented Groups

To start attacking questions about a particular group, we need to ask how it is described / represented. This is a common theme about any computational problem actually, not just group theory.

A multiplication table (as a python dictionary for example) suffices for rather small finite groups.  This table gets unusably big pretty fast. For permutation groups of elements n, there are n! group elements.

So often you need to come at the group from the side. Sometimes you might describe the group in terms of its action of some other set, like the set of all rubik's cube positions. You similarly might describe it as some subgroup of a fixed finite permutation group.

In some cases, a group is described as a finite number of generators and relations/equations between those generators. These are called finitely [presented groups](https://en.wikipedia.org/wiki/Presentation_of_a_group). For example `<a | a**8 = 1>` is a finite presentation of the [cyclic group](https://en.wikipedia.org/wiki/Cyclic_group) of order 8. There's a nice table here <https://en.wikipedia.org/wiki/Presentation_of_a_group#Examples>. This is what we'll work with.

Here we make a group generated as strings `abbbaaaabbbbaaa` but we identify `aa = 1` and `bbb = 1`. Sympy has a coset enumeration thing in it for us.

<https://docs.sympy.org/latest/modules/combinatorics/fp_groups.html> finitely presented groups in sympy

```python
from sympy.combinatorics.free_groups import free_group, vfree_group, xfree_group
from sympy.combinatorics.fp_groups import FpGroup, CosetTable#, coset_enumeration_rf
from sympy.combinatorics.fp_groups import low_index_subgroups
F, a, b = free_group("a, b")
G = FpGroup(F, [a**2, b**3, (a*b)**4])
l = low_index_subgroups(G, 4)
for coset_table in l:
    print(coset_table.table)
# columns are multiplication a a^-1 b  b^-1 respectively

```

    [[0, 0, 0, 0]]
    [[0, 0, 1, 2], [1, 1, 2, 0], [3, 3, 0, 1], [2, 2, 3, 3]]
    [[0, 0, 1, 2], [2, 2, 2, 0], [1, 1, 0, 1]]
    [[1, 1, 0, 0], [0, 0, 1, 1]]

This shows 4 coset tables.

The rows of coset tables correspond to the cosets.

The first row is the subgroup itself in question.
THe columns refer to the generators `a` `a^-1` `b` `b^-1`.

The first coset table is just `[0,0,0,0]` which corresponds to G considered as a subgroup of G, for which the only coset is just G itself.

`[[0, 0, 1, 2], [1, 1, 2, 0], [3, 3, 0, 1], [2, 2, 3, 3]]` corresponds to this table

|  coset # | a | a^-1 | b | b^-1 |
|---|---|------|---|------|
| 0 | 0 | 0    | 1 | 2    |
| 1 | 1 | 1    | 2 | 0    |
| 2 | 3 | 3    | 0 | 1    |
| 3 | 2 | 2    | 3 | 3    |

The coset ids don't mean much of anything. We can see some similarity to eclass ids in that respect.

For a more performant implementation, look at GAP <https://www.gap-system.org/>

## Equality Saturation

Here I'm going to use egglog <https://github.com/egraphs-good/egglog> a general purpose equality saturation <https://egraphs.org/> engine to do the same sort of thing. Equality saturation uses defined rewrite rules to add new equations into an egraph over and over.

The way coset enumeration works is by building coset tables and propagating / filling in equalities implied by the relations and by inverse. Mechanically it really does feel like a variation of equality saturation. I don't think there is persay an explicit union find under the hood anywhere though. Depending on how you model it, egglog will actually hold tables that correspond to the tables that appear in a coset enumeration implementation.

Here I run an egglog program describing the left action on the subgroup generated by `<a>`. The "easiest" way to know what the moving target of the egglog language is currently working is to just look at the lalrpop grammar <https://github.com/egraphs-good/egglog/blob/main/src/ast/parse.lalrpop>.

```python
%%file /tmp/coset1.egg
(datatype GSet (H))
(function A (GSet) GSet)
(function B (GSet) GSet)
(function AInv (GSet) GSet)
(function BInv (GSet) GSet)

(rewrite (AInv (A x)) x)
(rewrite (BInv (B x)) x)
(rewrite (A (AInv x)) x)
(rewrite (B (BInv x)) x)

; a**3 = 1
(rewrite (A (A (A x))) x)

; b**4 = 1
(rewrite (B (B (B (B x)))) x)

; they commute. a**-1 * b **-1 * a * b = 1  ===>  a * b = b * a
(rewrite (AInv (BInv (A (B x)))) x) 

(relation cosets (GSet))

(cosets (H)) ; H is one of the cosets

; generate all left actions
(rule ((cosets x)) ; given any coset

      ; generate all left actions
      ((cosets (A x))
       (cosets (B x))
       (cosets (AInv x))
       (cosets (BInv x))
))

; H is generated by A
; aH = H
(union (A (H)) (H))

(run 10) ; run up to 10 iterations. we'll saturate before that

(print-function cosets 1000) ; print up to 1000 entries. We'll have way fewer
(print-function A 1000)
(print-function AInv 1000)
(print-function B 1000)
(print-function BInv 1000)
```

    Overwriting /tmp/coset1.egg

```python
! egglog /tmp/coset1.egg
```

    Declared sort GSet.
    Declared function H.
    Declared function A.
    Declared function B.
    Declared function AInv.
    Declared function BInv.
    Declared rule (rewrite (AInv (A x)) x).
    Declared rule (rewrite (BInv (B x)) x).
    Declared rule (rewrite (A (AInv x)) x).
    Declared rule (rewrite (B (BInv x)) x).
    Declared rule (rewrite (A (A (A x))) x).
    Declared rule (rewrite (B (B (B (B x)))) x).
    Declared rule (rewrite (AInv (BInv (A (B x)))) x).
    Declared function cosets.
    Declared rule (rule ((cosets x))
              ((cosets (A x))
               (cosets (B x))
               (cosets (AInv x))
               (cosets (BInv x)))
                 ).
    Ran schedule (repeat 10 (run)).
    Report: Rule (rule ((cosets x))       ((cosets (A x))        (cosets (B x))        (cosets (A...: search 0.000s, apply 0.000s, num matches 156
        Rule (rule ((= rewrite_var__ (A (AInv x))))       ((union rewrite_var__ x))          ...: search 0.000s, apply 0.000s, num matches 25
        Rule (rule ((= rewrite_var__ (A (A (A x)))))       ((union rewrite_var__ x))         ...: search 0.000s, apply 0.000s, num matches 17
        Rule (rule ((= rewrite_var__ (B (BInv x))))       ((union rewrite_var__ x))          ...: search 0.000s, apply 0.000s, num matches 25
        Rule (rule ((= rewrite_var__ (B (B (B (B x))))))       ((union rewrite_var__ x))     ...: search 0.000s, apply 0.000s, num matches 16
        Rule (rule ((= rewrite_var__ (AInv (A x))))       ((union rewrite_var__ x))          ...: search 0.000s, apply 0.000s, num matches 26
        Rule (rule ((= rewrite_var__ (AInv (BInv (A (B x))))))       ((union rewrite_var__ x)...: search 0.000s, apply 0.000s, num matches 15
        Rule (rule ((= rewrite_var__ (BInv (B x))))       ((union rewrite_var__ x))          ...: search 0.000s, apply 0.000s, num matches 25
        Ruleset : search 0.000s, apply 0.000s, rebuild 0.000s
        
     Printing up to 1000 tuples of table cosets: 
        (cosets (BInv (H)))
        (cosets (B (B (H))))
        (cosets (B (H)))
        (cosets (H))
     Printing up to 1000 tuples of table A: 
        (A (B (B (H)))) -> (B (B (H)))
        (A (BInv (H))) -> (BInv (H))
        (A (B (H))) -> (B (H))
        (A (H)) -> (H)
     Printing up to 1000 tuples of table AInv: 
        (AInv (B (B (H)))) -> (B (B (H)))
        (AInv (BInv (H))) -> (BInv (H))
        (AInv (B (H))) -> (B (H))
        (AInv (H)) -> (H)
     Printing up to 1000 tuples of table B: 
        (B (B (B (H)))) -> (BInv (H))
        (B (B (H))) -> (B (B (H)))
        (B (H)) -> (B (H))
        (B (BInv (H))) -> (H)
     Printing up to 1000 tuples of table BInv: 
        (BInv (B (H))) -> (H)
        (BInv (BInv (H))) -> (B (B (H)))
        (BInv (B (B (H)))) -> (B (H))
        (BInv (H)) -> (BInv (H))
    (
       (cosets (BInv (H)))
       (cosets (B (B (H))))
       (cosets (B (H)))
       (cosets (H))
    )
    
    (
       (A (B (B (H)))) -> (B (B (H)))
       (A (BInv (H))) -> (BInv (H))
       (A (B (H))) -> (B (H))
       (A (H)) -> (H)
    )
    
    (
       (AInv (B (B (H)))) -> (B (B (H)))
       (AInv (BInv (H))) -> (BInv (H))
       (AInv (B (H))) -> (B (H))
       (AInv (H)) -> (H)
    )
    
    (
       (B (B (B (H)))) -> (BInv (H))
       (B (B (H))) -> (B (B (H)))
       (B (H)) -> (B (H))
       (B (BInv (H))) -> (H)
    )
    
    (
       (BInv (B (H))) -> (H)
       (BInv (BInv (H))) -> (B (B (H)))
       (BInv (B (B (H)))) -> (B (H))
       (BInv (H)) -> (BInv (H))
    )
    

# Bits and Bobbles

There is a common thread amongst the things I'm looking at. It's all equations, baby. Completion is perhaps a common perspective.

Coset-enumeration really actually ought to saturate, which is kind of interesting. Many equality saturation problems we don't think will saturate.

Coset enumeration as a benchmark is a bit off base from other applications because its weird. One could compare to GAPs speed. Presumably egglog loses badly, but it gives you a "speed of light".

coset enumeration can useful use many heuristic choices on how to proceed. Maybe egraph scheduling could take inspiration from these heurostics?

There is a common trick in the egraph world. You often want to model sequences, but you don't want to throw in all the associations. So you bias your rules in the tail carrying form foo*bar -> biz*baz` becomes `foo(bar(x)) -> biz(baz(x))`

There are other ways of modelling the egglog program. An explicit `(act (A) (H)) binary group action function`G -> GSet -> GSet` is another possibility. You want to be careful if you explicit model the group multiplication `mul : G -> G -> G` to avoid associativity blowup and also the possibility of

Group theory has many applications. Symmetries lead to good solution methods. Physical PDEs become solvable by symmetry, [symmetry breaking](https://en.wikipedia.org/wiki/Symmetry-breaking_constraints) is important to reduce combinatorial search space. Graph isomorphisms are graph symmetries.

This is akin to taking the free monoid and turning it into a right associated list.

<https://egraphs.zulipchat.com/#narrow/channel/375765-egg.2Fegglog/topic/lowering.20using.20egglog-python/near/427957380>
"
Associating sequences all the way to the right like a list and writing your pattern in the open tail form foo(bar(x)) -> biz(baz(x)) aka cons(foo,cons(bar, x)) -> cons(biz,cons(baz,x)) can work. Maybe not for every possible pattern. This doesn't let you capture big chunks of the list for which brute force associativity might be your only option. It feels to me based on little that if one wanted to do equational reasoning over sequences / strings, some kind of specialized egraph data structure could be used. People use special knuth bendix automata-like data structures for strings into group theory stuff for example. <https://gap-packages.github.io/kbmag/doc/chap0_mj.html>
"

Completion is a forward chaining method. Equality saturation is a goal oriented method because you start with a target term in the egraph. You can model the same thing in completion using a set of supprot strategy

for more on computational group theory I recommend  the Handbook of Computational Group Theory. In the series ‘Discrete Mathematics and its Applications’, Chapman & Hall/CRC 2005, xvi + 514 p.

coset enumeration is

Coset enumeration is a technique to extract information about groups presented in this form. Even when the group is infinite or large, the number of cosets may be be finite or small.

Computational Group Theory is a thing.

<https://en.wikipedia.org/wiki/Computational_group_theory>

A subgroup of G divides the group into chunks. The image of the subgroup under applications of G are cosets of H.

A coset is <https://en.wikipedia.org/wiki/Coset>

`cargo install --path .`

The coset algorithm biases the associativity of group theory, breaking it by having things act on some kind of terminator thing.
This is akin to taking the free monoid and turning it into a right associated list.
Or annihilation and creation operators acting on a vacuum state.

<https://docs.gap-system.org/pkg/itc/htm/CHAP001.htm> interactive todd coxeter
<https://docs.gap-system.org/doc/ref/chap47.html> gap finitely presented groups

How to enumerate H? One, could just pick generators. Or Could just pick how many cosets you want to allow and then do search?

Redemeister schreier finds presentation of subgroup.

<https://www.philipzucker.com/string_knuth/>
Knuth bendix on strings is a method for computational group theory,
Coset enumeration is closer to equality saturation. It doesn't bake in the string behavior.

 Neubüser, J. (Campbell, C. M. and Robertson, E. F., Eds.), An elementary introduction to coset table methods in computational group theory, in Groups–St Andrews 1981 (St Andrews, 1981), Cambridge Univ. Press, London Math. Soc. Lecture Note Ser., 71, Cambridge (1982), 1–45.

John J. Cannon, Lucien A. Dimino, George Havas, and Jane M. Watson. Implementation and analysis of the Todd-Coxeter algorithm. Math. Comp., 27:463– 490, 1973.

[Hav91]
George Havas, Coset enumeration strategies. In Proceedings of the International Symposium on Symbolic and Algebraic Computation (ISSAC’91), Bonn 1991, pages 191–199. ACM Press, 1991.

<https://staff.itee.uq.edu.au/havas/addct.pdf> ADDENDUM TO
AN ELEMENTARY INTRODUCTION TO COSET TABLE
METHODS IN COMPUTATIONAL GROUP THEORY

Sims book Computing with Finitely Presented Groups.

S. Carmody, M. Leeming and R. F. C. Walters, The Todd-Coxeter procedure and left Kan extensions, J. Symbolic Comput. 19 (1995), 459-488.
<https://dl.acm.org/doi/10.1016/S0747-7171%2802%2900102-5> Computing left Kan extensions

Kan extension (categorical database), the chase and knuth bendix, egraphs. all connected. GATs? Kan ~ galois ext. hmmm. mathmeth. AoP

<https://arxiv.org/abs/2205.02425> Fast Left Kan Extensions Using The Chase

```python
%%file /tmp/coset1.egg
(datatype GSet (H))
(datatype G (A) (B) (Inv G))

(function act (G GSet) GSet)

(rewrite (Inv (Inv x)) x)
(rewrite (act (Inv x) (act x s)) s)
(rewrite (act x (act (Inv x) s)) s)


(rewrite (act (A) (act (A) (act (A) s)))
         s
)
; same for B



```

```python
%%file /tmp/coset1.egg
(datatype GSet (H))
(function A (GSet) GSet)
(function B (GSet) GSet)
(function AInv (GSet) GSet)
(function BInv (GSet) GSet)
;(datatype GAct (A GSet) (AInv GSet) (B GSet) (BInv GSet))

(rewrite (AInv (A x)) x)
(rewrite (BInv (B x)) x)
(rewrite (A (AInv x)) x)
(rewrite (B (BInv x)) x)

(rewrite (A (A (A x))) x)
(rewrite (B (B (B (B x)))) x)
(rewrite (AInv (BInv (A (B x)))) x) ; they commute

(relation cosets (GSet))

(cosets (H))
(rule ((cosets x))

      ((cosets (A x))
       (cosets (B x))
       (cosets (AInv x))
       (cosets (BInv x))
))

; H is generated by A
(union (A (H)) (H))

;(datatype G (A) (B) (Inv G))
;(function act (G GSet) GSet)
;(rewrite (A s) (act (A) s))
;(rewrite (B s) (act (B) s))
;(rewrite (AInv s) (act (AInv) s))
;(rewrite (BInv s) (act (BInv) s))

(run 10)

(print-function cosets 1000)
(print-function A 1000)
(print-function AInv 1000)
(print-function B 1000)
(print-function BInv 1000)
```

```python
F, a, b = free_group("a, b")
G = FpGroup(F, [a**3, b**3, a**-1 * b**-1 * a * b]) # product of 2 cyclic groups order 3
l = low_index_subgroups(G, 9)
for coset_table in l:
    print(coset_table.table)
```

```python
from kdrag.all import *
from z3 import *
G = DeclareSort("G")
mul = Function("mul", G, G, G)
kd.notation.mul.register(G, mul)
e = Const("e", G)
inv = Function("inv", G, G)
x,y,z = Consts("x y z", G)
mul_id = kd.axiom(smt.ForAll([x], x * e == x))
inv_mul = kd.axiom(smt.ForAll([x], inv(x) * x == x))
mul_assoc = kd.axiom(smt.ForAll([x,y,z], x * (y * z) == (x * y) * z))




```

    Admitting lemma ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x) >= 0))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(x)**2 == x))
    Admitting lemma ForAll(x, Implies(x >= 0, sqrt(sqr(x)) == x))

```python
GSet = Set(G)


H = Const("H", GSet)
S = Const("S", GSet)
act = Function("act", G, GSet, GSet)
act_def = kd.define("act", [z,S], Lambda([x], smt.QExists([y], S[y], z*y = x))) #left action
subgroup = kd.define("subgroup", [H], H[e] & smt.ForAll([x], H[x], H[inv(x)]). smt.ForAll([x,y], H[x] & H[y],  H[x*y]))

#left_coset = kd.define("left_coset", [H], Lambda([x], act(x, H))



act_inv = ForAll([x, S], act(x, act((inv(x), S)) == S)
act_inv2 = ForAll([x, S], act(inv(x), act(x, S)) == S)
act_e = ForAll([S], act(e, S) == S)

# we don't want to refer to mul for the coset method. We define relations only with respect to their action on a set
#act_mul = ForAll([g, h, S], act(mul(g, h), S) == act(g, act(h, S))



    =



```

      Cell In[39], line 7
        act_def = kd.define("act", [z,S], Lambda([x], smt.QExists([y], S[y], z*y = x))) #left action
                                                                             ^
    SyntaxError: expression cannot contain assignment, perhaps you meant "=="?
