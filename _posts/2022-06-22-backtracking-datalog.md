---
date: 2022-06-22
layout: post
title: "Backtracking a Datalog"
description: Backtracking in Datalog is actually pretty easy.
tags: datalog
---

Yihong and I had a conversation at PLDI that I thought was interesting.

In terms of datalogs that support deletion, [Differential Datalog](https://github.com/vmware/differential-datalog) is the main name I know of.

It is difficult to delete facts because then you need to clean up all the facts that were inferred using this fact. Hence you need to record in some manner what facts rely on which facts, a kind of provenance. I believe the differential datalog method involves extending datalog to multiset semantics, where you tag facts with  the number of ways to derive them. When you retract, you can calculate a number of negative derivations, which if this number matches the number of ways to make it, the derived fact is now gone.

This is somewhat complex and must surely pay a decent amount of storage and computation cost.

If however you don't need to be able to assert and retract an arbitrary sequence of facts, you can do better. One example of a pattern that is easy to deal with is backtracking assertions. You can easily track enough info to retract the most recent additions to the database. All it requires is tagging facts with a number representing the scope depth at which they were introduced. This also can be considered a kind of timestamp.

This sort of pattern can be useful for example if you have a guess for a fact you'd like to assert, and then after seeing the datalog analysis finish you can confirm or deny it was a good guess. A place this might happen is in a datalog disassembler, where you might guess an address is code, and then see if good stuff or garbage comes out.

It turns out that if we make this scope a lattice, we don't even need to compute the scopes in serial. This could be useful if you have a sequence of increasingly speculative guesses. More importantly for this blog post, it means I can express the idea in a single souffle program rather than a sequence of them. This program may look less clunky in a datalog that natively supports lattices, like Flix or Ascent.


```souffle
.type scope <: number
.decl edge(x : number, y : number, s : scope)
.decl path(x : number, y : number, s : scope)


path(x,y,s) :- edge(x,y,s).
path(x,z,max(s1,s2)) :- edge(x,y,s1), path(y,z,s2). 

// The combination of max(s1,s2) and these subsumption rules means scope is a lattice
edge(x,y,s) <= edge(x,y,s1) :- s1 <= s.
path(x,y,s) <= path(x,y,s1) :- s1 <= s.

edge(1,2,0).
edge(3,4,0).
edge(2,3,1).
edge(4,5,2).

.output path


// We can then backtrack path to scope 1
.decl path2(x : number, y : number, s : scope)
path2(x,y,s) :- path(x,y,s), s <= 1.
.output path2
/*
path
x       y       s
===============
1       2       0
3       4       0
1       3       1
1       4       1
2       3       1
2       4       1
1       5       2
2       5       2
3       5       2
4       5       2
===============
---------------
path2
x       y       s
===============
1       2       0
1       3       1
1       4       1
2       3       1
2       4       1
3       4       0
===============

*/
```

Alternatively, here is a naive python implementation that implements a push pop interface.

```python
scope = 0
edger = {}
pathr = {}
def push():
  global scope
  scope += 1
def pop():
  global scope, edger, pathr
  # we could index this better
  # non destructive version:
  edger = {k : s for k,s in edger.items() if s < scope}
  pathr = {k : s for k,s in pathr.items() if s < scope}
  scope -= 1

def add_edge(x,y):
  if (x,y) not in edger:
    edger[(x,y)] = scope

def strata():
  for k, s in  edger.items():
    if k not in pathr:
      pathr[k] = s
  while True:
    newpath = {(x,z) for (x,y) in edger.keys() for (y1,z) in pathr.keys() if y == y1}
    if newpath.issubset(pathr.keys()):
      return
    for (x,y) in newpath:
      if (x,y) not in pathr:
        pathr[(x,y)] = scope

add_edge(1,2)
add_edge(2,3)
add_edge(4,5)
strata()
print(pathr)
push()
add_edge(3,4)
strata()
print(pathr)
pop()
print(pathr)
'''
{(1, 2): 0, (2, 3): 0, (4, 5): 0, (1, 3): 0}
{(1, 2): 0, (2, 3): 0, (4, 5): 0, (1, 3): 0, (3, 4): 1, (2, 4): 1, (3, 5): 1, (1, 4): 1, (2, 5): 1, (1, 5): 1}
{(1, 2): 0, (2, 3): 0, (4, 5): 0, (1, 3): 0}
'''
```

# Bits and Bobbles
As a further extension, you don't need to have integers to index your scopes, you could have your scopes labelled by nodes of a tree of scopes, or really an arbitrary lattice of scope labels. The deletion command can then accept a scope label for which to delete any scope which is greater according to the partial order of scopes.

I wonder what you could use that for :)