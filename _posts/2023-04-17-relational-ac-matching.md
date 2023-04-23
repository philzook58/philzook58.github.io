---
date: 2023-04-23
layout: post
title: "Relational AC Matching"
description: Associativity and Commutativity through Relational Graph Matching
tags: egraphs sql
---

Matching modulo associativity and/or commutativity is something people tend to want. Addition, multiplication, conjunction (and), and disjunction (or) are very common associative and commutative operations. AC is a very common, simple pattern that it feel worth building special support for. Using brute force methods to deal with it lead to exponential blowups. Commutativity is orderings and there are $n!$ orderings. The Maude term rewriting system and eprover and vampire theorem provers all have special AC support I believe. 

It can be partially dealt with by taking AC pieces and normalizing them to canonical forms. We can do this by flattening out the parenthesis into a list (right associating) to deal with the "A" and then sorting the elements to deal with "C".

In functional programming languages, we are used to having pattern matching be semi-deterministic (it either fails or succeeds once). If you need to pattern match into this AC normal form though, you need to search through choices from this flat sorted expression and pattern matching even a single term becomes nondeterministic, possibly returning many results. Another reason we might expect pattern matching to return many results is that we may be seeking patterns in a database of terms and all their subterms.
 
An insightful idea that I learned of from the [Relational E-matching paper](https://arxiv.org/abs/2108.02290) is that it can be very useful to flatten term matching problems so that they are amenable to database engines.

While we might be tempted to typically use top down search in a term (perhaps as an artifact of the typical pointer representation), a relational database can search for terms top down, bottom up, and side-to-side and they have lots of smarts put into them to pick the best plan. There can be extreme asymptotic and actual performance benefits to this. It gets more extreme when there are nonlinear uses (multiple occurances) of pattern variables. Database/relational joins are a very natural efficient mechanism to deal with these rather that just pruning the incompatible matches. Nonlinear patterns are a _boon_ for efficiency if used, not a burden. See the discussion [here](https://github.com/egraphs-good/egg/pull/74)

In addition, we get to reuse the effort that has been put into databases. Databases are very sophisticated, declarative, high performance solver systems.

In E-matching, you need to search the equivalence classes for things that might match your pattern. Even if you start from a single eclass, there may be many solutions. E-matching and AC-matching are in this sense similar problems and it appears basically the same relational approach works.

Perhaps this is unsurprising given that commutativity and associativity are popular difficult to direct rewrite rules that people like throwing in their egraph rewriting. But people also complain that this blows up the egraph. This blog post might be a step towards correcting that.

It's pretty simple, first we think about how AC-terms are graphs and then how to treat graph matching relationally.

# AC-terms as graphs

A term is a tree and a tree is a type of graph. The typical conception of each node in a term is that the order of it's children matter. The most used definition of a graph does not, but there are a number of variations in what we may mean by the word "graph" (directed/undirected, multigraph, edge labelled, ported).

A term is a "ported" graph where each vertex has exactly one incoming edge.

Sometimes we prefer to think of the term as a ported directed acyclic graph (DAG) where common subterms are shared. DAGs and trees are basically the same for many purposes.

To add AC to this picture, we want to have "AC-nodes" for which the order and number of children is not specified. This is the more usual notion of vertex in a graph. The `+` node in the following diagram does not differentiate it's children, while the other nodes do

![foo(bar, baz + baz + biz(bar) + bar)](/assets/acgraph.svg)

`foo(bar, bar + bar + biz(bar) + baz)`

We can also put e-graphs in this graphical picture (indeed that's why they are called egraphs) as a bipartite graph with ported enodes combined and unported eclass nodes (there is no notion of ordering or constrained number of children of an eclass). Again AC and E are rather similar from this perspective. In the usual drawing of an egraph, we represent the edge coming from the eclass node to an enode (representing the relationship of the enoe being in the eclass) by representing the eclass as a dotted outline surrounding its enodes.

![](/assets/egraphs.svg) [source](https://egraphs-good.github.io/)
# Graphs as Relational Databases

A graph is easily encoded into a relational database and graph matching problems to relational queries. It is obvious once said, but not well known enough.

For example, we can construct an edge table and here is a query that finds all triangle patterns in the graph.
```sql
create table edge(a INTEGER, b INTEGER);
INSERT INTO edge VALUES (1,2), (2,3), (3,4), (3,1);
SELECT * FROM edge as x, edge as y, edge as z WHERE x.b = y.a AND y.b = z.a AND z.b = x.a; 
```

I am not exactly clear on what [graph databases](https://en.wikipedia.org/wiki/Graph_database) offer other than syntactic sugar over this and similar encoding. Perhaps better support for transitive path queries, which are not relevant for this blog post.


To encode terms into a relational database, one approach is to make a one n+1 column table for every n-arity function symbol. That $n$ argument functions are special case of $n+1$ relations may be a familiar idea from math class.

The entries of the columns are unique integer ids. For example, the term `f(g(a), a)` could be encoded as

```sql
create table f(x0,x1,x2);
create table g(x0,x1);
create table a(x0);
INSERT INTO a VALUES (0);
INSERT INTO g VALUES (0,1);
INSERT INTO f VALUES (1,0,2);
```


To reconstruct the term, we need to join the tables together by these ids. The ids play a role similar to pointers might in an AST. Pointers are nice in that they have maximally fast notion of dereferencing, but by using ids less connected to the underlying memory we gain the ability to index and move around things as we see fit. In general, lifting pointer based data structures to integer indexed data structures is a fruitful line of thought.

To search for a pattern in the database, we flatten the tree-like pattern into a relational query

For example `foo(biz(X), bar(Y))` flattens to become in datalog-like notation `foo(A,B,C), biz(X,A), bar(Y,B)` or in SQL `SELECT * FROM foo, biz, baz WHERE foo.x0 = biz.x1 AND foo.x1 = bar.x0`

Now for AC nodes, this encoding does not work. We don't want to order te children and we may have many. Instead, we can encode the AC node using a binary relation of the AC-node identifier and it's children.

Hence the pattern `foo(X) + bar(Y) + ...` flattens to `foo(X,A), ac(A,B), bar(Y,C), ac(C,B)` or `SELECT * FROM foo, ac as ac1, ac as ac2, bar WHERE foo.x1 = ac1.in_ AND ac1.out_ = ac2.out_ AND bar.x2 = ac2.in_ AND ac1.rowid != ac2.rowid`.

Note that the multiset nature of SQL is needed here as the node `a + a` turns into a database that has duplicate entries in the `ac` table

```sql
create table a(x0);
create table ac(in_, out_);
insert into a values (0);
insert into ac values (0,1), (0,1);
```

So given a term mod AC, we can canonicalize it and then insert it into the database according to these recipes. Then to find all AC patterns


# Bits and Bobbles
- Eli had a very similar proposal I think
- I am intrigued by this relational AC matching idea but am stumped on how to flesh them out further and actually validate its usefulness. This blog post is an imperfect attempt to push on that. I'm a little stumped how to move forward.
- Arguably the system I have presented only deals with C and not A. A flattening process deals with A
- Does one want (a + b + ...) patterns where `a` and `b` cannot contain `+` or do we want `(A + B)` patterns where A and B are partitions of the terms in the `+` node?
- Can AC and E matching be combined in a manner compatible with rebuilding? In a sense AC "flattening" is similiar to rebuilding. The original conception of relational E-matching had the canonization/rebuilding happening outside the database, and this blog post is in a similar spirit.
- Ordering needs to be readjusted in the equality saturation case.
- `GROUP BY` and [`group_concat` aggregator](https://www.sqlitetutorial.net/sqlite-group_concat/) is useful for reconstituting the ac-term from SQL. 

Some other articles and examples on AC matching:

- [flat and orderless patterns in mathematica](https://reference.wolfram.com/language/tutorial/Patterns.html#28368)
- [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907)
- [Compilation of Pattern Matching with Associative-Commutative Functions ](https://link.springer.com/content/pdf/10.1007/3-540-53982-4_4.pdf)
- [matchpy docs](https://matchpy.readthedocs.io/en/latest/)
- [Commutative unification](https://matthewrocklin.com/blog/work/2013/01/25/Commutative-Unification)
- [Equational Unification and Matching, and Symbolic Reachability Analysis in Maude 3.2 (System Description)](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_31)
- [associative commutative rules Symbolics.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/12)


# Less Well Digested Thoughts


## What are AC patterns?
I don't actually find this that obvious.

What should `(X + Y)` be capable of finding? Is `X` bound to a cluster of terms? Can `Y` be the empty multiset?

Maybe the terminology "multiset pattern" is better.

I think really the more natural pattern operationally speaking to allow is _open_ AC patterns `(X + Y + ...)` where `X` and `Y` can only bind to non plus terms.

Perhaps really we ought to bind te multiset to a pattern and then add constraints on the multiset about its membership and cardinality. 

`X + Y` with two variables is a goofy thing to be doing because you get pointless duplication due to symmettry.

There should not be multiple variables under a plus node. `p @ (1 + ...)`. This matches a multiset `p` that contains `1`. It could be written as `1 in p`.  `p @ (1 + 2)` is `1 in p AND 2 in p AND #(p) = 2` vs `p @ (1 + 2 + ...)` is `1 in p AND 2 in p`

Commutative matching is simple. We just need to try every possible permutation.

Combined with flattening this sort of gives AC.

Full AC requires flattening on both the pattern and term side. The pattern `(x + y) + z` ought to be flattened.

1. Is the plus at the head of the pattern  `x + y`? This is "unsealed" in some sense since it should also match `1 + 2 + 3`. The pattern `1 + 2` ought to find the subterm in `1 + 3 + 2` . No it's really about point 2. Are there vars in the pattern or not.
2. Is there a var or a constant as te child of plus `foo(x + foo(1))` The var then can absorb everything else
3. multiple vars `x + y` is silly? unless they nonlinearly appear elsewhere.
4. 


## Pattern Matching Combinators
There's a nice style of building pattern matching combinators. A pattern is represented as a function that takes in a binding environment and either fails or returns a new binding environment.

`type pat = term * env -> Maybe env`

Then then right hand side of a rule may be represented as `env -> term`, or more generically as `env -> 'a`. THis is a less well typed, less hoas-y version of the notion of a recursor.

A higher order pattern combinator has the type `pat -> pat -> pat`

For example, the pattern combinator for `foo(A,x)` ought to look like

```python
def pat_x(term, env):
    if term[0] == "x" and len(term) == 1:
        yield env

def var(x):
    def res(term, env):
        if x in env:
            if env[x] == term:
                yield env
        else:
            env = env.copy()
            env[x] = term
            yield env
    return res

def pat_foo(p1,p2):
    def res(term, env):
        if term[0] == "foo" and len(term) == 2 + 1:
            for env1 in p1(term[1], env):
                for env2 in p2(term[2], env1):
                    yield env2
    return res


def run(p, t):
    # run on empty environment and reify into list
    return list(p(t, {}))
print(run(pat_x, ["x"]))
print(run(pat_x, ["y"]))
print(run(pat_foo(pat_x, pat_x), ["foo", ["x"], ["x"]]))
print(run(pat_foo(var("Z"), pat_x), ["foo", ["q"], ["x"]]))

```


I should build a bunch of concrete matchers first

```python

import itertools
# open multiset matcher. "AC" matcher
def ms(f):
    def res0(*args):
        def res(sexp, env):
            if sexp[0] == f and len(sexp) >= len(args) + 1:
                for a1 in itertools.combinations(args, len(sexp) - 1): 
                    for a in itertools.permutatons(a1):
                        env = env.copy()
                        for arg, s in zip(a,sexp[1:]):
                            env = yield from arg(s,env)
            else:
                return
            yield env
        return res
    return res0

```

In some sense, an AC pattern is a multiset pattern, where you need to only match on multisets greater than that of the pattern. 

```python
class ACNode():
    multiset:Dict[Term,int]

# a1 + a2 + ..
def ground_acpat(pat):
    def res(ms):
        return all(k in ms for k in ts) and all(ms[k] >= v for k,v in ts)

```

```python
class PatFail(Exception):
    pass

# basic pattern matching combinators
def pat(f, n):
    def res0(*args):
        assert len(args) == n
        def res(sexp, env):
            if sexp[0] == f and len(sexp) == n + 1:
                for arg, s in zip(args,sexp[1:]):
                    env = arg(s,env)
            else:
                raise PatFail
            return env
        return res
    return res0

def var(x):
    def res(sexp, env):
        if x in env:
            if sexp != env[x]:
                raise PatFail
        else:
            env[x] = sexp
        return env
    return res

foo = pat("foo", 2)
x = var("x")
p = foo(x,x)
print(p(["foo", "b", "a"], {}))

import itertools
# Commutative pattern matcher
# It becomes a generator.
def comm(f):
    def res0(*args):
        def res(sexp, env):
            if sexp[0] == f and len(sexp) == len(args) + 1:
                for a in itertools.permutations(args): 
                    for arg, s in zip(a,sexp[1:]):
                        yield from arg(s,env)
            else:
                return
            yield env
        return res
    return res0

```
What does `a + b + c` mean

# SQLite

Using rowid, a questionable practice
```sql
create table plus(ac unique); -- functional to rowid
create table lit(n unique); -- functional to rowid
create table ac(in_,out_); -- a many to many relationship. A special table with special rebuild. Multiset semantics because can have terms like "a" + "a" + "a"
-- construct a + b + c as 
-- lit a  \
-- lit b -- ac - plus - 
-- lit c  /
insert into lit values ("a"), ("b"), ("c");--select * from generate_series(0,3);
insert into ac values (1,0), (2,0), (3,0);
insert into plus values (0);
​
select *, rowid from plus;
select *, rowid from ac;
-- This query is doing AC-matching
select * from plus, ac as n1, ac as n2, lit as x1, lit as x2
 where n1.out_ = plus.ac and n2.out_ = plus.ac 
 and n1.rowid != n2.rowid -- multiset but don't match same term twice
 and n1.in_ = x1.rowid and n2.in_ = x2.rowid 
 and n1.in_ < n2.in_  -- break permutation symmetry
 ;
```

## Flattening Combinators

Flattening terms to relations is an annoying but trivial pass. Basically, you need a way to generate fresh variables/names and a place to record the various constraints and things you have in scope. 
A kind of cute way to shallowly embed this is to use flattening combinators.

```python
counter = 0
def freshrow():
  global counter
  counter += 1
  return "row" + str(counter)

def foo(a):
  def res():
    (rid, froms, wheres) = a()
    row = freshrow()
    return (f"{row}.rowid",  [f"foo as {row}"] + froms, [f"{rid} = {row}.a"]+ wheres)
  return res

def x():
  row = freshrow()
  return (row + ".rowid" ,[f"x AS {row}"], [])

def func(f):
  def res(*args):
    def res1():
      args = [arg() for arg in args]
      rids, froms, wheres = zip(*args)
      row = freshrow()
      (f"{row}.rowid",  [f"{f} as {row}"] + froms, [f"{rid} = {row}.arg{n}" for n,rid in enumerate(rids)] + wheres)
    return res1
  return res

print(foo(foo(x))())

```


# graphs
https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)

There are multiple definitions/variations of what you might call a graph. The standard definition is that a graph is a set of vertices and a set of edges.

Sets have nice algebraic properties. But also computationally, you tend to have to actively _do_ something to remove the duplicates in the set, like maintain some kind of index.

If edges are ordered pairs or vertices, this is a directed graph. If the edges are 

The the collection of edges is a multiset, this is a multigraph

1. directed / undirected
2. multisets
3. labelled edges
4. planar graphs
5. Directed acyclic graphs
6. trees 
7. many vs one in/out edge
8. ports on vertices

These types of graphs tend to be fairly shallowly embeddable in each other using various tricks. For example, a labelled edge graph can be modelled by adding "edge" nodes that carry the labels that split every edge. Similarly,
ported vertex graphs can be modelled by adding "port" vertices attached to each vertex.

The simple graph is not necessarily the easiest one to implement though


The ac table does have an odd variation of functional dependency. An “aggregate fd”. Instead of forall x y1 y2, r(x, y1), r(x,y2) -> y1 = y2 it is instead forall y1 y2, (forall x, r(x,y1) <-> r(x,y2)) -> y1 = y2

Oh, not quite since I need multiset semantics. forall y1 y2, (forall x, r(x,y1) = r(x,y2)) -> y1 = y2
Where r is a function to multiplicity rather than bool
I guess that’s something like extensionality

It can be useful to be searching over a database of terms. For example, if you want to search all subterms of a term to perform rewriting.