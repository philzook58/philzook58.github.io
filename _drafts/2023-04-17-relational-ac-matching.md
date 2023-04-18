


Matching modulo associativity and/or commutativity is something people tend to want. Addition, multiplication, conjunction (and), and disjunction (or) are very common associative and commutative operations. AC is a very common, simple pattern that it feel worth building special support for. Using brute force methods to deal with it lead to exponential blowups. Commutativity is orderings and there are $n!$ orderings.

It can be partially dealt with by taking AC pieces and normalizing them to canonical forms. We can do this by flattening out the parenthesis into a list (right associating) to deal with the A and then sorting the elements to deal with C.

In functional programming languages, we are used to having pattern matching be semi deterministic (it either fails or succeeds once). If you need to pattern match into this AC normal form though, you need to search through choices from this flat sorted expression and pattern matching even a single term becomes nondeterminstic, possibly returning many results.
 
An insightful idea that I learned of from the [Relational E-matching paper](https://arxiv.org/abs/2108.02290) is that it can be very useful to flatten term matching problems so that they are amenable to database engines.

While we might be tempted to use top down search in a term, a relational database can search for terms top down, bottom up, and side-to-side and they have lots of smarts put into them to pick the best plan. There can be extreme asymptotic and actual performance benefits to this.
In addition, we get to reuse the effort that has been put into databases. Databases are very sophisticated, declarative, high performance solver systems.

In E-matching, you need to search the equivalence classes for things that might match your pattern. Even if you start from a single eclass, there may be many solutions. E-matching and AC-matching are in this sense similar problems and basically the same relational approach works.

It can be useful to be searching over a database of terms. For example, if you want to search all subterms of a term to perform rewriting. 

# AC-terms as graphs

A term is a tree and a tree is a type of graph. The typical conception of each node in a term is that the order of it's children matter. The most used definition of a graph does not, but there are a number of variations in mwhat we may mean by the word "graph" (directed/undirected, multigraph, edge labelled, ported).

A term is a "ported" graph where each vertex has exactly one incoming edge.

Very often we prefer to think of the term as a ported directed acyclic graph (DAG) where common subterms are shared.

To add AC to this picture, we want to have "AC-nodes" for which the order and number of children is not specified. This is the more usual notion of vertex in a graph.

As an aside, we can also put e-graphs in this picture as a bipartite graph with ported enodes combined and unported eclass nodes. Again AC and E are rather similar from this perspective.

# Graphs as Relational Databases

A graph is easily encoded into a relational database and graph matching problems to relational queries.

For example, we can construct an edge table and here is a query that finds all triangle patterns in the graph.
```sql
create table edge(a INTEGER, b INTEGER);
INSERT INTO edge VALUES (1,2), (2,3), (3,4), (3,1);
SELECT * FROM edge as x, edge as y, edge as z WHERE x.b = y.a AND y.b = z.a AND z.b = x.a; 
```

I am not exactly clear on what [graph databases](https://en.wikipedia.org/wiki/Graph_database) offer other than syntactic sugar over this encoding. Perhaps better support for transitive path queries, which are not relevant for this blog post.


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

For example `foo(biz(X), bar(Y))` flattens to become `foo(A,B,C), biz(X,A), bar(Y,B)` or in SQL `SELECT * FROM foo, biz, baz WHERE foo.x0 = biz.x1 AND foo.x1 = bar.x0`

This flattening can be performed by 

Now for AC nodes, this encoding does not work. We don't want to order te children and we may have many. Instead, we can encode the AC node using a binary relation of the AC-node identifier and it's children.

Hence the pattern `foo(X) + bar(Y) + ...` flattens to `foo(X,A), ac(A,B), bar(Y,C), ac(C,B)` or `SELECT * FROM foo, ac as ac1, ac as ac2, bar WHERE foo.x1 = ac1.in_ AND ac1.out_ = ac2.out_ AND bar.x2 = ac2.in_ AND ac1.rowid != ac2.rowid`. We might also want to break the permutation symmetry by adding `foo.x1 <= bar.

Note that the multiset nature of SQL is needed here as the node `a + a` turns into a database that has duplicate entries in the `ac` table

```sql
create table a(x0);
create table ac(in_, out_);
insert into a values (0);
insert into ac values (0,1), (0,1);
```

So given a term mod AC, we can canonicalize it and then insert it into the database according to these recipes. Then to find all AC patterns

# SQLite


# Bits and Bobbles
- Arguably the system I have presented only deals with C and not A. A flattening process deals with A
- Does one want (a + b + ...) patterns where `a` and `b` cannot contain `+` or do we want `(A + B)` patterns where A and B are partitions of the terms in the `+` node?
- Can AC and E matching be combined in a manner compatible with rebuilding?

# 

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







