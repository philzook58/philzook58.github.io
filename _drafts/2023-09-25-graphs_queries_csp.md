---
author: philzook58
date: 2020-12-06
layout: post
title: "SQL. homomorphisms and constraint satsfactin probems"
---


SQL queries are enumerating homomorphisms between the query and the database. This perspective puts the query and the database on smilar footing, which feels odd.

As a subcase of this capability, if the database is holding an edge table and attributes, then a query is a graph homomorphism solver.
If we dymmetrically place two graphs into the database and in a query, we can enumerate isomoprhisms. Isn't that fun?

Another perspective is that the query is a formula, and the database is a model of the formula.

We are used to small queries and large databases, but this is not a definition

A perspective on what a constraint satisfaction problem is is that is is a homomorphism problem.
For example, graph coloring is a homomorphism from a graph to a complete graph of colors (with no self edges).

Constraint satisfaction is an assignment to variables values frm their domain subject to constraints. The particular connectivty of a problem can be represented by a hypergraph. The target structure represents the domains the variables can take on, and the constraint hyperedges map to a relation representing the constraint.
A class of CSP problems is allowing the connecvtivity graph to vary, while keeping the target (the types of constraints fixed). Is this a useful characterization? Eh. It's interesting that it ties into other mathemtical topicas.

The naive solution of a constraint satsifaction problem is to just make a big sequence of loops, pruning / breaking with checks that constraint are satisifed. We want to push the checks as high as possible.
This a a very static perspective.
More dynammically, we want to pick the variable ordering inside the choice branches. This is more of a backtracking feel. We do proppagation to disallow subchoices

A problem that is easy to embed into database queries is graph homomomorphism. Queries and databases feel very different, but they are more symettric than you might think.

In typical usage, queries are small and databases are large.
A graph coloring problem can be mdelled as fnding a graph homomorphism into a complete graph. This flips the intuition on it's head with a large query and small database. Examples like these are better served probably by a constraint satisfaction solver or SAT style techniques.

The middle ground of roughly equal graphs is a graph isomorphism problem. Custom solvers like nauty exist for this case too.

```python
import sqlite3
import networkx as nx
def db_of_graph(conn, G):
    con.executemany("INSERT INTO nodes VALUES (?)", map(lambda v : (v,),  G.nodes))
    con.executemany("INSERT INTO edges VALUES (?, ?)", G.edges)
def graph_of_db(con):
    G = nx.DiGraph()
    res = con.execute("SELECT * FROM nodes")
    G.add_nodes_from(map(lambda x: x[0], res.fetchall()))
    res = con.execute("SELECT * FROM edges")
    G.add_edges_from(res.fetchall())
    return G
def query_of_graph(G):
    selects = []
    froms = []
    wheres = []
    for node in G:
        froms += [f"nodes AS v{node}"]
        selects += [f"v{node}.v AS v{node}"]
    for i, (a,b) in enumerate(G.edges):
        froms += [f"edges as e{i}"]
        wheres += [f"e{i}.src = v{a}.v"  , f"e{i}.dst = v{b}.v"]
    sql = "SELECT " + ", ".join(selects) + \
          "\nFROM " +  ", ".join(froms) + \
          "\nWHERE " + " AND ".join(wheres)
    return sql
G = nx.path_graph(7, create_using=nx.DiGraph)
lhs = nx.path_graph(3, create_using=nx.DiGraph)
con = sqlite3.connect(":memory:")

con.execute("CREATE TABLE nodes(v)")
con.execute("CREATE TABLE edges(src,dst)")
db_of_graph(con, G)
res = con.execute(query_of_graph(lhs))
print(res.fetchall())
# Result: [(0, 1, 2), (1, 2, 3), (2, 3, 4), (3, 4, 5), (4, 5, 6)]

print(graph_of_db(con))
"DELETE FROM nodes WHERE nodes.v = ?"
"DELETE FROM edges where edges.src = ? OR edges.dst = ?"

con.execute("DELETE FROM nodes")
con.execute("DELETE FROM edges")
colors = nx.complete_graph(2) # a two coloring
db_of_graph(con,colors)
# symmetrize. Maybe db_of_graph should do this. if not isinstanc(G,nx.DiGraph)
con.execute("INSERT INTO edges SELECT edges.dst, edges.src FROM edges")

res = con.execute("SELECT * FROM edges")
res = print(res.fetchall())
res = con.execute(query_of_graph(G))
print(res.fetchall())
# [(1, 0, 1, 0, 1, 0, 1), (0, 1, 0, 1, 0, 1, 0)]
```

Graph coloring can be solved through dynamic programming. If we cut up a graph, we only need to know if it can be colored with particular choices at interfaces. Choosing interfaces like this is a graph partitioning problem, but also is a tree decomposition.

One of the things that I found appealing about category theory is that it presents a design methodology to convert things that look graph-like like string diagrams into term-like expresssions of combinators.

Hmm. python-metis is not a thing anymore? Just pip install metis, it works with networkx anyway

```python
import metis

import networkx as nx
G = nx.path_graph(7)
edgecuts, parts = metis.part_graph(G,3)
print(edgecuts, parts)

print(nx.community.kernighan_lin_bisection(G)) # anneal a cut by node swapping
print(list(nx.community.girvan_newman(G))) # remove edges from graph
```

Recursively partition to build query plan (?)

You can build a query plan using these graph partitioners
but also query planners can be used to find partitions / tree decompositions.

There are also custom solvers for this.

graph datastructure

`[(v1,v2)]`

```
Node(outs,ins)
= [(outs,ins)]
out, inner , in

```

dynamic tree decomposition
hyprgraph data structure

```python
g1 = {(1,2), (2,3)}  # graph as set of (directed) edges
g2 = {{1,2}, {2,3}} #graph as sets of undirected edges

# ((multi)graph as map from named edges to src target vertices.
src = {"e1" : 1}
dst = {"e1" : 2}

{"e1": (1,2)}

# hypergraph as named edges
{"e1": {1,2,3}, "e2": {2,3,4}}

g = {{1,2,3}, {2,3,4}} # set of sets of vertices as hypergraph

#partition tree representation
g = ( [edges_between] , g1, g2  )

# rebalancing
```
