

Egraphs (equivalence graphs) are a data structures for efficiently and compactly storing many equivalent versions of expressions. They are useful for performing compiler optimizations and theorem proving.

Ultimately, one is interested in extracting out a version of an expression from inside the egraph with good properties so you can turn it into efficient code or a piece of hardware. A method for doing so is to apply dynamic programming. The cost of nodes in the egraphs is a function of it's children. You can compute 

It occurs rather often however that this framework does not model the actual costs well. Shared subpexpressions can be reused cheaply. In this case, what one wants to extract is not an optimal AST, but instead an optimal DAG. The cost function of the DAG is intrinsically more nonlocal or noncompositional that the cost function of an AST.

A simple additive cost model is  $\sum_n c_n m_n$  where $c_n$ is the cost of enode $n$ and $m_n$ is the multiplicity you have picked it.

THe DAG cost model would instead be  $\sum_n c_n b_n$ where instead $b_n$ is not a boolean 0-1 variable saying whether you picked the node or not.

In either case, the optimization problem is constrained to be selecting subgraphs of the egraph which form valid trees or valid DAGs. Tree-ness or DAG-ness is a subtle property that is surprisingly difficult/impossible to describe in first order logic. It is an example where you need a notion of least fixed point in your logic.

`Tree(node) :- forall c, child(c,node) => Tree(c)`

Leaf nodes with no children are Tree.



# The tree selection problem

[](https://en.wikipedia.org/wiki/Tree_(graph_theory))

The canonical datalog program is the path program. This shows that datalog is capabble of expressing trasnitivty/ transitive closure

```clingo
path(X,Y) :- edge(X,Y), path(Y,Z).
istree(X) :- node(X), not path(X,X).

```