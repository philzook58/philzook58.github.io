
A rosette stone: Egraphs as ground rewrite systems

There is a long history of the field of term rewriting and in particular completion.

The egraph itself is a compact representation of a system of ground equations over terms

Completion is a methodology to do automated reasoning over equations. The starting point is terms with variables in them.

The basic algorithm is simple:

- find possibly diverging (critical) pairs
- simplify them
- Orient them according to a term ordering into a rewrite rule and add to your equation set

This process is not guaranteed to terminate, but it is complete expansion of
It is intuitively appealing that you may want to shrink your set of equations. This makes the algorithm more subtle.

Fact: Ground completion is guaranteed to terminate (under the appropriate term order)

Tree Automata. It has been noted that egraphs are tree automata. tree automata themselves can be represented as ground rewrite systems.
Noting that egraphs are ground rewrite systems is an observation in the same vein, with close to the same content. I find it subjectively find it conceptually superior in that rewrite systems are closely related to the task of equational reaosning, whereas tree automata are couched in the language of automata theory, a more unfamiliar entity.

The field of automata

NFA can be easily translated to a ground rewrite system. For every edge

A string rewriting system

$qx -> q$
Can be encoded in terms as

$q(x(A)) -> q(A)$

Ground form.
x(q) -> q

NFA
x(q) -> q1
x(q) -> q2

Overlap pairs are both possible transitions
q1 -> q2. Hmm. Adding in this transition is not sensible.
Yeah, they aren't equal regardless of context. Huh

q(x(A)) -> q1(A)
q(x(A)) -> q2(A)
No this isn't determinization

GRS + eager rewrite rules

Yihong's post
automata talks

Pictures:

# Tree Automata

# Union Finds As

# Extending the Egraph

There are a variety of directions to extending egraphs

Lambdas

Context
ASSUME nodes
colored egraphs

Eager rewriting
