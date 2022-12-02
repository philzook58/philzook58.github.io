---
layout: post
title: Automata
---

See also note on Parsing regularexp



Determinization - turn nondeterministic automaton to deterministic


https://github.com/ondrik/libvata
[Tree Automata Techniques and Applications](https://jacquema.gitlabpages.inria.fr/files/tata.pdf)


[E-Graphs, VSAs, and Tree Automata: a Rosetta Stone](https://remy.wang/reports/dfta.pdf) [slides](https://docs.google.com/presentation/d/1oDNmzxJpsdLE51lmybcfzzzv4jRLDdrVpmMhMpFEoFk/edit?usp=sharing) [merge only rules](https://gist.github.com/remysucre/1788cf0153d7db240e751fb698f74d99)


https://en.wikipedia.org/wiki/Tree_automaton



Computing regex from automata
Kleene's algorithm
Tarjan's algorithm
Basic algorithm of going back an forth is simple.
Consider edges to be labelable by regexs. regex is equal to simple 2 state automata then with 1 edge
You can eliminate states by performing the product of their in and out edges.
You can create states and edges by expanding the regexp. Sequence is a new intermiedtae state. alternate is two parall arrows







Myhill Nerode theorem
Pumping Lemma


Automata minimization - Partition refinement
Separate into separate sets those which are definitely distinguishable (the remaining in same partition may or may not be). Things that transition into distinguishable things are distinguishable from each other

Datalog partition refinement?
Sets. Things definitely not in set.

DAWG - transitions are single labelled edges. Transitions are
