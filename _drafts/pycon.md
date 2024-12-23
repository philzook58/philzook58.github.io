Knuckledragger: A Semi Automated Proof Assistant

Knuckledragger is a python library that provides proof assistant infrastructure built on top of the Z3 SMT solver.
This talk will have a shot introduction to Z3 and automated theorem proving, interactive theorem proving, and a minimal approach to making an embedded facilities that play nice with Jupyter.
Python has a large community, good tooling, and the best interactive programming experience available today.

Automated solvers cannot complete things in one shot.
At some point they need to be guidied.
In addition, the point of mathemtical and scientific computation is often understanding. A black box solver that supplies a yes or no with no ability to explore the reasons behind it is good for some purposes but not all.

NEPLS:
Knuckledragger is a work in progress proof assistant built around the pre-existing python bindings for the Z3 SMT solver. Because of this, Knuckledragger inherits its core logic from SMT-LIB. This relatively weak logic entails many compromises compared to popular proof assistants, but also advantages. It aims to be as unsurprising as possible from both a proof assistant and python idiom perspective. The core applications being targeted are calculus, numerics, and software verification.
