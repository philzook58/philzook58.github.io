
delta debugging  - https://ddsmt.readthedocs.io/en/master/

https://twitter.com/RanjitJhala/status/1391074098441187328 - jhala asks for 

running `perf`
`perf record -F 99  --call-graph dwarf ./z3 /tmp/review.smt2;  perf report |  c++filt | less`

z3 -st

The axiom profiler and quantifier instantiations

Differences between solvers is important

Check regression on same solver - much better if true.

LLogic debugging - https://www.metalevel.at/prolog/debugging

"Try Smt.arith.solver=2"
"All automatic Z3 bot sometimes uses git bisect."
"rewriter.flat=false"
-v:10

