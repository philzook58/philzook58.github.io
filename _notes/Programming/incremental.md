---
layout: post
title: Incremental Computation
---


See also:

- datalog
- rust (timely dataflow/ differential dataflow)
- note on Databases Streaming

[Incremental λ-Calculus giarusso](https://inc-lc.github.io/)

[differential dataflow v datalog](https://github.com/frankmcsherry/blog/blob/master/posts/2016-06-21.md) Uses magic sets in incrmenetal system in a cool way. Datalog is dataflow system with giant fixpoint around it. Generic join in a rust macro

Szabo <https://szabta89.github.io/publications.html>  [thesis](https://openscience.ub.uni-mainz.de/handle/20.500.12030/5617)

[Incremental Datalog with Differential Dataflows blog](https://www.nikolasgoebel.com/2018/09/13/incremental-datalog.html)
3df <https://github.com/comnik/declarative-dataflow> <https://www.youtube.com/watch?v=CuSyVILzGDQ>

<https://www.clockworks.io/en/blog/> I guess this is a company / consulting service associated with differential dataflow.

Differential Dataflow is kind of semi naive on steroids. Instead of just having a totally ordered iteration time, it keeps a partially ordered set of previous times. This means we have to store more than just good, new, delta. We have to store a bunch of deltas until we can coalesce them.

Yihong described it as "2d seminaive". 1 dimension is datalog iteration number, and the other dimension is incoming user data time.

Timestamps kind of are like reference counts or arena cleanup. They can trigger caolascing, compaction, or gabarge collection events. Watermarks are garbage collecting events

Incrmenetal dataflow is semi naive without the fixpoint. Instead the deltas are coming in from outside in a streaming like situation.

Hmm. Do queries go backwards? A lens? holy shit is magic set a lens?

Adaptive function programming
Self adjusting computation <https://www.umut-acar.org/research#h.x3l3dlvx3g5f>
adapton
incremnetal  <https://blog.janestreet.com/introducing-incremental/>
[salsa](https://github.com/salsa-rs/salsa)
salsa.jl

Man I really need to decided where this stuff should go.

<https://twitter.com/wilton_quinn/status/1516501193660325889?s=20&t=7564nBvc82Jdkz_E3ccZbA>
[DRed paper](https://dl.acm.org/doi/pdf/10.1145/170035.170066)
[Recursive Computation of Regions and Connectivity in Networks](https://www.cis.upenn.edu/~zives/research/maintenance.pdf)

[seminaive for higher order languages](https://dl.acm.org/doi/abs/10.1145/3371090)
