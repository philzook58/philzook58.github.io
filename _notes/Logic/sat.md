---
layout: post
title: SAT Solvers
---
- [BDD](#bdd)
  - [Encoding](#encoding)
  - [Preprocessing](#preprocessing)
  - [CDCL](#cdcl)
  - [Parallel SAT](#parallel-sat)
  - [Stochastic local search solvers](#stochastic-local-search-solvers)
- [Beyond NP](#beyond-np)
  - [Model Counting](#model-counting)
  - [knowledge compilation](#knowledge-compilation)
  - [QBF](#qbf)
  - [Maxsat](#maxsat)
- [Misc](#misc)

See:

- Verilog

Sat competition

Minisat
glucose
kissat

<https://github.com/imandra-ai/minisat-ml?tab=readme-ov-file> minisat-ml ocaml.

# BDD

<https://www.cs.cmu.edu/~bryant/pubdir/fmcad22.pdf> tbuddy a proof generating sat solver
buddy
cudd

zdd

pgbdd <https://github.com/rebryant/pgbdd>
pgpbs <https://github.com/rebryant/pgpbs-artifact>

<https://arxiv.org/abs/2211.06818> CFLOBDDs: Context-Free-Language Ordered Binary Decision Diagrams

See also berkely abc. AIG and inverter graphs.
(RO)BDD are canonical. AIG aren't

## Encoding

At most one constraints (AMO)
Quadratic encoding. not x1 \/ not x2 \/ x3 /\ the other combos
logarithmic encoding. y is bitvector of which one is selected.
heule encoding

Graph constraints

Tseitsin - encode subformulas into a variable

Adders

[pysat](https://pysathq.github.io/)
[encoding into sat](https://www.cs.upc.edu/~erodri/webpage/cps/theory/sat/encodings/slides.pdf)
<http://www.cs.cmu.edu/~15414/s21/lectures/13-sat-encodings.pdf>

## Preprocessing

aiger

[preprcoessing in sat, maxsat, qbf](https://simons.berkeley.edu/talks/preprocessing-sat-maxsat-qbf)

## CDCL

## Parallel SAT

[Scalable SAT in the cloud](https://arxiv.org/pdf/2205.06590.pdf) Mallob 2022
[HordeSat: A Massively Parallel Portfolio SAT Solver](https://arxiv.org/pdf/1505.03340.pdf) 2015
Cube and Conquer

## Stochastic local search solvers

Simple and sometimes good.
[DDFW](http://crcodel.com/research/ddfw_pos.pdf)
Some examples:
<http://ubcsat.dtompkins.com/>
<http://fmv.jku.at/yalsat/>
<https://github.com/adrianopolus/probSAT>
matrix multiplication, problems with high symettry, graph coloring, pythoagorean triple problem

Seems very reasonable for max sat too?

# Beyond NP

<https://simons.berkeley.edu/workshops/beyond-satisfiability>

## Model Counting

<https://mccompetition.org/>

<https://github.com/crillab/d4>
<https://github.com/rebryant/cpog> CPOG Knowledge Compiler Certifier

beyond np <https://beyondnp.org/> hmm. This website is dead?

## knowledge compilation

<https://en.wikipedia.org/wiki/Knowledge_compilation>

## QBF

<https://simons.berkeley.edu/talks/quantified-boolean-formulas>

## Maxsat

<https://maxsat-evaluations.github.io/>
<https://github.com/FlorentAvellaneda/EvalMaxSAT>
[Combining Clause Learning and Branch and Bound for MaxSAT](https://drops.dagstuhl.de/opus/volltexte/2021/15329/pdf/LIPIcs-CP-2021-38.pdf) maxcdcl

<https://github.com/forge-lab/upmax>

# Misc

[Quadrangulation using a SAT solver](https://github.com/hjwdzh/QuadriFlow)
[satsort](https://github.com/arminbiere/satsort) I'm not sure what this is

[AWS automated reasoning frontier](https://www.amazon.science/blog/automated-reasonings-scientific-frontiers)
[mallob-mono](https://github.com/domschrei/mallob)
Good sat solver enabled "Seshia" tehcnique for smt? <https://github.com/awslabs/rust-smt-ir> bounds integers and turns to bitvectors + ackermannization

[beyond SAT](https://simons.berkeley.edu/workshops/schedule/14087)
quantified boolean. Combining SAT and comuter aogebra
model counting

[Soos proof traces for sat solvers FRAT](https://twitter.com/SoosMate/status/1513985102941982720?s=20&t=-ertSPtY87GogVCFq4f-Rw)

[sat solver for factorio](https://github.com/R-O-C-K-E-T/Factorio-SAT)

[similiarty metric between solutions](https://twitter.com/ShriramKMurthi/status/1522580546005745664?s=20&t=Q_7w5cTcsscGpoie1QtnCg) model-core in cvc5

[gimsatul](https://github.com/arminbiere/gimsatul) another armin biere experiment. parallel?

<https://twitter.com/ArminBiere/status/1556292768607207425?s=20&t=yqv3psiW3ByDbnVTBLr_GA> Kissat is domainting. The parallel and cloud solvers have really interesting things going on. mallob-ki. parkissat-rs is parallel winner

[The silent revolution of sat](https://news.ycombinator.com/item?id=36079115#36081904)

[creusat](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) <https://github.com/sarsko/CreuSAT>

[IPASIR-UP: User Propagators for CDCL](https://www.youtube.com/watch?v=pgsvqXAPgqA&ab_channel=SimonsInstitute)

[On Solving Word Equations Using SAT](https://arxiv.org/pdf/1906.11718.pdf)
