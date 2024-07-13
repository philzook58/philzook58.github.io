---
title: OPLSS 2024 Boston
---

<https://www.cs.uoregon.edu/research/summerschool/summer24/topics.php>

# Pfenning

snax

semi axiomatic

# Ahmed

What is a logical relation?
"semantics" as sets of terms or sets of values
"semantics" as parametrzied sets of terms. This persepctive also helps understand NbE

# Downen

# Silva

# Bourgeat

# Holtzen - Probablsitic Programs

Probabilistic programming form the ground up steven holzten
PPL

PL people vs AI people

1. PL
you want to verify programs, programs have uncertiainty in them. randomized algos. dist systems and networking.  Differential privacy. programs should have probablistic semantics. 1982 - dexter kozen.

2. AI
why ppl from ai perspective? want to be able to create agents that reason rationally about the world. represent the world to the computer. World is too complicated. use probablisitc reasonig to simplify the world. Judea pearl - netowkrx of pluasible inference. Cyc. Probablistic graphical models. PPLS provide expressive languages for modeling the world

Implement a series of languages
synatx and semanitcs of ppl - dneotationla
sampling - operatoinal
tractiubility and expressivity
topics

probablistic programs denote
probablsility dsitrbutiond

```
x <- flip .5
y <- flip .5
return x || y
```

= 3/4
[tt |-> 3/4, f |-> 1/4]
A sample space is a set $\Omega$
$\Omega -> [0,1]$

TinyPPL

pure
p ::= x | if p then qp else p | p /\ p | true | false
impure
e ::= x <- e, e | return p | x <- flip theta

semantics of pure

```
Env -> bool
[|x|] rho = rho x  -- \ [x -> tt] = tt
[|true] _ = true
```

probablistic terms

Env -> {tt, ff} -> [0,1]
[e] rho =

monadic semantics of ppl
[x <- e; e] = \sum [e](rho)(v)
Ramsey and Pfeffer '02
Michelle Giry 1986 - categorical semantics of probablity distributions

`#P hard`

observe syntacti  feature
