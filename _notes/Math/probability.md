---
layout: post
title: Probability
---

- [Graphical Models](#graphical-models)
- [Statistics](#statistics)
  - [Bayesian](#bayesian)
- [Distributions](#distributions)
- [Information](#information)
- [Mathematical](#mathematical)

See also:

- Discrete math / combinatorics
-

# Graphical Models

<https://en.wikipedia.org/wiki/Bayesian_network> bayesian networks directed edges express conditional rpobablity. Hopefully acyclic.
<https://en.wikipedia.org/wiki/Graphical_model> graphical models
<https://en.wikipedia.org/wiki/Markov_random_field>

# Statistics

```python

```

student's t
chi squared
p value


I should have more to say here?
Probability
Experimental design
Hypothesis testing
Goodness of fit metrices
Bayes rules
Regularization
Bayes rule and regularization can be seen to be related. Regularization corresponds to a prior that the values of your parameters aren't going to be ridiculous. A Gaussian prior and guassian distrubtion of error

$$ e^{ -\frac{\eps^2}{\sigma^2} } $$
$$ y_j = \eps_j +  \sum a_i f_i(x_j) $$

Machine learning

Cumulants
Paradoxes

Measure theory
stochastic calculus

Combinatorics

Markov decision processes
Monte carlo algos
las vegas algos

## Bayesian

bayesian vs freqeuntist
Priors as regularization

# Distributions

Gaussian
Poisson
Binomial

# Information

Entropy
Mackay <https://www.inference.org.uk/itprnn/book.pdf> Information Theory, Inference, and Learning Algorithms <https://www.youtube.com/watch?v=BCiZc0n6COY&ab_channel=JakobFoerster>

# Mathematical

<https://en.wikipedia.org/wiki/Cox%27s_theorem>

```python
from z3 import *
E = Sort("Event")
P = Function("P", E, RealSort())

# Proof system for probability theory?
```

<https://en.wikipedia.org/wiki/Probability_axioms> Kolmogorov axioms

Sets and probability. You need to know an ambient space X to be working in.

<https://en.wikipedia.org/wiki/Probabilistic_logic>

[Law of Total Probability](https://en.wikipedia.org/wiki/Law_of_total_probability)
$P(A) = \sum P(A \cap B_i) = \sum P(A | B_i) P(B_i)$
if $B_i$ is a partition of the sample space

<https://en.wikipedia.org/wiki/Law_of_total_expectation>

Central limit theorem

Markov bound
Chernoff bound
