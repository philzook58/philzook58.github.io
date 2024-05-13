---
layout: post
title: Game Theory
---
- [Games](#games)
  - [Logic Math](#logic-math)
  - [Differential](#differential)
  - [algorithmic game theory](#algorithmic-game-theory)
- [Combinatorial game thoery](#combinatorial-game-thoery)
  - [Surreal Numbers](#surreal-numbers)

# Games

Nash equilibrium
Bimatrix games

Bilevel programming

Jules Hedges course
<https://www.youtube.com/watch?v=HzJE2eyA6e4&ab_channel=JulesHedges>
open games

Shoham course

normal form

extensive form
backwards induction <https://en.wikipedia.org/wiki/Backward_induction> Bellman equation. Dynamic programming. Bottom up.

```clingo
win(S).
trans(x,S,S1)
trans(o,S,S1)

win(x, S) :- trans(x,S,S1), not win(o,S1)

```

## Logic Math

<https://en.wikipedia.org/wiki/Ehrenfeucht-Fraisse_game>
<https://plato.stanford.edu/entries/logic-games/#BacForGam>
<https://www.youtube.com/watch?v=ZS8PfP_JCdA>
Introducing Model Theory with Ehrenfeucht-Fraïssé Games on Linear Orderings
<https://trkern.github.io/efg.html>
<https://trkern.github.io/hrumc>
<https://pi.math.cornell.edu/~mec/Summer2009/Raluca/index.html>
Seperability of structures via formula.

Model theory and finite model theory. What structures can EF gamers seperate? Finite models EF games are reasonably computable. QBF?
descriptive set theory

Determinacy <https://en.wikipedia.org/wiki/Determinacy>

<https://plato.stanford.edu/entries/logic-games/>
game semantics. One plays gets and other gets or.

<https://poleiro.info/posts/2013-09-08-an-introduction-to-combinatorial-game-theory.html>

<https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)> finite non draw games have winning stretgiies

altewrnating choice sequences.
Strategy sets and outcomes - normal form
transition system. `<L,S> -> <R,S'>`

Osborn book

<https://arxiv.org/pdf/1709.02096> An Existence Theorem of Nash Equilibrium in Coq and Isabelle∗

<https://proofassistants.stackexchange.com/a/1530> Mechanization of game semantics?
<https://www.ps.uni-saarland.de/extras/fol-completeness-ext/> coq fol completeness. Buity they include game semantics. Cody's Dom

<https://plato.stanford.edu/entries/logics-for-games/>
Benthem

## Differential

differential games - rufus book. <https://en.wikipedia.org/wiki/Differential_game>

Constructive reals and differential games? Probably rich thought there.

<https://arxiv.org/abs/2003.05013> An Introduction to Pursuit-evasion Differential Games
So like what? maybe do a subdivisision expansion?
do a graident descent but eagerly starting from the end?
Partamtrize the solution in a neighjborhood? Quandratic?
Hmalinton Joacib Rufus

cops and robbers game. <https://en.wikipedia.org/wiki/Cop-win_graph>
<https://en.wikipedia.org/wiki/Pursuit-evasion> Pursuit–evasion
declans' mouse game

## algorithmic game theory

<https://en.wikipedia.org/wiki/Algorithmic_game_theory>
<https://en.wikipedia.org/wiki/Price_of_anarchy>
<https://en.wikipedia.org/wiki/PPAD_(complexity)>

<https://www.youtube.com/watch?v=4dFPVJrNLDs&t=165s> games generalized geography, sipser

QBF as games. Should be "easy" to encode tic tac toe?

alpha beta pruning <https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning>
minimax <https://en.wikipedia.org/wiki/Minimax>

Tim Roughgarden <https://timroughgarden.org/> 20 lecture book <https://www.youtube.com/watch?v=TM_QFmQU_VA&ab_channel=TimRoughgardenLectures>
Noam Nisan <https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf>

Mechanism design
auction

# Combinatorial game thoery

 <https://en.wikipedia.org/wiki/Combinatorial_game_theory>

partisan games <https://en.wikipedia.org/wiki/Partisan_game>
<https://en.wikipedia.org/wiki/Impartial_game>
<https://en.wikipedia.org/wiki/Sprague-Grundy_theorem>

nim

```python

def nim_move(heaps): # heaps is a list of integers. This is the size of the heaps
    for n, heap in enumerate(heaps):
        for i in range(heap):
            new_heaps = copy(heaps)
            new_heaps[n] = i
            yield new_heaps 

```

tictactoe

```python

```

## Surreal Numbers

HACKENBUSH: a window to a new world of math <https://www.youtube.com/watch?v=ZYj4NkeGPdM&t=2818s&ab_channel=OwenMaitzen> Owen Maitzen rip.

Hackbusch is like a poset right? It's the hasse diagram? But it's colored. Hmm.
P - {x | x >= a & not exist y != a, x >= y}. Uhh. Maybe. but down hanging is ok.
G - {x | !path(ground,x) } Something like this.
trasnitivity --> datalog useful?

```python
#hackbusch
import networkx as nx

# path to ground vertex



```

hydra is kind of like hackbussch  <https://en.wikipedia.org/wiki/Buchholz_hydra>

poset game <https://en.wikipedia.org/wiki/Poset_game>

```python

zero = (None,None)
one = (zero,None)
two = (one,None)
three = (two,None)
neg_one = (None,zero)
neg_two = (None,neg_one)
neg_three = (None,neg_two)
```

Von Neumann

```python
_univ = 

def internset(x):
  x = frozenset(x)
  if x in _univ:
    return _univ[x]
  else:
    _univ[x] = x
    return x
# von neumann
zero = internset([])
def succ()
def univ():
  return internset(_univ)
# https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory

def pair(a,b):
  return frozenset([a,b])
def order_pair(a,b):
  return frozenset(frozenset({a}), frozenset({a,b}))

# separation axiom
def separate(A, P):
  return frozenset({x for x in A if P(x)})

from itertools import chain, combinations

def powerset(iterable):
  #https://stackoverflow.com/questions/1482308/how-to-get-all-subsets-of-a-set-powerset
  powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
  s = list(iterable)
  return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

# NBG class? == P, just a indicator function.
```

```python

def surreal(a,b):
  if (a,b) in univ:
    return univ[(a,b)]
  else:
    univ[(a,b)] = (a,b)
    return (a,b)
empty = frozenset()
zero = surreal(empty,empty)
one = surreal(frozenset(zero),empty)

class Surreal():
  def __init__(self, a, b):
    self.a = a
    self.b = b
  def __le__(self, other):
    #return self.a <= other.b
  #def __add__(self)

# surreal as pair of game trees
tictactoe = [[],[],[]]




```

Is there a normal form? That helped ordinals a lot

Hackenbusch
Nimbers
Combinatorial Game theory
Aaron N. Siegel's "Combinatorial Game Theory

`{|}` sets of available moves. Tic tac toe as a number ("ontinutatons") So programming languages have game semantics. Could one make a PL game?
*, uparrow, double up, eps, omega.
`*` is like a cloud

The game of quantifiers is how we discuss reals. Connection? We are reifying
Cody's ordinal game.

on off dud
oof hi lo
These are non well founded? Or just

<https://www.youtube.com/@elwynberlekamp5528> berlekamp videos
