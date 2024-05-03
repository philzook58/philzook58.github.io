---
author: philzook58
comments: true
date: 2018-09-19 14:24:36+00:00
layout: post
link: https://www.philipzucker.com/?p=1118
published: false
slug: Solving the Pin Game with a SAT solver
title: Solving the Pin Game with a SAT solver
wordpress_id: 1118
---

While in a diner before our hike last weekend, there was a pin puzzle game on the table, the kind where you leap pins over pins and try to get it down to one. Given that we have discrete optimization on the brain (among other things), I wondered how to formulate this problem to a solver.

First off, a straight up tree search on moves is totally feasible and conceptually simple. But encoding to a SAT solver is a fun challenge, and may pay dividends if the board gets quite large.



Trick 1, we can unroll over time. Every move removes 1 pin, so we know exactly how many moves we need.

A binary variable for every hole at each time step, telling us if it is full of a pin or empty

a binary variable at each half time step for every possible move (pin to move and a direction to move it)

Then we need to write up such that only 1 move is selected per turn, and that the move is valid (that pin hole is full, the one it is jumping over is there and it's landing spot is empty), and that the board state changes correctly (remove jumped over pin, fill new pin location and vacate the old one, everything else stays the same).

We also need constraint that the initial board state is as given and that the final board state is a winning one. The game in the restaurant mentioned a challenge mode where the last pin has to be at the original empty spot.

We can encode an XOR into CNF via $latex (x_1 \lor \lnot x_2 \lor \lnot x_3 ) \land (\lnot x_1 \lor x_2 \lor \lnot x_3)  \land ( \lnot x_1 \lor \lnot x_2 \lor x_3)$

This will allow us to pick only one move per turn

If we pick a move, it's precondition must have been satisified

$latex m_{(t+\frac{1}{2})pd} \implies f_{tp} \land f_{t(p+d) }\land \lnot f_{(t(p+2d)) }  $

And then if the move is picked, the board must change accordingly

$latex m_{(t-\frac{1}{2})pd} \implies \lnot f_{tp} \land \lnot f_{t(p+d) }\land f_{(t(p+2d)) } \land_{all other pins p'} (f_{tp'} \iff f_{(t-1)p'} ) $



It does seem like a fun time to try out some Haskell sat solver bindings

Ersatz

Satchmo

SBV - more binds to SMT solvers







* * *



A tool more appropriate for the job is TLA+

We can make an array of the pin state

VARIABLE board, stuck

INIT == stuck = False /\ board == [  |->   IF i == 0 j==0 THEN "empty" ELSE "pin" ]

[ i \in 1..5  /\ j \in 1..5  /\ j < i   |->     ]

STUCK =

JUMPMOVE == \not STUCK



NEXT == JUMPMOVE /\ not STUCK

\/   stuck = FALSE /\ STUCK /\ stuck' = TRUE /\ board = board'

\/  stuck = TRUE /\ stuck' = TRUE /\ board = board'





Could we also use TLA+ to demosntrate the puzzle box deduction game?


