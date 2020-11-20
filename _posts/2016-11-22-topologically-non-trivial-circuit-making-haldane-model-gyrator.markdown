---
author: philzook58
comments: true
date: 2016-11-22 21:13:30+00:00
layout: post
link: https://www.philipzucker.com/topologically-non-trivial-circuit-making-haldane-model-gyrator/
slug: topologically-non-trivial-circuit-making-haldane-model-gyrator
title: Topologically Non-Trivial Circuit or Making the Haldane Model with a Gyrator
wordpress_id: 561
---

The gyrator is a funny little guy. You don't hear about him much.

[https://en.wikipedia.org/wiki/Gyrator](https://en.wikipedia.org/wiki/Gyrator)

He's kind of like a transformer. He converts voltage to current and current to voltage in such a way as to dissipate no power. You can build active ones out of op amps or in the microwave regime you can build them out of pieces with built in permanent magnets. I saw an interesting article suggesting that people could use a sample in the Quantum Hall Effect as a gyrator. I'm chewing on that.

The gyrator feels very much like the Lorentz force or rotational stuff, hence the name probably. In ordinary dynamics, if the force is proportional to the velocity the dynamics is dissipative and lossy, like sliding on mud. However, if a key piece is that the velocity and force point in different directions, the force can be non-dissipative.

The device breaks time reversal symmetry. If you flip time, the currents flip direction but the voltages stay the same. If you look at the equations one of the current and voltage connecting equations has a minus sign and one doesn't. This is important to keep the thing non-dissipative. Flipping time would flip which equation has the minus sign in it, which isn't the same dynamics anymore. Resistors also aren't time reversal symmetric, but that is not unexpected since they are dissipative and dissipation relies on entropy production and the arrow of time.

Capacitors and inductors are time reversal symmetric. When you flip the current sign you also flip the sign on the derivative with respect to t that is in their defining equation.

Anyhow, this all makes it plausible that you can get a funky topological character to a 2 dimensional grid built out of these things.

The basic arrangement can be built out of gyrators and capacitors.[![drawing](http://www.philipzucker.com/wp-content/uploads/2016/11/Drawing-300x172.jpeg)](http://www.philipzucker.com/wp-content/uploads/2016/11/Drawing.jpeg)

The laws of motion come from conservation of current at every node

$latex (j\omega C + z/R - 1/Rz)V=0$

This equations gives the dispersion relations $latex C\omega=2 \sin(ka)$

The 2d arrangement is very similar, just place gyrators also going in the y direction. But to get a topologically nontrivial band structure we need to dimerize the unit cell (or work on a hexagonal lattice where your unit cell is sort of force to be doubled). In totality you have 4 gyrator parameters to play with and 2 capacitance parameters. And you can in fact arrange the parameters such that the circuit is in the topological regime. It's easiest to see this by writing the thing in terms of Pauli matrices with the pesudospin referring to which point of the unit cell

$latex j \omega C V= \sigma\cdot B(k_x,k_y) V$

If you arrange the parameters (not even that carefully, which is kind of the point) you can get it such that the normalized B vector wraps the sphere as you traverse the entire Brillouin zone.

This circuit has band gap. There will be chiral propagating modes within the band gap on the edge.

Food for thought: Circuits have to have real values for voltage and current.  Hence there always has to be a correspondence between a plus and minus frequency in the system. The is not a general constraint on Schroedinger's equation. Is this similar to particle-hole symmetry? If so, can you construct a nontrivial phase with the analog of a Majorana mode. Would that be a non oscillating charge or current that must occur at some positions (not particularly exotic)? Not sure how much this line of thought makes any sense.
