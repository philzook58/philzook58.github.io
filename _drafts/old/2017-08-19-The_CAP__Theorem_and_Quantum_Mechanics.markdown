---
author: philzook58
comments: true
date: 2017-08-19 16:09:38+00:00
layout: post
link: https://www.philipzucker.com/?p=809
published: false
slug: The CAP  Theorem and Quantum Mechanics
title: The CAP  Theorem and Quantum Mechanics
wordpress_id: 809
---

The cap theorem says that no distributed system can have consistency availability and partition tolerance.

Partitions make sections of the network unable to communicate to each other. In physics-ish talk they are space-like separated.

But if that happens, the pieces can't coordinate. So either they can't necessarily know that you fiddled with something over in the other guy (consistency) or they have to say you can't use me until I talk to my bro (availability).

Now, suppose instead you used branching on every possible response every time you got a unavailable response due to a partition, then eventually when the system gets back together you could just select the branch of your computation where . This is an explosive use of resources though.

However, if the system has entanglement resources and you have a quantum channel and quantum computing resources, I think you can do the branching quantum mechanically. However you have to wait for the partition to heal and classical communication to occur in the system before any measurement because to actually use the entanglement for communication is classic EPR paradox. (okay I just think this is consistent with principles and don't yet have a way to do so. You could just unwind all the computation you've done.)

To submit a bit, pick to measure x or z on the entanglement resouce. Then eventually you can communicate what you got to the other side once the partition heals, and the quantum computation can.

Whats the point though? Quantum communication that you can't measure until the partition is healed is useless for Facebook and human stuff.

But what about parallel quantum computation? (Parallel running quantum machines, not the pseudo parallelism of a single quantum machine. One could imagine multicore quantum chips with entanglement buses. Hmm. That strips off a lot of the database system feel)
