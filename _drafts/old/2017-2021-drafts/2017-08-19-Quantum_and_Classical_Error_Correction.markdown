---
author: philzook58
comments: true
date: 2017-08-19 15:51:18+00:00
layout: post
link: https://www.philipzucker.com/?p=808
published: false
slug: Quantum and Classical Error Correction
title: Quantum and Classical Error Correction
wordpress_id: 808
---

Quantum error correction.



 	
  1. Measure the error not the signal. I can know if three bits are not the same without knowing the actual values of any of the bits.

 	
  2. Measurement of the error actually projects the possible infinitude of possible error unitaries into a discrete finite set (bit flip, phase flip and combo, AKA X, Z, Y). $latex \cos(\theta)I+i\sin(\theta)X |00> \rightarrow \cos(\theta)|00>+i\sin(\theta)|10>$ When you measure the error of whether or not these two qubits are equal, you project the state probabilistically


Linear Codes

Using Z2 arithmetic. Which is weird. You can think of it being addition mod 2 or think of addition as an xor.

Matrix formulation, each data bit correponds to a code bit vector and the encoded guys are the xor of all the vectors. You can write this as a rectangular matrix taking the smaller dimensioned data space to a larger dimensional encoded space. Anything that lies outside of the subspace that is spanned by the vectors was due to an error.

Conceptually, you can correct errors by just computing which actually possible encoded vector is closest, defining closeness by counting bitwise differences (Hamming distance).

You can produce a check matrix that will tell you if you have an error or not. It is a set of vectors orthonormal to the good code subspace. Then you can build a table for each possible result into what error to fix.



Physical error correction: Ferromagnets duplicate all the spins in a big clump. They point in the same way. If some cosmic ray flips one of the spins, the others will pull it back to the right direction. You have to flip a significant number of them at once in order to cause a true error, which is usually hard and unlikely.

Physical Quantum Error Correction: Topological Matter. There are quantum mechanical features that cannot be accessed or changed locally. You have to do something globally, like dragging a quasiparticle all the way round the surface or suppressing the phase in a big way. These materials/phases of matter are called topological because they are so global. They will "notice" global topological things like the number of holes in the surface you put the phase on.


