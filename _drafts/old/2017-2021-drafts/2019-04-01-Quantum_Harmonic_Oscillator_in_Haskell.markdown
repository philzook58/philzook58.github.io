---
author: philzook58
comments: true
date: 2019-04-01 20:57:39+00:00
layout: post
link: https://www.philipzucker.com/?p=1906
published: false
slug: Quantum Harmonic Oscillator in Haskell
title: Quantum Harmonic Oscillator in Haskell
wordpress_id: 1906
---




I've talked about the free vector space type before. There is a simple way to encode the concept of a free vector space in Haskell. It is in the form of a sparse vector data type that holds the coefficients corresponding to each basis element. I've implemented it using a tuple list, for ease. This is a horrifically inefficient data structure for the record. We could do better. Alternatives include using a Map, with coefficients keyed on basis vectors, or using the Vector data type rather than lists. http://hackage.haskell.org/package/vector







We can build a pretty convenient representation of the simple harmonic oscillator. The vector space of the quantum simple harmonic oscillator has a basis labelled by how many quanta of energy the oscillator has. $latex E = \hbar \omega (n + \frac{1}{2})$ In other words, the vector space is described by `Q Int`.







We can write down the raising and lowering operators $latex a^\dagger a$ simply.







Linear operators behave very similarly to numbers. The operators in quantum mechanics are very similar to classical variables (except they don't necessarily commute under multiplication).







What this means is we can define a reasonable Num typeclass instance (for the most part) for `LinOp`. Addition can be defined as addition on the output vectors. Multiplication is the same as composition. `fromInteger`creates a scaled identity operator.







`abs` and `signum` are tougher. While it is easy to define polynomials of operators, general nonlinear operators are tougher. the usual way to think about it is the think of the operator in it's eigenbasis. Then you can just apply the nonlinear function to the eigenvalues individually. One bummer of the approach I've been following is that we don't have an explicit representation of the operator. It is hidden behind an opaque functional interface. One could reconstitute an explicit form by applying to a complete basis and handing off to an external eigenvalue solver, but this is rather unsatisfying.







A similar thing can be said about inversion of an operator. We could reconstitute an explicit matrix, and then hand it off to some external solver. However, it actually makes sense to merge these two processes. A standard very effective set of methods known as Krylov methods actually build the vector space by repeated application of the operator. The intuitive idea is that applying the operator over and over tends to extract out the dominant eigenvectors of the system, which are the most important bits for the purpose of solving a system of equations.  








Similarly a spin-1/2 or qubit can be represented as `Q Bool`. 







If we have two oscillators, the state space is `Q (Int, Int)`. If we had a entire lattice of oscillators, the vector space would be `Q (f Int)` where `f` is some container type with a slot for every location on the lattice. This is also the data type of a multi particle bosonic system. It makes sense as some bosonic systems are thought of as the quantization of a field of oscillators (photons, phonons).







For fermion systems we have a similar story. For fermions, we have an occupation number presrentation where a state can iether be full or empty. Hence the type of a lattice of Fermion sites is the same as a lattice of spin sites. `Q (f Bool)`. The antisymmettric nature of Fermions only comes in when we actually implement the appropriate operators.







Another interesting representation for Fermions is `Q [a]` where `a` is an index into the `f` container type. This is because there is a reasonable relationship between `f Bool` and `[a]`. Only list an `a` if that slot in `f` has a `True` indicating it is full. It isn't quite as clear because not all possible values of `[a]` actually have an associated element in the vector space. You can't double fill a state, but you can have the same value twice in a list.







Conceptually though, this representation feels like a more particle centric perspective on Fock space.  








What are the standard questions of quantum mechanics?







We often want the eigenvectors and eigenvalues of operators.







We also want the time evolution of a system.







We want scattering coefficients.  










