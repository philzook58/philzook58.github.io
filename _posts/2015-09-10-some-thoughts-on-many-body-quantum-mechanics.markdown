---
author: philzook58
comments: true
date: 2015-09-10 16:07:29+00:00
layout: post
link: https://www.philipzucker.com/some-thoughts-on-many-body-quantum-mechanics/
slug: some-thoughts-on-many-body-quantum-mechanics
title: Some thoughts on many body quantum mechanics
wordpress_id: 130
---

There is a lot going on all at once when you open up a textbook on many body. Also, an insistence (which for practical calculational reasons makes a lot of sense, but leaves a conceptual hole) on using second quantized talk and notations, when before the thing you're most familiar with and spend years grappling is schroedinger style quantum mechanics. It is not impossible to do most if not all things you do in second quantized form in first quantized form.

A good question to ask throughout is what the hell are we talking about? In the sense of what subspace are we talking about really.

Let us suppose that things really are made of "just" electrons. Then the total vector space is clear and the total Hamiltonian is clear. A reasonable wavefunction will be $ \psi(x_1,x_2,x_3,...)$ which is properly antisymmetric in all the variables, one variable for each electron. In a discretized form the vector will look like $ \psi_{i_1 i_2 i_3 ...} $ where it is properly antisymmetrized between indices, one index for each electron. If you have a lattice of N sites and m electrons, then the number of amplitudes you have to give to specify your vector is roughly $ N^m/m!$ (Number for independent particles divided by permutations) not including some mild savings that you could achieve because of the antisymmetrization. This is quickly enormous. You might equivalently talk about solving PDE in 1,2,3 dimensions. 3d PDEs are way harder because for even modest lattice sizes the total size of vectors is huge.

So really, it is unacceptable to really discuss a vector in the context of the full configuration space of all the particles for most purposes.

Let us say that a power on high has given you the true ground state wavefunction of the system. How would you construct a reasonable space to work in? A simple answer is the single particle subspace, which can be constructed $ \sum_P (-1)^P \psi(x)\psi_0 (x,x,x,x,x...)$, where we are summing over all permutations of the variables with that pesky -1 for odd permutations. Perhaps I should stick to distinguishable particles for the moment. It cleans things up a bit and we don't need all these sums for symmetrization. $ \psi(x_{new})\psi_0 (x,x,x,x,x...)$

For concreteness, we'll worry about evolving a given wavefunction forward in time, sort of the canonical quantum mechanics problem. It tends to be that if you can solve that one, you can solve any other question you might ask. Evolving wavefunctions forward in time is related to all the high falutin Green's function techniques that maybe I'll get to in another post.

If the extra particle had no interaction with the other particles, let us say it is on venus or something, this would be a very good wavefunction indeed. The new wavefunction would evolve independently of the ground state wavefunction (which evolves trivially with a phase since it is a energy eigenstate) under its own hamiltonian.

$ \psi(x,t)e^{-i\omega_0 t}\psi_0 (x,x,x,x,x...)$

However, if the particle really does interact, then the wavefunction does not maintain this nice factored form, and that is what we really should expect. The factored form implies that really the new particle is not correlated at all in what it is doing to all the other particles. If they interact then of course they get correlated. If we want to be perfectly honest we really need to play in the full unusably huge vector space.

Luckily physics is not honest so ALL HOPE IS NOT LOST.

Here's the dumbest thing we can do (I don't mean that disparagingly. The dumbest thing you can do is the first thing you should do. Don't get fancier than you need to.). Let's hope that by restricting ourselves to wavefunctions of the form $ \psi(x)\psi_0 (x,x,x,x,x...)$ we can do a good enough job of describing the system. Maybe if they aren't interacting _that _much those wavefunctions will still be pretty good since they were really good when they didn't interact at all. Now all we need to specify is the new $ \psi(x) $ that we put on there, which has only N entries. Much more swallowable.

Ok. So how can we go about evolving the system in time? Well, we have the Hamiltonian, which probably has messy coulomb interactions or something in it. What about if we just find the matrix elements of the true hamiltonian in the subspace (which form and $ N\times N$ matrix) we're working in, then solve the thing by exponentiating it? Sure. Doable. For reasonable lattice sizes, we can totally solve the eigenvalues of that matrix or whatever. When we find the effective interaction between the ground state particles and the new particle, it is essentially the potential that would   be between a continuum blob with a density that is equal to the probability density of the ground state wavefunction  and the new particle $V(x)=\int dx\frac{\rho(x_1}{\|x-x_1\|}$ .

Cool. Let's say we've done this. Was this smart? Wellllllllllllllllllllllllllllll...

No.

What do we really want?

What we actually want is the matrix elements between the true correctly evolved wavefunction, whatever that happens to be, and our goofy subspace. Let's call the projection to our subspace the operator P which is 1 if you're in the subspace and 0 if you're outside.

What we kind of would prefer is this

$ <\psi |Pe^{-iHt}P|\psi >$

The evolution is for real and honest, but we only allow our restricted beginning and end states.

What we've done is this

$ <\psi |e^{-iPHPt}|\psi >$

Which has dishonest evolution and really can't be trusted.

Here is where things start to and will continue to be interesting. How do we achieve the former? We are now touching upon one of the many faces of renormalization! Isn't that exciting!

Let us form a definition of the effective hamiltonian

$ e^{-iP H_{eff} P t} = P e^{-iHt} P $

Ok. Definitions are nice, but to be certain, this does not immediately tell us how to calculate $ H_{eff}$.

We'll start there next time.

(PS wordpress latex freaks if you have an double whitespace. Are you kidding me?)






