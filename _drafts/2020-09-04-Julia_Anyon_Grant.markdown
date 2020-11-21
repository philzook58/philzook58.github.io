---
author: philzook58
comments: true
date: 2020-09-04 03:26:54+00:00
layout: post
link: https://www.philipzucker.com/?p=2954
published: false
slug: Julia Anyon Grant
title: Julia Anyon Grant
wordpress_id: 2954
---




A project that has been interesting to me is 







The statistics of anyonic quasiparticles are the foundation of the approach of toplogocial quantyum computaiton. This mathematics is foreboding. The proposed project is building a library in Julia for the numerical and symbolic computation of the braiding diagrams. Lowering the barrier for numerical experimentation with these systems.







Topological quantum computation is one of the possible avenues by which error corrected quantum computation could be achieved. The idea is based around using a fundamental physical protection of quantum information in an exotic phase of matter in a manner analogous to how magnetic phases of matter protect information on a hard disk today. The exotic phases of matter support quasiparticle excitations known as anyons, which are a generalization of bosons and fermions. The theory of these anyons and topological quantum field theory is somewhat intimidating. 506 chars







Topological quantum computation is one of the possible avenues by which error corrected quantum computation could be achieved. The approach encodes a quantum computation into the braiding of quasiparticles known as anyons. The theory of these anyons and topological quantum field theory is somewhat intimidating. While computer simulation has been carried out for anyonic systems, I am not aware of a systematic computer library for expressing and evaluating these calculations. The proposed project is to implement such a library in the programming language Julia, a nexus of exciting numerical computation ideas.







A previous prototype written in the programming language Haskell has been developed as explained in these blogs posts. Haskell was a chosen language because of it's known connections with category theory, a mathematical language in which anyon algebra is often described.







Why Julia? Julia has an exciting community of scientist and numerical computation experts. It aims to be a language that offers comforts above those of languages like python and matlab with the speed of C++.







The goals of the project







  * Port a related approach to Julia
  * Investigate more HPC compatible approaches to structuring the computation
  * Interoperation with the Julia library Catlab.jl
  * Explicate the structure of anyon algebra through a concrete implementation
  * Lower the barrier for numerical experimentation with anyonic systems.






@Philip Zucker . Mostly I deal with (bosonic) tensor networks for quantum many body systems. However, in [TensorKit.jl](https://github.com/search?q=TensorKit.jl&type=Repositories), a `TensorMap` can represent a morphism in an arbitrary fusion category (with some additional properties). In particular, there is code to manipulate fusion trees etc, and to perform arbitrary braids on such morphisms. The most important thing missing is an easy to use interface for defining and computing arbitrary string diagrams including braids etc. The current interface is using Einstein summation convention with the `@tensor` macro from [TensorOperations.jl](https://github.com/search?q=TensorOperations.jl&type=Repositories), but as we are discussing, this does not uniquely specify a string diagram, unless the braiding is symmetric. Even then it cannot handle non-trivial twists, so I would say it really only unambiguously deals with a trivial braiding, i.e. a swap. So for fermions, there are still some issues. - Jutho Haegeman



