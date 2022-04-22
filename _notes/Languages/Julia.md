---
date: 2020-10-16 23:49:48+00:00
layout: post
title: Julia
wordpress_id: 2987
---


```julia
println("hello world")
#using Plots
#using JuMP
using LinearAlgebra
x = [1,2,3,4]
print(x)
using Metatheory
```

[packagecompiler](https://julialang.github.io/PackageCompiler.jl/dev/index.html) make sys images so that packages load faster

Metaheuristics.jl

If you want just linear problems, you can also try Tulip (this is me self-advertising; I wrote it). It's pure Julia, and should give you decent performance.
If you want nonlinear problems, among the open-source pure Julia solvers, you have:
COSMO, which supports several cones & quadratic objective. It's based on ADMM, same as SCS/OSQP
Hypatia, which supports the largest variety of cones (especially the ones you've never heard of). It's based on interior-point, same as ECOS/Mosek.
For LP and convex QP, there is also https://github.com/JuliaSmoothOptimizers/RipQP.jl

JuliaSmoothOptimizers https://www.youtube.com/watch?v=FsQJ6NEUF6g&ab_channel=TheJuliaProgrammingLanguage

- [Fellisson course](https://felleisen.org/matthias/4400-s20/lecture15.html) Nice description of expression problem and multiple dispatch
- [Rackauckas comments on paper about julia types](https://twitter.com/ChrisRackauckas/status/1468610935673831430?s=20)
- [Gotchas](https://www.stochasticlifestyle.com/7-julia-gotchas-handle/)
- [Type Stability in Julia: Avoiding Performance Pathologies in JIT Compilation (Extended Version)](https://arxiv.org/abs/2109.01950)
- [World Age in Julia: Optimizing Method Dispatch in the Presence of Eval (Extended Version)](https://arxiv.org/abs/2010.07516)
- [Keno describing his lens AD thing diffractor](https://twitter.com/KenoFischer/status/1465925184578363392?s=20)
- [What scientists must know about hardware to write fast code](https://viralinstruction.com/posts/hardware/)
Interesting topics:
- World Age
- Multiple dispatch
- Subtyping and most specific type
- Max_methods = 1 as a good default?
- Type ambiguity?
- Function barriers

[Runtimegeneratedfunctions.jl](https://github.com/SciML/RuntimeGeneratedFunctions.jl)

Evan's new talk. Seems really cool. Categories for multiphysics?


Interesting project ideas:
- PyRes translation
- That prolog engine
- SMT modulo Convex
- Interactive Proofs
- probabilistic games use homotopy continuation
- Guarded rewrite rules
- Constraint programming compilation
- CHC from SSA
- WP
- anyon
- linear relations / modules



Scientific Computing in Julia. Numerical Computing in Julia
HPC in Julia
Data Science in Julia
Deep Learning in Julia
Algorithm Design in Julia
Physics for Programmers



Audience: 
Someone at my level or higher?
People who do scientific computing? At labs?
Engineers?
Grad students?
Hobbyists?

End Expectations:
? No one actually reads books



that optimization book in julia

Strang Book


Fluid Solver
Wave Solver
Fitting Data -
An Inverse Problem
Particle simulation
Convnet
ODE and PDE



Function Breaks, Type Stability
Examining Code, llvm and native
Fast Loops SIMD
Parallelism
GPU
DSLs
Partial Evaluation / Macros. generative functions
Dispatch - Fast matrix overloading




Minimal: you can activate a environment. 

From a julia repl, you can press `]` to put it into Pkg mode

    
    <code>pkg> activate .</code>

Revise.jl - You can use Revise.jl. If you're editting a one off file, you can bring it into the repl with `includet` so that it automatically reloads anytime you change the file.

    
    <code>julia> using Revise
    julia> includet("myfile.jl")
    julia> myfunction(7)
    </code>

You should take a gander

[https://docs.julialang.org/en/v1/stdlib/Pkg/](https://docs.julialang.org/en/v1/stdlib/Pkg/)

[https://julialang.github.io/Pkg.jl/v1/](https://julialang.github.io/Pkg.jl/v1/)

[https://github.com/invenia/PkgTemplates.jl](https://github.com/invenia/PkgTemplates.jl) [https://invenia.github.io/PkgTemplates.jl/stable/user/](https://invenia.github.io/PkgTemplates.jl/stable/user/)

This is how you get those slick little badges for documentation and  

https://www.youtube.com/watch?v=QVmU29rCjaA&t=1157s&ab_channel=TheJuliaProgrammingLanguage

Unit testing. I don't write tests for my code often enough, I know it's a good thing to do. Here's how you do it.

    
    <code>using MyPkg
    using Test
    
    @testset "MyPkg.jl" begin
        # Write your tests here.
        @test true
        @test MyPkg.foo(2) == 4
    end</code>

    
    <code>pkg> test MyPkg</code>
