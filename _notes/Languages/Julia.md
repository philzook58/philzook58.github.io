---
date: 2020-10-16 23:49:48+00:00
layout: post
title: Julia
wordpress_id: 2987
---

<https://github.com/sumiya11/Groebner.jl> claims quite fast

[LiftedTrajectoryGames](https://github.com/lassepe/LiftedTrajectoryGames.jl)

[bare metal julia arduino](https://news.ycombinator.com/item?id=31481895)

```julia
println("hello world")
using Plots
using JuMP
using LinearAlgebra
x = [1,2,3,5]
print(x)
using Metatheory
```

```bash
time echo "
println(\"hello world\")
using Plots
#using JuMP
#using LinearAlgebra
x = [1,2,3,5]
print(x)
#plot(x)
#gui()
#using Metatheory
#exit() 
" | julia -i

```

Time to first plot is 2 seconds now. Not bad. It seems mad about something `qt.qpa.plugin: Could not find the Qt platform plugin "wayland" in ""`

hmm if I want julia to work good, I need to make a command that is valid julia but also valid bash

# = =# multiline julia is not a bash comment

```
#= 
bash code julia won't run
# =# julia code bash won't run
```

```
#= 
julia
# =# julia code bash won't run
```

```
"julia": "#=\njulia\n# =#\ninclude($dir * \"$fileName\")",
```

Yes, that's right, Mr. Vice President. I _am_ a genius.

[packagecompiler](https://julialang.github.io/PackageCompiler.jl/dev/index.html) make sys images so that packages load faster

Metaheuristics.jl

If you want just linear problems, you can also try Tulip (this is me self-advertising; I wrote it). It's pure Julia, and should give you decent performance.
If you want nonlinear problems, among the open-source pure Julia solvers, you have:
COSMO, which supports several cones & quadratic objective. It's based on ADMM, same as SCS/OSQP
Hypatia, which supports the largest variety of cones (especially the ones you've never heard of). It's based on interior-point, same as ECOS/Mosek.
For LP and convex QP, there is also <https://github.com/JuliaSmoothOptimizers/RipQP.jl>

JuliaSmoothOptimizers <https://www.youtube.com/watch?v=FsQJ6NEUF6g&ab_channel=TheJuliaProgrammingLanguage>

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

<https://www.youtube.com/watch?v=QVmU29rCjaA&t=1157s&ab_channel=TheJuliaProgrammingLanguage>

Unit testing. I don't write tests for my code often enough, I know it's a good thing to do. Here's how you do it.

    <code>using MyPkg
    using Test
    
    @testset "MyPkg.jl" begin
        # Write your tests here.
        @test true
        @test MyPkg.foo(2) == 4
    end</code>

    
    <code>pkg> test MyPkg</code>

## JuliaCon 23

### worlddynamics

"global integrated assessment models" IAM
<https://github.com/worlddynamics/WorldDynamics.jl>
<https://worlddynamics.github.io/WorldDynamics.jl/dev/>
simulating economics?
earth4all
World3 model introduced in the book Dynamics of Growth in a Finite World (1974).
plotlyjs.jl <https://github.com/JuliaPlots/PlotlyJS.jl>

### CirculatorySystemModels.jl

<https://pretalx.com/juliacon2023/talk/AYQRRE/>

modelingtoolkit.jl

### differentiable gpu

<https://pretalx.com/juliacon2023/talk/GTKJZL/>
ParallelStencil.jl, [ImplicitGlobalGrid.jl](https://github.com/eth-cscs/ImplicitGlobalGrid.jl) and Enzyme.jl J
<https://github.com/PTsolvers/gpu-workshop-JuliaCon23>
[Solving PDEs in parallel on GPUs with Julia - ETH course](https://pde-on-gpu.vaw.ethz.ch/)
<https://github.com/PTsolvers>
Enzyme
Parallelstencil
Optim
CairoMakie

`@parallel`
`@views`

```julia
typeof(pi)
using LinearAlgebra
I(3)
[1 2; 3 4] # matrix
[1]
[1,2,3] # vector
rand(2,3)
3im
#transpose()
Bidiagonal([2,2,2,2], [-1,-1,-1], :U)
```

Hmm. Differentiating through a forward problem.

Broadcasting with `.`

### Image processing

<https://pretalx.com/juliacon2023/talk/TTAJXA/>
<https://github.com/JuliaImages/JuliaCon23_ImageProcessingWorkshop>
Images.jl

```julia
using Images

```

[juliaup](https://github.com/JuliaLang/juliaup)
My how the times change
`juliaup add release`
`juliaup default release`
`juliaup update release`

```
using Pkg
Pkg.activate(path_to_repository_clone)
Pkg.instantiate()
Pkg.precompile()
```

### dataframes

<https://dataframes.juliadata.org/stable/>

parquet for large data

```julia
using DataFrames
using Parquet2
using Random using Statistics
using StatsBase
isdir("foo")
mkdir("/tmp/mytemp")
@info "here we gooo"
```

```julia
using DataFrames



```

```julia
#commands
run(`echo foo`)
```

### NeuralODEs

<https://www.uni-augsburg.de/de/fakultaet/fai/informatik/prof/imech>
<https://fmi-standard.org/> functional model interface. What
<https://github.com/ThummeTo/FMIFlux.jl>

- FMI.jl: High level loading, manipulating, saving or building entire FMUs from scratch
- FMIImport.jl: Importing FMUs into Julia
- FMIExport.jl: Exporting stand-alone FMUs from Julia Code
- FMICore.jl: C-code wrapper for the FMI-standard
- FMIBuild.jl: Compiler/Compilation dependencies for FMIExport.jl
- FMIFlux.jl: Machine Learning with FMUs (differentiation over FMUs)
- FMIZoo.jl: A collection of testing and example FMUs

hypterparamter optimization
[DifferentiableEigen.jl](https://github.com/ThummeTo/DifferentiableEigen.jl)

Sciml

- Chen T Q, Rubanova Y, Bettencourt J and Duvenaud D. 2018. Neural ordinary dierential equations. (Preprint 1806.07366) URL <http://arxiv.org/abs/1806.07366>
- Tobias Thummerer, Johannes Stoljar and Lars Mikelsons. 2022. NeuralFMU: presenting a workflow for integrating hybrid neuralODEs into real-world applications. Electronics 11, 19, 3202. DOI: 10.3390/electronics11193202
- Tobias Thummerer, Lars Mikelsons and Josef Kircher. 2021. NeuralFMU: towards structural integration of FMUs into neural networks. In Martin Sjölund,
- Lena Buffoni, Adrian Pop and Lennart Ochel (Ed.). Proceedings of 14th Modelica Conference 2021, Linköping, Sweden, September 20-24, 2021. Linköping University Electronic Press, Linköping (Linköping Electronic Conference Proceedings ; 181), 297-306. DOI: 10.3384/ecp21181297
- Tobias Thummerer, Johannes Tintenherr and Lars Mikelsons. 2021. Hybrid modeling of the human cardiovascular system using NeuralFMUs. Journal of Physics: Conference Series 2090, 1, 012155. DOI: 10.1088/1742-6596/2090/1/012155
- Bezanson J., Karpinsky S., Shah V. B. and Edelman A. 2012. Julia: A fast dynamic language for technical computing. (Preprint 1209.5145) URL <http://arxiv.org/abs/1209.5145>
- Danquah, B. Component Library for Full Vehicle Simulations repository on GitHub. Available online: <https://github.com/TUMFTM/Component_Library_for_Full_Vehicle_Simulations> (accessed on 4 October 2022).
- Tobias Thummerer, Artem Kolesnikov, Julia Gundermann, Denis Ritz and Lars Mikelsons. 2023. Paving the way for Hybrid Twins using Neural Functional Mock-up Units. Proceedings of 15th Modelica Conference 2023, Aachen, Germany, October 9-11, 2023. (submitted Paper)
- Tobias Thummerer, Lars Mikelsons. 2023. Eigen-informed NeuralODEs: Dealing with stability and convergence issues of NeuralODEs. arXiv. <https://doi.org/10.48550/arXiv.2302.10892>
- Rackauckas, Christopher and Ma, Yingbo and Martensen, Julius and Warner, Collin and Zubov, Kirill and Supekar, Rohit and Skinner, Dominic and Ramadhan, Ali. 2020. Universal differential equations for scientific machine learning. arXiv preprint arXiv:2001.04385

<https://github.com/modelica/fmi-standard>
Physics-enhanced Neural Ordinary Differential Equations (PeNODEs)
Combine ODE models but allow fitting to data

### Genie

<https://genieframework.com/>
Stipple ORM
Make dahsabords

### sciml and ode

symbolicregression
<https://en.wikipedia.org/wiki/Symbolic_regression>
<https://github.com/MilesCranmer/SymbolicRegression.jl>
Miles cranmer <https://astroautomata.com/>

modelling toolkit
pharmcometrics
SIR model
universal approximators using ODEs
differentiate through ODEs

<https://juliapackages.com/p/momentclosure> memont closure approximations

### compressed sensing mri

###

dyve - catlab to sciml bridge?
isdef.jl
SARprocessing.jl - synthetc aperture radar
PmmAocsSimulator.jl. SatelliteToolbox.jl, ReferenceFrameRotations.jl,
<https://github.com/awslabs/Braket.jl>
Snoopcompile how much time in llvm <https://timholy.github.io/SnoopCompile.jl/stable/>
threadpinning <https://github.com/carstenbauer/ThreadPinning.jl>

<https://github.com/qojulia/QuantumOptics.jl> quantom optics

<https://pretalx.com/juliacon2023/talk/A3LVDS/>
fluxml <https://fluxml.ai/>
<https://lux.csail.mit.edu/stable/> lux.jl some other neural thing
scrna-seq data <https://en.wikipedia.org/wiki/Single-cell_sequencing> single cell autoencdoer?

3d u-net of liver-ct  <https://en.wikipedia.org/wiki/U-Net> biomedical ct scan segmentation

<https://github.com/gamma-opt/DecisionProgramming.jl>
<https://github.com/gamma-opt>
<https://github.com/gamma-opt/optimisation-notes>
decision analysis vs stochastic programming
"influence diagram" <https://en.wikipedia.org/wiki/Influence_diagram>

<https://github.com/JuliaCollections/SortingAlgorithms.jl> sorting algorithms

<https://github.com/JuliaQuantumControl>

XGboost

`develop --local Bed` puts local version
Pkgtemplate.js

```julia
bar(x) = x + 4
foo(x) = bar(x) * 3

@code_llvm 1 + 2
@code_llvm foo(7)
```

seahorn
llbmc
crucible maybe
surely trail of bits has something
<https://repositum.tuwien.at/bitstream/20.500.12708/81355/1/Priya-2022-Bounded%20Model%20Checking%20for%20LLVM-vor.pdf>
CBMC, SMACK, KLEE and SYMBIOTIC.

### Genomics

<https://tecosaur.github.io/DataToolkit.jl/stable/>

<https://biojulia.dev/>
<https://github.com/BioJulia/BioTutorials>

<https://openmendel.github.io/>

<https://bowtie-bio.sourceforge.net/index.shtml> Bowtie is an ultrafast, memory-efficient short read aligner. Ben angmead
<https://en.wikipedia.org/wiki/Bowtie_(sequence_analysis)>

snakemake python make files? <https://snakemake.readthedocs.io/en/stable/>
<https://www.nextflow.io/>
<https://nf-co.re/> cf-core

```julia
@show ARGS
```

BED files <https://en.wikipedia.org/wiki/BED_(file_format)>
genomicfeatures.kl <https://github.com/BioJulia/GenomicFeatures.jl>
 BED, GFF3, bigWig and bigBed.

<https://github.com/aviatesk/JET.jl>

Tensoroperations.jl
`@tensor D[i,j,k] := A[i,l,k] * ...`
Tensornetwork.jl <https://github.com/Jutho/TensorOperations.jl>
`@tensoropt` contraction order
hmm, could triejoin be useful for tensorf contraction? low rank summary? summation?

TensrKit.jl

<https://www.youtube.com/@doggodotjl/videos>
waterlily.jl <https://github.com/weymouth/WaterLily.jl>

<https://github.com/lucaferranti/GeometricTheoremProver.jl> <https://www.youtube.com/watch?v=q_08LE4UOU8&ab_channel=TheJuliaProgrammingLanguage>

<https://www.osti.gov/servlets/purl/1761359> Prove-It
<https://sandialabs.github.io/Prove-It//>
<https://github.com/sandialabs/Prove-It>

<https://www.andrew.cmu.edu/user/avigad/Students/rojas_thesis.pdf> EuclidZ3

<https://arxiv.org/abs/2211.11912> Graph coloring. Approximate graph compression?

graph alignement. graphoptim.jl <https://github.com/gdalle/GraphsOptim.jl>

geometric algebra <https://github.com/MonumoLtd/SimpleGA.jl>

sound syntehsis

<https://github.com/numericalEFT/GreenFunc.jl> <https://github.com/numericalEFT>

Julia on arduino

<https://github.com/narijauskas/PRONTO.jl> pronto trajectory optimization

<https://github.com/danspielman/Laplacians.jl>

<https://github.com/blegat/MacaulayLab.jl>

transport MParT.jl
