---
author: philzook58
comments: true
date: 2020-10-16 23:49:48+00:00
layout: post
link: https://www.philipzucker.com/?p=2987
published: false
slug: Julia Packages
title: Julia Packages
wordpress_id: 2987
---




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



