---
author: Philip Zucker
date: 2021-04-10
layout: post
title: "Partial Evaluation of a Pattern Matcher for E-graphs"
categories: julia
tags: julialang julia datastructures
---

Partial Evaluation is cool.

There are different interpretations of what partial evaluation means. I think the term can be applied to anything that you're, well, partially evaluating. This might include really reaching down into and ripping apart the AST of a code block finding things like `1 + 7` and replacing them with `8`.
However, my mental model of partial evaluation is a function that takes 2 arguments, one given at compile time and one at run time. Given the argument at compile time, you can hopefully do all sorts of decisions and control flow choices based off that information.
What I know of this, I've learned from reading Oleg Kiselyov <http://okmij.org/ftp/meta-programming/index.html> and his and other's work in MetaOcaml. Sometimes this technique is called staged metaprogramming, or generative metaprogramming because you don't really peek inside of `Expr`.

- <https://strymonas.github.io/>
- <https://github.com/yallop/ocaml-asp>
- <http://homes.sice.indiana.edu/ccshan/tagless/jfp.pdf>
- More links  <https://www.philipzucker.com/metaocaml-style-partial-evaluation-in-coq/>

I wrote an implementation of a pattern matching in EGraphs that is slow. <https://www.philipzucker.com/egraph-2/> I think partial evaluation in this style is a nice way to speed it up.

A useful pattern for organizing programming tasks is to build tiny programming languages (DSLs) and then write a function that takes a data structure containing a program written in this tiny language and interprets them over inputs. It is very often the case that the actual form of this program one is going to interpret is known at compile time.

A reasonable problem solving strategy is
1. Try some maximally concrete examples and see what hand written code you would write
2. Write an interpreter over some DSL describing the class of programs
3. Stage the interpreter with quasiquotation, rearranging minimally as necessary.
4. Check that your examples produce the same code or good enough compared to your hand written code.

So let's start with 1.

Pattern matching feels a little scary, but when you actually sit down to do it on a concrete pattern, it ends up being a straightforward and boring pile of if-then-else clauses.

Here's some straightforward examples of regular pattern matching

```julia
# pattern f(X)
function matchfx(e)
    if e isa Expr
        if e.head == :f and length(e.args) == 1
            return e.args[1]
        end
    end
end

# pattern f(X,Y)
function matchfxy(e)
    if e isa Expr
        if e.head == :f and length(e.args) == 2
            return [:X => e.args[1], :Y => e.args[2]]
        end
    end
end
```

EMatching throws a wrench into the simplicity that you need to return multiple matches and traverse a search through the multiple enodes per eclass. Nevertheless, for concrete patterns, it isn't really that complicated either.

```julia
#pattern f(X)
function matchfx(G, e::Int64)
    buf = []
    for enode in G[e]
        if enode.head == :f && length(enode.args) == 1
            push!(buf, enode.args[1])
        end
    end
    return buf
end

#pattern f(X,Y) returns 2 variable bindings
function matchfxy(G, e::Int64)
buf = []
for enode in G[e]
    if enode.head == :f && length(enode.args) == 2
        push!(buf, [enode.arg[1], enode.arg[2]])
    end
end
return buf
end

#pattern f(X,X) requires a check 
function match(G, e::Int64)
    buf = []
    for enode in G[e]
        if enode.head == :f && enode.args[1] == enode.args[2]
            push!(buf, enode.args[1])
        end
    end
    return buf
end

#f(g(X)) requires deeper traversal. # of loops is proprtional to number of eclasses expanded
function matchfgx(G, e::Int64)
    buf = []
    for enode in G[e]
        if enode.head == :f and length(f.args) == 1
            for enode in G[f.args[1]]
                if enode.head == :g and length(enode.args) == 1
                    push!(buf, enode.args[0])
                end
            end
        end
    end
end
```

Ok, well how can we generate these?

# An Interpreter

I just so happen to know from the egg <https://egraphs-good.github.io/> paper and the de Moura, Bjorner paper <http://leodemoura.github.io/files/ematching.pdf> that it is smart to compile patterns into a sequence of instructions. This is also similar to what is done in Prolog with the Warren Abstract Machine. Sequences of instructions clarify the control flow compared to directly writing recursive functions to interpret patterns. This explicit control flow is subtly important for the ability to stage programs.

For what I've shown above we need 3 instructions
1. Opening up an eclass. This makes a `for` loop
2. Checking if two variables are the same like in `f(X,X)`
3. Yielding a binding of variables

Here is a simple data type to describe patterns and a helper macro to construct them. It considers capital symbols to be variables.

```julia
@auto_hash_equals struct Pattern
    head::Symbol
    args
end

struct PatVar
    name::Symbol
end

pat(e::Symbol) = isuppercase(String(e)[1]) ? PatVar(e) : Pattern(e, [])
pat(e::Expr) = Pattern(e.args[1], pat.(e.args[2:end]) )
macro pat(e) 
    return pat(e)
end
# example usage: @pat f(g(X), X)
```

And here are the data types `Bind`, `CheckClassEq`, `Yield` of the instructions of my language corresponding to 1-3 above. 

```
@auto_hash_equals struct ENodePat
    head::Symbol
    args::Vector{Symbol}
end

@auto_hash_equals struct Bind 
    eclass::Symbol
    enodepat::ENodePat
end

@auto_hash_equals struct CheckClassEq
    eclass1::Symbol
    eclass2::Symbol
end

@auto_hash_equals struct Yield
    yields::Vector{Symbol}
end
```

Here is a function that takes a `Pattern` and turns it into a sequence of instructions by traversing it depth first. This may not be the most optimal ordering to produce. During the pass I maintain a context from which you can lookup variables from the `Pattern` and find their new names that I bound in the `Insns`.

```julia
function compile_pat(eclass, p::Pattern,ctx)
    a = [gensym() for i in 1:length(p.args) ]
    return vcat(  Bind(eclass, ENodePat(p.head, a  )) , [compile_pat(eclass, p2, ctx) for (eclass , p2) in zip(a, p.args)]...)
end

function compile_pat(eclass, p::PatVar,ctx)
    if haskey(ctx, p.name)
        return CheckClassEq(eclass, ctx[p.name])
    else
        ctx[p.name] = eclass
        return []
    end
end
    
function compile_pat(p)
    ctx = Dict()
    insns = compile_pat(:start, p, ctx)
    
    return vcat(insns, Yield( [values(ctx)...]) ), ctx
end
```

Then I can write an interpreter over these instructions. You case on which instruction type. If it is a `Bind` you make a for loop over all `ENodes` in that eclass, check if the head matches the pattern's head and the length is right, add all the new found enode numbers to the context, and finally recurse into the next instruction. If it is a `CheckClassEq` you check with the context to see if we should stop this branch of the search. If it is a `Yield` we add the current solution to the `buf`. The `buf` thing came up in Alessandro's journey to optimize the ematcher in Metatheory.jl <https://github.com/0x0f0f0f/Metatheory.jl> and it really cleared things up for me compared to my monstrous Channel based implementation.

```julia
function interp_unstaged(G, insns, ctx, buf) 
    if length(insns) == 0
        return 
    end
    insn = insns[1]
    insns = insns[2:end]
    if insn isa Bind
        for enode in G[ctx[insn.eclass]] 
            if enode.head == insn.enodepat.head && length(enode.args) == length(insn.enodepat.args)
                        for (n,v) in enumerate(insn.enodepat.args)
                            ctx[v] = enode.args[n]
                        end
                        interp_unstaged(G,  insns, ctx, buf)
                end
            end
        end
    elseif insn isa Yield
        quote
            push!( buf, [ctx[y] for y in insn.yields])
        end
    elseif insn isa CheckClassEq
        quote
            if ctx[insn.eclass1] == ctx[insn.eclass2]
                interp_unstaged(G, insns, ctx, buf)
            end
        end
    end
end

function interp_unstaged(G, insns, eclass0)
        buf = []
        interp_unstaged(G, insns, Dict{Symbol,Any}([:start => eclass0]) , buf)
        return buf
end

```

Ok, that is kind of complicated but also kind of not. It's may be more complicated to explain and read than it is to write.

Let's stage it!

# Staging the Intepreter

We know the Pattern at compile time, but we want to run matches many, many times quickly at runtime. It makes sense to partially evaluate things. Let's look at a related example first.

### An aside: Partial Evaluating Many For Loops

Consider a brute force search over 3 bits. You could write it like this

```julia
for i in (false,true)
    for j in (false, true)
        for k in (false,true)
            println([i,j,k])
        end
    end
end
```

Now suppose I want code that works for arbitrary number n of bits. A bit more complicated. One way of doing it is via recursion. If you know how to solve the n-1 bits problem, all you need to do is run that problem in a single extra loop.

```julia
function allbits(n, partial)
   if n == 0
        println(partial)
        return 
   end
   for i in (false,true)
       partial[n] = i
       allbits(n-1, partial)
   end
end
function allbits(n) 
    allbits(n, fill(false, n))
end
```

We can by adding quasiquotation annotations to this code actually produce the same code as above. We assume `n` is known at compile time. We also know the size of the partial vector, but the values inside the partial vector are no longer boolean values, instead they represent the code of boolean values available at runtime.
It is unfortunate that I need to gensym the `i` variable. Perhaps there are facilities in Julia to avoid this, perhaps not. Note however that the code is otherwise structurally identical to the above.

```julia
function allbits(n, partial::Vector{Symbol})
   if n == 0
        return :(println([$(partial...)]))  
   end
    i = gensym()
    quote
       for $i in (false,true)
           $(begin
                partial[n] = i
                allbits(n-1, partial)
            end)
       end
   end
end
function allbits(n) 
    allbits(n, fill(:foo, n))
end

prettify(allbits(3))
#=
:(for coati = (false, true)
      for caterpillar = (false, true)
          for seahorse = (false, true)
              println([seahorse, caterpillar, coati])
          end
      end
  end)
=#
# To use
eval(allbits(3))
```

## Staged Interpeter

I just so have happened to have written the unstaged interpreter that very minimal changes are necessary to build the staged version.

Now the `ctx` is a compile time mapping of Insn variables to the expressions that at runtime will hold the appropriate values. `G` and `buf` are the runtime values that hold the egraph and vector of return variable bindings.
The way I did this is going through and thinking about what is avaiable at compile time and keeping it out of quotes, and what is available at runtime and putting it in quotes. It is a remarkably mechanical process to write this stuff once you get the hang of it. I suggest reading Oleg Kiselyov's tutorials and mini-book for more.

```julia
Code = Union{Expr,Symbol}

function interp_staged(G::Code, insns, ctx, buf::Code) # G could be an argument or a global variable.
    if length(insns) == 0
        return 
    end
    insn = insns[1]
    insns = insns[2:end]
    if insn isa Bind
        enode = gensym(:enode)
        quote
            for $enode in $G[$(ctx[insn.eclass])] # we can store an integer of the eclass.
                if $enode.head == $(QuoteNode(insn.enodepat.head)) && length($enode.args) == $(length(insn.enodepat.args))
                    $(
                        begin
                        for (n,v) in enumerate(insn.enodepat.args)
                            ctx[v] = :($enode.args[$n])
                        end
                        interp_staged(G,  insns, ctx, buf)
                        end
                    )
                end
            end
        end
    elseif insn isa Yield
        quote
            push!( $buf, [ $( [ctx[y] for y in insn.yields]...) ])
        end
    elseif insn isa CheckClassEq
        quote
            if $(ctx[insn.eclass1]) == $(ctx[insn.eclass2])
                $(interp_staged(G, insns, ctx, buf))
            end
        end
    end
end

function interp_staged(insns)
    quote
        (G, eclass0) -> begin
            buf = []
            $(interp_staged(:G, insns, Dict{Symbol,Any}([:start => :eclass0]) , :buf))
            return buf
        end
    end
end

using MacroTools # for prettify
p1, ctx1 = compile_pat(@pat f(X))
println(prettify(interp_staged( p1  )))
#=
(G, eclass0)->begin
        buf = []
        for sardine = G[eclass0]
            if sardine.head == :f && length(sardine.args) == 1
                push!(buf, [sardine.args[1]])
            end
        end
        return buf
    end
=#
```


## Bits and Bobbles

- Code in progress here <https://github.com/philzook58/EGraphs.jl/blob/proof/src/matcher.jl>
- It _would_ be kind of fun to do this in MetaOcaml itself. I love the typed staged metaprogramming.
- How much staging do Symbolics and MatchCore do? I don't think they use generative metaprogramming style. 
- Let's get proof output workin'! Next time.
- We can optimize our insns either during the insn generation process or afterward before converting them into the matcher code. We want ot push `CheckClassEq` as soon and as eagerly as possible to get early pruning.
- Egg version <https://github.com/egraphs-good/egg/blob/main/src/machine.rs>

Example tests

```julia
@testset "Basic Compile" begin
    @test compile_pat(@pat f)[1] == [Bind(:start, ENodePat(:f, [])), Yield([])]

    p1, ctx1 = compile_pat(@pat f(X))
    @test p1 == [Bind(:start, ENodePat(:f,  [ctx1[:X]]  )), Yield([ctx1[:X]])]
    
    p1, ctx = compile_pat(@pat f(X, Y))
    @test p1 == [Bind(:start, ENodePat(:f,  [ctx[:X], ctx[:Y] ]  )), 
                 Yield([ctx[:X], ctx[:Y]])]
    @test ctx[:X] != ctx[:Y]
    @test length(ctx) == 2

    p1, ctx = compile_pat(@pat f(X, X))
    x2 = p1[1].enodepat.args[2]
    @test length(ctx) == 1
    @test p1 == [Bind(:start, ENodePat(:f,  [ctx[:X], x2 ]  )), 
                 CheckClassEq( x2 , ctx[:X] ),
                 Yield([ctx[:X]])]

    p1, ctx = compile_pat(@pat f(g(X)))
    g = p1[1].enodepat.args[1]
    @test length(ctx) == 1
    @test p1 == [Bind(:start, ENodePat(:f,  [g ]  )),
                Bind(g, ENodePat(:g,  [ctx[:X] ]  )) ,
                Yield([ctx[:X]])]

end

using MacroTools
@testset "Basic Match" begin
    G = EGraph()
    a = addexpr!(G, :a) 
    b = addexpr!(G, :b) 
    fa = addexpr!(G, :( f(a)  ))
    fb = addexpr!(G, :( f(b)  ))

    p1, ctx1 = compile_pat(@pat f(X))

    println(prettify(interp_staged( p1  )))
    match = eval(interp_staged( p1  ))
    @test match(G, fa) == [ [ a ] ]
    @test match(G, fb) == [ [ b ] ]
    union!(G, fa, fb)
    #println(G)
    @test match(G, fa) == [ [ b ], [ a ]  ]
    union!(G, a, b)
    #println(G)
    #println(congruences(G))
    propagate_congruence(G)
    #println(G)
    #println(congruences(G))
    rebuild!(G) # There is something kind of sick here.
    #println(G)
    a = addexpr!(G, :a)
    @test match(G, fa) == [ [ a ] ]


    p1, ctx = compile_pat(@pat f(g(X)))
    match = eval(interp_staged( p1  ))
    G = EGraph()
    a = addexpr!(G, :a) 
    b = addexpr!(G, :b) 
    fga = addexpr!(G, :( f(g(a))  ))
    fb = addexpr!(G, :( f(b)  ))
    @test match(G,fb) == []
    @test match(G,fga) == [[a]]
    union!(G, fb, fga)
    @test match(G,fb) == [[a]]
    @test match(G,fga) == [[a]]



    p1, ctx = compile_pat(@pat f(X, X))
    #println(prettify(interp_staged( p1  )))
    match = eval(interp_staged( p1  ))
    G = EGraph()
    a = addexpr!(G, :a) 
    b = addexpr!(G, :b) 
    fga = addexpr!(G, :( f(g(a))  ))
    fb = addexpr!(G, :( f(b)  ))
    fab = addexpr!(G, :( f(a,b)  ))
    @test match(G,fab) == []
    faa = addexpr!(G, :( f(a,a)  ))
    @test match(G,faa) == [[a]]
    @test match(G,fab) == []
    union!(G,a,b)
    rebuild!(G)
    #propagate_congruence(G)
    @test match(G,faa) == [[b]]
    @test match(G,fab) == [[b]]



    #println(prettify(interp_staged( p1  )))
end
```
