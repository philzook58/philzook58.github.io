---
author: Philip Zucker
date: 2021-07-31
layout: post
title: "JuliaCon 2021 Talk on Metatheory.jl and Snippets From the Cutting Room Floor"
tags:
- julia
- egraphs
- julialang
---

<iframe width="560" height="315" src="https://www.youtube.com/embed/tdXfsTliRJk" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>

Alessandro very graciously invited me to join him giving a talk on [Metatheory.jl](https://github.com/0x0f0f0f/Metatheory.jl), his package for rewriting and egraphs. Thanks Alessandro!

I keep saying to myself I should try to give more talks, but hoo boy is it stressful. I felt like the whole month of June I was freaking out. And yet, it came off just fine I think. I was worried for nothing. Whenever these things come up, I always think that this time I need to tie up all the loose ends that I don't know the answer to. But these loose ends exist because they are hard or they need stewing time.

It's lunacy and hubris to think I can fix it all, but I do it every time. We had way way too much material anyway!

Here's a snippet of todos from my notes.

> Metatheory talk:
> - PEGs
> - Rewriting functional programs - https://www.haskellforall.com/2013/12/equational-reasoning.html
> - Gries equational logic?
> - datalog?
> - Summation - WIP though.
> - Automating catlab translation - This is only half built
> - The ideas behind the catlab trasnlation
> - Rearranging linear algerba expressions
> - translate Egg Projects
> - rewriting aexpr + bexpr

Ridiculous. Here's some of the bits and pieces I did make though.


### Stream Fusion

I started writing down how to optimize iterator expressions. This is known as stream fusion This is an interesting application, especially if you extract for asymptotic complexity rather than ast size. This is a very cool application though

```julia
using Pkg
Pkg.activate("metatheory")
Pkg.add(url="https://github.com/0x0f0f0f/Metatheory.jl.git")
using Metatheory
using Metatheory.EGraphs
@metatheory_init ()

array_theory = @theory begin
    reverse(reverse(x)) => x
    map(f,reverse(x)) => reverse(map(f, x))
    map(f,fill(x,N)) => fill(apply(f,x), N) # hmm
    filter(f,reverse(x)) => reverse(filter(f,x))
    reverse(fill(x,N)) => fill(x,N) 
    #map(f,x)[n:m] = map(f,x[n:m]) # but does NOT commute with filter
    filter(f, fill(x,N)) => f(x) ? fill(x,N) : fill(x,0)
    filter(f, filter(g, x)) => filter(f && g, x) # using functional &&
    cat(fill(x,N),fill(x,M)) => fill(x,N + M)
    cat(map(f,x), map(f,y)) => map(f, cat(x,y))
    map(f, cat(x,y)) => cat(map(f,x), map(f,y)) 
    map(f,map(g,x)) => map(f ⋅ g, x)
    reverse( cat(x,y) ) => cat(reverse(y), reverse(x))
    sum(fill(x,N)) => x * N
    map(f,x)[n] => apply(f,x[n]) #?
    apply(f ⋅ g, x) => apply(f, apply(g, x))
    fill(x,N)[n] => x
    cumsum(fill(x,N)) => collect(x:x:(N*x))
    length(fill(x,N)) => N
end

#G = EGraph(:(a * b * c * d * e));
#G = EGraph(:( reverse(reverse(fill(10,20))) )) 
#G = EGraph(:( map(x -> 7 * x, reverse(cat(fill(13,40),fill(10,20))) )))
G = EGraph(:( map(x -> 7 * x, fill(3,4) )))
G = EGraph(:( map(x -> 7 * x, fill(3,4) )[1]))



report = saturate!(G,array_theory);
ex = extract!(G, astsize)

```

Links on stream fusion:
- <https://hackage.haskell.org/package/base-4.15.0.0/docs/src/GHC-List.html#drop>
- <https://www.cs.ox.ac.uk/ralf.hinze/publications/IFL10.pdf> theory and practice of fusion
- <http://citeseer.ist.psu.edu/viewdoc/summary?doi=10.1.1.104.7401> from list and stream to nothing 
- <https://teh.id.au/#/posts/2017/06/30/notes-on-fusion/index.html>
- <https://twitter.com/SandMouth/status/1399510138487283713?s=20>
List.v
- HLint <https://t.co/A2FYzWU1za?amp=1>
- <https://t.co/DvyoxctdHT?amp=1> 

### E-PEGs

E-PEGs <https://www.cs.cornell.edu/~ross/publications/eqsat/> are a compiler IR format that plays with the egraph. It's interestingly related to the above. The basic idea I think is to enhance the CFG into being effectively in a purely functional form. Gated Phi nodes really are basically functional if the else constructs, since they reify the path condition. The other kinds of funky nodes they use for loops can be though of as functional stream combinators. In some sense the values things take on inside loops is a stream of values.

I started translating the table from Tate's thesis chapters 7/8 into metatheory.jl and julia but I didn't finish. I now appreciate the cleverness of the @capture macro from MacroTools though.

```julia
using MacroTools

function translate_prog(p)
    @capture(p, function f_(args__) body_ end)
    translate_statement(body, Dict(zip(args,args)), 0)[:retvar]
end


function translate_statement(s, env, loop_level) # translate statement
    #println(s)
    if @capture(s, begin s1_; s2__ end) && length(s2) > 0
        return translate_statement( Expr(:block, s2...), translate_statement(s1, env, loop_level), loop_level)
    elseif @capture(s, x_ = e_)
        env2 = copy(env)
        env2[x] = translate_expr(e, env)
        return env2
    elseif @capture(s, if e_ s1_ else s2_ end)
        return phi( translate_expr(e, env), translate_statement(s1, env, loop_level) , translate_statement(s2, env, loop_level) )
    elseif @capture(s, while c_ b_ end)
        
    end
    println("no match", e)
end

function translate_expr(e, env)
    if @capture( e , op_(args__))
        args = [translate_expr(arg, env) for arg in args]
        :($op( $(args...) ))
    elseif e isa Number
        e
    else
        env[e]
    end
end

function combine(m1,m2,conflict)
    res = Dict()
    for (k,v) in m1
        res[k] = v
    end
    for (k,v) in m2
        if haskey(res,k)
            res[k] = conflict( m1[k], m2[k] )
        else
           res[k] = v     
        end
    end
    return res
end

function phi(n, env1, env2,)
    combine(env1,env2, (t,f) -> :(ϕ($n, $t, $f )  ))
end
```

### Automating The Catlab Translation

<https://www.philipzucker.com/metatheory-progress/>
This is only half built. It sounded like Alessandro was on the case a while back so I got discouraged. I really do not remember what state this is in, but here it is to those curious and extremely bold.

```julia
using Pkg
Pkg.activate("metacat")
Pkg.add(url="git@github.com:AlgebraicJulia/Catlab.jl.git")
Pkg.add(url="https://github.com/0x0f0f0f/Metatheory.jl.git")
using Metatheory
using Metatheory.EGraphs

using Catlab
using Catlab.Theories

function convert_types(types)
    ret = []
    for typ in types
        for accessor in typ.params
            lhs = Expr(:call, accessor, Expr(:call , :type, Expr(:call,  typ.name, hom.params... )))
            push!(ret, :( $lhs => $accessor ))
        end
    end
    return ret
end


symbols(e::Expr) = length(e.args) > 1 ? reduce(union, symbols.(e.args[2:end]) ) : Set([])
symbols(s::Symbol) = Set([s])

find_field(typ::Expr, a) = findfirst(x -> x == a, typ.args[2:end])
find_field(typ::Symbol, a) = nothing
function find_context(context, a)
    for (f,typ) in context
        i = find_field(typ,a)
        if i != nothing
            return (f,typ,i)
        end
    end
end

find_field(:(Hom(A,B)), :C)
find_context(Dict(:f => :(Hom(A,B))), :A)

function build_type_finder(ctx, u) # builds functional form of extractor from context.
    ident, typ, pos = find_context(ctx, u) 
    u => :(proj($pos, type($ident )))
end

type_finder_dict(ctx, unknowns) = Dict([ build_type_finder(ctx, u) for u in unknowns])

replace(e::Symbol, ud) = begin
    #println(e)
    haskey(ud,e) ?  ( ud[e])  : e
end
replace(e::Expr, unknown_replace_dict) = begin
    Expr(e.head, e.args[1], [ replace(a, unknown_replace_dict) for a in e.args[2:end] ]... ) end

function type_terms(terms)
    ret = []
    for term in terms
        lhs = Expr(:call , :type, Expr(:call,  term.name, term.params... ))
        
        
        known = Set(term.params)
        unknowns = setdiff(symbols(term.typ) , known)

        
        unknown_replace_dict = type_finder_dict(term.context, unknowns)
        builtterm = replace(term.typ, unknown_replace_dict)
        #println(unknown_replace_dict)
        #println(builtterm)
        #=
        typ_map = Dict()
        
        while !isempty(unknowns)
            u = pop!(unknowns)
            push!(known, u)
            type_u = term.context[u]
            typ_map[u] = type_u
            unknowns = unknowns ∪ (setdiff(symbols(type_u) , known ))
        end
        println(typ_map)
        =#
        push!(ret, :( $lhs => $(builtterm)))
    end
    return ret
end
type_terms( theory(Category).terms )

# If we want to go with the accessor encoding, We need to lookup parameters on the right hand side


# I should possible use metatheory to do replacement


# should I make these function singular and just map them?
function convert_axioms(axioms)
    ret = []
    for axiom in axioms
        #lhs = Expr(:call , :type, Expr(:call,  term.name, term.params... ))
        #println(axiom)

        leftsyms = symbols(axiom.left)
        rightsyms = symbols(axiom.right)
        # left to right
        unknowns = setdiff(rightsyms, leftsyms)
        #println(unknowns)
        #println([ find_context(axiom.context, u) for u in unknowns])
        d = type_finder_dict(axiom.context, unknowns)
        newright = replace(axiom.right, d)
        push!(ret, :( $(axiom.left) => $(newright)))
        
        
        unknowns = setdiff(leftsyms, rightsyms)
        d = type_finder_dict(axiom.context, unknowns)
        newleft = replace(axiom.left, d)
        push!(ret, :( $(axiom.right) => $(newleft)))
    end
    return ret
end
#convert_axioms( theory(Category).axioms)
convert_axioms( theory(MonoidalCategory).axioms)
#theory(MonoidalCategory).axioms


function find_term(termcons, n)
    for termcon in termcons
        if termcon.name == n
            return termcon
        end
    end
end

function typing_equuations(theory,s::Symbol)
    return []
end
function typing_equations(theory, e::Expr)
    @assert e.head == :call
    name = e.args[1]
    term_con = find_term(theory.terms, name)
    println(e)
    #freshparams = [p => gensym(p)  for p in term_con.params ]    
    #rec_equations = [ kv[2] => a  for (kv,a)  in   zip(freshparams, e.args[2:end]) ]
    rec_equations = [k => v for (k,v) in zip(term_con.params, e.args[2:end])]
    r2 = [  replace( k, Dict(rec_equations)) => replace( v, Dict(rec_equations))  for (k,v) in term_con.context]
    r3 = [ typing_equations(theory, a) for a in e.args[2:end] ]
    return vcat(r2,r3)
    
end
typing_equations( theory(MonoidalCategory), :(otimes(f,id(a))) )
```