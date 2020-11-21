---
author: philzook58
comments: true
date: 2020-09-07 19:22:46+00:00
layout: post
link: https://www.philipzucker.com/yet-another-microkanren-in-julia/
slug: yet-another-microkanren-in-julia
title: Yet Another MicroKanren in Julia
wordpress_id: 2961
categories:
- Formal Methods
tags:
- julialang
- minikanren
---




Minikanren is a relation and logic programming language similar in many respects to prolog. It's designed to be lightweight and embeddable in other host languages.







There is a paper about a minimal implementation call MicroKanren that has spawned many derivatives. It's impressively short. [http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf) . 







I'm intrigued about such things and have my reasons for building a version of this in Julia (perhaps as an inference engine for Catlab stuff? More on that another day). There are already some implementations, but I'm opinionated and I really wanted to be sure I know how the guts work. Best way is to DIY.







There are at least 3 already existing implementations in Julia alone.







  * [https://github.com/latticetower/MuKanren.jl](https://github.com/latticetower/MuKanren.jl)
  * [https://github.com/habemus-papadum/LilKanren.jl](https://github.com/habemus-papadum/LilKanren.jl)
  * [https://github.com/RAbraham/MiniKanren](https://github.com/RAbraham/MiniKanren)






Logic programming consists of basically two pieces, search and unification. The search shows up as a stream. MiniKanren does a kind of clever search by interleaving looking at different branches. This stops it from getting stuck in a bad infinite branch in principle. The interleaving is kind of like a riffled list append.






    
    
```julia

interleave [] ys = ys
interleave (x:xs)  = x : interleave ys xs 
```








But then the actual streams used in Kanren have thunks lying around in them that also need to get forced. These thunk positions are where it chooses to switch over to another branch of the search.







Unification is comparing two syntax trees with variables in them. As you scan down them, you can identify which variables correspond to which subtrees in the other structure. You may find a contradictory assignment, or only a partial assignment. I talked more about unification [here](https://www.philipzucker.com/unification-in-julia/). Kanren uses triangular substitutions to record the variable assignments. These subsitutions are very convenient to make, but when you want to access a variable, you have to walk through the substitution. It's a tradeoff.







Here we start describing my Julia implementation. Buyer beware. I've been finding very bad bugs very recently.







I diverged from microKanren in a couple ways. I wanted to not use a list based structure for unification. I feel like the most Julian thing to do is to use the Expr data structure that is built by Julia quotation `:`.  You can see here that I tried to use a more imperative style where I could figure out how to, which I think is more idiomatic Julia.






    
    
```julia

struct Var 
    x::Symbol
end

function walk(s,u) 
    while isa(u,Var) && haskey(s,u)
            u = get(s,u)
    end
    return u
end

function unify(u,v,s) # basically transcribed from the microkanren paper
    u = walk(s,u)
    v = walk(s,v)
    if isa(u,Var) && isa(v,Var) && u === v # do nothing if same
        return s
    elseif isa(u,Var)
        return assoc(s,u,v)
    elseif isa(v,Var)
        return assoc(s,v,u)
    elseif isa(u, Expr) && isa(v,Expr)
        # Only function call expressions are implemented at the moment 
        @assert u.head === :call && v.head === :call 
        if u.args[1] === v.args[1] && length(u.args) == length(v.args) #heads match
            for (u,v) in zip( u.args[2:end] , v.args[2:end] )  # unify subpieces
                s = unify(u,v,s)
                if s === nothing
                    return nothing
                end
            end
            return s
        else # heads don't match or different arity
            return nothing 
        end
    else # catchall for Symbols, Integers, etc
        if u === v
            return s
        else
            return nothing
        end
    end
end

```








I decided to use the `gensym` facility of Julia to produce new variables. That way I don't have to thread around a variable counter like microkanren does (Julia is already doing this somewhere under the hood). Makes things a touch simpler. I made a couple `fresh` combinators for convenience. Basically you pass them an anonymous function and you get fresh logic variables to use.






    
    
```julia


fresh(f) = f(Var(gensym()))
fresh2(f) = f(Var(gensym()), Var(gensym()))
fresh3(f) = f(Var(gensym()), Var(gensym()), Var(gensym()))
freshn(n, f) = f([Var(gensym()) for i in 1:n ]...) # fishy lookin, but works. Not so obvious the evaluation order here.

```








Kanren is based around composing goals with disjunction and conjunction. A goal is a function that accepts a current substitution dictionary `s` and outputs a stream of possible new substitution dictionaries. If the goal fails, it outputs an empty stream. If the goal succeeds only one way, it outputs a singleton stream. I decided to attempt to use iterators to encode my streams. I'm not sure I succeeded. I also decided to forego separating out `mplus` and `unit` to match the microkanren notation and inlined their definition here. The simplest implementation of conjunction and disjunction look like this.






    
    
```julia

# unification goal
eqwal(u,v) = s -> begin   
                     s = unify(u,v,s)
                     (s == nothing) ? () : (s,)
                  end

# concatenate them
disj(g1,g2) = s -> Iterators.flatten(  (g1(s)  , g2(s)) ) 
# bind = "flatmap". flatten ~ join
conj(g1,g2) = s -> Iterators.flatten( map( g2 ,  g1(s) ))
```








However, the next level throws thunks in the mix. I think I got it to work with a special thunk Iterator type. It mutates the iterator to unthunkify it upon first forcing. I have no idea what the performance characteristics of this are.






    
    
```julia

# Where do these get forced. Not obvious. Do they get forced when flattened? 
mutable struct Thunk #{I}
   it # Union{I,Function}
end

function pull(x) # Runs the trampoline
    while isa(x,Function)
        x = x()
    end
    x
end

function Base.length(x::Thunk) 
    x.it = pull(x.it)
    Base.length(x.it)
end

function Base.iterate(x::Thunk) 
    x.it = pull(x.it)
    Base.iterate(x.it)
end

function Base.iterate(x::Thunk, state) 
    x.it = pull(x.it) # Should we assume forced?
    Base.iterate(x.it, state)
end

# does this have to be a macro? Yes. For evaluation order. We want g 
# evaluating after Zzz is called, not before
macro Zzz(g) 
    return :(s -> Thunk(() -> $(esc(g))(s)))
end
```








Then the fancier conjunction and disjunction are defined like so. I think conjunction does not need to be changed since `iterate` takes care of the trampoline. (Edit: No this is fundamentally busted insofar as it was intended to be a miniKanren style complete search. It is instead doing something closer to depth first. I might as well not even do the swapping. I suspect one cannot use flatten as is if one wants minikanren style search. )






    
    
```julia

disj(g1,g2) = s -> begin
     s1 = g1(s)
     s2 = g2(s)
     if isa(s1,Thunk)  && isa(s1.it, Function) #s1.forced == false  
        Iterators.flatten(  (s2  , s1) )
     else
        Iterators.flatten(  (s1  , s2) )
     end
end

conj(g1,g2) = s -> Iterators.flatten( map( g2 ,  g1(s) )) # eta expansion
```








Nice operator forms of these expressions. It's a bummer that operator precedence is not use definable. ≅ binds more weakly than ∧ and ∨, which is not what you want.






    
    
```julia


∧ = conj # \wedge
∨ = disj # \vee
≅ = eqwal #\cong
```








I skipped using the association list representation of substitutions (Although Assoc Lists are in Base). I've seen recommendations one just use persistent dictionaries and it's just as easy to drop that it. I'm just using a stock persistent dictionary from FunctionalCollections.jl [https://github.com/JuliaCollections/FunctionalCollections.jl](https://github.com/JuliaCollections/FunctionalCollections.jl) .






    
    
```julia


using FunctionalCollections
function call_empty(n::Int64, c) # gets back the iterator
    collect(Iterators.take(c( @Persistent Dict() ), n))
end

function run(n, f)
    q = Var(gensym())
    res = call_empty(n, f(q))
    return map(s -> walk_star(q,s), res)    
end

# walk_star uses the substition to normalize an expression
function walk_star(v,s)
        v = walk(s,v)
        if isa(v,Var)
            return v
        elseif isa(v,Expr)
            @assert v.head == :call
            return Expr(v.head ,vcat( v.args[1], 
                        map(v -> walk_star(v,s), v.args[2:end]))...)
        else
            return v
        end
end
```








Here's we define an append relation and an addition relation. They can be used in reverse and all sorts of funny ways!






    
    
```julia

function nat(n) # helper to build peano numbers
    s = :zero
    for i in 1:n
        s = :(succ($s))
    end
    return s
end

function pluso(x,y,z)
      (( x ≅ :zero ) ∧ (y ≅ z) ) ∨
      fresh2( (n,m) -> (x ≅ :(succ($n))) ∧ (z ≅ :(succ($m))) ∧ @Zzz(pluso( n, y, m)))
end

function appendo(x,y,z)
    (x ≅ :nil) ∧ (y ≅ z) ∨
    fresh3( (hd, xs ,zs) ->  (x ≅ :(cons($hd,$xs)) )  ∧ (z ≅ :(cons($hd, $zs)))  ∧ @Zzz( appendo( xs,y,zs )))
end
```








Here we actually run them and see results to queries.






    
    
```julia

# add 2 and 2. Only one answer
>>> run(5, z -> pluso(nat(2), nat(2), z))
1-element Array{Expr,1}:
 :(succ(succ(succ(succ(zero)))))

>>> run(5, z -> fresh2( (x,y) -> (z ≅ :( tup($x , $y))) ∧ pluso(x, :(succ(zero)), y)))
5-element Array{Expr,1}:
 :(tup(zero, succ(zero)))
 :(tup(succ(zero), succ(succ(zero))))
 :(tup(succ(succ(zero)), succ(succ(succ(zero)))))
 :(tup(succ(succ(succ(zero))), succ(succ(succ(succ(zero))))))
 :(tup(succ(succ(succ(succ(zero)))), succ(succ(succ(succ(succ(zero)))))))

>>> run(3, q ->  appendo(   :(cons(3,nil)), :(cons(4,nil)), q )  )
1-element Array{Expr,1}:
 :(cons(3, cons(4, nil)))

# subtractive append
>>> run(3, q ->  appendo(   q, :(cons(4,nil)), :(cons(3, cons(4, nil))) )  )
1-element Array{Expr,1}:
 :(cons(3, nil))

# generate partitions
>>> run(10, q -> fresh2( (x,y) ->  (q ≅ :(tup($x,$y))) ∧ appendo( x, y, :(cons(3,cons(4,nil)))  )))
3-element Array{Expr,1}:
 :(tup(nil, cons(3, cons(4, nil))))
 :(tup(cons(3, nil), cons(4, nil)))
 :(tup(cons(3, cons(4, nil)), nil))

```














### Thoughts & Links







I really should implement the occurs check







Other things that might be interesting: Using Async somehow for the streams. Store the substitutions with mutation or do union find unification. Constraint logic programming. How hard would it be get get JuMP to tag along for the ride?







It would probably be nice to accept Expr for tuples and arrays in addition to function calls.













[http://minikanren.org/](http://minikanren.org/) You may also want to check out the book The Reasoned Schemer.







[http://io.livecode.ch/](http://io.livecode.ch/) online interactive minikanren examples







[http://tca.github.io/veneer/examples/editor.html](http://tca.github.io/veneer/examples/editor.html) more minikanren examples.







Microkanren implementation tutorial [https://www.youtube.com/watch?v=0FwIwewHC3o](https://www.youtube.com/watch?v=0FwIwewHC3o) . Also checkout the Kanren online meetup recordings [https://www.youtube.com/user/WilliamEByrd/playlists](https://www.youtube.com/user/WilliamEByrd/playlists)







Efficient representations for triangular substitutions - [https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf](https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf)







[https://github.com/ekmett/guanxi](https://github.com/ekmett/guanxi) [https://www.youtube.com/watch?v=D7rlJWc3474&ab_channel=MonadicWarsaw](https://www.youtube.com/watch?v=D7rlJWc3474&ab_channel=MonadicWarsaw)







Could it be fruitful to work natively with Catlab's GATExpr? Synquid makes it seem like extra typing information can help the search sometimes.







LogicT [http://okmij.org/ftp/Computation/LogicT.pdf](http://okmij.org/ftp/Computation/LogicT.pdf)







Seres Spivey [http://www.jucs.org/jucs_6_4/functional_reading_of_logic](http://www.jucs.org/jucs_6_4/functional_reading_of_logic)







Hinze backtracking [https://dl.acm.org/doi/abs/10.1145/357766.351258](https://dl.acm.org/doi/abs/10.1145/357766.351258)



