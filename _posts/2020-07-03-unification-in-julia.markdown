---
author: philzook58
comments: true
date: 2020-07-03 16:50:32+00:00
layout: post
link: https://www.philipzucker.com/unification-in-julia/
slug: unification-in-julia
title: Unification in Julia
wordpress_id: 2848
categories:
- Formal Methods
tags:
- Julia
- julialang
---




[Unification](https://en.wikipedia.org/wiki/Unification_(computer_science)) is a workhorse of symbolic computations. Comparing two terms (two syntax trees with named variables spots) we can figure out the most general substitution for the variables to make them syntactically match.







It is a sister to pattern matching, but it has an intrinsic bidirectional flavor that makes it feel more powerful and declarative.







Unification can be implemented efficiently (not that I have done so yet) with some interesting variants of the [disjoint set / union-find](https://en.wikipedia.org/wiki/Disjoint-set_data_structure#:~:text=In%20computer%20science%2C%20a%20disjoint,(non%2Doverlapping)%20subsets.) data type.







  * The magic of Prolog is basically built in unification + backtracking search.
  * The magic of polymorphic type inference in Haskell and OCaml comes from unification of type variables.
  * Part of magic of SMT solvers using the theory of uninterpreted functions is unification.
  * Automatic and Interactive Theorem provers have unification built in somewhere.






To describe terms I made a simple data types for variables modelled of those in [SymbolicUtils](https://github.com/JuliaSymbolics/SymbolicUtils.jl) (I probably should just _use_ the definitions in SymbolicUtils but i was trying to keep it simple).






    
    
```

#variables
struct Sym
    name::Symbol
end

struct Term
    f::Symbol
    arguments::Array{Any} # Array{Union{Term,Sym}} faster/better?
end
```








The [implementation by Norvig](https://github.com/aimacode/aima-python/blob/9ea91c1d3a644fdb007e8dd0870202dcd9d078b6/logic4e.py#L1307) and Russell for the their [AI book](http://aima.cs.berkeley.edu/) is an often copied simple implementation of unification. It is small and kind of straightforward.  You travel down the syntax trees and when you hit variables you try to put them into your substitution dictionary. Although, like anything that touches substitution, it can be easy to get wrong. See his note below.







I used the multiple dispatch as [a kind of pattern matching](https://discourse.julialang.org/t/are-there-idioms-in-julia-for-fast-algebraic-data-types-adt/37244/13) on algebraic data types whether the variables are terms or variables. It's kind of nice, but unclear to me whether obscenely slow or not. This is not a high performance implementation of unification in any case.






    
    
```

occur_check(x::Sym,y::Term,s) = any(occur_check(x, a, s) for a in y.arguments)

function occur_check(x::Sym,y::Sym,s)
    if x == y
        return s
    elseif haskey(s,y)
        return occur_check(x, s[y], s)
    else
        return nothing
    end  
end


function unify(x::Sym, y::Union{Sym,Term}, s) 
   if x == y
        return s
   elseif haskey(s,x)
        return unify(s[x], y, s)
   elseif haskey(s,y) # This is the norvig twist
        return unify(x, s[y], s)
   elseif occur_check(x,y,s)
        return nothing
   else
        s[x] = y
        return s
   end
end

unify(x::Term, y::Sym, s) = unify(y,x,s)

function unify(x :: Term, y :: Term, s)
    if x.f == y.f && length(x.arguments) == length(y.arguments)
        for (x1, y1) in zip(x.arguments, y.arguments)
            if unify(x1,y1,s) == nothing
                return nothing
            end
        end
        return s
    else
        return nothing
    end
end

unify(x,y) = unify(x,y,Dict())
```








I also made a small macro function for converting simple julia expressions to my representation. It uses the prolog convention that capital letter starting names are variables.






    
    
```

function string2term(x)
    if x isa Symbol
        name = String(x)
        if isuppercase(name[1])
           return Sym( x)
        else
           return Term( x, []  )
        end
    elseif x isa Expr
        @assert(x.head == :call)
        arguments = [string2term(y) for y in x.args[2:end] ]
        return Term( x.args[1], arguments )
    end
end
macro string2term(x)
    return :( $(string2term(x)) )
end

print(unify( @string2term(p(X,g(a), f(a, f(a)))) , @string2term(p(f(a), g(Y), f(Y, Z)))))
# Dict{Any,Any}(Sym(:X) => Term(:f, Any[Term(:a, Any[])]),Sym(:Y) => Term(:a, Any[]),Sym(:Z) => Term(:f, Any[Term(:a, Any[])]))
```








## Links







Unification: Multidisciplinary Survey by Knight [https://kevincrawfordknight.github.io/papers/unification-knight.pdf](https://kevincrawfordknight.github.io/papers/unification-knight.pdf)







[https://github.com/roberthoenig/FirstOrderLogic.jl/tree/master/src](https://github.com/roberthoenig/FirstOrderLogic.jl/tree/master/src) A julia project for first order logic that also has a unification implementation, and other stuff







An interesting category theoretic perspective on unification [http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.48.3615](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.48.3615) what is unification by Goguen







There is also a slightly hidden implementation in sympy (it does not appear in the docs?)  [http://matthewrocklin.com/blog/work/2012/11/01/Unification](http://matthewrocklin.com/blog/work/2012/11/01/Unification)  [https://github.com/sympy/sympy/tree/master/sympy/unify](https://github.com/sympy/sympy/tree/master/sympy/unify)







PyRes [https://github.com/eprover/PyRes/blob/master/unification.py](https://github.com/eprover/PyRes/blob/master/unification.py)







Norvig unify  
[https://github.com/aimacode/aima-python/blob/9ea91c1d3a644fdb007e8dd0870202dcd9d078b6/logic4e.py#L1307](https://github.com/aimacode/aima-python/blob/9ea91c1d3a644fdb007e8dd0870202dcd9d078b6/logic4e.py#L1307)







norvig - widespread error  
[http://norvig.com/unify-bug.pdf](http://norvig.com/unify-bug.pdf)







Efficient unification note  
[ftp://ftp.cs.indiana.edu/pub/techreports/TR242.pdf](ftp://ftp.cs.indiana.edu/pub/techreports/TR242.pdf)







blog post  
[https://eli.thegreenplace.net/2018/unification/](https://eli.thegreenplace.net/2018/unification/)







Efficient representations for triangular substitituions  
[https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf](https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf)







conor mcbride - first order substitition structurly recursive dependent types  
[http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=880725E316FA5E3540EFAD83C0C2FD88?doi=10.1.1.25.1516&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=880725E316FA5E3540EFAD83C0C2FD88?doi=10.1.1.25.1516&rep=rep1&type=pdf)







z3 unifier - an example of an actually performant unifier  
[https://github.com/Z3Prover/z3/blob/520ce9a5ee6079651580b6d83bc2db0f342b8a20/src/ast/substitution/unifier.cpp](https://github.com/Z3Prover/z3/blob/520ce9a5ee6079651580b6d83bc2db0f342b8a20/src/ast/substitution/unifier.cpp)







Warren Abstract Machine Tutorial Reconstruction [http://wambook.sourceforge.net/wambook.pdf](http://wambook.sourceforge.net/wambook.pdf)







Handbook of Automated Reasoning - has a chapter on unification







Higher Order Unification - LambdaProlog, Miller unification







Syntax trees with variables in them are a way in which to represent sets of terms (possibly infinite sets!). In that sense it asks can we form the union or intersection of these sets.  The intersection is the most general unifier. The union is not expressible via a single term with variables in general. We can only over approximate it, like how the union of convex sets is not necessarily convex, however it's hull is. This is a join on a term lattice. This is the process of anti-unification.







What about the complement of these sets? Not really. Not with the representation we've chosen, we can't have an interesting negation. What about the difference of two sets?







I had an idea a while back about programming with relations, where I laid out some interesting combinators. I represented only finite relations, as those can be easily enumerated. 



