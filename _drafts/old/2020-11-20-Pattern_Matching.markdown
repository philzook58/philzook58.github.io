---
author: philzook58
comments: true
date: 2020-11-20 13:37:03+00:00
layout: post
link: https://www.philipzucker.com/?p=2991
published: false
slug: Pattern Matching
title: Pattern Matching
wordpress_id: 2991
---

Noam Zielberger. Patterns as primitive construct.

https://matchpy.readthedocs.io/en/latest/index.html matchpy

Egison https://arxiv.org/pdf/1808.10603.pdf https://www.egison.org/

The first class representation of pattern matching is the eliminator or recursor. This function is also the translator between a data type and it's church/bohm-berarducci encoding. With some slight adjustment, it is also the translator between trhe initial encoding of a data type and it's final encoding.

The eliminator takes a function for every possible case of an algebraic datatype. One function for `true`, one for `false`. This function accepts all the arguments of the constructor. It emulates the binding that occurs in pattern matching by using the binding features of lambdas.


```haskell
type MaybeP a s = s -> (a -> s) -> s
type BoolP = forall s. s -> s -> s

-- matchMaybe is in some respect a direct reflection of depth 1 pattern matching as a function
matchmaybe :: Maybe a -> MaybeP a s
matchmaybe :: Maybe a -> s -> (a -> s) -> s
matchMaybe (Just x) d f = f x
matchMaybe Nothing d f = d  
```
Eliminators are nice in that they are a total pattern match. By construction they know what to do for every possible case.

An alternative is the partial pattern match. We could also just let the match actually fail and catch the exception in the exception system. Pretty hacky though


```haskell
true :: Bool -> s -> Maybe s
true True s = Just s
true False _ = Nothing

left :: (a -> s) -> Either a b -> Maybe s
left (Left x) f = Just (f x)
right :: Either a b -> (

left (true 7) (Left True) -- returns 7. No it doesn't

-- CPS that shit, son
-- No make it recursive in left?
    (a -> s)
left :: ((a -> s) -> Maybe s) -> Either a b -> Maybe s
left pat (Left x) = pat 
left :: (a -> Maybe s) -> Either a b -> Maybe s
left pat (Left x) = (pat x)
left _ (Right _) = Nothing

left (true 
```


In an untyped setting

```julia
dict -> data -> Maybe dict
 
lit(x) = (dict,y) -> y == x ? dict : nothing </code>
```

It is mostly clear that a pattern match can be compiled into an ugly chain of if then else constructs or switch-case statements, checking for tags, or at the assembly level into a jump table.

Open pattern matching. Pattern macthing can be compiled a little bit more if we don't pass the arguments in a dictionary, but instead number them. Unless the julia compiler is smart enough to fuse this, which I kind of doubt

Compiling natural features or extensions of pattern matching down to eliminators can be a challenge. This is like a whole _thing_ in the world of dependent pattern matching. See Equations package https://github.com/mattam82/Coq-Equations , Conor Mcbride's thesis [https://era.ed.ac.uk/handle/1842/374](https://era.ed.ac.uk/handle/1842/374) ? and references therein.


Compiling pattern matching. Simon Peyton Jones book https://www.microsoft.com/en-us/research/publication/the-implementation-of-functional-programming-languages/.  https://link.springer.com/chapter/10.1007%2F3-540-15975-4_48 Augustsson

The lisp/scheme tradition does not close off it's world of data types. The eliminator does not make sense then. Instead, we can

```julia 
# I don't really see a reason why we would use the next continuation?
# an rgument could be made for throwing an exception if failed
lit(x) = (term,dict) -> term == x ? dict : nothing
pat(x) = (term,dict) -> begin
    if haskey(dict,x)
        dict[x] == term ? dict : nothing
    else
        dict[x] = term
        dict
    end
end
# x doesn't have to be a literal here. It could be a variable.
func(x, args...) = (term,dict) -> 
    begin
        if term.head != :call || x != term.args[1] || length(term.args) != length(args) + 1
            nothing
        else          
        for (pat,term) in zip(args, term.args[2:end]) # this is some kind of bind operation / apply <*>
                    dict = pat(term,dict)
                    if dict == nothing
                        return nothing
                    end
            end
            return dict
        end
    end

```

[https://github.com/axch/rules](https://github.com/axch/rules)


[https://github.com/JuliaSymbolics/SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl) https://groups.csail.mit.edu/mac/users/gjs/6.945/  PAIP


Rule rewriting, term rewriting, pattern matching are all sides of the same coin. One step to the left is unification. Nearby topics: Knuth Bendix completion, string matching like regex. A recursive pattern match learns something by how far it gets like Knuth Pratt.


Pattern matching is not symmettrical like unification. The pattern has variab;es but the pattee is ground. Matching patterns against patterns is intuitively what unification is. Higher order unification (unification of patterns with binding forms) is scary. Is higher order pattern matching scary? Dependent pattern matching involes higher order unification at the type level

Nipkow: Term rewriting and all that


Termination checking. AProve [https://aprove.informatik.rwth-aachen.de/](https://aprove.informatik.rwth-aachen.de/)



Term indexing techniques. The Handbook of Automated Reasoning. It is quite the tome.


The functional representation of match is very powerful, as it often is.  
But we lose something when we seal our data behind the functional interface, as we often do.  
Like matrix multiply, functional form is flexible.  
For example we could make a trie to do many patterns at once

[https://hal.inria.fr/hal-01183817/file/eqLogicRw.pdf](https://hal.inria.fr/hal-01183817/file/eqLogicRw.pdf) equational logic



