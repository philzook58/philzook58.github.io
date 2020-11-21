---
author: philzook58
comments: true
date: 2020-09-26 15:28:37+00:00
layout: post
link: https://www.philipzucker.com/notes-on-synthesis-and-equation-proving-for-catlab-jl/
slug: notes-on-synthesis-and-equation-proving-for-catlab-jl
title: Notes on Synthesis and Equation Proving for Catlab.jl
wordpress_id: 2974
categories:
- Formal Methods
- Julia
tags:
- categorytheory
- julialang
---




[Catlab](https://github.com/AlgebraicJulia/Catlab.jl) is a library and growing ecosystem (I guess the ecosystem is called [AlgebraicJulia](https://algebraicjulia.github.io/) now) for computational or applied category theory, whatever that may end up meaning.







I have been interested to see if I could find low hanging fruit by applying off the shelf automated theorem proving tech to Catlab.jl. 







There area couple problems that seem like some headway might be made in this way:







  * Inferring the type of expressions. Catlab category syntax is pretty heavily annotated by objects so this is relatively easy. (`id` is explicitly tagged by the object at which it is based for example)
  * Synthesizing morphisms of a given type.
  * Proving equations






In particular two promising candidates for these problems are to use eprover/vampire style automated theorem provers or prolog/kanren logic programming.







## Generalized Algebraic Theories (GATs)







Catlab is built around something known as a Generalized Algebraic Theory. [https://algebraicjulia.github.io/Catlab.jl/dev/#What-is-a-GAT?](https://algebraicjulia.github.io/Catlab.jl/dev/#What-is-a-GAT?) In order to use more conventional tooling, we need to understand GATs in a way that is acceptable to these tools. Basically, can we strip the GAT down to first order logic?







I found GATs rather off putting at first glance. Who ordered that? The nlab article is 1/4 enlightening and 3/4 obscuring. [https://ncatlab.org/nlab/show/generalized+algebraic+theory](https://ncatlab.org/nlab/show/generalized+algebraic+theory) But, in the end of the day, I think it it's not such a crazy thing.







Because of time invested and natural disposition, I understand things much better when they are put in programming terms. As seems to be not uncommon in Julia, one defines a theory in Catlab using some specialized macro mumbo jumbo.






    
    
```

@theory Category{Ob,Hom} begin
  @op begin
    (→) := Hom
    (⋅) := compose
  end

  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE

  id(A::Ob)::(A → A)
  compose(f::(A → B), g::(B → C))::(A → C) ⊣ (A::Ob, B::Ob, C::Ob)

  (f ⋅ g) ⋅ h == f ⋅ (g ⋅ h) ⊣ (A::Ob, B::Ob, C::Ob, D::Ob,
                                f::(A → B), g::(B → C), h::(C → D))
  f ⋅ id(B) == f ⊣ (A::Ob, B::Ob, f::(A → B))
  id(A) ⋅ f == f ⊣ (A::Ob, B::Ob, f::(A → B))
end
```








Ok, but this macro boils down to a data structure describing the syntax, typing relations, and axioms of the theory. This data structure is not necessarily meant to be used by end users, and may change in it's specifics, but I find it clarifying to see it.







Just like my python survival toolkit involves calling `dir` on everything, my Julia survival toolkit involves hearty application of `dump` and `@macroexpand` on anything I can find.







We can see three slots for types terms and axioms. The types describe the signature of the types, how many parameters they have and of what type. The `terms` describe the appropriate functions and constants of the theory. It's all kind of straightforward I think. Try to come up with a data structure for this and you'll probably come up with something similar







I've cut some stuff out of the dump because it's so huge. I've placed the full dump at the end of the blog post.






    
    
```

>>> dump(theory(Category))

Catlab.GAT.Theory
  types: Array{Catlab.GAT.TypeConstructor}((2,))
    1: Catlab.GAT.TypeConstructor
      name: Symbol Ob
      params: Array{Symbol}((0,))
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((0,))
        vals: Array{Union{Expr, Symbol}}((0,))
        ndel: Int64 0
        dirty: Bool false
      doc: String " Object in a category "
    2: ... More stuff
  terms: Array{Catlab.GAT.TermConstructor}((2,))
    1: Catlab.GAT.TermConstructor
      name: Symbol id
      params: Array{Symbol}((1,))
        1: Symbol A
      typ: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol Hom
          2: Symbol A
          3: Symbol A
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((1,))
          1: Symbol A
        vals: Array{Union{Expr, Symbol}}((1,))
          1: Symbol Ob
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
    2: ... More stuff
  axioms: Array{Catlab.GAT.AxiomConstructor}((3,))
    1: Catlab.GAT.AxiomConstructor
      name: Symbol ==
      left: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol compose
              2: Symbol f
              3: Symbol g
          3: Symbol h
      right: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Symbol f
          3: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol compose
              2: Symbol g
              3: Symbol h
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[5, 0, 0, 0, 1, 0, 4, 0, 2, 7, 0, 6, 0, 0, 0, 3]
        keys: Array{Symbol}((7,))
          1: Symbol A
          2: Symbol B
          3: Symbol C
          4: Symbol D
          5: Symbol f
          6: Symbol g
          7: Symbol h
        vals: Array{Union{Expr, Symbol}}((7,))
          1: Symbol Ob
          2: Symbol Ob
          3: Symbol Ob
          4: Symbol Ob
          5: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol A
              3: Symbol B
          6: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol B
              3: Symbol C
          7: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol C
              3: Symbol D
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
    2: ... More stuff
  aliases: ... Stuff
```








This infrastructure is not necessarily for category theory alone despite being in a package called Catlab. You can describe other algebraic theories, like groups, but you won't need the full flexibility in typing relations that the "Generalized" of the GAT gets you. The big hangup of category theory that needs this extra power is that categorical composition is a partial function. It is only defined for morphisms whose types line up correctly, whereas any two group elements can be multiplied.






    
    
```

@theory Group(G) begin

  G::TYPE

  id()::G
  mul(f::G, g::G)::G
  inv(x::G)::G

  mul(mul(f, g), h) == mul(f,  mul(g , h)) ⊣ ( f::G, g::G, h::G)
   # and so on
end
```








Back to the first order logic translation. If you think about it, the turnstile ⊣ separating the context appearing in the Catlab theory definition is basically an implication. The definition `id(A)::Hom(A,A) ⊣ (A::Ob)` can be read like so: for all A, given A has type `Ob` it implies that `id(A)` has type `Hom(A,A)`. We can write this in first order logic using a predicate for the typing relation. $ \forall A,  type(A,Ob) \implies type(id(A), Hom(A,A))$. 







The story I tell about this is that the way this deals with the partiality of compose is that when everything is well typed, compose behaves as it axiomatically should, but when something is not well typed, compose can return total garbage. This is one way to make a partial function total. Just define it to return random trash for the undefined domain values or rather be unwilling to commit to what it does in that case.







Even thought they are the same thing, I have great difficulty getting over the purely syntactical barrier of `_::_` vs `type(_,_)`. Infix punctuation never _feels_ like a predicate to me. Maybe I'm crazy.







Turnstiles in general are usually interchangeable with or reflections of implication in some sense. So are the big horizontal lines of inference rules for that matter. I find this all very confusing. 







Everything I've said above is a bold claim that could be actually proven by demonstrating a rigorous correspondence, but I don't have enough interest to overcome the tremendous skill gap I'm lacking needed to do so. It could very easily be that I'm missing subtleties.







## Automated Theorem Provers







While the term automated theorem prover could describe any theorem prover than is automated, it happens to connote a particular class of first order logic automated provers of which the E prover and Vampire are canonical examples. 







In a previous post, I tried axiomatizing category theory to these provers in a different way [https://www.philipzucker.com/category-theory-in-the-e-automated-theorem-prover/](https://www.philipzucker.com/category-theory-in-the-e-automated-theorem-prover/) , with a focus on the universal properties of categorical constructions. Catlab has a different flavor and a different encoding seems desirable.







What is particularly appealing about this approach is that these systems are hard wired to handle equality efficiently. So they can handle the equational specification of a Catlab theory. I don't currently know to interpret to proofs it outputs into something more human comprehensible.







Also, I wasn't originally aware of this, but eprover has a mode `--conjectures-are-questions` that will return the answers to existential queries. In this way, eprover can be used as a synthesizer for morphisms of a particular type. This flag gives eprover query capabilities similar to a prolog.







`eprover cartcat.tptp --conjectures-are-questions --answers=1 --silent`







One small annoying hiccup is that TPTP syntax takes the prolog convention of making quantified variables capitalized. This is not the Catlab convention. A simple way to fix this is to append a prefix of `Var*` to quantified objects and `const*` to constant function symbols.







All of the keys in the context dictionary are the quantified variables in an declaration. We can build a map to symbols where they are prefixed with `Var`






    
    
```

varmap = Dict(map(kv -> kv[1] => Symbol("Var$(kv[1])")  , collect(myterm.context )))
```








And then we can use this map to prefixify other expressions.






    
    
```

prefixify(x::Symbol, varmap) = haskey(varmap,x) ?  varmap[x] : Symbol( "const$x")
prefixify(x::Expr, varmap) = Expr(x.head, map(y -> prefixify(y, varmap),  x.args)... )
```








Given these, it has just some string interpolation hackery to port a catlab typing definition into a TPTP syntax axiom about a typing relation






    
    
```

function build_typo(terms)
    map(myterm ->  begin
                varmap = Dict(map(kv -> kv[1] => Symbol("Var$(kv[1])")  , collect(myterm.context )))
                prefix_context = Dict(map(kv -> kv[1] => prefixify(kv[2] , varmap) , collect(myterm.context )))
                context_terms = map( kv -> "typo($(varmap[kv[1]]), $(kv[2]))", collect(prefix_context))
                conc = "typo( const$(myterm.name)($(join(map(p -> prefixify(p,varmap) , myterm.params), ", "))) , $(prefixify(myterm.typ, varmap)) )"
                if length(myterm.context) > 0
                    "
                    ![$(join(values(varmap),","))]: 
                        ($conc <=
                            ($(join( context_terms , " &\n\t"))))"
                else # special case for empty context
                    "$conc"
                end
                    end
    , terms)
end
```








You can spit out the axioms for a theory like so






    
    
```

query = join(map(t -> "fof( axiom$(t[1]) , axiom, $(t[2]) ).", enumerate(build_typo(theory(CartesianCategory).terms))), "\n")
```







    
    
```

fof( axiom1 , axiom, 
![VarA]: 
    (typo( constid(VarA) , constHom(VarA, VarA) ) <=
        (typo(VarA, constOb))) ).
fof( axiom2 , axiom, 
![Varf,VarA,VarB,Varg,VarC]: 
    (typo( constcompose(Varf, Varg) , constHom(VarA, VarC) ) <=
        (typo(Varf, constHom(VarA, VarB)) &
	typo(VarA, constOb) &
	typo(VarB, constOb) &
	typo(Varg, constHom(VarB, VarC)) &
	typo(VarC, constOb))) ).
fof( axiom3 , axiom, 
![VarA,VarB]: 
    (typo( constotimes(VarA, VarB) , constOb ) <=
        (typo(VarA, constOb) &
	typo(VarB, constOb))) ).
fof( axiom4 , axiom, 
![Varf,VarA,VarD,VarB,Varg,VarC]: 
    (typo( constotimes(Varf, Varg) , constHom(constotimes(VarA, VarC), constotimes(VarB, VarD)) ) <=
        (typo(Varf, constHom(VarA, VarB)) &
	typo(VarA, constOb) &
	typo(VarD, constOb) &
	typo(VarB, constOb) &
	typo(Varg, constHom(VarC, VarD)) &
	typo(VarC, constOb))) ).
fof( axiom5 , axiom, typo( constmunit() , constOb ) ).
fof( axiom6 , axiom, 
![VarA,VarB]: 
    (typo( constbraid(VarA, VarB) , constHom(constotimes(VarA, VarB), constotimes(VarB, VarA)) ) <=
        (typo(VarA, constOb) &
	typo(VarB, constOb))) ).
fof( axiom7 , axiom, 
![VarA]: 
    (typo( constmcopy(VarA) , constHom(VarA, constotimes(VarA, VarA)) ) <=
        (typo(VarA, constOb))) ).
fof( axiom8 , axiom, 
![VarA]: 
    (typo( constdelete(VarA) , constHom(VarA, constmunit()) ) <=
        (typo(VarA, constOb))) ).
fof( axiom9 , axiom, 
![Varf,VarA,VarB,Varg,VarC]: 
    (typo( constpair(Varf, Varg) , constHom(VarA, constotimes(VarB, VarC)) ) <=
        (typo(Varf, constHom(VarA, VarB)) &
	typo(VarA, constOb) &
	typo(VarB, constOb) &
	typo(Varg, constHom(VarA, VarC)) &
	typo(VarC, constOb))) ).
fof( axiom10 , axiom, 
![VarA,VarB]: 
    (typo( constproj1(VarA, VarB) , constHom(constotimes(VarA, VarB), VarA) ) <=
        (typo(VarA, constOb) &
	typo(VarB, constOb))) ).
fof( axiom11 , axiom, 
![VarA,VarB]: 
    (typo( constproj2(VarA, VarB) , constHom(constotimes(VarA, VarB), VarB) ) <=
        (typo(VarA, constOb) &
	typo(VarB, constOb))) ).

% example synthesis queries
%fof(q , conjecture, ?[F]: (typo( F, constHom(a , a) )  <=  ( typo(a, constOb)  )   ) ).
%fof(q , conjecture, ?[F]: (typo( F, constHom( constotimes(a,b) , constotimes(b,a)) )  <=  ( typo(a, constOb) & typo(b,constOb) )   ) ).
%fof(q , conjecture, ?[F]: (typo( F, constHom( constotimes(a,constotimes(b,constotimes(c,d))) , d) )  <=  ( typo(a, constOb) & typo(b,constOb) & typo(c,constOb) & typo(d,constOb) )   ) ). % this one hurts already without some axiom pruning

```








For dealing with the equations of the theory, I believe we can just ignore the typing relations. Each equation axiom preserves well-typedness, and as long as our query is also well typed, I don't think anything will go awry. Here it would be nice to have the proof output of the tool be more human readable, but I don't know how to do that yet. **Edit: It went awry. I currently think this is completely wrong.**






    
    
```

function build_eqs(axioms)
        map(axiom -> begin
            @assert axiom.name == :(==)
            varmap = Dict(map(kv -> kv[1] => Symbol("Var$(kv[1])")  , collect(axiom.context )))
            l = prefixify(axiom.left, varmap)
            r = prefixify(axiom.right, varmap)
            "![$(join(values(varmap), ", "))]: $l = $r" 
            end,
        axioms)
end

t = join( map( t -> "fof( axiom$(t[1]), axiom, $(t[2]))."  , enumerate(build_eqs(theory(CartesianCategory).axioms))), "\n")
print(t)
```







    
    
```

fof( axiom1, axiom, ![Varf, VarA, VarD, VarB, Varh, Varg, VarC]: constcompose(constcompose(Varf, Varg), Varh) = constcompose(Varf, constcompose(Varg, Varh))).
fof( axiom2, axiom, ![Varf, VarA, VarB]: constcompose(Varf, constid(VarB)) = Varf).
fof( axiom3, axiom, ![Varf, VarA, VarB]: constcompose(constid(VarA), Varf) = Varf).
fof( axiom4, axiom, ![Varf, VarA, VarB, Varg, VarC]: constpair(Varf, Varg) = constcompose(constmcopy(VarC), constotimes(Varf, Varg))).
fof( axiom5, axiom, ![VarA, VarB]: constproj1(VarA, VarB) = constotimes(constid(VarA), constdelete(VarB))).
fof( axiom6, axiom, ![VarA, VarB]: constproj2(VarA, VarB) = constotimes(constdelete(VarA), constid(VarB))).
fof( axiom7, axiom, ![Varf, VarA, VarB]: constcompose(Varf, constmcopy(VarB)) = constcompose(constmcopy(VarA), constotimes(Varf, Varf))).
fof( axiom8, axiom, ![Varf, VarA, VarB]: constcompose(Varf, constdelete(VarB)) = constdelete(VarA)).

% silly example query
fof( q, conjecture, ![Varf, Varh, Varg, Varj ]: constcompose(constcompose(constcompose(Varf, Varg), Varh), Varj) = constcompose(Varf, constcompose(Varg, constcompose(Varh,Varj)) )).

```








It is possible and perhaps desirable fully automating the call to eprover as an external process and then parsing the results back into Julia. Julia has some slick external process facilities [https://docs.julialang.org/en/v1/manual/running-external-programs/](https://docs.julialang.org/en/v1/manual/running-external-programs/)







## Prolog and Kanrens







It was an interesting revelation to me that the typing relations for morphisms as described in catlab seems like it is already basically in the form amenable to prolog or a Kanren. The variables are universally quantified and there is only one term to the left of the turnstile (which is basically prolog's `:-`) This is a [Horn clause](https://en.wikipedia.org/wiki/Horn_clause).







In a recent post I showed how to implement something akin to a minikanren in Julia [https://www.philipzucker.com/yet-another-microkanren-in-julia/](https://www.philipzucker.com/yet-another-microkanren-in-julia/) I built that with this application in mind







Here's an example I wrote by hand in in minikaren






    
    
```

(define (typo f t)
(conde
  [(fresh (a) (== f 'id) (== t `(hom ,a ,a))) ]
  [(== f 'f) (== t '(hom a c))]
  [(fresh (a b) (== f 'snd) (== t `(hom ( ,a ,b) ,b)))]
  [(fresh (a b) (== f 'fst) (== t `(hom ( ,a ,b) ,a)))]
  [(fresh (g h a b c) (== f `(comp ,g ,h))
                       (== t `(hom ,a ,c)) 
                       (typo g `(hom ,a ,b ))
                       (typo h `(hom ,b ,c)))]
  [ (fresh (g h a b c) (== f `(fan ,g ,h))
                       (== t `(hom ,a (,b ,c))) 
                       (typo g `(hom ,a ,b ))
                       (typo h `(hom ,a ,c)))  ]
  )
  )

;queries
; could lose the hom
;(run 3 (q) (typo  q '(hom (a b) a)))
;(run 3 (q) (typo  q '(hom ((a b) c) a)))
(run 3 (q) (typo  q '(hom (a b) (b a))))
```








And here is a similar thing written in my Julia minikanren. I had to depth limit it because I goofed up the fair interleaving in my implementation.






    
    
```

function typo(f, t, n)
    fresh2( (a,b) -> (f ≅ :fst) ∧ (t  ≅ :(Hom(tup($a,$b),$a)))) ∨
    fresh2( (a,b) -> (f ≅ :snd) ∧ (t  ≅ :(Hom(tup($a,$b),$b)))) ∨
    freshn( 6, (g,h,a,b,c,n2) -> (n ≅ :(succ($n2))) ∧ (f ≅ :(comp($g, $h)))  ∧ (t  ≅ :(Hom($a,$c))) ∧ @Zzz(typo(g, :(Hom($a,$b)), n2))  ∧ @Zzz(typo(h, :(Hom($b,$c)), n2))) ∨
    fresh(a -> (f ≅ :(id($a))) ∧ (t  ≅ :(Hom($a,$a))))
end


run(1, f ->  typo( f  , :(Hom(tup(a,tup(b,tup(c,d))),d)), nat(5)))
```








## Bits and Bobbles







Discussion on the Catlab zulip. Some interesting discussion here such as an alternative encoding of GATs to FOL [https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207919104](https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207919104)







Of course, it'd be great it these solvers were bullet proof. But they aren't. They are solving very hard questions more or less by brute force. So the amount of scaling they can achieve can be resolved by experimentation only. It may be that using these solvers is a dead end. These solvers do have a number of knobs to turn. The command line argument list to eprover is enormous.







These solvers are all facing some bad churn problems







  * Morphism composition is known to be a thing that makes dumb search go totally off the rails.
  * The identity morphism can be composed arbitrary number of times. This also makes solvers churn
  * Some catlab theories are overcomplete.
  * Some catlab theories are capable are building up and breaking down the same thing over and over (complicated encodings of id like pair(fst,snd))).






use SMT? [https://github.com/ahumenberger/Z3.jl](https://github.com/ahumenberger/Z3.jl) SMT is capable of encoding the equational problems if you use quantifiers (which last I checked these bindings do not yet export) . Results may vary. SMT with quantifiers is not the place where they shine the most. Is there anything else that can be fruitfully encoded to SMT? SAT?







Custom heuristics for search. Purely declarative is too harsh a goal. Having pure Julia solution is important here.







GAP.jl [https://github.com/oscar-system/GAP.jl](https://github.com/oscar-system/GAP.jl) has facilities for knuth-bendix. This might be useful for finitely presented categories. It would be interesting to explore what pieces of computational group theory are applicable or analogous to computational category theory






    
    
```

>>> dump(theory(Category))

Catlab.GAT.Theory
  types: Array{Catlab.GAT.TypeConstructor}((2,))
    1: Catlab.GAT.TypeConstructor
      name: Symbol Ob
      params: Array{Symbol}((0,))
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((0,))
        vals: Array{Union{Expr, Symbol}}((0,))
        ndel: Int64 0
        dirty: Bool false
      doc: String " Object in a category "
    2: Catlab.GAT.TypeConstructor
      name: Symbol Hom
      params: Array{Symbol}((2,))
        1: Symbol dom
        2: Symbol codom
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]
        keys: Array{Symbol}((2,))
          1: Symbol dom
          2: Symbol codom
        vals: Array{Union{Expr, Symbol}}((2,))
          1: Symbol Ob
          2: Symbol Ob
        ndel: Int64 0
        dirty: Bool true
      doc: String " Morphism in a category "
  terms: Array{Catlab.GAT.TermConstructor}((2,))
    1: Catlab.GAT.TermConstructor
      name: Symbol id
      params: Array{Symbol}((1,))
        1: Symbol A
      typ: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol Hom
          2: Symbol A
          3: Symbol A
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((1,))
          1: Symbol A
        vals: Array{Union{Expr, Symbol}}((1,))
          1: Symbol Ob
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
    2: Catlab.GAT.TermConstructor
      name: Symbol compose
      params: Array{Symbol}((2,))
        1: Symbol f
        2: Symbol g
      typ: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol Hom
          2: Symbol A
          3: Symbol C
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[4, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 5, 0, 0, 0, 3]
        keys: Array{Symbol}((5,))
          1: Symbol A
          2: Symbol B
          3: Symbol C
          4: Symbol f
          5: Symbol g
        vals: Array{Union{Expr, Symbol}}((5,))
          1: Symbol Ob
          2: Symbol Ob
          3: Symbol Ob
          4: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol A
              3: Symbol B
          5: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol B
              3: Symbol C
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
  axioms: Array{Catlab.GAT.AxiomConstructor}((3,))
    1: Catlab.GAT.AxiomConstructor
      name: Symbol ==
      left: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol compose
              2: Symbol f
              3: Symbol g
          3: Symbol h
      right: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Symbol f
          3: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol compose
              2: Symbol g
              3: Symbol h
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[5, 0, 0, 0, 1, 0, 4, 0, 2, 7, 0, 6, 0, 0, 0, 3]
        keys: Array{Symbol}((7,))
          1: Symbol A
          2: Symbol B
          3: Symbol C
          4: Symbol D
          5: Symbol f
          6: Symbol g
          7: Symbol h
        vals: Array{Union{Expr, Symbol}}((7,))
          1: Symbol Ob
          2: Symbol Ob
          3: Symbol Ob
          4: Symbol Ob
          5: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol A
              3: Symbol B
          6: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol B
              3: Symbol C
          7: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol C
              3: Symbol D
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
    2: Catlab.GAT.AxiomConstructor
      name: Symbol ==
      left: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Symbol f
          3: Expr
            head: Symbol call
            args: Array{Any}((2,))
              1: Symbol id
              2: Symbol B
      right: Symbol f
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((3,))
          1: Symbol A
          2: Symbol B
          3: Symbol f
        vals: Array{Union{Expr, Symbol}}((3,))
          1: Symbol Ob
          2: Symbol Ob
          3: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol A
              3: Symbol B
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
    3: Catlab.GAT.AxiomConstructor
      name: Symbol ==
      left: Expr
        head: Symbol call
        args: Array{Any}((3,))
          1: Symbol compose
          2: Expr
            head: Symbol call
            args: Array{Any}((2,))
              1: Symbol id
              2: Symbol A
          3: Symbol f
      right: Symbol f
      context: OrderedCollections.OrderedDict{Symbol,Union{Expr, Symbol}}
        slots: Array{Int32}((16,)) Int32[3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        keys: Array{Symbol}((3,))
          1: Symbol A
          2: Symbol B
          3: Symbol f
        vals: Array{Union{Expr, Symbol}}((3,))
          1: Symbol Ob
          2: Symbol Ob
          3: Expr
            head: Symbol call
            args: Array{Any}((3,))
              1: Symbol Hom
              2: Symbol A
              3: Symbol B
        ndel: Int64 0
        dirty: Bool true
      doc: Nothing nothing
  aliases: Dict{Symbol,Symbol}
    slots: Array{UInt8}((16,)) UInt8[0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    keys: Array{Symbol}((16,))
      1: Symbol ⋅
      2: #undef
      3: #undef
      4: #undef
      5: #undef
      ...
      12: #undef
      13: #undef
      14: #undef
      15: #undef
      16: #undef
    vals: Array{Symbol}((16,))
      1: Symbol compose
      2: #undef
      3: #undef
      4: #undef
      5: #undef
      ...
      12: #undef
      13: #undef
      14: #undef
      15: #undef
      16: #undef
    ndel: Int64 0
    count: Int64 2
    age: UInt64 0x0000000000000002
    idxfloor: Int64 1
    maxprobe: Int64 0
```




