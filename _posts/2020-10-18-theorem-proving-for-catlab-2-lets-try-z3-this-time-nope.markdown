---
author: philzook58
comments: true
date: 2020-10-18 21:52:12+00:00
layout: post
link: https://www.philipzucker.com/theorem-proving-for-catlab-2-lets-try-z3-this-time-nope/
slug: theorem-proving-for-catlab-2-lets-try-z3-this-time-nope
title: 'Theorem Proving For Catlab 2: Let''s Try Z3 This Time. Nope.'
wordpress_id: 2985
categories:
- Formal Methods
- Julia
tags:
- categorytheory
- julialang
---




Welp, you win some, you lose some.







As I had left [off last time](https://www.philipzucker.com/notes-on-synthesis-and-equation-proving-for-catlab-jl/), I had realized that my encoding of the equations of Catlab was unsound.







As an example, look at the following suggested axioms.






    
```
fof( axiom2, axiom, ![Varf, VarA, VarB]: constcompose(Varf, constid(VarB)) = Varf).
fof( axiom3, axiom, ![Varf, VarA, VarB]: constcompose(constid(VarA), Varf) = Varf).
```







It is a theorem from these axioms that `compose(id(A),id(B)) = id(A) = id(B)`, which should not be a theorem. Evan made the interesting point that this is the standard proof that shows the identity of a group is unique, so we're reducing our magnificent category into a pitiful monoid. How sad. And inspecting the trace for some "proofs" returned by eprover shows that the solver was actually using this fact. Oh well.







An approach that I feel more confident in being correct is using "type guards" as preconditions for the equations. In the very useful paper [https://people.mpi-inf.mpg.de/~jblanche/mono-trans.pdf](https://people.mpi-inf.mpg.de/~jblanche/mono-trans.pdf) this technique is described as well known folklore, albeit in a slightly different context. The type guard is an implication clause that holds the necessary typing predicates from the typing context required for the equation to even make sense. For example composition associativity look like `forall A B C D f g h, (type(f) = Hom A B /\ type(g) = Hom B C /\ type(h) = Hom C D /\ type(A) = Ob /\ type(B) = Ob /\ type(C) = Ob /\ type(C) = Ob) => compose(f (g, h)) = compose( compose(f,g),h)`.







Adding the guards seems to work, but slows the provers to a crawl for fairly trivial queries. My running example is `pair(proj1(A,B), proj2(A,B)) = otimes(id(A),id(B))`. In Catlab `proj1`, `proj2`, and `pair`, are defined in terms of `mcopy` and `delete`, which makes this theorem not as trivial as it would appear. Basically it involves unfolding the definitions, and then applying out of nowhere some identities involving braiding.







I decided to give Z3, an SMT solver, a go since I'm already familiar with it and its python bindings. There are native Julia bindings [https://github.com/ahumenberger/Z3.jl](https://github.com/ahumenberger/Z3.jl) which may be useful for a more high performance situation, but they don't appear to have quantifier support yet.







Julia has the library PyCall [https://github.com/JuliaPy/PyCall.jl](https://github.com/JuliaPy/PyCall.jl) which was a shear joy to use. I actually could copy and paste some python3 z3 code and run it with very few modifications and I couldn't imagine going into and out of Julia data types being more seemless. 







Z3 does a better job than I expected. I thought thus problem was more appropriate to eprover or vampire, but z3 seemed to consistently out perform them.







At first I tried using a single z3 sort `z3.DeclareSort("Gat")` , but eventually I switched to a multisorted representation  `z3.DeclareSort("Ob")` and `z3.DeclareSort("Hom")` as this gets a step closer to accurately representation the types of the GATs in the simply sorted smtlib language. Which of these sorts to use can be determined by looking at the head symbol of the inferred Catlab types. I wrote a custom type inference just so I could try stuff out, but after asking in the zulip, apparently catlab has this built in also.







Some Z3 debugging tips:







I tend to make my z3 programs in python, dump the `s.sexpr()` in a file and then run that via the z3 command line. It's easier to fiddle with the smtlib2 file to try out ideas fast. Take stuff out, put stuff in, make simpler questions, etc. Be aware most ideas do not work. 







Z3 appears to be inferring pretty bad triggers. The main way z3 handles quantifiers is that it looks for patterns from the quantified expression in the currently known assertion set and instantiates the quantified expression accordingly. Hence I kind of think of quantified expressions as a kind of macro for formulas. This is called E-matching [https://rise4fun.com/z3/tutorialcontent/guide#h28](https://rise4fun.com/z3/tutorialcontent/guide#h28). Running z3 with a `-v:10`  flag let's you see the triggers. Z3 tries to find very small pieces of expressions that contain the quantified variables. I think we don't really want any equations instantiated unless it finds either the  full right or left hand side + context types. In addition, the triggers inferred for the type inference predicates were not good. We mostly want z3 to run the typing predicate forward, basically as a type inference function. So I tried adding all this and I _think_ it helped, but not enough to actually get my equation to prove. Only simpler problems.






    
    
```


(assert (forall ((A Ob)) (! (= (typo (id A)) (Hom A A)) :pattern ((id A)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom B C)))
         (= (typo (compose f g)) (Hom A C)))
     :pattern ((compose f g) (Hom A B) (Hom B C)))))
(assert (forall ((A Ob) (B Ob)) (! (= (typo (otimes A B)) Ob) :pattern ((otimes A B)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
         (= (typo (otimes f g)) (Hom (otimes A C) (otimes B D))))
     :pattern ((otimes f g) (Hom A B) (Hom C D)))))
;(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom))
;  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
;         (= (typo (otimes f g)) (Hom (otimes A C) (otimes B D))))
;     :pattern ((= (typo f) (Hom A B)) (= (typo g) (Hom C D))))))
(assert (= (typo munit) Ob))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (braid A B)) (Hom (otimes A B) (otimes B A)))
     :pattern ((braid A B)))))
(assert (forall ((A Ob))
  (! (= (typo (mcopy A)) (Hom A (otimes A A))) :pattern ((mcopy A)))))
(assert (forall ((A Ob)) (! (= (typo (delete A)) (Hom A munit)) :pattern ((delete A)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom A C)))
         (= (typo (pair f g)) (Hom A (otimes B C))))
     :pattern ((pair f g) (Hom A B) (Hom A C)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (proj1 A B)) (Hom (otimes A B) A)) :pattern ((proj1 A B)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (proj2 A B)) (Hom (otimes A B) B)) :pattern ((proj2 A B)))))
```








I tried the axiom profiler to give me any insight.  [http://people.inf.ethz.ch/summersa/wiki/lib/exe/fetch.php?media=papers:axiomprofiler.pdf](http://people.inf.ethz.ch/summersa/wiki/lib/exe/fetch.php?media=papers:axiomprofiler.pdf) [https://github.com/viperproject/axiom-profiler](https://github.com/viperproject/axiom-profiler)  I do see some quantifiers that have an insane number of instantiations. This may be because of my multipattern approach of using the Hom type and separately the term as patterns. It will just randomly fire the trigger on Homs unrelated to the one their connected to. That's awful. The associativity axioms also seem to be triggering too much and that is somewhat expected.







Z3 debugging is similar to prolog debugging since it's declarative. [https://www.metalevel.at/prolog/debugging](https://www.metalevel.at/prolog/debugging) Take out asserts. Eventually, if you take out enough, an `unsat` problem should turn `sat`.  That may help you isolate problematic axiom







Another thing I tried was to manually expand out each step of the proof to see where z3 was getting hung up. Most simple step were very fast, but some hung, apparently due to bad triggers? Surprisingly, some things I consider 1 step trivial aren't quite. Often this is because single equations steps involves associating and absorbing `munit` in the type predicates. The interchange law was difficult to get to fire for this reason I think.







Trimming the axioms available to only the ones needed really helps, but doesn't seem practical as an automated thing.







## Code







Here's the Julia code I ended up using to generate the z3 query from the catlab axioms. It's very hacky. My apologies. I was thrashing.






```julia
# here we're trying to use Z3 sorts to take care of some of the typign
using Catlab
using Catlab.Theories
using PyCall
z3 = pyimport("z3")

# my ersatz unnecessary type inference code for Cartesian category terms

function type_infer(x::Symbol; ctx = Dict())
    if x == :Ob
        return :TYPE
    elseif x == :munit
        return :Ob
    else 
        return ctx[x]
    end 
    
end
    
function type_infer(x::Expr; ctx = Dict())
        @assert x.head == :call
        head = x.args[1]
        if head == :compose
            t1 = type_infer(x.args[2], ctx=ctx)
            @assert t1.args[1] == :Hom
            obA = t1.args[2] 
            t2 = type_infer(x.args[3], ctx=ctx)
            @assert t2.args[1] == :Hom
            obC = t2.args[3] 

            if t1.args[3] != t2.args[2]
                #println("HEY CHECK THIS OUT ITS WEIRD")
            #println(t1)
            #println(t2)
        end

            return :(Hom($obA, $obC))
        elseif head == :otimes
            t1 = type_infer(x.args[2], ctx=ctx)
            #@assert t1.args[1] == :Hom
            if t1 isa Symbol && t1 == :Ob
                return :Ob
            end
            @assert t1.args[1] == :Hom
            obA = t1.args[2] 
            obC = t1.args[3] 
            t2 = type_infer(x.args[3], ctx=ctx)
            @assert t2.args[1] == :Hom
            obB = t2.args[2] 
            obD = t2.args[3] 
            return :(Hom(otimes($obA,$obB),otimes($obC, $obD)))
        elseif head == :pair
            t1 = type_infer(x.args[2], ctx=ctx)
            @assert t1.args[1] == :Hom
            obA = t1.args[2] 
            obB = t1.args[3] 
            t2 = type_infer(x.args[3], ctx=ctx)
            @assert t2.args[1] == :Hom
            obC = t2.args[3] 
            @assert t1.args[2] == t2.args[2]
            return :(Hom($obA, otimes($obB,$obC)))
        elseif head == :mcopy
            ob = x.args[2]
            return :(Hom($ob, otimes($ob,$ob)))
        elseif head == :id
            ob = x.args[2]
            return :(Hom($ob, $ob))
        elseif head == :delete
            ob = x.args[2]
            return :(Hom($ob, munit))
        elseif head == :proj1
            obA = x.args[2]
            obB = x.args[3]
            return :(Hom(otimes($obA, $obB), $obA))
        elseif head == :proj2
            obA = x.args[2]
            obB = x.args[3]
            return :(Hom(otimes($obA, $obB), $obB))
        elseif head == :braid
            obA = x.args[2]
            obB = x.args[3]
            return :(Hom(otimes($obA, $obB), otimes($obB, $obA)))
        elseif head == :Hom
            return :TYPE
        elseif head == :munit
            return :Ob
        else
            println(x, ctx)
            @assert false
        end
end

TYPE = z3.DeclareSort("TYPE")

# sortify takes a type expression, grabs the head, and returns the corresponding Z3 sort.
function sortify(ty) 
    if ty isa Symbol
        return z3.DeclareSort(String(ty))
    elseif ty isa Expr
        @assert ty.head == :call
        return z3.DeclareSort(String(ty.args[1]))
    end
end

# z3ify take an Expr or Symbol in a dictionary typing context and returns the z3 equivalent
z3ify( e::Symbol , ctx) = z3.Const(String(e), sortify(type_infer(e,ctx=ctx)))

function z3ify( e::Expr , ctx)
    @assert e.head == :call
    out_sort = sortify(type_infer(e,ctx=ctx))
    z3.Function(e.args[1], [sortify(type_infer(x,ctx=ctx)) for x in e.args[2:end]]..., out_sort)(map(x -> z3ify(x,ctx), e.args[2:end])...)
end

# typo is a helper routine that takes an Expr or Symbol term and returns the Z3 function typo applied to the z3ified term
function typo(x, ctx)
    f = z3.Function("typo" , sortify(type_infer(x,ctx=ctx))  , TYPE ) 
    f(z3ify(x,ctx))
end

# a helper function to z3ify an entire context for the implication
function build_ctx_predicate(ctx)
    map( kv-> begin
        #typo = z3.Function("typo" , sortify(typ)  , TYPE ) 
        typo(kv[1], ctx) == z3ify(kv[2], ctx)
        end
        
        , filter( kv -> kv[2] isa Expr , # we don't need to put typo predicates about simple types like Ob 
              collect(ctx)))

end

# converts the typing axioms of a GAT into the equivalent z3 axioms
# This is quite close to unreadable I think
function build_typo_z3(terms)
    map(myterm ->  begin
                ctx = myterm.context
                conc =  length(myterm.params) > 0  ?  Expr(:call, myterm.name, myterm.params...) : myterm.name
                  preconds = build_ctx_predicate(myterm.context) 
                    if length(myterm.context) > 0 && length(preconds) > 0
                        z3.ForAll( map(x -> z3ify(x,ctx), collect(keys(myterm.context))) ,
                            z3.Implies( z3.And(preconds)  , 
                                      typo(conc,myterm.context) == z3ify(myterm.typ, myterm.context)),
                  patterns = [ z3.MultiPattern(z3ify(conc,ctx),  
                                [ z3ify(x ,ctx ) for x in collect(values(myterm.context)) if x isa Expr]...) # not super sure this is a valid way of filtering generally
                              ],
                  )
                elseif length(myterm.context) > 0
                        z3.ForAll( map(x -> z3ify(x,ctx), collect(keys(myterm.context))) ,
                                      typo(conc,myterm.context) == z3ify(myterm.typ, myterm.context),
                          patterns = [z3ify(conc,ctx)])
                    else
                        typo(conc,myterm.context) == z3ify(myterm.typ, myterm.context)
                    end
            end
              
    , terms)
end

# convert the equations axioms of a GAT into the equivalent z3 terms
function build_eqs_z3(axioms)
        map(axiom -> begin
            @assert axiom.name == :(==)
            ctx = axiom.context
            l = z3ify(axiom.left, axiom.context)
            r = z3ify(axiom.right, axiom.context)
            preconds= build_ctx_predicate(axiom.context) 
            ctx_patterns = [ z3ify(x ,ctx ) for x in collect(values(axiom.context)) if x isa Expr]
            println([z3.MultiPattern( l , ctx_patterns...  ) , z3.MultiPattern( r , ctx_patterns...  ) ])
            if length(axiom.context) > 0 && length(preconds) > 0
                    try
                    z3.ForAll( map(x -> z3ify(x,ctx), collect(keys(axiom.context))) , 
                    z3.Implies(  z3.And( preconds) ,   l == r),
                patterns = [z3.MultiPattern( l , ctx_patterns...  ) , z3.MultiPattern( r , ctx_patterns...  ) ])
                    catch e
                      println(e)
                        z3.ForAll( map(x -> z3ify(x,ctx), collect(keys(axiom.context))) , 
                        z3.Implies(  z3.And( preconds) ,   l == r))
                end
                elseif length(axiom.context) > 0  && length(preconds) == 0
                    z3.ForAll( map(x -> z3ify(x,ctx), collect(keys(axiom.context))) , l == r, patterns = [l,r])
                
                else
                    l == r
                end
            end,
        axioms)
end

# jut trying some stuff out
sortify( :Ob )
sortify( :(Hom(a,b)))
ctx = Dict(:A => :Ob, :B => :Ob)
z3ify(:(id(A)) , ctx)
#=typing_axioms = build_typo_z3(theory(CartesianCategory).terms)
eq_axioms = build_eqs_z3(theory(CartesianCategory).axioms)

s = z3.Solver()
s.add(typing_axioms)
s.add(eq_axioms)
#print(s.sexpr())
=#

inferall(e::Symbol, ctx) = [typo(e,ctx) == z3ify(type_infer(e,ctx=ctx),ctx)]
inferall(e::Expr, ctx) = Iterators.flatten([[typo(e,ctx) == z3ify(type_infer(e,ctx=ctx),ctx)], Iterators.flatten(map(z -> inferall(z,ctx), e.args[2:end]))])


function prove(ctx, l,r; pr = false)
    typing_axioms = build_typo_z3(theory(CartesianCategory).terms)
    eq_axioms = build_eqs_z3(theory(CartesianCategory).axioms)
    s = z3.Solver()
    s.add(typing_axioms)
    s.add(eq_axioms)
    s.add(collect(inferall(l,ctx)))
    s.add(collect(inferall(r,ctx)))
    s.add(z3.Not( z3ify(l,ctx) == z3ify(r,ctx)))
    #println("checking $x")
    #if pr
    println(s.sexpr())
      #else
    #println(s.check())
    #end
end
ctx =  Dict(:A => :Ob, :B => :Ob)
prove( ctx, :(pair(proj1(A,B), proj2(A,B))), :(otimes(id(A),id(B))))
```







The returned smtlib2 predicate with a `(check-sat)` manually added at the end






    
    
```

(declare-sort Ob 0)
(declare-sort TYPE 0)
(declare-sort Hom 0)
(declare-fun id (Ob) Hom)
(declare-fun Hom (Ob Ob) TYPE)
(declare-fun typo (Hom) TYPE)
(declare-fun compose (Hom Hom) Hom)
(declare-fun otimes (Ob Ob) Ob)
(declare-fun Ob () TYPE)
(declare-fun typo (Ob) TYPE)
(declare-fun otimes (Hom Hom) Hom)
(declare-fun munit () Ob)
(declare-fun braid (Ob Ob) Hom)
(declare-fun mcopy (Ob) Hom)
(declare-fun delete (Ob) Hom)
(declare-fun pair (Hom Hom) Hom)
(declare-fun proj1 (Ob Ob) Hom)
(declare-fun proj2 (Ob Ob) Hom)
(declare-fun B () Ob)
(declare-fun A () Ob)
(assert (forall ((A Ob)) (! (= (typo (id A)) (Hom A A)) :pattern ((id A)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom B C)))
         (= (typo (compose f g)) (Hom A C)))
     :pattern ((compose f g) (Hom A B) (Hom B C)))))
(assert (forall ((A Ob) (B Ob)) (! (= (typo (otimes A B)) Ob) :pattern ((otimes A B)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
         (= (typo (otimes f g)) (Hom (otimes A C) (otimes B D))))
     :pattern ((otimes f g) (Hom A B) (Hom C D)))))
(assert (= (typo munit) Ob))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (braid A B)) (Hom (otimes A B) (otimes B A)))
     :pattern ((braid A B)))))
(assert (forall ((A Ob))
  (! (= (typo (mcopy A)) (Hom A (otimes A A))) :pattern ((mcopy A)))))
(assert (forall ((A Ob)) (! (= (typo (delete A)) (Hom A munit)) :pattern ((delete A)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom A C)))
         (= (typo (pair f g)) (Hom A (otimes B C))))
     :pattern ((pair f g) (Hom A B) (Hom A C)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (proj1 A B)) (Hom (otimes A B) A)) :pattern ((proj1 A B)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (typo (proj2 A B)) (Hom (otimes A B) B)) :pattern ((proj2 A B)))))
(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom) (h Hom))
  (! (=> (and (= (typo f) (Hom A B))
              (= (typo g) (Hom B C))
              (= (typo h) (Hom C D)))
         (= (compose (compose f g) h) (compose f (compose g h))))
     :pattern ((compose (compose f g) h) (Hom A B) (Hom B C) (Hom C D))
     :pattern ((compose f (compose g h)) (Hom A B) (Hom B C) (Hom C D)))))
(assert (forall ((A Ob) (B Ob) (f Hom))
  (! (=> (and (= (typo f) (Hom A B))) (= (compose f (id B)) f))
     :pattern ((compose f (id B)) (Hom A B))
     :pattern (pattern f (Hom A B)))))
(assert (forall ((A Ob) (B Ob) (f Hom))
  (! (=> (and (= (typo f) (Hom A B))) (= (compose (id A) f) f))
     :pattern ((compose (id A) f) (Hom A B))
     :pattern (pattern f (Hom A B)))))
(assert (forall ((A Ob) (B Ob) (C Ob))
  (! (= (otimes (otimes A B) C) (otimes A (otimes B C)))
     :pattern ((otimes (otimes A B) C))
     :pattern ((otimes A (otimes B C))))))
(assert (forall ((A Ob))
  (! (= (otimes A munit) A) :pattern ((otimes A munit)) :pattern (pattern A))))
(assert (forall ((A Ob))
  (! (= (otimes munit A) A) :pattern ((otimes munit A)) :pattern (pattern A))))
(assert (forall ((A Ob) (B Ob) (C Ob) (X Ob) (Y Ob) (Z Ob) (f Hom) (g Hom) (h Hom))
  (! (=> (and (= (typo f) (Hom A X))
              (= (typo g) (Hom B Y))
              (= (typo h) (Hom C Z)))
         (= (otimes (otimes f g) h) (otimes f (otimes g h))))
     :pattern ((otimes (otimes f g) h) (Hom A X) (Hom B Y) (Hom C Z))
     :pattern ((otimes f (otimes g h)) (Hom A X) (Hom B Y) (Hom C Z)))))
(assert (forall ((A Ob)
         (B Ob)
         (C Ob)
         (X Ob)
         (Y Ob)
         (Z Ob)
         (f Hom)
         (h Hom)
         (g Hom)
         (k Hom))
  (! (=> (and (= (typo f) (Hom A B))
              (= (typo h) (Hom B C))
              (= (typo g) (Hom X Y))
              (= (typo k) (Hom Y Z)))
         (= (compose (otimes f g) (otimes h k))
            (otimes (compose f h) (compose g k))))
     :pattern ((compose (otimes f g) (otimes h k))
               (Hom A B)
               (Hom B C)
               (Hom X Y)
               (Hom Y Z))
     :pattern ((otimes (compose f h) (compose g k))
               (Hom A B)
               (Hom B C)
               (Hom X Y)
               (Hom Y Z)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (id (otimes A B)) (otimes (id A) (id B)))
     :pattern ((id (otimes A B)))
     :pattern ((otimes (id A) (id B))))))
(assert (forall ((A Ob) (B Ob))
  (! (= (compose (braid A B) (braid B A)) (id (otimes A B)))
     :pattern ((compose (braid A B) (braid B A)))
     :pattern ((id (otimes A B))))))
(assert (forall ((A Ob) (B Ob) (C Ob))
  (! (= (braid A (otimes B C))
        (compose (otimes (braid A B) (id C)) (otimes (id B) (braid A C))))
     :pattern ((braid A (otimes B C)))
     :pattern ((compose (otimes (braid A B) (id C)) (otimes (id B) (braid A C)))))))
(assert (forall ((A Ob) (B Ob) (C Ob))
  (! (= (braid (otimes A B) C)
        (compose (otimes (id A) (braid B C)) (otimes (braid A C) (id B))))
     :pattern ((braid (otimes A B) C))
     :pattern ((compose (otimes (id A) (braid B C)) (otimes (braid A C) (id B)))))))
(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
         (= (compose (otimes f g) (braid B D))
            (compose (braid A C) (otimes g f))))
     :pattern ((compose (otimes f g) (braid B D)) (Hom A B) (Hom C D))
     :pattern ((compose (braid A C) (otimes g f)) (Hom A B) (Hom C D)))))
(assert (forall ((A Ob))
  (! (= (compose (mcopy A) (otimes (mcopy A) (id A)))
        (compose (mcopy A) (otimes (id A) (mcopy A))))
     :pattern ((compose (mcopy A) (otimes (mcopy A) (id A))))
     :pattern ((compose (mcopy A) (otimes (id A) (mcopy A)))))))
(assert (forall ((A Ob))
  (! (= (compose (mcopy A) (otimes (delete A) (id A))) (id A))
     :pattern ((compose (mcopy A) (otimes (delete A) (id A))))
     :pattern ((id A)))))
(assert (forall ((A Ob))
  (! (= (compose (mcopy A) (otimes (id A) (delete A))) (id A))
     :pattern ((compose (mcopy A) (otimes (id A) (delete A))))
     :pattern ((id A)))))
(assert (forall ((A Ob))
  (! (= (compose (mcopy A) (braid A A)) (mcopy A))
     :pattern ((compose (mcopy A) (braid A A)))
     :pattern ((mcopy A)))))
(assert (forall ((A Ob) (B Ob))
  (! (let ((a!1 (compose (otimes (mcopy A) (mcopy B))
                         (otimes (otimes (id A) (braid A B)) (id B)))))
       (= (mcopy (otimes A B)) a!1))
     :pattern ((mcopy (otimes A B)))
     :pattern ((compose (otimes (mcopy A) (mcopy B))
                        (otimes (otimes (id A) (braid A B)) (id B)))))))
(assert (forall ((A Ob) (B Ob))
  (! (= (delete (otimes A B)) (otimes (delete A) (delete B)))
     :pattern ((delete (otimes A B)))
     :pattern ((otimes (delete A) (delete B))))))
(assert (= (mcopy munit) (id munit)))
(assert (= (delete munit) (id munit)))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom C A)) (= (typo g) (Hom C B)))
         (= (pair f g) (compose (mcopy C) (otimes f g))))
     :pattern ((pair f g) (Hom C A) (Hom C B))
     :pattern ((compose (mcopy C) (otimes f g)) (Hom C A) (Hom C B)))))
(assert (forall ((A Ob) (B Ob))
  (! (= (proj1 A B) (otimes (id A) (delete B)))
     :pattern ((proj1 A B))
     :pattern ((otimes (id A) (delete B))))))
(assert (forall ((A Ob) (B Ob))
  (! (= (proj2 A B) (otimes (delete A) (id B)))
     :pattern ((proj2 A B))
     :pattern ((otimes (delete A) (id B))))))
(assert (forall ((A Ob) (B Ob) (f Hom))
  (! (=> (and (= (typo f) (Hom A B)))
         (= (compose f (mcopy B)) (compose (mcopy A) (otimes f f))))
     :pattern ((compose f (mcopy B)) (Hom A B))
     :pattern ((compose (mcopy A) (otimes f f)) (Hom A B)))))
(assert (forall ((A Ob) (B Ob) (f Hom))
  (=> (and (= (typo f) (Hom A B))) (= (compose f (delete B)) (delete A)))))
(assert (= (typo (pair (proj1 A B) (proj2 A B))) (Hom (otimes A B) (otimes A B))))
(assert (= (typo (proj1 A B)) (Hom (otimes A B) A)))
(assert (= (typo A) Ob))
(assert (= (typo B) Ob))
(assert (= (typo (proj2 A B)) (Hom (otimes A B) B)))
(assert (= (typo A) Ob))
(assert (= (typo B) Ob))
(assert (= (typo (otimes (id A) (id B))) (Hom (otimes A B) (otimes A B))))
(assert (= (typo (id A)) (Hom A A)))
(assert (= (typo A) Ob))
(assert (= (typo (id B)) (Hom B B)))
(assert (= (typo B) Ob))
(assert (not (= (pair (proj1 A B) (proj2 A B)) (otimes (id A) (id B)))))
(check-sat)
```








### Other junk







One could use z3 as glue for simple steps of proofs as is, but it doesn't appear to scale well to even intermediately complex proofs. Maybe this could be used for a semi-automated (aka interactive) proof system for catlab? This seems misguided though. You're better off using one of the many interactive proof assistants if that's the way you wanna go. Maybe one could generate the queries to those system?







I tried the type tagging version, where every term `t` is recursively replaced with `tag(t, typo_t)`. This allows us to avoid the guards and the axioms of the GAT take the form of pure equations again, albeit ones of complex tagged terms. This did not work well. I was surprised. It's kind of interesting that type tagging is in some sense internalizing another piece of Catlab syntax into a logic, just like how type guards internalized the turnstile as an implication and the context as the guard. In this case we are internalizing the inline type annotations (f::Hom(A,B)) into the logic, where I write the infix notation :: as the function tag(). 







Notebook here [https://github.com/philzook58/thoughtbooks/blob/master/catlab_gat.ipynb](https://github.com/philzook58/thoughtbooks/blob/master/catlab_gat.ipynb)







[file:///home/philip/Downloads/A_Polymorphic_Intermediate_Verification_Language_D.pdf ](file:///home/philip/Downloads/A_Polymorphic_Intermediate_Verification_Language_D.pdf )The 3.1 method. If we have an extra argument to every function for the type of that argument inserted, then quantifier instantiation can only work when the 







We could make it semi interactive (I guess semi interactive is just interactive though







[https://hal.inria.fr/hal-01322328/document](https://hal.inria.fr/hal-01322328/document) TLA+ encoding. Encoding to SMT solvers is a grand tradition







Wait, could it be that id really is the only problem? It's the only equation with a raw variable in an equality. And that poisons all of Hom. Fascinating. I thought the problem was compose, but it's id?







[https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324017/](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324017/) vampire now supports polymorphism.







I realized that things that felt like a single step, were in fact not. This is because 







Asserting the types of all subexpressions helped the solver sometimes and sometime hurt.







Solvers often use a heuristic where they want to look at the oldest generated inferences first. This means that the deeper you make your proof, the hard it is to for the solver to find it (well that's true anyway). Making the proof depth harder for trivial type inference purposes is foolish.







Of course, taken to some extreme, at a certain point we're asserting so many derived facts to the solver we have written a fraction of a solver ourselves.







I wonder what the recent burst of higher order capabilities of zipperposition, eprover, and vampire might do for me? The thing is we're already compiling to combinators. That's what categories are. https://matryoshka-project.github.io/







Functor example [http://page.mi.fu-berlin.de/cbenzmueller/papers/J22.pdf ](http://page.mi.fu-berlin.de/cbenzmueller/papers/J22.pdf )THF is higher order format of tptp.







Exporting to Isabelle in particular is a viable approach, as it is well known to have good automation. I mean, I'm reading the sledgehammer guy's papers for tips. Also, exporting to an interactive theorem prover of any kind seems kind of useful.

































