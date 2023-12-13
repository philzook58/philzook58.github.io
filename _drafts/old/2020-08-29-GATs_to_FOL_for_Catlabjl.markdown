---
author: philzook58
comments: true
date: 2020-08-29 16:35:19+00:00
layout: post
link: https://www.philipzucker.com/?p=2951
published: false
slug: GATs to FOL for Catlab.jl
title: GATs to FOL for Catlab.jl
wordpress_id: 2951
---




[https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207964406](https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207964406)







Evan pointed to Essentially Algebraic theories, which are logical like theories that have function symbols that are partially defined.







My encoding might just _be _essentially algebraic theories. I'm designating the domain for which equations hold.







Philip Zucker: I've been tinkering further in this direction and learning a bit in the process. I've been building some simple tooling to output TPTP files from a julia DSL. I also think I have an approach that can embed a GAT into first order logic. The idea is to use a typing predicate that has to be enforced as a precondition. I'm not super sure the encoding is right, and even if it is, whether the solver will choke on it. I've been poking around in the GAT representation of catlab to do so automatically. It also appears that the tools I have been exploring (e-prover and vampire) have some support for _finding_ things, something which I thought they didn't, so it's possible they may be able to synthesize expressions of some given type for example.







Philip Zucker: Actually, does anyone know if there is an encoding from GATs to first order logic? Maybe Cartmell mentions that somewhere







Philip Zucker: The two options that eprover has that give me hope on this synthesis angle are these






    
      --answers[=<arg>]
        Set the maximal number of answers to print for existentially quantified
        questions. Without this option, the prover terminates after the first
        answer found. If the value is different from 1, the prover is no longer
        guaranteed to terminate, even if there is a finite number of answers. The
        option without the optional argument is equivalent to
        --answers=2147483647.
    
      --conjectures-are-questions
        Treat all conjectures as questions to be answered. This is a wart
        necessary because CASC-J6 has categories requiring answers, but does not
        yet support the 'question' type for formulas.
    







Philip Zucker: To be more specific about the translation, I'm thinking it's reasonable to encode the GAT for category into asserting the following first order formulae






    
    # A very literal translation from the GAT signature.
    # ⊣ becomes <= first order implication
    # typing is internalized into the theory
    
    # tt is a special value for TYPE. Maybe there is no reason to assert these?
    ty(hom(A,B)) = tt <= (ty(A) = ob & ty(B) = ob)
    ty(ob) = tt <= true
    
    ty(id(A)) = hom(A,A) <=  (ty(A) = ob)
    ty(comp( F,G )) = hom(A,C)) <= (ty(A) = ob &  ty(B) = ob  &  ty(C) = ob   & ty(F) = hom(A,B)  &  ty(G) = hom(B,C))
    
    comp(comp(F,G),H) == comp(F,comp(G,H)) <= (ty(A) = ob, ty(B) = ob, ty(C) = ob,  ty(D) = obt, y(F) = hom(A,B), ty(g) = Hom(B,C), ty(h) = hom(C,D))
    comp(id(A),F) = F <= (ty(A) = ob & ty(B) = ob & ty(F) = hom(A,B))
    comp(F,id(B)) = F <= (ty(A) = ob & ty(B) = ob & ty(F) = hom(A,B))
    
    
    #query, synthesize a morphism
    exists F, ty(F) = hom(tup(A,B), A)  <=  ty(A) = ob, ty(B) = ob
    







Philip Zucker: it smells unexpectedly prology. Don't know what to make of that







Evan Patterson: Philip Zucker [said](https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207919169):







<blockquote>Actually, does anyone know if there is an encoding from GATs to first order logic? Maybe Cartmell mentions that somewhere
> 
> </blockquote>







I think I know how to convert a GAT into multisorted first-order logic, breaking it down into two steps:







  1. Convert the generalized algebraic theory into an [essentially algebraic theory](https://ncatlab.org/nlab/show/essentially+algebraic+theory) by converting total operations with dependent types into partial operations with simple types. Importantly, the domains of the partial operations are defined by equations of _total_ operations.
  2. Convert the essentially algebraic theory into a multisorted first-order theory by replacing partial operations with relations plus existence and uniqueness axioms.






For example, for the [GAT of categories](https://github.com/AlgebraicJulia/Catlab.jl/blob/c252a655f0a8f75ffa6bce149d771134e7aa1fd8/src/theories/Category.jl#L19):







  1. Convert the GAT to the EAT given by:
    * two types, \text{Ob}Ob and \text{Hom}Hom
    * total operations \text{dom}, \text{codom}: \text{Hom} \to \text{Ob}dom,codom:Hom→Ob
    * total operation \text{id}: \text{Ob} \to \text{Hom}id:Ob→Hom with equations \text{dom}(\text{id}(x)) = xdom(id(_x_))=_x_ and \text{codom}(\text{id}(x)) = xcodom(id(_x_))=_x_
    * partial operation \cdot: \text{Hom} \times \text{Hom} \to \text{Hom}⋅:Hom×Hom→Hom, whose domain is defined by the equation f, g: \text{Hom} \vdash \text{codom}(f) = \text{dom}(g)_f_,_g_:Hom⊢codom(_f_)=dom(_g_), with further equations \text{dom}(f \cdot g) = \text{dom}(f)dom(_f_⋅_g_)=dom(_f_) and \text{codom}(f \cdot g) = \text{codom}(g)codom(_f_⋅_g_)=codom(_g_)
    * axioms of associativity, left unitality, and right unitality (omitted)
  2. Convert the EAT to the multisorted first-order theory with equality given by:
    * two types, \text{Ob}Ob and \text{Hom}Hom
    * two function symbols, \text{dom}, \text{codom}: \text{Hom} \to \text{Ob}dom,codom:Hom→Ob
    * two relation symbols, \text{id}: \text{Ob} \times \text{Hom}id:Ob×Hom and \text{compose}: \text{Hom} \times \text{Hom} \times \text{Hom}compose:Hom×Hom×Hom
    * axioms for \text{id}id (omitted)
    * axioms for \text{compose}compose, namely
      * \forall f, g: \text{Hom}.\ \text{codom}(f) = \text{dom}(g) \implies \exist h: \text{Hom}.\ \text{compose}(f,g,h)∀_f_,_g_:Hom. codom(_f_)=dom(_g_)⟹∃_h_:Hom. compose(_f_,_g_,_h_)
      * \forall f,g,h,k: \text{Hom}.\ \text{compose}(f,g,h) \wedge \text{compose}(f,g,k) \implies h = k∀_f_,_g_,_h_,_k_:Hom. compose(_f_,_g_,_h_)∧compose(_f_,_g_,_k_)⟹_h_=_k_.
      * \forall f, g, h: \text{Hom}.\ \text{compose}(f,g,h) \implies \text{codom}(f) = \text{dom}(g) \wedge \text{dom}(f) = \text{dom}(h) \wedge \text{codom}(g) = \text{codom}(h)∀_f_,_g_,_h_:Hom. compose(_f_,_g_,_h_)⟹codom(_f_)=dom(_g_)∧dom(_f_)=dom(_h_)∧codom(_g_)=codom(_h_)
    * axioms of associativity, left unitality, and right unitality (omitted)






Note that the first transformation preserves the "algebraic character" of the theory, while the second does not because it introduces existential quantifiers.







Owen Lynch: Just out of curiousity, why do you want to encode a GAT as first order logic? As Evan said, the algebraic character is lost, so it seems to me that a theorem prover specialized for GATs would do much better than a theorem prover for first order logic that was fed in a GAT. Relevant to this: is there a GAT theory for MMT that matches up with how we use GATs in Catlab? That might make things unexpectedly easy.







James Fairbanks: I think PZ’s goal is to use FOL tools which have been built for formal methods in software engineering to verify stuff.







Philip Zucker: That's right. You can get off the shelf FOL solvers whose implementations have been refined for over 30 years, with techniques researched for over 60. It seems to me at least worth a shot to try to meet them halfway. Some of the automated capabilities of interactive systems like Coq and Isabelle are based around finding ways to call these same provers. Now the encoding will probably not be pleasant to the human eye for a GAT, but since they'd be machine generated hopefully this is less of an issue. The GAT might very well be a better human facing thing







Philip Zucker: It does appear that a project intending to be a pure Julia version of these solvers was underway [https://github.com/roberthoenig/FirstOrderLogic.jl](https://github.com/roberthoenig/FirstOrderLogic.jl) , but the commit history makes it seem like it may be in hibernation. It would take many years of work by someone very good to get even close to replicating the power of existing provers. I have a similar concern for any bespoke solver that is customized to GATs.







Philip Zucker: @Evan Patterson The transformation you're suggesting makes sense to me. Partial functions rewritten as a relation seems like a good approach and something I looked into. What I'm hoping is happening in the new suggested translation is that axioms about partial functions are only satisfied when the proper typing exists and otherwise returns "garbage", in other words the properties of the function symbols are unconstrained. To me this is reminiscent of somethings I've seen occur for example in the Hilbert epsilon operator [https://en.wikipedia.org/wiki/Epsilon_calculus](https://en.wikipedia.org/wiki/Epsilon_calculus) , which returns an integer satisfying a property if it exists, but otherwise returns arbitrary garbage integers. I think the approach has to be unsorted FOL in this case because that's the only way we can emulate the type dependency. I am not hyper confident that this translation makes sense, but I think it does preserve the universal quantified character of the original theory







Philip Zucker: I like that it looks like a very straightforward syntactic transformation of GATs.







James Fairbanks: I agree that FOL provers are much more stable technology, but this also reminds me of a recurring problem in CS where we try to shove everything into the simplest abstraction that works instead of building tools for the problem at hand. Complexity theory is full of this, eg. "polynomial time reduction to a known problem". That polytime reduction doesn't have to preserve any other structure but the input/output pairs. For example, it doesn't have to respect approximate solutions, which is why you get different answers about complexity of solving a problem and complexity of approximating a solution.







I think about this all the time because CS uses graphs for everything but you have to remember what the graph means because you forgot all the problem specific structure when constructing the graph. For example solving a pipeline routing problem as a max flow problem. You discarded the geometric nature of the pipeline network when representing it as a graph, which is good for getting an algorithm for solving small pipeline problems. But when you want to scale up to large problem instances on parallel computers, you need to reconstruct that geometric information in order to decompose the problem into nearly independent subproblems that can be solved in parallel. I have a graph that represents the pipeline network, but there is information about spatial layout and the subtleties about junctions and gas interchanges that gets lost by that representation.







In the same sense sense, everything can be expressed in FOL, but just because you can encode it in FOL doesn't mean that is the best way to solve the problem. Since ATP won't be on the Catlab roadmap for a long time, having a bridge to FOL provers would be the way to go until someone comes along with the need and skill to write an ATP for GATs on top of Catlab.







Philip Zucker: Yup, I agree. I have a personal preference for finding ways to jam problems into a linear programs, SDPs, mixed integer program, SAT problem, or SMT problem and consider doing so a pragmatic choice not a theoretical one since the solvers are so dang good. I think it shows that all the people who built those technologies were right, that they are a fruitful intermediate language for wide class of problems. Graphs _are_ an unreasonably effective abstraction but now we're in the unfortunate position of trying to find a less obvious structure that can beat them for some purposes, the higher hanging fruit.









