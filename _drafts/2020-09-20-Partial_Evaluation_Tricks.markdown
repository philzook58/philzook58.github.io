---
author: philzook58
comments: true
date: 2020-09-20 03:24:45+00:00
layout: post
link: https://www.philipzucker.com/?p=2677
published: false
slug: Partial Evaluation Tricks
title: Partial Evaluation Tricks
wordpress_id: 2677
---




I have more stuff in the coq metaocaml post













7/4/20







Partial evaluation has some tricks







Basically







  1. Do CPS
  2. Specialize branching






Partial evluation of AExp, BExp







staged-fun. And this is already available in a friendly Haskell compiler near you.







It really helps to have a system where you can see the result of the partial evaluation. You may be surprisied by what you see. Coq is decent.  But you can also get the dump of 







The optimizations that partial evaluation achieves are also I suspect the optimization achieved by the folklore CPS transformation for making faster code. Part of the optimization an optimzing compiler _is_ partial evaluation.







Some of the things that people like to do in the type system can also (perhaps even more naturally) be done with a partial evaluation system. 







In systems like Ocaml and Haskell, the types are fully erased at runtime, so that any type level computation becomes compile time computation.







One thing that is done is to convert something into a special type by checking that it obeys teh predicate. Like taking [a] -> Maybe (Vec 10 a) needs to confirm that the length of the list is in fact 10. Then that fact is recorded for further use, inviting possible optimizations. But we can do basically the same thing. is_length_10 : code [a] -> code bool. And type vec = (int * code [a])







Like what about a  (code int, Z3.expr) as a kind of refined int type. 













Coq is from one persepctive a kind of janky restrictive Ocaml with steroidal metaprogramming capabilities. 







We can use this to perform rewrite rules. It isn't quite as straightforward as you might hope. When you perform rewrites in a proof, I'm not so clear how to get the new forms reflected back. But there is at least one trick, you can use an existential variable and then unify it at the end.







The canonical fusion is `map f . map g = map (f . g)` It avoids two passes over the same structure.  An even better fusion is build/fold fusion. If you build up a big structre just to consume it immediately, this can often be fused into 







Here are some examples using rewrite rules to fuse






    
    <code>Lemma idea2: { q : list nat -> list nat | forall l,  map S (map S (map S l)) = q l}.
    Proof. eexists. intros. Print map_map.
           (* assert  (map S (map S (map S l)) = map S (map S (map S l))). *)
           pose (map S (map S (map S l))) as opaque_lhs .
           assert (opaque_lhs =  map S (map S (map S l))).
           reflexivity. 
           rewrite map_map in H. rewrite map_map in H.  unfold opaque_lhs in H. rewrite H. auto. Defined.
    Print idea2.</code>







Recursion schemes in coq.







MetaOcaml in coq. A similar trick can be. Coq by it's nature doesn't appear to be so super concerened about efficiency differences in implementations. Things that are equal under. MetaOcaml allows controlled inlining and other partial evaluations at compile time in order to create more efficient programs that remain clearly written.







MetaCoq. Why have I not even downloaded it?







[https://youtu.be/fJ5HHvWZWfc?t=7584](https://youtu.be/fJ5HHvWZWfc?t=7584) Modal analysis of metaprogramming







This reminds of well-typed ASTs. Sometimes those well typed asts have an explicit slot for contexts. In some sense, an introspective well typed metaprogramming langueg should reflect the surface language into a well typed ast. Pure opaqueness is a cop out. It is acceptable but not desired.







box letbox vs box unbox



