---
date: 2023-07-13
layout: post
title: "Egraphs are Ground Rewrite Systems 2: E-matching"
description: Connecting E-Graphs and Term Completion
tags: egraphs term-rewriting
---

A further checkpoint on the ideas [here](https://www.philipzucker.com/egraph-ground-rewrite/). It's good to just dump stuff out there.

Buyer beware. I think the basic ideas are right, the details of the code as it stands are probably wrong and definitely slow.

I am also writing way more checks than I can currently cash about lambdas and theories. But I still see promise.

# Ematching on GRS

The ground rewrite system implicitly defines a possibly infinite set of terms. It is the set of terms that reduces to a subterm on the left or right hand side of the system. Taking a term and reducing an effective method to check if a term is in the egraph term set `val mem : term -> egraph -> bool` .

To generate/enumerate this set, one can start with all the terms and subterms in the GRS, and run the rules backwards (right to left) to produce the set of terms. This will produce larger and larger terms with respect to the term ordering in use, which can be useful (you can know when to stop). `val iter : egraph -> term Seq.t`

The ematching problem is, given a syntactic pattern, find a term in this implicit set of terms and return bindings to the variables of the pattern. `val ematch : pat -> egraph -> subst list`. In principle this could be implemented using `iter` and filtering using ordinary pattern matching. This would not be that efficient, but it is conceptually simple.

I use the phrase eclass somewhat interchangeably with the canonical term of that eclass. The set of terms that results from backwards rule application is the eclass. Every term in this set reduces to a unique smallest representative term under reduction by the GRS (because we have a total term ordering and build a confluent system), so they are in 1-1 correspondence.

## Top Down Ematching
The typical way I've seen ematching done is [top down ematching](https://www.philipzucker.com/egraph-2/), which recurses down the pattern while searching the egraph.

Simple pattern matching ignoring the egraph would look like this. We represent match failure as returning the empty list and pattern success as returning an assoc list of the substitution.

```ocaml
let match_ pat t : subst list =
  let rec worker pat t subst =
    match (pat, t) with
    | Const x, Const y ->
        if String.equal x y then [ subst ] else []
    | App (f, x), App (f2, x2) ->
        List.concat_map (fun subst -> worker x x2 subst) (worker f f2 subst)
    | _, Var _ -> failwith "ematch does not support Var in term"
    | Var x, _ -> (
        match List.assoc_opt x subst with
        | None -> [ (x, t) :: subst ]
        | Some t' -> if equal_term t t' then [ subst ] else [])
    | App (_, _), Const _ | Const _, App (_, _) -> []
  in
  worker pat t []
```

Ematching requires only a light adjustment to this. Now in addition to looking for exactly syntactic matches we can also try applying a rewrite step that would make the ematch work.

Applying the rewrite rules once in reverse is very much analogous to expanding an eclass into its enodes. The `invert` function takes the Map defining the GRS and reverses the keys and values. The values are not necessarily unique in the right hand side so the inversion is `term list TermMap.t`.

```ocaml
let invert (e : egraph) : term list TermMap.t =
  TermMap.fold
    (fun k v acc ->
      TermMap.update v
        (fun ot -> match ot with Some x -> Some (k :: x) | None -> Some [ k ])
        acc)
    e TermMap.empty

let ematch e pat t : subst list =
  let eclass = invert e in
  let rec worker pat t subst =
    match (pat, t) with
    | Const x, Const y ->
        if String.equal x y || equal_term (find e pat) (find e t) then [ subst ]
        else []
    | App (f, x), App (f2, x2) -> (
        (* Boring case that occurs in ordinary matching *)
        List.concat_map (fun subst -> worker x x2 subst) (worker f f2 subst)
        @
        (* Interesting case where we match via a simplification rule *)
        match TermMap.find_opt t eclass with
        | None -> []
        | Some enodes -> List.concat_map (fun t -> worker pat t subst) enodes
        (* The kbo order might protect us here. Naively this looks like an infinite loop *)
        )
    | _, Var _ -> failwith "ematch does not support Var in term"
    | Var x, _ -> (
        match List.assoc_opt x subst with
        | None -> [ (x, t) :: subst ]
        | Some t' -> if equal_term (find e t) (find e t') then [ subst ] else [])
    | App (_, _), Const _ | Const _, App (_, _) -> []
  in
  worker pat t []
```

In the canonicalized GRS, there are no terms that are both on the left and right hand side. This is because such a term would get reduced away during canonicalization using the R-simplify rule. This, combined with the fact we are using a "good" term ordering, is why the `| Some enodes -> List.concat_map (fun t -> worker pat t subst) enodes` does not result in an infinite loop (I think).

This assumes we have a given term we are trying to match to the pattern modulo the equalities in the egraph.

To actually search over the egraph, we need to enumerate the possible starting terms to match in.

```ocaml
let ematch_all e pat =
  let terms =
    TermMap.fold
      (fun t1 t2 s -> TermSet.add t1 (TermSet.add t2 s)) (* wrong i need to add subterms too *)
      e TermSet.empty
  in
  let terms = TermSet.to_seq terms in
  Seq.map (ematch e pat) terms
```


## Bottom Up Ematching

Top down ematching has at least one bulk total guess in it: what is the root eclass we are searching for the pattern in.

In our application of equality saturation, we are not really interested in searching inside a particular eclass, we are interested in matching inside the entire egraph. It is not obvious we should break down the problem in this way. Perhaps it is better to bulk search the entire egraph without first enumerating roots.

Suppose for example we had a pattern that had only one variable in it. We might as well use our already spent nondeterministic guess just guessing this variable. The variable can only be bound to an eclass inside the egraph. Then we just need to build up the pattern with that guess substituted in, reduce the term, and then see if that reduct is in the egraph.

Altogether, these are capabilities we already had and are easy to express.

```ocaml
let bottom_up (e : egraph) pat =
  let eclasses = eclasses e in
  let elist = TermSet.to_seq eclasses |> List.of_seq in
  let rec worker subst pat =
    match pat with
    | Const _s ->
        let t = reduce e pat in
        [ (t, subst) ]
    | Var v -> (
        match List.assoc_opt v subst with
        | None -> List.map (fun eid -> (eid, (v, eid) :: subst)) elist
        | Some eid -> [ (eid, subst) ])
    | App (f, x) ->
        let* f, subst = worker subst f in
        let* x, subst = worker subst x in
        let eid = reduce e (App (f, x)) in
        if TermSet.mem eid eclasses then [ (eid, subst) ] else []
  in
  worker [] pat

```

Now, for every variable in the pattern, we add another loop of search and another factor of `#eclasses` to our complexity. Smarter joining and filtering can reduce this (joins on compatible substitutions). It is not apriori obvious that top down ematching is superior and bottom up lends itself to simpler access patterns and easier indexing.

I often come back to thinking about this discussion [Improved e-matching for ground terms](https://github.com/egraphs-good/egg/pull/74)

Bottom up ematching can be seen as more directly related to the technique of narrowing for e-matching. If we narrow a pattern variable with respect to a ground rewrite system, it will narrow that variable completely ground. Perhaps the narrowing perspective lends to more optimizations than the totally guess and check version I've described above.

I grow more confident on this point that it is reasonable to consider egglog a bottom up functional logic programming language akin to how datalog is bottom up prolog, since narrowing is part of the explanation of what FLP is.

One insight I'm excited about is that I believe "bottom up" ematching plays nicer with theories than top down ematching, but I haven't reached a point of clarity in implementation where I'm sure that's true. The thing is that in bottom up ematching, you only really need a notion of reduction, which is easier to implement in a theory specific way. You also are only dealing with very ground entities, whereas top down ematching is in some sense dealing with "less ground" residual patterns.

For example, in AC matching, it is hard to guess the right correspondence of subterms to pattern pieces top down. Whereas bottom up, we just have to normalize (sort and flatten) the current guess term.

Incrementalization feels easier to me bottom up.

These different approaches are all subsumed by 
## Term Orderings, Analyses and Extraction
Also, I said at some point in the last post that I didn't know if GRS had a notion of analyses for extraction, but I'm not so sure that's true anymore. It seems like using the analyses to build a custom ground term order and then extraction merely being reducing a term with respect to the GRS works pretty well

It is interesting to use the term ordering as the tie breaker in the directed union find. This is at least a meaningful tie breaker, whereas using max/min eid can't be all that semantically meaningful because the number of the eid itself is not meaningful (this isn't quite true because eid tends to be associated with age / distance from original terms as in the aegraph)

The design space of term orderings is very interesting. Especially when I only care about ground terms.

# Lambda
I go back and forth whether x-x = 0 is fine or not. If x is supposed to be a bound variable, x can escape its scope if you consider using it as a substitution from right to left. One can give an interpretation to terms with free variables though, maybe scope escape isn't so bad. I have a suspicion that one can use a variation of the directed union find and "scope tagging" use sites of eids to prevent this if it's worth it (scoped union finds). More definitely an issue is accidental capture. foo ?a => \x foo ?a . If you use d bruijn numbers, you need to lift free indices in ?a. If you go named, I don't know how to do alpha equiv, and you need to know there are no x in ?a (the free var set, which has been done). I dunno. I've been tinkering with adding lambda in a ground rewrite system based egraph, which I feel is a simpler arena than the relationalized egraph.

- Are lambda terms really ground?
- Do I want beta or would alpha only be good enough?

# Simple Term Rep
After fiddling with log-tk, I decided to experiment with going more bare bones, using my own maximally naive term representation. [git commit](https://github.com/philzook58/lambda-egglog/commit/b2a43af57db640030fa1eced2a3b2cfabc1b4553)
I keep having to fight the impulse to worry about performance at all. This is not my concern yet. I do not even know what it is exactly I'm trying to build.

Going for a fully curried form of ground terms. This is interesting from the perspective of attempting lambda free HOL and eventually adding lambdas.

```ocaml
type term = Const of string | App of term * term
```

It may be desirable to compress partially applied terms to a `App of term array` constructor as an optimization.
More literal types `Lit of lit` could be interesting

I'm explicitly fighting the temptation to hash cons everything and cache all term statistics like depth even though it's so easy.

# Bare bones DSLs using sexplib
A feature of ocaml that I like is autoderiving s-expression printers and parsers. Making actual parsers isn't persay that hard using parser generators, but I find they suck my energy out of a project.

This is the fastest way to get a DSL up and running after an embedded dsl. 

There is something very satisfying about having a separate file and watching your language grow.

Lispers are surely rolling their eyes at me.

This is inspired and modelled after the workflow I saw on the UW egglog project.

```ocaml
type st = { egraph : egraph; rules : (term * term) list }

let empty_state = { egraph = TermMap.empty; rules = [] }

type action =
  | Rewrite of term * term
  | Assert of term
  | Extract of term
  | Union of term * term
  | Run of int
  | Print
  | Match of term
  | Clear
[@@deriving sexp]

let pp_action ppf a = Sexplib.Sexp.pp_hum ppf (sexp_of_action a)
let info = Format.printf

let run_action st = function
  | Assert t -> { st with egraph = TermMap.add t true_ st.egraph }
  | Rewrite (lhs, rhs) -> { st with rules = (lhs, rhs) :: st.rules }
  | Union (lhs, rhs) -> { st with egraph = union st.egraph lhs rhs }
  | Extract t ->
      info "%a" pp_term (reduce st.egraph t);
      st
  | Run _n ->
      let e = canon st.egraph in
      info "%a@\n" pp_egraph e;
      let e =
        List.fold_left (fun e (lhs, rhs) -> apply_rule e lhs rhs) e st.rules
      in
      { st with egraph = e }
  | Print ->
      Format.printf "%a@\n" pp_st st;
      st
  | Match p ->
      let matches = bottom_up st.egraph p in
      List.iter
        (fun (t, subst) -> Format.printf "%a: %a@\n" pp_term t pp_subst subst)
        matches;
      st
  | Clear -> empty_state
```

# Theories

Nelson oppen or shostak makes theory integration (egraphs modulo theory) into egraphs not unusual <https://arxiv.org/abs/1207.3262> except that I have not seen a satisfactory reference on ground ematching modulo theories. The rule of thumb I am aware of from z3 is to not have interpreted symbols in you ematching patterns because it doesn’t work. I am unsure if lambda is “just another theory” or not.

Some intriguing theories:

- Multsets (AC?)
- Sets
- Linear (gaussian elimination as a rewrite system)
- Nonlinear (grobner)
- Beta normalization ?
# Blah blah blah




Normalization by evaluation

What is the interface theories should present?
User defined propagators in Z3.
Give theories new equalities, they propagate new equalities.
Theories have to hold opaque symbols.
The safest notion of theories are ones I could emulate using rules but have chosen not to for convenience and speed. AC fits in this category

Possible interface jazz:
```ocaml

type ctx
type t
compare
equal
solve : term -> ctx -> t
inform_eq : term -> term -> ctx -> (t * t) list * ctx



module type Theory = sig
  type 'a t
  type ctx
  val norm : ctx -> 'a t -> 'a t
  val compare : ctx -> ('a -> 'a -> int) -> 'a t -> 'a t -> int 

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val reify : term -> t term 
  val reflect : term t -> term
end

```


## Generic Join Through a Term Lens

## Discrimination Tries

suffix tries

ground terms are even easier to search than strings. You only need to search subterm positions instead of all positions.
##

## 

Hash consing
Memoizing size / lattice data in the nodes. Off to the side or in the node itself?

Pivoting - Can we change term orderings mid stream? Is this sound? Fruitful?

Go ground, young man.

Contexts

GRS is even more extreme in the "terms are important" direction that as I'm considering it, there are no eids at all anymore. Only terms. This also helps context a bit, since subterms in less flattened terms can derive context from their parents.

Intrinsic support for auto zippers as a method for treating context.
