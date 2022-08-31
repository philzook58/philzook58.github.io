---
author: Philip Zucker
date: 2020-11-16 19:20:24+00:00
layout: post
title: Separation Logic
---


https://blog.sigplan.org/2020/03/03/go-huge-or-go-home-popl19-most-influential-paper-retrospective/

There is a theme that "special" logics are implicitly talking about something. The two examples are temporal logics, which are implicitly talking about some kind of notion of time, and separation logic. I suppose intuitionistic logic could be put on the same pedestal.


Dynamic assertions of separation logic queries. Programmers like these. Can be written in host language. Can be turned off. Useful debugging and documentation tool. Gets people thinking about the right stuff. Lightweight verification.
Cody had the idea that garbage collectors must already be doing a lot of the work necessary.
Might be an interesting 
&& is easy
(heap, bool) * (heap, bool)

emp * (x -> y)
x.head -> y is   ([x.head] , x.head === y)
emp is ([], true)
(x, a ) * (y, b) = ( x ++ y,  noverlap(xs, ys) && a && b )

nooverlap(  )

Using physical equality to reify the heap graph.


A language that is low level enough
What about a seperation logic fuzzer?

Shape analysis is talking about something similar. It tracks graphs https://research.cs.wisc.edu/wpis/papers/cc2000.pdf  Null? May alias, must alias, others. An abstract domain for heap states.

Abstract domain of other graphs. Armando had that one class.

Heaps as partial maps. Heaps as graphs?



strong equality
=== 

Points-to analysis



Compiling speration logic to Z3. I'd want to representy maps.
The big shift for me is that seperation logic wants to talk about partial maps/functions.

Choices for map:
association lists
Sets of tuples
Abstract definition with axioms



https://stackoverflow.com/questions/52313122/map-data-structure-in-z3 dafny axioms for maps. Maybe use this to model
 https://github.com/Z3Prover/z3/issues/811 pointers to seperation logic stuff in smt
viper has seperation logic?

https://alastairreid.github.io/RelatedWork/notes/separation-logic/

CVC4 for automatically checking simple seperation logic.



https://sl-comp.github.io/


Chris : Sequent and Hoarse are similiar
Could you intersperse tactics and commands? {A /\ B }split{A, B} drop A { B } 
apply C x { x : B,  } 
if() {} {}


What is logic?

Logic can mean discussion in prose the faculty of human reasoning.

Logic is manipulation of syntax according to rules that seem to demonstrate the truth of something to people. Syntax in my mind is typically a tree data structure. The rules are functions that can inspect the data structure and output a changed out if it fits their criteria. The things that i wish to prove are usually mathematuical statements.

Logic is ~ first order logic ~ boolean logic. If something feels like a small change from these, then i also accept it as a logic. This occurs transitively, so the subjects which I accept as logic are changing with time.

Logic is anything with horizontal bars.

What is physics? It's what physicist's do. The interests of people who call themselves physicist's diffuse over centuries. Perspectives widen.

The imperative curry howard correspondence. Chris put forward that the command in hoare logic is the analog of turnstile. What makes hoare logic a logic?

What makes a reduction relation not a logic? Is it a logic?

What is "the logic" and what are the subjects, the axioms?

The heap is modeled as a partial function. Concretely then, the heap can be modeled conveniently as a dictionary for the purposes of simulation or interpetation, which is a finite data structure familiar and readily available in most languages. `heap = {}`. The seperating conjunction is non-deterministic or slightly under specified in that it does not tell you how to split the dictionary. You'll need to perform search.

    
    <code>def split(d): # recusrive definition of all splits. 2^numkeys
       k = d.keys()[0]
       del k d
       for d1,d2 in split(d):
          yield d1+k, d2
          yield d1, d2 + k</code>


You can model program behavior inside a logic. Hoare logic is intuitively not a logic to me.

That something that is a framework for truth has explicit reference to a heap inside of it feels insane.

The easiest thing that sometimes feels so trivial or useful is to intrepet the syntax of a logical statement and see whther a particular example. For example $latex x >\gt 3$ is a statement that requires a value of x to interpret it's meaning. Another statement is $latex x \gt 4$.

The logic and the metalogic.

Separation logic vs temporal logic. In some light sense, seperation logic is a spatial logic kind of how temporal logic with time. Not the full properties of space, and not 2 or 3 or 4 dimensional space either.


Separation logic gives us lightweight partial functions for some purposes. Apparenlty it's about partial commutative monoids, for which combining definitions of partial functions is one useful example

We do not intrinisically want to support pointer airthmetic. We need not have references be integers. There are still interesting questions about aliasing

  * Reynolds course  https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/cs818A3-11.html Reynolds has a 2006 course as well https://www.cs.cmu.edu/~jcr/seplogic.pdf 2001 review paper
  * https://iris-project.org/tutorial-material.html Iris tutorial
  * https://cacm.acm.org/magazines/2019/2/234356-separation-logic/fulltext ACM survey ohearn
  * https://www.chargueraud.org/teach/verif/
  * VST, Bedrock
  * Frama-C ?
  * https://www.youtube.com/watch?v=ZmqvuxORL88&list=PLiHLLF-foEez5Dis-VqoGcg3WepdMh4XT&index=25&ab_channel=MicrosoftResearchMicrosoftResearchVerified OPLSS summer school 2016. Hoare triples as indexed monad.
  * verifast, small foot
  * https://fbinfer.com/docs/separation-logic-and-bi-abduction/ facebook infer
  * http://staff.ustc.edu.cn/~fuming/papers/p97-cao.pdf veryfing C in coq. some useful references 

One way we understand what a logic is is by seeing what it is talking about. It's semnatics. The syntactical rules of the logic correspond with aspects of it's models

A very useful method for me to understand computer science and logic papers is to translate the inference rule style notation into some function or relation. Often a checker function is easiest. The syntax of computer science notation (see Guy Steele talk) is off putting and confusing to me. You can directly translate stuff into inductive relations in Coq often. What about prolog?

```
data Addr = Int -- Many choices here. It is interesting to consider a finite set of addresses
data Value = Addr Addr | Bool Bool 
data HeapProp = Star HeapProp HeapProp | Emp | Singleton Addr Value |
type Heap = Map Addr Value
hasprop :: HeapProp -> Heap -> Bool
hasprop (Star hp1 hp2) h = any [  hasprop hp1 h1 && hasprop hp2 h2  |  (h1,h2) <- split h ]
hasprop Emp h = isempty h
hasprop (Singleton p x) h = h == (singleton p x)

``` 

The sentences of HeapProp are are description language for sets of heaps. 

We could equivalently think about logical sentences as describing sets of integers. The free variables of the sentence tell us what dimensionality of set of the integers we are describing. Closed formula are propositions. Open formula I dunno. https://en.wikipedia.org/wiki/Sentence_(mathematical_logic) , predicate. well formed formula. So formula involving emp are in some sense open formula. And this is why it may not make sense  to consider the assertions in isloation from the hoare reasoning. However, it is commonplace also to assume universal quantification as implicit over all remaining free variables. x < x + 1  is shorthand for forall x. x < x + 1. We implcitly unversally quantify over the heap.

[https://en.wikipedia.org/wiki/Bunched_logic](https://en.wikipedia.org/wiki/Bunched_logic)

A map can be built out of the following definitions: empty, singleton a b, and the disjoint union of dictionaries `union m1 m2` . An alternative definition might be empty, `add a b m`. This is the difference between cons and append.

A sentence made of only Emp,Singleton, and Star is specificed by exactly zero or one heap. If it's impossbiel because seperation tried to use the saem address there is no heap. 

It is essential that the heap is treated as a partial map. In principle, memory is a total map of addresses to values. 

Addresses may or may not be considered abstract entities. It is not quite clear to me if they must be capable of equality comparison, but certainly inequality and arithmetic are not necessary.

Now this language is not very interesting. We can spice it up however by adding existential quantifiers. Now we have sort of hidden explicit pointers. This gives us the ability to describe very similar heaps. 

```haskell
data HeapProp = Star HeapProp HeapProp | Emp | Singleton Addr Value | Exists (p -> HeapProp)
hasprop (Exists hp) h = any [  hp k |  k <- keys h] -- ? Is this ok actually? Surely sometimes we must p to not be in the heap

-- is there a seperating quantifier?

hasprop (Disj hp1 hp2) h = hasprop hp1 h || hasprop hp2 h
hasprop (Conj hp1 hp2) h = hasprop hp1 h && hasprop h

hasprop (Not hp) h = not (hasprop hp h)

hasprop (Implies hp1 hp2) h = if (hasprop hp1 h) then (hasprop hp2 h) else True
hasprop (Wand hp1 hp2) h = all [  hasprop hp2 (merge h h1) |  h1 <- satisfies hp1] -- we have to check merge succeeds
```


But what if I wanted a set of heaps that didn't all have the same size? I need disjunction. `Disj (Singleton p x) Emp` describes a union on possibilities. In the sense that `hasprop hp` is a functional representation of a set of heaps, disj and conj take the union and intersection of these sets. Star takes the "merge" of the two sets.

    
```haskell

data Expr = Add Expr Expr | Var String | ReadRef p | 
data PointLang = Seq PointLang PointLang | Skip | SetRef Expr Expr |  
-- maybe get rid of var string and read
```

Hoare logic. You can consider features of programming languages in isolation. Assignment of variables. If then else control flow. Loops. 

separation logic and ST. Could we build liquid haskell predicates?

  *   * 
