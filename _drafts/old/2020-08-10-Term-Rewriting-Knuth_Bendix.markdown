---
author: philzook58
comments: true
date: 2020-08-10 20:35:44+00:00
layout: post
link: https://www.philipzucker.com/?p=2892
published: false
slug: Knuth Bendix
title: Knuth Bendix
wordpress_id: 2892
---
2020-12-07


Newman's lemma weak conlfuence + termination => strong confluence
http://www.cs.tau.ac.il/~nachum/papers/klop.pdf - Klop review on term Rewriting. Cody's RG pick
critical pair for terms - 1 is unifiable with the other.

Similarity to grobner basis
similarity to gaussian elimination

Knuth Bendix asks a lot though. The more obvious approahc is to heuristically aspply rewrite to your actual problem rather than try to completely solve all possible problems up front. Why not do this fro grobner? It sounds stupid for gaussian though. Maybe. Just sort of greedily try to write your query polynomial in terms of the ones you have? This might be the analog of some iteraitve scheme like gauss jacobi.


Finite state machines are rewrite systems with each state being a single simple constant



Term Rewriting using linux command line tools

The string search and manipulation tools are very powerful and efficient. They compile queries like grep into simple machines and such I think.

There's a big difference between ground and non ground terms. They appear subtly different when latexed, but the are way different beats
Ground terms equation proving can be done through the e graph efficiently.

Ground term rewriting seems to be identical to string rewriting. Just layout serially a traversal of the term.

It seems like named pattern string rewriting and variable term rewriting might be close enough

You could imagine

((x + 0) + 0 + 0) laid out as + + + x 0 0 0. and the found ground rewite rule + x 0 -> x being applied iteratively.

Labelling shifts:
f(g(a), b) ->   f +0 g +1 a -1 b -0

the pattern 
f(?x)  -> ?x
 becoming
 f +0 <x> -0 -> <x>
 f +1 <x> -1 -> <x>
 f +2 <x> -2 -> <x>
and so on to some upper limit
We could occasionally renormalize maybe if there are no +n -n pairs remaining.
then shuffle all the above ones down.
Ok but what about something that increases the depth
x -> f(x)
... hmmm.

And if we number from the bottom?

f +2 <X> -2 -> <X>

and
<X> -> ??? Well a raw pattern is pretty shitty
f(x) -> f(f(x)) becomes
f +n <X> -n -> f +(n+1) f +n <x> 
Yeah. Numbering from the bottom is better. We don't have to 

f(stuff,stuff)
f +n <X> -n +n <Y> -n

even without enumerating
plus +<n1> <X> -<n1> +<n2> <Y> -<n2> 

Oooh. We have to enumerate every combo of possible subterm depths.

Hmm. This adjust levels

http://matt.might.net/articles/sculpting-text/

A unique terminator for the subexpression is the point. 
f +2 (^ -2)* -2

could have a counter per symbol. per symbol depth.
f1 ( yadayada) \f1

fa1 <X> fb1 <Y> fc1


huh. What about the CPP? Won't that basically work?

This is horribly inefficent because it'll expand out huge terms.
And big backtracking jumps. Or rather big seeks while it tries to find the next spot to go to. The next argument of f.

For ground term rewriting it seems actually reasonable and faster than having indirections. We can't have sharing though. That is a bummer.Maybe with zip.
Unless our goal is simplifcation.


using the rule 

We could try to use the e-matching strategy where we iteratively instantiate fixed ground rewrite rules into the sed file itself?

Instead of using parenthesis, one could use numbered enter level exit level. And then bound the number of levels.
Each term rewriting becomes a string rewriting (with named regex holes ) replicated by the number of supported levels.

using sed on itself we might be able to implement knuth bendix

One could compile into a human unreadable huffman encoded like thing


https://superuser.com/questions/1366825/how-to-recursively-replace-characters-with-sed looping in sed
You can gnu parallel into chunks
grep is much faster. If terms are rare, maybe find using grep first?

Suffix trees can store every subterm of ground term with efficient query.

https://spencermortensen.com/articles/serialize-a-binary-tree-in-minimal-space/ an interesting perspective on tree serialization
catalan numbers. We know size of tree if we give elements. 
https://www.educative.io/edpresso/what-is-morris-traversal woah. Bizarre. It mutates the true as it goes down it and store
Kind of reminscent of dancing links in a way

f 20 90 190 yada yada yada could desribe links to the approprate spots.
This would be the analog of flatterms. 

There is something like encoding lambda terms with de bruijn. vs unique signifiers.
If we could encode the unique signifiers in a way such that they never collide.

There is something to that we're kind of converting to rpn.
https://github.com/GillesArcas/numsed
https://github.com/shinh/sedlisp 

http://cl-informatik.uibk.ac.at/teaching/ws20/trs/content.php term rewriting course mitteldorp
https://github.com/bytekid/mkbtt - does knuth bendix completion. There is a web interface
https://github.com/bytekid/maedmax ? 
http://cime.lri.fr/ cime


KBO
RPO
LPO

stable under subsitition
stable under contect
terminating

kbo - maps all variables to number that is less than all actual symbols
Then upon subsitution, the cost can only increase
first check variabnle count is ok
complicated tie breaking
https://www.cs.miami.edu/home/geoff/Courses/TPTPSYS/FirstOrder/SyntacticRefinements.shtml




https://www.regular-expressions.info/recurse.html

2020-07-17 from "Bash"
There is a thing I've heard that bash and piping is shockingly performant for some tasks. Stream processing and stuff.

You can kind of get database operations  

  * wc - word count
  * grep
  * head
  * sort - can sort of columns?
  * uniq
  * awk - all kinds of crap
  * join
  * seq 1 100

http://williamslab.bscb.cornell.edu/?page_id=287

Gnu parallel [https://www.youtube.com/watch?v=OpaiGYxkSuQ&list=PL284C9FF2488BC6D1&index=2&t=0s](https://www.youtube.com/watch?v=OpaiGYxkSuQ&list=PL284C9FF2488BC6D1&index=2&t=0s)

2020-08-10

Knuth Bendix completion is interesintg. It solves the word problem

String rewriting can be use to normalize finitely presented categories sometimes. If we list the generating morphisms and the base equalities of composition, knuth bendix may be able to generate the closure, which we can use to figure out if two morphisms are the same with a guarantee.

String matching algorithms are relevant.

The Boyer Moore algorithm makes some jumps based on comparisons you've already made. These jumps can be calculated based on properties of the pattern

[https://www.sciencedirect.com/science/article/pii/S1567832610001025](https://www.sciencedirect.com/science/article/pii/S1567832610001025) - efficiency issues in the kbmag procedure. Describes using suffix trees to find critical pairs

[https://gap-packages.github.io/kbmag/doc/chap1.html#X7DFB63A97E67C0A1](https://gap-packages.github.io/kbmag/doc/chap1.html#X7DFB63A97E67C0A1) KBMAG gap package. Accessible through GAP.jl

Are the SKI combinators expressible in string rewriting? They have a tree structure and are expressed as such ordinarily. Maybe parenthesis can be used as inhibitors? Or we could have a moving evaluation marker?

    
    <code>(S) -> S
    (K) -> K
    (I) -> I
    IK -> K
    IS -> S
    II -> I
    ... all concrete
    Sxyz = xz(yz)
    
    </code>

Building a turing machien out of a string rewrite system. Have special characters represent the state. and have the patterns include the surrounding context. Enumerate all the characters in state and tape characters.

    
    <code>aSb -> acS
    aSb -> Scb</code>

Computational group theory is a thing.

Finite categories which have both finite morphisms and finite objects are approachable. It is clear that most questions one might ask about a finite category is approachable by brute force or maybe by encoding to some graph problems or SAT problem.

Finitely presented categories are the next up the chain in complexity. In this case we take a free category generated by some morphisms and some equations identifying certain composition patterns. It is less clear whether natural questions are decidable or not.

What questions do we care about:

  * Are two morphisms expressions equal?
  * Produce a morphism from object A to B
  * Confirm some mapping is a Functor
  * Confirm some functor mapping is a natural transformation.

It is my belief that some questions about these can 

The next level of category one might want to talk about is one for which you have guaranteed constructions, such as cartesian, closed, dagger, monoidal, etc. I'm not sure which of these qualifiers are compatible with being finite. [https://arxiv.org/abs/0908.3347](https://arxiv.org/abs/0908.3347)  To me, this feels analogous to being able to work with terms rather than just strings.

jk [https://www.youtube.com/watch?v=WdawrT-6Qzk](https://www.youtube.com/watch?v=WdawrT-6Qzk) gershom Bazerman Homological computation for term rewriting systems

