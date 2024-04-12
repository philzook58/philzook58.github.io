---
date: 2024-04-12
title: "EGRAPHS 2024 submission: E-graphs and Automated Reasoning"
layout: post
---

Welp, I got an abstract submitted to [EGRAPHS 2024](https://pldi24.sigplan.org/home/egraphs-2024) "E-graphs and Automated Reasoning: Looking back to look forward".

It's not anonymous submission and I asked if it's ok to write this BP.

So here's the pdf <https://github.com/philzook58/egraphs2024-talk/blob/main/egraphs2024.pdf>

Maybe I'll get some comments for edits before the deadline in a couple hours. If I don't end up making the cut, oh well. It was good to write it up.

This was mentally a tough one. As I was writing on Wednesday I got driven into such an incredible funk of self reproach and loathing that I thought I would never feel happiness again. But then on thursday I felt ok. I have no idea how to write papers and get very stressed out by it.

It's interesting. I think I can tell that from the eyes of others, my self doubt of this sort seems ludicrous. I'm not an idiot. I'm in the ballpark of being halfway through life (a third? the singularity might help.), when exactly would I have done enough for those feelings to go away? It appears confidence and self worth comes from within and that no amount of reading new math textbooks or twitter likes is going to heal your self doubt. On the other hand, I was once told a story of a Nobel prize winner, behind closed doors, saying that it felt pretty great. So maybe I'm wrong. Maybe I just need to win a Nobel prize. Should get on that.

I guess I'm bringing this up in the hopes that you, dear reader, take it easy on yourself. You're good. I believe in you.

I do worry that the subject matter is just an accumulation of things already pointed out. But perhaps that is the value. It is very similar in some parts to posts Yihong <https://effect.systems/blog/ta-completion.html> and Oliver have written. The "joy" of competing with younger smarter peopler. But I think the emphasis is very different and there is a new central thesis there.

I was writing about this and trying to implement it using pieces of zipperposition last year <https://www.philipzucker.com/egraph-ground-rewrite/> . I lost the thread for some reason. I think I was exhausted by those two posts, but also generally burned out and depressed. I'm doing a lot better. I hope to reimplement more stuff from my new perspective in python blog posts before the conference.

The battle plan is:

- ground knuth bendix ordering
- ground knuth bendix completion
- ground superposition

And maybe sprinkle in some nominal or miller unification in there. This functionality ought to be sufficient to have a contextual, lambda supporting egraph rewriting system. It will not be hyper performant obviously, but it will make sense.

Do some cool diagrams or animations for my talk? Manim?

It was a great relief to have Max say that works in progress were ok. I do think I have enough to be worth 15 minutes of peoples time and I really do think the e-graphs as ground rewrite system perspective clears up a lot of mysticism about how one might approach e-graph extensions.

Really the abstract is written almost against my own myopic and ignorant perspective from a few years ago in regards to the greater context of e-graphs in automated reasoning. Certainly automated reasoning experts must think there is no content to this talk. E-graphs are congruence closure, congruence closure is a subproblem of those treated in the 60s. This is all in the textbooks (term rewriting and all that, automated reasoning: an introduction). But I hadn't read any of those textbooks at that point and a drive to understand e-graphs has been the thread leading me through these things. I haven't seen anybody say this all in exactly the way I'm saying either though. I dunno.

## Bits and Bobbles

I became quite overwhelmed trying to literature review AC techniques in the automated reasoning literature. It is a swamp. Bill McCune mentions resisting implementing it for a long time. His untimely death is a huge shame. We all really missed out something there.

<https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=419b4ebf8d78060093fd28b2e7d10b8b2623442b>
Shostak's Congruence Closure as Completion

<https://arxiv.org/pdf/2109.03720.pdf> Congruence Closure Modulo Permutation Equations
<https://arxiv.org/abs/2310.05014> Congruence Closure Modulo Groups
<https://lmcs.episciences.org/11073/pdf>  MODULARITY AND COMBINATION OF ASSOCIATIVE
COMMUTATIVE CONGRUENCE CLOSURE ALGORITHMS ENRICHED WITH SEMANTIC PROPERTIES - deepak kapur

The rewriting rule laboratory seems really cool

Hey I got a blog this week after all!

## The eclipse

I saw the eclipse this monday with Amanda and her parents. It was rad. We stayed at there play in NH and drove up to the side of the Androscoggin south of Errol. I have to downplay how cool it was to people who didn't go. We only hit 2 hours of traffic on the way back, but Raffi hit over 12? That's nuts.

# Drafts bits

# A Rosette Stone: Egraphs as ground rewrite systems

Egraphs from the Term Rewriting Lens

This talk is about the location of egraphs within the solution space of term rewriting which is a subset of equational reasoing which is a subset of automated reasoning.

There is an intuitive appeal to egraphs. The bipartite diagram showing enodes and eclasses does more than a lot of text for deomsntrating the basic idea.

There is a long history of the field of term rewriting and in particular completion.

The egraph itself is a compact representation of a system of ground equations over terms

Completion is a methodology to do automated reasoning over equations. The starting point is terms with variables in them.

The basic algorithm is simple:

- find possibly diverging (critical) pairs
- simplify them
- Orient them according to a term ordering into a rewrite rule and add to your equation set

This process is not guaranteed to terminate, but it is complete expansion of
It is intuitively appealing that you may want to shrink your set of equations. This makes the algorithm more subtle.

Fact: Ground completion is guaranteed to terminate (under the appropriate term order)

Tree Automata. It has been noted that egraphs are tree automata. tree automata themselves can be represented as ground rewrite systems.
Noting that egraphs are ground rewrite systems is an observation in the same vein, with close to the same content. I find it subjectively find it conceptually superior in that rewrite systems are closely related to the task of equational reaosning, whereas tree automata are couched in the language of automata theory, a more unfamiliar entity.

The egraph offers a graphical intuition that has been crucial to it's popularity and user for pragmatic purposes.

The egraph communities focus on compiler optimization is different from the most traditional automated reasoning problems.

The operational character of egraph saturation and datalog is not distinct from the Argonne school.

# Union Finds As Completion

Given a set of equations between 0-arity constants.
We can pick some arbitrary total ordering go our constants to orient these equations.
a = b
a = b
c = b
d = e
{a=b;c=b;d=e}  {}
------------------

orient
       {b -> a; c -> b; d -> e}
-------------------------------

simplify
c -> a

Now it is a compressed union find

```python
class UF():
    def __init__(self):
        self.rules = {}
    def find(self, x):
        # `find` reduces x with respect to the current rules (x -R-> retval)
        while self.rules.get(x) != None:
            x = self.rules.get(x)
        return x
    def union(self, x, y):
        # Do incremental completion starting with
        # (E,R) == ({x = y}, self.rules )
        x1 = self.find(x) # SIMPLIFY  ( {x1 = y} , R)
        y1 = self.find(y) # SIMPLIFY  ( {x1 = y1}, R)
        if x1 == y1: # TRIVIAL ({x1 = x1}, R)
            return x1 # (Empty, self.rules)
        else:
            if x1 < y1: # the "term order"
                x1,y1 = y1,x1 # swap
            self.rules[x1] = y1 # ORIENT  (empty, R U {x1 -> y1})
            return y1
    def canon(self):
        for lhs,rhs in self.rules.items():
            self.rules[lhs] = self.find(rhs) # r-simplify

e = UF()
e.union("a", "b")
e.union("c", "d")
e.union("a", "d")
print(e.rules)
e.canon()
print(e.rules)
```

# Egraphs as completion

For every term in a set of ground equations.
The flattening transformation can be achieve by creating fresh ground symbols for every function in the original set of equations

foo(biz(baz), bar)

bar = e1
baz = e2
biz(e2) = e3
foo(e3) = e4

With a ground term ordering that puts every e less than a function symbol will orient the system into the form

bar -> e1
baz -> e2
biz(e2) -> e3
foo(e3) -> e4

If we write e as q, this becomes indeed the definition of a tree automata as has been noted.

# Egraph Saturation

In the automated reasoning community, there is a history of incomplete strategies.

One example is the set of support strategy.
Hyper resoluttion
UR (unit resulting resolution)

Tree Automata completion

## Ematching a rewrite system

# WIP: Extending the Egraph

The egraph is a peculiar data structure which has a had a lot of difficulty being extended to non-first order use cases.

There are a variety of directions to extending egraphs

## Lambdas

The crucial step for the flattened form is no longer possible

lam x. foo(bar(x, biz))
biz = e1
bar(x,e1) -> e2(x)
foo(e2(x)) -> e3(x)
lam x. e3(x) -> e4

lam x. foo(bar(x, \z biz(z)))  = lam x y. foo(baz(x,y), y)
e4 -> e5
\ x y -> baz(x,y) = \x y -> e6(x,y)
foo(e6(x,y), y) -> e7(x,y)

\z e3(z) = e4

Does completion still terminate?
bar(X, biz) -> e5(X)

So this is maximal lambda lifting.

We're naming subexpresions, which is a lot like some kind of closure conversion

bar(x,y) -> e

\x. 0 + x = \x. x + 0
0 -> e1
e1 + X -> e2(X)
X + 0 -> e3(X)
e3(X) -> e2(X)

obviously this is not ground anymore.

alpha atoms. Ground nominal completion
e1 + x -> e2(x)

The persepctive also does not _require_ the normal form of the egraph. A compound term
bar(foo(x),x) of alpha equivalent pieces can't be split

nominal techniques.

## Context

A notion of context has been been necessary for describing contextuall correct rewrites.
`if x == 0 then y + x else x * y`. Contextually, we know that y + x = y in that branch. But we cannot globally equate x = 0 or else the then branch will perform a false optimization.

The contextual extension of knuth bendix completion is the superposition calculus.
In particular superposition of ground clauses.
Is this guarantee to terminate?
Ground superposition.
~ foo = bar | a = b.

ASSUME nodes
colored egraphs

## Backwards Search

## Sketching and Hints

## Eager Rewriting in Egraphs

Eager rewriting is presumably the addition of an already terminnaing confluect rewrite system to a set of ground equations.
Demodulation

# Term Orderings and Extraction

The original point of term orderings are they are generalization and sophistications on the idea that in most cases we want smaller terms.
One sophistication is using a knuth bendix ordering that allows adding weights to different function symbols. This correspond nicely to the notion of extraction with weights.
Running the compiled ground system _does_ extract the minimal term.

# Tree Automata

The field of automata

NFA can be easily translated to a ground rewrite system. For every edge

A string rewriting system

$qx -> q$
Can be encoded in terms as

$q(x(A)) -> q(A)$

Ground form.
x(q) -> q

NFA
x(q) -> q1
x(q) -> q2

Overlap pairs are both possible transitions
q1 -> q2. Hmm. Adding in this transition is not sensible.
Yeah, they aren't equal regardless of context. Huh

q(x(A)) -> q1(A)
q(x(A)) -> q2(A)
No this isn't determinization

GRS + eager rewrite rules

Yihong's post
automata talks

Pictures:

Automata post <https://remy.wang/reports/dfta.pdf>
Auto2
<https://uwplse.org/2023/11/14/Eqsat-theory-i.html>
<https://effect.systems/doc/egraphs-2023-theory/paper.pdf>

{|
|-
| '''Delete'''
| ‹ ''E''∪{''s'' = ''s''}
| , ''R'' ›
| ⊢
| ‹ ''E''
| , ''R'' ›
|-
| '''Compose''' &nbsp; &nbsp; &nbsp; &nbsp;
| ‹ ''E''
| , ''R''∪{''s'' → ''t''} › &nbsp; &nbsp; &nbsp; &nbsp;
| ⊢  &nbsp; &nbsp; &nbsp; &nbsp;
| ‹ ''E''
| , ''R''∪{''s'' → ''u''} › &nbsp; &nbsp; &nbsp; &nbsp;
| if {{math|''t'' {{underset|''R''|⟶}} ''u''}}
|-
| '''Simplify'''
| ‹ ''E''∪{''s'' = ''t''}
| , ''R'' ›
| ⊢
| ‹ ''E''∪{''s'' = ''u''}  
| , ''R'' ›
| if {{math|''t'' {{underset|''R''|⟶}} ''u''}}
|-
| '''Orient'''
| ‹ ''E''∪{''s'' = ''t''}
| , ''R'' ›
| ⊢
| ‹ ''E''
| , ''R''∪{''s'' → ''t''}   ›
| if {{math|''s'' > ''t''}}
|-
| '''Collapse'''
| ‹ ''E''
| , ''R''∪{''s'' → ''t''} ›
| ⊢
| ‹ ''E''∪{''u'' = ''t''}
| , ''R'' ›
| if {{math|''s'' {{underset|''R''|⟶}} ''u''}} by {{math|''l'' → ''r''}} with {{math|(''s'' → ''t'') ▻ (''l'' → ''r'')}}
|-
| '''Deduce'''
| ‹ ''E''
| , ''R'' ›
| ⊢
| ‹ ''E''∪{''s'' = ''t''}
| , ''R'' ›
| if {{math|(''s'',''t'')}} is a [[critical pair (logic)|critical pair]] of ''R''
|}
