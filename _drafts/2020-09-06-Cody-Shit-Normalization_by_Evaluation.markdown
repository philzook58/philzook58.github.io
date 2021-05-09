---
author: philzook58
comments: true
date: 2020-09-06 01:56:49+00:00
layout: post
link: https://www.philipzucker.com/?p=2660
published: false
slug: Normalization by Evaluation
title: Normalization by Evaluation
wordpress_id: 2660
---

Cody talks about stuff he cares about:

Conversion
Weak normalization
Strong normalization - Tait proof
Saturating Sets https://mathoverflow.net/questions/206526/explanation-of-the-definition-of-saturated-sets-in-lambda-calculus
PTS - System U-
Subterm property
Consistency
orthogonality/ biorthogonality
Weak head
neutral term
Kleene realizability arrow
Types as Sets of terms
logical relations




2020 -09 

[http://www.davidchristiansen.dk/tutorials/nbe/#%28part._.Further_.Reading%29](http://www.davidchristiansen.dk/tutorials/nbe/#%28part._.Further_.Reading%29)

[https://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html](https://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html)

[https://github.com/webyrd/normalization-by-evaluation](https://github.com/webyrd/normalization-by-evaluation)

https://www.youtube.com/watch?v=wyA1jByI89E&ab_channel=MicrosoftResearch

https://www.youtube.com/watch?v=CpADWJa-f28&ab_channel=AmbroseBonnaire-Sergeant

2/21/20

Cody gave a talk recently mentioning a mechanism by which one can use the yoneda embedding to compute normal forms

[http://www.cse.chalmers.se/~peterd/papers/nbe.html](http://www.cse.chalmers.se/~peterd/papers/nbe.html)

[http://www.cse.chalmers.se/~peterd/papers/Yonedaccc.pdf](http://www.cse.chalmers.se/~peterd/papers/Yonedaccc.pdf)

[http://www.cse.chalmers.se/~peterd/slides/Leicester.pdf](http://www.cse.chalmers.se/~peterd/slides/Leicester.pdf)

A normalizer / canonizer is a function that converts elements of an equivalence class into a normal form, for which we can use on the nose equality. It's kind of a factorization of an equivalence relation. [https://en.wikipedia.org/wiki/Canonical_form](https://en.wikipedia.org/wiki/Canonical_form)

A good (canonical? Tee hee.) example of such a thing is the free monoid

    
    <code>data FM a = Pure a | Mappend (FM a) (FM a) | Mempty deriving Eq
    
    instance Monoid (FM a) where
       (<>) = Mappend
       mempty = mempty
    
    lift :: FM a -> (FM a -> FM a)
    lift (Pure x) = \y -> (Pure x) <> y
    lift (Mappend x y) = (lift x) . (lift y) 
    lift Mempty = id
    
    
    
    
    
    </code>

Notions of monoids as computation- [https://arxiv.org/pdf/1406.4823.pdf](https://arxiv.org/pdf/1406.4823.pdf)

Kmett stack overflow

The yoneda lemma in haskell is

    
    <code>forall b. (a -> b) -> f b  ~ f a</code>

Nat(Hom(a  , - ), F) ~ F a

Free Monad constructions. There was a small revolution that occurred with Voightlanders'

Reason isomorphically [http://www.cs.ox.ac.uk/people/daniel.james/iso/iso.pdf](http://www.cs.ox.ac.uk/people/daniel.james/iso/iso.pdf)

It is useful to take a step back and examine "what is it I want". This helps to see w.

When I see a categorical manipulation, my impulse is to translate it into Haskell types. This is like someone explaining some geometrical theorem to you and insisting on using drawings. Kind of the point of euclid's axioms is that the drawing is superfluous commentary.

