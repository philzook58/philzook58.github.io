---
author: philzook58
comments: true
date: 2017-01-17 20:58:24+00:00
layout: post
link: https://www.philipzucker.com/?p=503
published: false
slug: Category Theory by Bartosz Milewski
title: Category Theory by Bartosz Milewski
wordpress_id: 503
---

I'm watching Category Theory videos by Bartosz Milewski and they are quite understandable. To be seen how much they expand my programming horizons.

There is supposed to be a "[holy trinity](https://existentialtype.wordpress.com/2011/03/27/the-holy-trinity/)" according to Bob Harper of which category theory is one corner (and then topology is a fourth corner according to HoTT?). I think a puzzling aspect of category theory is that while it is about objects and arrows, it's tough to say what that means. I think by analogy to the other objects in this trinity, that it is attempting to replace something so primal that you rarely consider it when doing less basic things (Logic is pretty darn basic. More basic than Set theory).

I thought maybe I should be taking notes.

Video 2.1 and 2.2

epimorphism - rephrase the concept of a function be onto (covering it's entire range, like f(x)=x rather than arctan(x) ) in terms of composition of functions.



In terms of functions we need that

$latex \forall g_1 g_2$, $latex g_1 \circ f = g_2 \circ f$ implies $latex g_1 = g_2$

Since the function f is onto, we can assume that to match in composition g1 and g2 have to match everywhere on the range.

Monomorphism is the opposite

$latex \forall g_1 g_2$, $latex f \circ g_1 = f \circ g_2$ implies $latex g_1 = g_2$

Video 3.1

Preorder. Only requires composability between existing order.

What does associativity mean here?

A Hom-set is the set of morphism C(a,b).

Thin category. Hom-set is either empty or has single object.

epimorphism and monomorphism don't have to be invertible. Unlike in sets.

every arrow in a thin category is an epimorphism and monomorphism.

In partial order, this is true but no arrows are invertible.

A general category can be though of as a preorder that is thick

Proof relevant preoder. Every arrow that has buddos is a different proof for that ordering.

monoid. A single object with a bunch of arrows to itself.

Monoids are also in algebra. They are items with a binary operation (call it multiplication). There is an identity element and the operation is associative.

The homset M(m,m) is like our monoid elements. Multiplication is composition.

In Haskell the objects are types (usually thats the analogy we're making) The object here is the type String let's say. Then the morphisms are the curried form of all strings "Hello"++, "YOYO"++. These objects are functions of type String -> String so it makes sense. You can compose them  ("Hello"++) . ("YOYO"++) is the same as  "HelloYOYO"++

And the evaluation order (where you put parenthesis) in which you do this doesn't matter. Associativity.



What is going on in category theory.

Focus on the idea of a function. How you get at stuff via functions.

A simple thing you can do is form pairs.

How do you do that with functions?

What is a function? It composes.












