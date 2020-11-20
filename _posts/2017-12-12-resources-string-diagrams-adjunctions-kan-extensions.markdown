---
author: philzook58
comments: true
date: 2017-12-12 22:20:51+00:00
layout: post
link: https://www.philipzucker.com/resources-string-diagrams-adjunctions-kan-extensions/
slug: resources-string-diagrams-adjunctions-kan-extensions
title: Resources on String Diagrams, and Adjunctions, and Kan Extensions
wordpress_id: 943
tags:
- Category Theory
- haskell
---

I've been trying to figure out Kan Extensions

Ralf Hinze on Kan Extensions

[https://www.cs.ox.ac.uk/ralf.hinze/Kan.pdf](https://www.cs.ox.ac.uk/ralf.hinze/Kan.pdf)



But while doing that I went down a rabbit hole on String Diagrams

This post is the first one on String Diagrams that made sense to me.

[https://parametricity.com/posts/2015-07-18-braids.html](https://parametricity.com/posts/2015-07-18-braids.html)

I had seen this stuff before, but I hadn't appreciated it until I saw what Haskell expressions it showed equivalence between. They are not obvious equivalences

This seems like a very useful video on this topic.

https://skillsmatter.com/skillscasts/8807-categories-and-string-diagrams

In Summary, it is an excellent notation for talking about transformations of a long sequence of composed Functors  F G H ... into some other long sequence of Functors. The conversion of functors runs from up to down. The composition of functors procedes left to right.  F eta is the fmap of eta, and eta F is eta with the forall'ed type unified to be of the form F a.

Adjunctions L -| R are asymmetric between cups and caps. L is on the left in cups and on the right in caps. That's what makes squiggles pull straightable

I think I have an interesting idea for a linear algebra library based on this stuff



John Baez and Mike Stay's Rosetta Stone (A touch stone I keep returning to)

math.ucr.edu/home/baez/rosetta.pdf

Dan Piponi gave a talk which is another touch stone of mine that I come back to again and again. There is a set of corresponding blog posts.

https://vimeo.com/6590617

Other resources:

NCatLab article

[https://ncatlab.org/nlab/show/string+diagram](https://ncatlab.org/nlab/show/string+diagram)

John Baez hosted seminars

[http://www.math.ucr.edu/home/baez/QG.html](http://www.math.ucr.edu/home/baez/QG.html)

Catsters

[https://www.youtube.com/view_play_list?p=50ABC4792BD0A086](https://www.youtube.com/view_play_list?p=50ABC4792BD0A086)



https://www.youtube.com/watch?v=V4m8x6C7pWI

Dan Marsden's Article

https://arxiv.org/abs/1401.7220

Marsden and Hinze have been collaborating

events.inf.ed.ac.uk/wf2016/slides/hinze.pdf

https://link.springer.com/chapter/10.1007/978-3-319-30936-1_8

Stephen Diehl on Adjunctions

http://www.stephendiehl.com/posts/adjunctions.html



A Section From an old Oregon Programming Language Summer School (a rich set of resources)

https://www.youtube.com/playlist?list=PLGCr8P_YncjWX6YHOq1-SyyP7zf4a_E_E



Marsden and Hinze have been collaborating

events.inf.ed.ac.uk/wf2016/slides/hinze.pdf

https://link.springer.com/chapter/10.1007/978-3-319-30936-1_8



Mike Stay doing a very interesting series of Category Theory in Javascript. He uses contracts in place of types. Defeats one of the big points of types (static analysis), but still pretty cool

https://www.youtube.com/watch?v=i8_Ae6VUF0I



https://www.youtube.com/watch?v=cOjmaFbnsyY



I think that about covers everything I know about.

Oh yeah, there is the whole Coecke and Abramsky categorical quantum mechanics stuff too.
