---
author: philzook58
comments: true
date: 2020-07-10 14:54:22+00:00
layout: post
link: https://www.philipzucker.com/?p=2839
published: false
slug: Reifying the Stack with Lenses, Dialectica
title: Reifying the Stack with Lenses, Dialectica
wordpress_id: 2839
---




Dialectica ~ Markov. Markov says that if something is decidable, you can use a form of negation trasnformation of forall to exists. Indepdence of premise is about moving the exists quantifier around. Markov requires unbounded search.







Double negation ~ Pierce's Law







[https://www.irif.fr/~kerjean/papers/dial_diff.pdf](https://www.irif.fr/~kerjean/papers/dial_diff.pdf) Dialectica ~ lens. Higher order AD, list collect everywhere we actually evaluate somehow translates to multisets







Conal was doing something here. And i saw some other papers. The higher order exact reals are interesing. and higher order AD may have something to do with automatic differentiaion



















The lens data type is a good data type for forward back pass algorithms







There is a ubiquitous forward backward notion that occurs in every language. Function get called and then later return. Behind the scenes, most language build data structures to save enough information to return







Continuations are well known way of reifying control flow.







You can embed continuation passing style in a language, but perhaps at some overhead. If you weave it into the primitives of the language you can have gains. That's why Alexis King wants to add delimited continuation primops to GHC







One suggestion for a highly interwoven Lens structure is thrifty backtracking. Instead of saving the entirety of the current state of a backtrack on the stack, only save the diff. One does this by hand when one wants to build an efficient backtracking solver that operates by mutation on global state. You call deeper into the search, and then undo what you just did.







Delimited continuations can be implemented by literally capturing the stack. They are also known to be a technique for implementing coroutines. 







Converting to continuation passing style has something to do with the double negation translation. Of course, by type, it doesn't quite jive. Double negation explicitly uses Void whereas CPS uses a universal type. 







The Dialectica translation is something that can be mentioned in the same breath as double negation. Pedrot has some work on how the relates to an abstract machine. [https://www.xn--pdrot-bsa.fr/slides/thesis-09-15.pdf](https://www.xn--pdrot-bsa.fr/slides/thesis-09-15.pdf)







Conversion to Lens style seems possible. Then the holes in between can be filled by interesting operators?







Older stuff:







The dialectica interpretation trades complicated quantifer structure for complicated functional structure.







It is in the class of skolemization and double negation







Piedrot's response to coq club 6/25/2020 suggest that there is a dialgoue monad that perhaps is the analog of the cps monad? And that there is some relation with function extensitionality not being natural in this setting. Perhaps if function calling and returning







What about if you just made a new delimitted continuation every time you entered a function. 







Explicit stack model in Haskell. Use a STVar array as a stack. Do function calls manually? How do we know how much to allocate and stuff? Interesting







I was thinking maybe a use case might be to 







  * [https://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf](https://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf)
  * [https://julesh.com/2018/08/16/lenses-for-philosophers/](https://julesh.com/2018/08/16/lenses-for-philosophers/)
  * [http://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/](http://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/)
  * [https://www.sciencedirect.com/science/article/pii/0168007292900739](https://www.sciencedirect.com/science/article/pii/0168007292900739)
  * Valeria de paiva [https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf)
  * [https://cj-xu.github.io/agda/Dialectica/Dialectica.html](https://cj-xu.github.io/agda/Dialectica/Dialectica.html)


