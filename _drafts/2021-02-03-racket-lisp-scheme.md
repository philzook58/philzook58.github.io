---
author: Philip Zucker
date: 2021-02-06 19:08:24+00:00
layout: post
title: Scheme racket
---

Lisp-2 - seperate namespace for functions and vasriables -Common lisp
Condition system
lisp class system



Rosette - should be a confluence of my interests. 
I feel like I want some kind of macro engine for smtlib.
Perhaps it makes intermiedtae queries, perhaps not.
stage0 would be "just" a macro expander for smtlib.



Oleg of course. http://okmij.org/ftp/Scheme/
- Has an implementation of shift reset delimitted contianutations

Macro examples:
- Making a pattern matcher might be kind of interesting exercise.
- making your own short circuiting "or" or other non call by value constructs. In some sense this is defining a new interpreter back into scheme?
- making your own binding forms or introducing variables into the environment


https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_toc.html - an intorudcition to scheme and it's impllementation

https://ds26gte.github.io/tyscheme/index-Z-H-1.html teach yourself scheme in fixnum days

In particular the extneded examples section is kind of interesting
https://www.scheme.com/tspl4/examples.html#./examples:h0

The scheme objects technique. Let bindings are mutable. Isn't that nuts. Let's you do all kinds of shenanigans that you _could_ do in ocaml with refs, but would be unlikely to.



let make_counter () = let state = mk_ref 0 in fun () -> let state := !state + 1 in !state

amb is genuinely surprising. It isn't even that it's a macro. Its callcc that makes it possible
call/cc for break statements.

continuations
https://www.ps.uni-saarland.de/~duchier/python/continuations.html
call/cc let's you pretend you were writing in CPS the whole time.
- call/cc for break statements
- call/cc for coroutines
- search
- amb

https://letoverlambda.com/index.cl/guest/chap2.html
let over lambda. Let in common lisp makes a ref cell?


https://felleisen.org/matthias/7480-s21/lectures.html
history of PL. interesting discussion of hygienic macros at the least
https://www.sweetjs.org/ - hygienic macros

macros


What is the deal.

https://news.ycombinator.com/item?id=26008869

https://school.racket-lang.org/2019/plan/

https://beautifulracket.com/


https://github.com/namin/inc incremental compilter construction



Hmm a scheme in the broser
biwacheme
chicken -> C -> wasm
gambit has a backend
 racket has ab ackend
 https://www.reddit.com/r/scheme/comments/fhvuwl/the_best_uptodate_and_mature_schemejavascript/

 Like livecode.io
 right clojurescript. But that's clojure

https://github.com/webyrd/faster-miniKanren
https://github.com/jasonhemann/microKanren/blob/master/microKanren.scm

<script src="https://www.biwascheme.org/release/biwascheme-0.7.1-min.js"> 
   (console-log "Hello, world!")
</script>
    
<div id="bs-console">
</div>

<script type="text/biwascheme">
  (print "Hello, world!")
  (print (current-date))
  (console-log "ok.")
  (load "/assets/microkanren.scm")
  (print (call/goal (call/fresh (lambda (q)  (== q 1) ))))
  (print (call/run (lambda (q) 
  (call/fresh (lambda (r)
  (conj (== q `(,r ,r))  (== r 1) ))))))
  (define-macro (fizz x)
    `(buzz ,x))
  (print (macroexpand '(fizz 3)))
  (print (macroexpand '(Zzz f)))
  (print (macroexpand '(conj+ x y z)))
  (print (macroexpand '(fresh (x y) g1 g2)))
  (print (macroexpand '( conde  ((x y) (p q))  )))
  (print (run 1 (q) (== q 1)) )
  (print (run 2 (q) 
        (conde 
           ((== q 1))
           ((== q 2)))))
  (print (run 2 (x)
        (fresh (p q)
         (== x `(,p ,q))
        (conde 
           ((== q 1) (== p q))
           ((== q 2))))))
    (print (run 2 (q p)
        (conde 
           ((== q 1) (== p q))
           ((== q 2)))))

    (print (macroexpand '(run 2 (q p)
        goal)))
    ( print (macroexpand-1 '(conde 
           ((== q 1) (== p q))
           ((== q 2)))))




</script>