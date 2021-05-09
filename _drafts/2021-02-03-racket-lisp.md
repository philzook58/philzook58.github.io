---
author: Philip Zucker
date: 2021-02-06 19:08:24+00:00
layout: post
title: Scheme racket
---

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