---
author: Philip Zucker
date: 2021-02-06 19:08:24+00:00
layout: post
title: Scheme Racket Lisp
---

- [Implementations](#implementations)
- [Scheme](#scheme)
  - [Minikanren](#minikanren)
- [Racket](#racket)
  - [Rosette](#rosette)
- [Common Lisp](#common-lisp)
  - [CLOS](#clos)
  - [Condition System](#condition-system)
  - [ACL2](#acl2)
- [Other Lisps](#other-lisps)
- [Compilation](#compilation)
  - [Gambit compiling to javascript](#gambit-compiling-to-javascript)
- [Misc](#misc)

I'm really going to put scheme and common lisp in the same category?

# Implementations

- Racket
- Chez
- Guile
- Gambit
- Chicken

- SBCL

Gambit vs Chez vs Guile scheme. Me dunno
Gerbil is a system on top of Gambit approximately similar to racket

```scheme
(print "hello world")
(print "~a foo" 'bar)
```

```racket
#lang racket
(print "hello world")
```

# Scheme

[https://schemers.org/](https://schemers.org/)

[ribbit scheme](https://news.ycombinator.com/item?id=31096771)

[scheme primer](https://spritely.institute/static/papers/scheme-primer.html)

[Pre-Scheme: A Scheme Dialect for Systems Programming](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.3.4031&rep=rep1&type=pdf)

<https://gitlab.com/spritely/guile-hoot> hoot is scheme to wasm

<https://github.com/Calysto/calysto_scheme> jupyter enabled scheme

### Minikanren

<http://minikanren.org/>

<https://github.com/michaelballantyne/faster-minikanren>
`raco pkg install minikanren`

```racket
#lang racket
(require minikanren)
(run 1 (q) (fresh (x y z) (== x q) (== 3 y)))
```

[http://io.livecode.ch/](http://io.livecode.ch/) more minikanren examples [implementing microkanren](https://www.youtube.com/watch?v=0FwIwewHC3o)

[http://tca.github.io/veneer/examples/editor.html](http://tca.github.io/veneer/examples/editor.html) minikanren examples.

<https://www.philipzucker.com/aop-minikanren/>

[lambda kanren](https://www.youtube.com/watch?v=iUZasa7wzW4) assume all
[A New Higher-order Unification Algorithm for 𝜆Kanren](http://minikanren.org/workshop/2021/minikanren-2021-final8.pdf)

# Racket

<https://docs.racket-lang.org/index.html>

`raco pkg install`

[Creating Languages in Racket (2011)](https://news.ycombinator.com/item?id=26008869)

<https://school.racket-lang.org/2019/plan/>

[beautiful racket](https://beautifulracket.com/)

<https://github.com/wilbowma/cur> a curious dependently typed proof assistant

[racketscript](http://play.racketscript.org/)

[racket contest good links](https://racket.discourse.group/t/summer-lang-party/1128/2)

Mythical Macros tutorial
<https://soegaard.github.io/mythical-macros/>

Macros and Languages in Racket book draft
<http://rmculpepper.github.io/malr/> 1

Racket Guide: Creating Languages
<https://docs.racket-lang.org/guide/languages.html>

Racket Docs search for all languages:
<https://docs.racket-lang.org/search/index.html?q=H%3A>

[Extensible Pattern Matching in an Extensible Language](https://arxiv.org/pdf/1106.2578.pdf)

[Bowman how to hashlang](https://williamjbowman.com/tmp/how-to-hashlang/)
[Macro-embedding Compiler Intermediate Languages in Racket](https://williamjbowman.com/tmp/wjb2022-hashlang-x64.pdf)

FRTime

[implementing type systems as a macros](https://lambdaland.org/posts/2023-08-14_types_with_macros/)
[Type Systems as macros](https://dl.acm.org/doi/10.1145/3009837.3009886)

[Rhombus: A New Spin on Macros without All the Parentheses](https://users.cs.utah.edu/plt/publications/oopsla23-faadffggkkmppst.pdf)

### Rosette

<https://docs.racket-lang.org/rosette-guide/index.html>

Rosette - should be a confluence of my interests.
I feel like I want some kind of macro engine for smtlib.
Perhaps it makes intermiedtae queries, perhaps not.
stage0 would be "just" a macro expander for smtlib.

```racket
#lang rosette
(define-symbolic b boolean?)
(assert #t)
(assume b)
(verify b)

;(define-symbolic b boolean?)

```

<https://rdivyanshu.github.io/ma122.html> Solving a mathemattic problem using Rosette

# Common Lisp

[common lisp resources](https://news.ycombinator.com/item?id=31120359)

Lisp-2 - seperate namespace for functions and vasriables -Common lisp
Condition system
lisp class system CLOS

<https://letoverlambda.com/index.cl/guest/chap2.html>
let over lambda. Let in common lisp makes a ref cell?

SLIME

[coalton](https://github.com/coalton-lang/coalton)

[alive vscode extension](https://github.com/nobody-famous/alive)

[getting started](https://lisp-lang.org/learn/getting-started/)
[sbcl manual](http://www.sbcl.org/manual/)
[quick lisp library manager](https://www.quicklisp.org/beta/) This makes it easy to load up packages. I think using this is quite strandard. Follow  instructions to curl and load and add to init file

[lisp books](https://lisp-lang.org/books/#practical-common-lisp)

[Practical Common Lisp](https://gigamonkeys.com/book/)
[Common Lisp the Language 2nd ed](https://www.cs.cmu.edu/Groups/AI/html/cltl/cltl2.html)

[Cliki](http://www.cliki.net:8080/)

```bash
echo $'
;re
(write-line "Hello, World!")
(ql:quickload "vecto")
(format t "Hello, world!")
; comment one
#|
Multiline comment are nestable
|#

(defun fib (n)
  "return fib nuymber"
  (if (< n 2)
      1
      (+ (fib (- n 1)) (fib (- n 2)))
  )
)
(fib 3)
(funcall #\'fib 3)  ; funcall takes multiarity args. Functions quoting
(apply #\'fib (list 3)) ; apply takes list of args
#\'fib

; multiple value returns
(defun many (n)
  (values n (* n 2) (* n 3)))

(let ((str "Hello, world!")) ; let and let*
  (string-upcase str))

; defparameter and defvar

(defparameter *string* "I\'m global")

(defun print-variable ()
  (print *string*))

(print-variable)


(defun foobar (a b c) (+ a (* b c)))
(compiled-function-p #\'foobar)
(disassemble #\'foobar)

(format t "~a" t)

(vector 1 2 3)
#(1 2 3)
' | sbcl 
```

[disassemble](http://clhs.lisp.se/Body/f_disass.htm)

`(declaim (optimize (debug 3)))`
<https://malisper.me/category/debugging-common-lisp/>

save-lisp-and-die to save an image of current process.

## CLOS

art of metaobject protocol

<https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node260.html>

## Condition System

Like exceptions except you can restrta from them
[book](https://news.ycombinator.com/item?id=24867548)

## ACL2

The main theorem prover associated with common lisp. It is a granddaddy of a lot of other systems
<https://github.com/acl2/acl2>

`sudo apt-get install acl2` works.

proofpad? <http://proofpad.org/> online version too <http://new.proofpad.org/> There's a little tutorial button

"sedan". Looks out of date, eclipse doesn't warm my heart. I dunno.

applicative common lisp, it's a variant of common lisp using only pure (applicative) functions.

```bash
echo "
(+ 1 1)
(append (list 1 2) (list 3 4))
(cons 1 nil)
(car '(1 2 3)) ; cdr first rest
(defun triple (x) (* 3 x))
; Since TRIPLE is non-recursive, its admission is trivial.  We observe
; that the type of TRIPLE is described by the theorem 
; (ACL2-NUMBERP (TRIPLE X)).  We used primitive type reasoning.
(endp nil) ; t
(evenp 3) ; nil
(equal t t)

(defun hailstone (x)
  (if (evenp x) ; condition
      (/ x 2) ; what to do if it passes
      (+ (* 3 x) 1))) ; what to do if it fails

; uses guards. acl2 is proving termination
(defun factorial (n)
  (if (zp n)
      1
      (* n (factorial (- n 1)))))

(thm (> (factorial n) 0)) ; QED

:q ; exit acl2 rep back to lisp
(lp) ; back to acl2

:args assoc-eq ; guards and conditions associated wth

(quit)

; :mini-proveall

; (include-book )
" | acl2
```

Needs to reason about terminatin to define stuff.

<https://hilbert.math.wisc.edu/logic/kunen/ramsey.pdf> - ramsey theorem in ACL2

ACL2 hypperreals

Gamboa course on discrete math has some vids <https://www.youtube.com/watch?v=R0vgJbskXbM&ab_channel=RubenGamboa>
<https://arxiv.org/pdf/2205.11695.pdf> teaching acl2 gamboa
<https://github.com/rubengamboa/acl2_bridge>
<https://github.com/rubengamboa/acl2_jupyter>
<https://github.com/rubengamboa/acl2-math-book>
<https://github.com/rubengamboa/acl2-docker-images>
<https://github.com/rubengamboa/acl2-docker-images/tree/main/context/acl2-notebooks/programming-tutorial> jupter notebooks

rex page

<https://www.cs.utexas.edu/users/moore/publications/km97a.pdf> A Precise Description of the ACL2 Logic <https://cstheory.stackexchange.com/questions/32749/proof-software-for-primitive-recursive-arithmetic>
<https://proofassistants.stackexchange.com/questions/1867/is-acl2-first-order-logic-and-is-this-a-limitation-for-proving-math> `:doc ordinals`

Defines ordinals hmm
<https://www.khoury.northeastern.edu/home/pete/pub/acl2-ordinal-arithmetic-acl2.pdf> odinal airthmetic in acl2. cantor normal form. epsilon 0

```python
from z3 import *
U = Datatype('Univ')
U.declare('cons', ('car', U), ('cdr', U))
U.declare('bool', ('bool_val', BoolSort()))
U.declare('real', ('real_val', RealSort()))
U.declare('string', ('string_val', StringSort()))
U.declare('int', ('int_val', IntSort()))
U.declare('nil')
U = U.create()
print(dir(U))
print(simplify(U.is_bool(U.bool(True))))
print(simplify(U.int_val(U.int(1))))
print(U.cons(U.int(1), U.nil))

# Can I add operations?
#U.__add__ = lambda self, other: U.int(self, other)
car = U.car
cdr = U.cdr
cons = U.cons
nil = U.nil

def atom(x):
    return Not(U.is_cons(x))
def consp(x):
    return U.is_cons(x)
def integerp(x):
    return U.is_int(x)


Function("order", U, U, BoolSort())
= RecursiveFunc()
If(is_cons(x),
  And(e0_ordinalp(car(x)), car(x) != U.int(0), 
      e0_ordinalp(cdr(x)), 
      Or(atom(cdr(x)), 
      Not(e0-ord-<(car(x), cadr(x)))),
  And(integerp(x), U.int_val(x) >= 0)))


```

<https://www.cs.utexas.edu/users/moore/publications/index.html> moore publications
<https://www.cs.utexas.edu/users/moore/publications/gentle-intro-to-acl2-programming.html> gentl introduction
CLI veirifed stack - linker loader? <https://www.cs.utexas.edu/users/moore/best-ideas/piton/index.html> piton
[verified os stack](https://www.cs.utexas.edu/ftp/boyer/cli-reports/011.pdf)
<https://www.cs.utexas.edu/ftp/boyer/cli-reports/022.pdf>

controller

Computer-Aided Reasoning: An Approach
Computer-Aided Reasoning: ACL2 Case Studies
A computational logic handbook - book on ACL2

"the little prover" is about a simplified versio nof acl2

<https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=ACL2____The_02Proof_02of_02the_02Associativity_02of_02App> the proof of the associativty of app

<https://www.cs.utexas.edu/users/moore/acl2/v8-5/combined-manual/?topic=ACL2____GUARD> guards

<https://www.cs.utexas.edu/users/moore/acl2/v8-5/combined-manual/?topic=ACL2____STATE> von nuemmanesque state. Reads to me like th state monad

"history"

`(declare (xargs :guard (g x y)  :measure (m x y)))` xargs let's you state guard and measure

Hmm. Totalize in the logic, but have partiality guard rails at metalevel?
A global notion of ordinal and well founded?

```z3
;re
; actually make a datatype? But then not extendable. Maybe that's ok.
(declare-sort Atom)
(declare-datatype Value
  (cons (car Value) (cdr Value))
  (nil)
  (number Int)
  (real Real)
  (string String)
  (atom Atom)
)
(declare-sort Value)
(declare-fun cons (Value Value) Value)
(define-const nil Value)
(declare-fun car (Value) Value)
(assert (forall ((x Value)) (= (car x) (ite (is-cons x) ()  nil)))


```

# Other Lisps

- [Carp](https://github.com/carp-lang/Carp)  <https://news.ycombinator.com/item?id=28875051>
- Janet
- [Shen](https://shen-language.github.io/) <https://shenlanguage.org/>
- Clojure
- emacs lisp

# Compilation

[http://home.pipeline.com/~hbaker1/CheneyMTA.html](http://home.pipeline.com/~hbaker1/CheneyMTA.html)

Lisp in easy pieces

[http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/](http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/)

### Gambit compiling to javascript

[old gist](https://gist.github.com/roman01la/1d2f84357a2aef8ef053dd6ba4f0aad1)
[discussion](https://mailman.iro.umontreal.ca/pipermail/gambit-list/2019-July/009132.html)

You need to compile the javascript runtime special

```bash
make _gambit.js # This command finally build the needed Gambit Javascript runtime
LD_LIBRARY_PATH=..: ../gsc/gsc -:~~bin=../bin,~~lib=../lib,~~include=../include -f -target js  -prelude "(define-cond-expand-feature|enable-type-checking|)(define-cond-expand-feature|disable-auto-forcing|)(define-cond-expand-feature|enable-sharp-dot|)(define-cond-expand-feature|enable-bignum|)(define-cond-expand-feature|enable-ratnum|)(define-cond-expand-feature|enable-cpxnum|)(define-cond-expand-feature|disable-smp|)(##include\"../lib/header.scm\")" -o _gambit.js ../lib/_univlib.scm
cp _gambit.js /c/tools/gambit-c/lib/_gambit.js # This command publish the Javascript runtime to the installed Gambit-C.
```

Hmm. make_gambit does this stuff? <https://gitter.im/gambit/gambit?at=5bc7fb95435c2a518ec448d1>

This final concatenation step is bizarre. Hmm wasn't necessayr on minimal example in gitter above

```
% cat test.scm
(println "hello!")
% gsc/gsc -:=. -target js -exe test.scm
% ./test
hello!
```

[contrib/try repl](https://gitter.im/gambit/gambit?at=60aed31d0ff6de262b2e9f4a)
[gambit in the browwser](https://feeley.github.io/gambit-in-the-browser/) experiment using emscripten. Different from try.scheme.org using universal backend

# Misc

[tinylisp](https://github.com/Robert-van-Engelen/tinylisp) 99 lines of C. pretty cool
<https://news.ycombinator.com/item?id=32100035>  - interrsting comment about generic multiple dispatch. Is there a subsumption indexing issue here?

[build your own lisp](https://www.buildyourownlisp.com/)

<https://github.com/nojb/ocs-ng> ocaml scheme

[Papers on writing virtual machines for scheme?](https://old.reddit.com/r/scheme/comments/r5rn1s/papers_on_writing_virtual_machines_for_scheme/)
3 implementation models

[scheme bibliography](https://github.com/schemedoc/bibliography)

[State of Scheme to Javascript](https://call-with.cc/post/state-of-scheme-to-javascript) The Ribbit pathway seems interesting. Or maybe rather the Gambit pathway [scheme interp in browser](try.scheme.org)

["Let's Build a Hygienic Macro Expander" by Matthew Flatt](https://www.youtube.com/watch?v=Or_yKiI3Ha4&ab_channel=StrangeLoopConference)
Macro scope. So de bruijn indices are a way of dealing with some of the troubles of binding forms. But here I think he's saying that de bruijn indices are the wrong abstraction.

Scope sets
Syntax objects are paired with scope sets.
type syntax = Sexp.t * Int.Set.t

syntax_of_datum : Sexp.t -> syntax =

HUh that was an interesting trick. Use ref () and physical equality for gensym.
[](https://github.com/mflatt/expander)
[Binding as Sets of Scopes
Notes on a new model of macro expansion for Racket](http://www.cs.utah.edu/~mflatt/scope-sets-5/)

<https://github.com/jcubic/lips> lips - a scheme in javascript

<https://ianthehenry.com/posts/janet-game/the-problem-with-macros/> interesting blog post
cross stage persistence. How does one serialize a function?
<http://www.nhplace.com/kent/Papers/Technical-Issues.html> why a lisp 2 i guess

<https://turtleware.eu/> common lisp essay

<https://www.cs.utah.edu/plt/publications/macromod.pdf> composable and compileable macros - you want in whe?

Oleg of course. <http://okmij.org/ftp/Scheme/>

- Has an implementation of shift reset delimitted contianutations

Macro examples:

- Making a pattern matcher might be kind of interesting exercise.
- making your own short circuiting "or" or other non call by value constructs. In some sense this is defining a new interpreter back into scheme?
- making your own binding forms or introducing variables into the environment

<https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_toc.html> - an intorudcition to scheme and it's impllementation

<https://ds26gte.github.io/tyscheme/index-Z-H-1.html> teach yourself scheme in fixnum days

In particular the extneded examples section is kind of interesting
<https://www.scheme.com/tspl4/examples.html#./examples:h0>

The scheme objects technique. Let bindings are mutable. Isn't that nuts. Let's you do all kinds of shenanigans that you _could_ do in ocaml with refs, but would be unlikely to.

let make_counter () = let state = mk_ref 0 in fun () -> let state := !state + 1 in !state

amb is genuinely surprising. It isn't even that it's a macro. Its callcc that makes it possible
call/cc for break statements.

continuations
<https://www.ps.uni-saarland.de/~duchier/python/continuations.html>
call/cc let's you pretend you were writing in CPS the whole time.

- call/cc for break statements
- call/cc for coroutines
- search
- amb

<https://felleisen.org/matthias/7480-s21/lectures.html>
history of PL. interesting discussion of hygienic macros at the least
<https://www.sweetjs.org/> - hygienic macros

macros

What is the deal.

<https://github.com/namin/inc> incremental compilter construction

Hmm a scheme in the broser
biwacheme
chicken -> C -> wasm
gambit has a backend
 racket has ab ackend
 <https://www.reddit.com/r/scheme/comments/fhvuwl/the_best_uptodate_and_mature_schemejavascript/>

 Like livecode.io
 right clojurescript. But that's clojure

<https://github.com/webyrd/faster-miniKanren>
<https://github.com/jasonhemann/microKanren/blob/master/microKanren.scm>

```html
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
```
