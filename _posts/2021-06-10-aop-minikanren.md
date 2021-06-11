---
author: Philip Zucker
layout: post
date: 2021-06-10
title: "An Interpreter of the Algebra of Programming in MiniKanren"
---

<script src="/assets/biwascheme-0.7.2-min.js"> </script>
<script>
BiwaScheme.define_libfunc("myprint", 1, 1, function(ar){
  //BiwaScheme.assert_string(ar);
  document.getElementById("outputbox").value += ar;
    document.getElementById("outputbox").value += "\n";
});

function run(){
    document.getElementById("outputbox").value  = "";
   var code = document.getElementById("aopcode").value;
   var onError = function(e){ console.log(e); }
    var biwa = new BiwaScheme.Interpreter(onError)
    biwa.evaluate(code, function(result) {
        console.log(result);  //=> 3
    });
}

</script>

### The Demo

Here's the payoff. Read below for what the hell this is.

<label for="querybox"> <b>Code:</b> </label>
<textarea id="aopcode" style="width:100%" rows="20">
;;Scroll on below the microkanren implementation for the real meat of the post.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MicroKanren modified slightly for Biwa Scheme
;; https://github.com/jasonhemann/microKanren
;; http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
;; Jason Hemann and Dan Friedman
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (ext-s x v s) `((,x . ,v) . ,s))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (unit `(,s . ,(cdr s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (eqv? u v) s)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ c 1))))))

(define (disj g1 g2) (lambda (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (lambda (s/c) (bind (g1 s/c) g2)))

(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (lambda () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))

(define-macro (Zzz g) 
(let1 s/c (gensym)
    `(lambda (,s/c) (lambda () (,g ,s/c))))
)

(define-macro (conj+ g0 . gs)
  (if (eq? (length gs) 0)
     `(Zzz ,g0)
    `(conj (Zzz ,g0) (conj+ ,@gs))))

(define-macro (disj+ g0 . gs)
  (if (eq? (length gs) 0)
     `(Zzz ,g0)
    `(disj (Zzz ,g0) (disj+ ,@gs))))

(define-macro (fresh args . clauses)
    (if (eq? (length args) 0)
     `(conj+ ,@clauses)
     `(call/fresh 
        (lambda (,(car args))
           (fresh ,(cdr args) ,@clauses)
     ))
    )
)

(define-macro (conde . gs)
   `(disj+ ,@(map  ( lambda (c) `(conj+ ,@c))  gs  )  ))

(define-macro (run n qs . gs)
    `(map reify-1st (take ,n (call/goal (fresh ,qs ,@gs)))))

(define empty-state '(() . 0))

(define (call/goal g) (g empty-state))

(define (pull $)
  (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let (($ (pull $)))
    (if (null? $) '() (cons (car $) (take-all (cdr $))))))

(define (take n $)
  (if (zero? n) '()
    (let (($ (pull $)))
      (if (null? $) '() (cons (car $) (take (- n 1) (cdr $)))))))

(define (reify-1st s/c)
  (let ((v (walk* (var 0) (car s/c))))
    (walk* v (reify-s v '()))))

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s)
                   (walk* (cdr v) s)))
      (else  v))))

(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let  ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_" "." (number->string n))))

(define (fresh/nf n f)
  (letrec
    ((app-f/v*
       (lambda (n v*)
         (cond
           ((zero? n) (apply f (reverse v*)))
           (else (call/fresh
                   (lambda (x)
                     (app-f/v* (- n 1) (cons x v*)))))))))
     (app-f/v* n '())))

(define (call/run f)
   (map reify-1st (take 1 (call/goal (call/fresh f))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Relational Combinators
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (ido in out)
  (== in out)
)

(define (compo f g in out)
     (fresh (b) (f in b) (g b out))
)

(define (fsto in out)
  (fresh (a b) (== in `(Pair ,a ,b)) (== out a))
)

(define (sndo in out)
  (fresh (a b) (== in `(Pair ,a ,b)) (== out b))
)

(define (forko f g)
    (lambda (in out)
        (fresh (a b c)
            (== in a)
            (== out `(Pair ,b ,c))
            (f a b)
            (g a c)
        )
    )
)

(define (inj1o in out)
    (== out `(Left ,in))
)

(define (inj2o in out)
    (== out `(Right ,in))
)

(define (splito f g)
    (lambda (in out)
        (fresh (x)
            (conde
                ((== in `(Left ,x))  (f x out))
                ((== in `(Right ,x)) (g x out))
            )
        )
    )
)

(define (dumpo in out)
    (== out '())
)

(define (convo f in out)
    (f out in)
)

(define (distr in out)
  (fresh (a b)
  (conde
   ( (== in `(Pair (Left ,a) ,b))  (== out `(Left (Pair ,a ,b))  ))
   ( (== in `(Pair (Right ,a) ,b)) (== out `(Right (Pair ,a ,b))  ))
  )
)
)

(define (fmapo f in out)
  (conde
    ((fresh (x y)  (== in  `(Id ,x))
                   (== out `(Id ,y))
                   (f x y)
                  ))
    ((fresh  (x y)
          (== in  `(SuccF ,x))
          (== out `(SuccF ,y))
          (f x y)
               ))
    ((== in 'ZeroF) (== out 'ZeroF))
  )
)

(define (cata f)
  (lambda (in out)
    (fresh (x y)
      (== in  `(Fix ,x))
      (f y out)
      (fmapo (cata f) x y)
    )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; AoP interpreter
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (interpo prog)
  (lambda (in out)
  (conde 
    ((== prog 'dump) (dumpo in out))
    ((== prog 'id) (ido in out))
    ((== prog 'fst) (fsto in out))
    ((== prog 'snd) (sndo in out))
    ((== prog 'distr) (distr in out))
    ((fresh (f g) (== prog `(fork ,f ,g))
                      ((forko (interpo f)
                             (interpo g))
                             in out 
                      )))
    ((== prog 'inj1) (inj1o in out))
    ((== prog 'inj2) (inj2o in out))
    ((fresh (f g) (== prog `(split ,f ,g))
              ((splito (interpo f) (interpo g)) in out)
              ))
    ((fresh (f g) (== prog `(comp ,f ,g)) (compo (interpo f) (interpo g) in out)))
    ;((fresh (f)  (== prog `(conv ,f)) (convo (interpo f) in out)))
    ((fresh (f) (== prog `(cata ,f))  ((cata (interpo f)) in out)))
    ((fresh (f) (== prog `(fmap ,f))  (fmapo (interpo f) in out)))

  )
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example usage
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-macro (example e)
    `(begin
    (myprint ,( format "~s" e))
    (myprint ,e)
    (myprint "")
    )
)


(define false '(Left ()))
(define true '(Right ()))
(define (Pair a b) `(Pair ,a ,b))
(define (SuccF x) `(SuccF ,x)) 
(define (Succ x) `(Fix (SuccF ,x)))
(define Zero '(Fix ZeroF))
(define (doub in out)
 (fresh (a)
  (conde
  ((== in 'ZeroF) (== out Zero) )
  ((== in `(SuccF ,a)) (== out (Succ (Succ a))))
)))


(example "Hello World")


(example (run 1 (in out) ((interpo 'id) in out)))
(example (run 2 (in out) ((interpo '(comp id id)) in out)))
(example (run 1 (f) ((interpo f) '(Pair 1 2) 2)))
(example (run 1 (g) ((interpo g) '(Pair 1 (Pair 3 2)) 2)))
(example (run 1 (g) ((interpo g) '(Pair 1 (Pair 3 2)) 3)))
(example (run 1 (f) ((interpo f) '(Pair 1 (Pair 3 2)) '(Pair 2 3))))
(example (run 1 (f) ((interpo f) '(Pair 3 2) '(Pair 2 3))))
(example (run 1 (f)  ((interpo f) 1 '(Left (Left 1)))))
(example (run 1 (f)  ((interpo f) 1 '(Left (Right 1)))))
(example (run 1 (f)  ((interpo f) 1 '(Pair 1 1))))
; synthesize not
(example (run 1 (f) (let ((f0 (interpo f)))
     (conj+
         ;  (== f '(split (comp dump inj2) (comp dump inj1)))
            (f0 '(Left ()) '(Right ()))
            (f0 '(Right ())  '(Left ()))
     )
)
))

(example (run 1 (out)  (doub (SuccF 3) out ) ))
(example (run 1 (out)  (doub (SuccF 3) out ) ))
(example (run 1 (out)  ((cata doub) Zero out ) ))
(example (run 1 (out)  ((cata doub) (Succ Zero) out ) ))
(example (run 1 (out)  ((cata doub) (Succ (Succ Zero)) out ) ))
(example (run 1 (in)   ((cata doub) in (Succ (Succ Zero)) ) ))
(example (run 3 (out in)  ((cata doub) in out  ))) ; produces the evens
(example (run 1 (in)  ((interpo '(cata dump)) in '() ))) ; produces the evens


; I need distrib or possibly curry?
; synthesize nand
;(example (run 1 (f) (let ((f0 (interpo f)))
;     (conj+ 
;            ;(== f ())
;            (f0 (Pair true true) false)
;            (f0 (Pair false false) true)
;            (f0 (Pair true false) true)
;          (f0 (Pair false true) true)
;   )
;)
;))

; it took a good beat
; So the above seems like it must be possible to have come back?
;(example (run 1 (f) (let ((f0 (interpo f)))
;     (conj+ 
;            (f0 (Pair true true)   '(Right (Right ())))
;            (f0 (Pair false false) '(Left (Left ())))
;            (f0 (Pair true false) '(Right (Left ())))
;            (f0 (Pair false true) '(Left (Right ())))
;     )
;)
;))

;(example (run 1 (f) (let1 f0 (interpo f)
;     (conj+ 
;            ;(== f ())
;            (f0 '(Left (Left ())) false)
;            (f0 '(Left (Right ())) true)
;            (f0 '(Right (Left ())) true)
;            (f0 '(Right (Right ())) true)
;     )
;)
;))

</textarea>
<button onclick="run()">Run</button>
<br>
<label for="outputbox"> <b> Output:</b> </label>
<textarea id="outputbox" style="width:100%" rows="15">
Press Run button.
Use "myprint" function or "example" macro to see output here.
</textarea>

### WhAT iS ThIS

The algebra of programming is an approach to making programming algebraic.

-  <https://themattchan.com/docs/algprog.pdf> 
- <https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/> 
- <https://www4.di.uminho.pt/~jno/ps/pdbc.pdf> 

This means bringing the act of programming or analysis of programs to a place where it feels similar to manipulating polynomials or doing an integral.
Make things point-free, in other words use combinators or make it categorical. This simplifies the equational reasoning.

An important side effect of this is that programs become perhaps offputtingly concise. This is important if you intend to manipulate a program with pencil and paper, because you will need to copy a significant portion of it for every new line of your deduction. There is something also to sheer syntactic mass being an obstruction to thought. It is good or at least interesting to consider what happens when you can fit an entire complex program on a line or screen. It changes the game. I remember Aaron Hsu saying this about APL, a bug that has not yet bit me.
Combinators may take inspiration from traditional list combinators like fold, combinator calculus like SKI, or category theory. Depends on your backwards and predilections.

A second aspect that is interesting is to extend functional programming to relational specification. One has a sense that the concept of a mathematical function is a relatively nice fitting abstraction to the computers we've got. Functions are a special case of relations that are completely defined over the domain and deterministic. General relations feel in some sense farther from an implementation, but the extra oomph you get for tight concise specification of a problem is worth it, which can then be refined into a functional implementation. 

Minikanren also operates relationally, in a way that can actually execute, so there is a natural question if these two things can be mixed. Minikanren is a relational or logic programming language similar in some respects to prolog. A crucial difference here is that it has a complete search strategy, which is at the least very convenient. It achieves it's relational character essentially from the algorithm of unification, which is a kind of bidirectional pattern matching, or a method for solving a system of equations between terms with variables in them.

I fixed up a standard microkanren implementation to work on [Biwa Scheme](https://www.biwascheme.org/), which is a scheme that operates within javascript and hence the browser. The bits I needed to fix up were that Biwa does not support the suite of modern macro constructions, so I needed to convert the Microkanren macros to use unhygienic macros, something that is possible I did correctly, but who knows.

It's also kind of fun that [Repl.it](https://replit.com/new/scheme) supports Biwa Scheme, which was an ok dev environment. Many of my minikanren queries were infinite loops however, which it wasn't so happy about, and I wasn't super confident it was saving correctly every time.

I used something at least close to Haskell naming conventions for my operators. I knew I could do this minikanren relation algebra thing in haskell about two years ago, but it was too much of a project to do so and keep it well typed.

So I have a tendency when doing these point free things to shoot for the categorical combinators first. The identity relation is the same as the minikanren `==` relation and compose is kind of a standin for `fresh`. This is more or less the standard existential definition of relation composition, which can be thought of as a database join if you like.

```scheme
(define (ido in out)
  (== in out)
)

(define (compo f g in out)
     (fresh (b) (f in b) (g b out))
)
```

Then I like to think about the cartesian combinators for dealing with pairs. `forko` is our first higher order relational combinator. There is a difference between the parameters `f`/`g` and `in`/`out`. `f`/`g` are relations, which are scheme lambdas whereas `in` and `out` are minikanren logic variables. More on this later. 

```scheme
(define (fsto in out)
  (fresh (a b) (== in `(Pair ,a ,b)) (== out a))
)

(define (sndo in out)
  (fresh (a b) (== in `(Pair ,a ,b)) (== out b))
)

; forko requires a higher order program call to interpo though? Nope
(define (forko f g in out)
      (fresh (a b c)
              (== in a)
              (== out `(Pair ,b ,c))
              (f a b)
              (g a c)
              )
)
```

A combinator derivable from these is `duplicate`. `dup = fork id id`

```scheme
(define (dup in out)
  (== out `(Pair ,in ,in))
)
```


Then similarly we can deal with `Either`, aka the `Sum` type

```scheme
(define (inj1o in out)
      (== out `(Left ,in))
)
(define (inj2o in out)
      (== out `(Right ,in))
)
; to curry or not curry. That is thy question
; Is that how we can metaprogram?
; 
(define (splito f g in out)
  (fresh (x)
        (conde
          ((== in `(Left ,x))  (f x out))
          ((== in `(Right ,x)) (g x out))
        )
  )
)
```

A combinator that revels we're not in Kansas anymore is the converse combinator. So simple, and yet in some sense is solving the very difficult problem of inverting functions.

```scheme
(define (convo f in out)
  (f out in)
)
```

I started very lightly down the road of [recursion schemes](https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html), which is a point-free style for writing recursive programs with nice equational properties. It is recursion that is both a gift and a curse and for which the minikanren complete search is a great boon.
As part of defining recursion schemes, you need to define fmap.

We can define a metainterpreter in minikanren for these relations very easily. What makes this interesting is that it opens the door to program synthesis and other cute tricks. As compared to other styles of making relational interpreters in minikanren, we avoid having to think about binding issues and contexts, which seems very nice. Maybe you pay for it though?

```scheme
(define (interpo prog)
  (lambda (in out)
  (conde 
    ((== prog 'dump) (dumpo in out))
    ((== prog 'id) (ido in out))
    ((== prog 'fst) (fsto in out))
    ((== prog 'snd) (sndo in out))
    ((== prog 'distr) (distr in out))
    ((fresh (f g) (== prog `(fork ,f ,g))
                      ((forko (interpo f)
                             (interpo g))
                             in out 
                      )))
    ((== prog 'inj1) (inj1o in out))
    ((== prog 'inj2) (inj2o in out))
    ((fresh (f g) (== prog `(split ,f ,g))
              ((splito (interpo f) (interpo g)) in out)
              ))
    ((fresh (f g) (== prog `(comp ,f ,g)) (compo (interpo f) (interpo g) in out)))
    ;((fresh (f)  (== prog `(conv ,f)) (convo (interpo f) in out)))
    ((fresh (f) (== prog `(cata ,f))  ((cata (interpo f)) in out)))
    ((fresh (f) (== prog `(fmap ,f))  (fmapo (interpo f) in out)))

  )
))
```

With the converse operation is is very easy to derive the top relation that contains everything. `(converse snd) . snd` for example. I combatted this annoyance by just removing converse for the moment from the interpeter. A better solution may be to extend my microkanren with disequality operations, which the main minkanren already has, and include some anti-examples.


### Bits and Bobbles

I feel my energy flagging on this, so let's put it on the shelf by getting a blog post out and perhaps return to it someday.

You can synthesize programs by giving a bunch of examples. It is similar to barliman in a sense. <https://github.com/webyrd/Barliman> . Or perhaps you can write down a relational spec and insist that the outputs match for a pile of inputs. Or do some kind of cegar thing altenrating looking for bad inputs and good programs.

Something like
```
(define in '(1 2 3 4 5 6)) ; really we should conj over a list of possible inputs
(define spec ((compo sndo fsto))) ;; or some more interesting spec.
(run (f out) (conj (spec in out) ((interp f) in out)))
```

Even inferring a binary boolean operation based off it's truth table was pretty slow. Then again I am using a funky javascript scheme. Me dunno.

I defined fmap in kind of a closed way. One can do it openly with imperative relation extension operations.

Is this a metainterpeter? Even if I get enough combinators to be equivalent to minikanren there is a slight difference of flavor here. I dunno.

Can I modify minikanren or make some kind of query to determine if a given relation is a subset of another one?  AOP heavily dicsussed relational inclusion, which is part of what makes it particularly interesting

How do you get this to scale in the slightest? I need to actually read the minikanren quine interpreter paper <http://io.livecode.ch/learn/gregr/icfp2017-artifact-auas7pp>

Staging the interpeter? Nada Amin. Lisp conference 2021 keynote.

egraphs for aop.

Combinators for curry uncurry and apply. Makes it a closed catergory

I had forgotten about `distr`. It's important mostly in the abscence of the curry combinators

