#lang scribble/lp2
@(require scribble/manual)
; I had to install langserver from a jupyter notebook. I don't know why.
; alt  + enter
; also a little button at the top

@chunk[myexpr (+ 1 1)]

@(define (foo x) (+ x 1))

@(foo 7)


