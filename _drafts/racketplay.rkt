#lang racket

(define hello 'hello)




#|
BLock comments
|#

(module mymod racket
  (provide cake)
  (define cake '2cake)
  )

(require 'mymod)
cake


(syntax (+ 1 2))
#'(+ 1 3)
(identifier? #'car)

(begin-for-syntax (define age 9) (displayln age))

#'age