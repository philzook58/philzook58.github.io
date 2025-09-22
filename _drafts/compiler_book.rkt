#lang racket

; https://kmicinski.com//cis531-f25/


;(module ch1 racket
;  (provide (all-defined-out))
(require rackunit)
(struct Int (value))
(struct Prim (op args))
(struct Prog (info body))

(define (leaf arith)
    (match arith
        [(Int v) #t]
        [(Prim 'read '()) #t]
        [(Prim '- (list e1)) #f]
        [(Prim '+ (list e1 e2)) #f]
        [(Prim '- (list e1 e2)) #f]
))

(check-true (leaf (Int 3)))
(check-true (leaf (Prim 'read '())))


(define (is_exp ast)
    (match ast
        [(Int v) #t]
        [(Prim 'read '()) #t]
        [(Prim '- (list e1)) (is_exp e1)]
        [(Prim '+ (list e1 e2)) (and (is_exp e1) (is_exp e2))]
        [(Prim '- (list e1 e2)) (and ( is_exp e1) (is_exp e2))]
        [else #f]
    )
)

(check-true (is_exp (Int 3)))
(check-true (is_exp (Prim 'read '())))
(check-true (is_exp (Prim '- (list (Int 3)))))
(check-true (is_exp (Prim '+ (list (Int 3) (Int 4)))))
(check-false (is_exp (Prim 'foo '())))

(define (is_Lint ast)
    (match ast
        [(Prog info body) (and (string? info) (is_exp body))]
        [else #f]
    )
)

(define (interp_exp e)
    (match e
        [(Int v) v]
        [(Prim 'read '()) (read)]
        [(Prim '- (list e1)) (- (interp_exp e1))]
        [(Prim '+ (list e1 e2)) (+ (interp_exp e1) (interp_exp e2))]
        [(Prim '- (list e1 e2)) (- (interp_exp e1) (interp_exp e2))]
        [else (error "unknown expression" e)]
    )
)


;(module ch2 racket
;(require ch1)
;  (is_exp (Int 7))
; )

