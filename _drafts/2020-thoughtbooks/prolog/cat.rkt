#lang racket
(require minikanren)

(run 3 (q)
       (conde
        [(== q 3)]
        [(== q 4)]))

;(defrel (nullo x) (== '() x))

(fresh (x y z) (== z x))


(run 6 (q)
     (let loop ()
      (conde
[(== q #t)]
[(== q #f)]
[(loop)]
       )))

(define caro
    (lambda (p a)
      (fresh (d)
      (== (cons a d) p))))

(run 3 (q) (caro q 1))

(define (typo f t)
(conde
  [(fresh (a) (== f 'id) (== t `(hom ,a ,a))) ]
  [(== f 'f) (== t '(hom a c))]
  [(fresh (a b) (== f 'snd) (== t `(hom ( ,a ,b) ,b)))]
  [(fresh (a b) (== f 'fst) (== t `(hom ( ,a ,b) ,a)))]
  [(fresh (g h a b c) (== f `(comp ,g ,h))
                       (== t `(hom ,a ,c)) 
                       (typo g `(hom ,a ,b ))
                       (typo h `(hom ,b ,c)))]
  [ (fresh (g h a b c) (== f `(fan ,g ,h))
                       (== t `(hom ,a (,b ,c))) 
                       (typo g `(hom ,a ,b ))
                       (typo h `(hom ,a ,c)))  ]
  )
  )

; could lose the hom
;(run 3 (q) (typo  q '(hom (a b) a)))
;(run 3 (q) (typo  q '(hom ((a b) c) a)))
(run 3 (q) (typo  q '(hom (a b) (b a))))




