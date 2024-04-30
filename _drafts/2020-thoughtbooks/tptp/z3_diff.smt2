(set-option :print-success true) 
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-option :produce-proofs true) ; enable proof generation
(set-option :model.partial true)

(declare-fun diff (Real Real) Real)
(declare-fun x () Real)
(assert (forall ((y Real) (z Real))
  (! (= (+ (diff (* z y) x) (* (- 1.0) (diff y x) z) (* (- 1.0) (diff z x) y))
        0.0)
     :pattern ((diff (* y z) x)))))
(assert (forall ((y Real) (z Real))
  (! (= (+ (diff (+ y z) x) (* (- 1.0) (diff y x) z) (* (- 1.0) (diff z x) y))
        0.0)
     :pattern ((diff (+ y z) x)))))
(assert (= (+ (diff (* x x) x) (* (- 2.0) x)) 0.0))
(assert (= (diff x x) 1.0))
(assert (let ((a!1 (= (+ (diff (* x x x) x) (* (- 3.0) x x)) 0.0)))
  (not a!1)))
(check-sat)
(get-model)