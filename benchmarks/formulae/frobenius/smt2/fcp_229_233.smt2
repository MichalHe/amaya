(set-logic LIA)
(declare-fun P () Int)
(assert (and (<= 0 P) (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 229) (* x1 233)) P)))) (forall ((R Int)) (=> (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 229) (* x1 233)) R)))) (<= R P)))))
(check-sat)
(exit)
