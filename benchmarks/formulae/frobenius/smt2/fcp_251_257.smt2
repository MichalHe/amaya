(set-logic LIA)
(declare-fun P () Int)
(assert (and (<= 0 P) (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 251) (* x1 257)) P)))) (forall ((R Int)) (=> (forall ((x0 Int) (x1 Int)) (=> (and (<= 0 x0) (<= 0 x1)) (not (= (+ (* x0 251) (* x1 257)) R)))) (<= R P)))))
(check-sat)
(exit)
