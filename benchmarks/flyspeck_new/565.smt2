(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert (<= 2.5854 x1))
(assert (<= x1 2.6508))
(assert (<= 2.0 x2))
(assert (<= x2 2.46350884418))
(assert (<= 2.0 x3))
(assert (<= x3 2.46350884418))
(assert (<= 2.0 x4))
(assert (<= x4 2.46350884418))
(assert (<= 2.0 x5))
(assert (<= x5 2.46350884418))
(assert (<= 1.0 x6))
(assert (<= x6 1.0))
(assert (not (< (+ (* 1.0 (* 2.0 (* 3.14159265 0.128506))) (+ (* x1 0.290371) (+ (* x1 (- 0.070878)) (+ (* x1 (- 0.097658)) (+ (* x1 (- 0.121835)) (+ (* x2 (* 2.0 0.003287)) (+ (* x2 (* 2.0 (- 0.003287))) (+ (* x3 (* 2.0 (- 0.003287))) (+ (* x3 (* 2.0 0.003287)) (+ (* x4 (* 2.0 0.003287)) (+ (* x4 (* 2.0 (- 0.003287))) (+ (* x5 (* 2.0 (- 0.003287))) (+ (* x5 (* 2.0 0.003287)) (+ (* 1.0 (- 1.026581)) (+ (* 1.0 0.033394) (+ (* 1.0 0.050047) (* 1.0 0.13571))))))))))))))))) 0.0)))
(check-sat)
(exit)
