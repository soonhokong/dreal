(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert (<= 3.0 x1))
(assert (<= x1 64.0))
(assert (<= 1.0 x2))
(assert (<= x2 1.0))
(assert (<= 1.0 x3))
(assert (<= x3 1.0))
(assert (<= 1.0 x4))
(assert (<= x4 1.0))
(assert (<= 1.0 x5))
(assert (<= x5 1.0))
(assert (<= 1.0 x6))
(assert (<= x6 1.0))
(assert (not (< (+ (* 1.0 0.591) (+ (* x1 (- 0.0331)) (+ (* 1.0 (* 0.506 (* 1.26 (/ 1.0 (+ 1.26 (- 1.0)))))) (+ (* 1.0 (* 0.506 (- (/ 1.0 (+ 1.26 (- 1.0)))))) (+ (* 1.0 1.0) (+ (* 1.0 (* 2.0 (- 3.14159265))) (* (* x1 (arcsin (* (cos 0.797) (sin (/ 3.14159265 x1))))) 2.0))))))) 0.0)))
(check-sat)
(exit)
