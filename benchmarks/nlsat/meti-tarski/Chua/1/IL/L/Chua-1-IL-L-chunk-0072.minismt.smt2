(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (+ (* (- 42) skoS) (* (- 235) skoC)) 0)) (not (<= (+ (* 5175000 skoX) (* (- 207) (* skoX skoX))) 43125000000))))
(set-info :status unsat)
(check-sat)