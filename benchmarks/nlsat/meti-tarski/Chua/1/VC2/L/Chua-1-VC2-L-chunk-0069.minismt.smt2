(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoX 12500)) (and (not (<= skoX 0)) (or (not (<= (+ (* (- 13) skoS) (* 3 skoC)) 0)) (not (<= (+ (* 13 skoS) (* (- 3) skoC)) 0))))))
(set-info :status sat)
(check-sat)