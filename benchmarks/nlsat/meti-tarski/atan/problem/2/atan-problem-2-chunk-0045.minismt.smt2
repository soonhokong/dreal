(set-logic QF_NRA)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* (- 1) (* skoT skoS)) 0) (and (<= (+ (* 10 (* skoB skoS)) (* skoT skoT skoS) (* (- 10) (* skoT skoT skoB)) (* 10 (* skoT skoT skoA))) 0) (and (<= (* skoT skoS) 0) (and (not (<= skoT 0)) (and (= (+ (* skoS skoS) (* (- 1) (* skoT skoT skoA skoA)) (* (- 1) (* skoT skoT skoB skoB)) (* (- 1) (* skoT skoT skoT skoT)) (* (- 1) (* skoB skoB skoA skoA))) 0) (and (<= (* (- 1) skoS) 0) (and (not (= skoT 0)) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))))))
(set-info :status unsat)
(check-sat)