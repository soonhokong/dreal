(set-logic QF_NRA)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (+ (* (- 157) (* skoB skoT skoS)) (* (- 100) (* skoT skoT skoS)) (* (- 100) (* skoB skoA skoS)) (* 100 (* skoB skoT skoT skoA)) (* 100 (* skoB skoT skoT skoS)) (* (- 100) (* skoB skoB skoT skoT))) 0)) (and (not (<= skoA 0)) (and (or (not (<= (* (- 1) skoT) 0)) (not (<= skoT 1))) (and (not (<= skoA 0)) (and (not (<= (* (- 1) skoB) (- 2))) (not (<= (+ skoB (* (- 1) skoA)) 0))))))))
(set-info :status sat)
(check-sat)