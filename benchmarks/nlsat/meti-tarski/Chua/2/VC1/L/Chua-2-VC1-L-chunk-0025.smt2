(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (<= skoS (* skoC (/ 400. 441.))) (and (not (<= (* skoC (/ 400. 441.)) skoS)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoS))) (and (or (not (<= 0. skoX)) (or (not (<= skoX (/ 1570. 21.))) (<= 0. skoC))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)