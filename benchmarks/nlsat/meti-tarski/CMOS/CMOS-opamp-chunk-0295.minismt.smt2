(set-logic QF_NRA)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (+ (* 1800000000000000000000000 (* skoX skoX)) (* 1800000000 (* skoX skoX skoX skoX)) (* (- 900000000000000000000000) (* skoY skoY skoX skoX)) (* (- 900000000) (* skoY skoY skoX skoX skoX skoX))) 0) (and (not (<= (+ (* 143640000000000000000000 (* skoX skoX)) (* 4309343638803 (* skoX skoX skoX skoX)) (* (- 4309271820000000000000000000) (* skoY skoY skoX skoX)) (* (- 4309271820000) (* skoY skoY skoX skoX skoX skoX)) (* 1256850000000000000000000000 (* skoY skoY skoY skoY skoX skoX)) (* 1256850000000 (* skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 95760000000000000000000000) (* skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 95760000000) (* skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* 3099375000000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 3099375000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* (- 54625000000000000000000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* (- 54625000) (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX)) (* 593750000000000000000 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX)) (* 593750 (* skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoY skoX skoX skoX skoX))) 1161089999999997522000000000001197)) (and (<= (* (- 1) skoX) (- 100)) (and (<= skoX 120) (and (<= (+ (* (- 4) skoY) pi) 0) (and (<= (+ (* 3 skoY) (* (- 1) pi)) 0) (and (not (<= (* (- 10000000) pi) (- 31415927))) (not (<= (* 5000000 pi) 15707963))))))))))
(set-info :status unsat)
(check-sat)