(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* (- 1) skoX) 0)) (and (not (<= (* skoX skoX) (- 3))) (and (not (<= (+ (* 1200 skoX) (* 1200 skoY) (* 900 skoZ) (* 1330 (* skoX skoX)) (* 1596 (* skoX skoY)) (* 1197 (* skoY skoY)) (* 2394 (* skoX skoZ)) (* 2394 (* skoY skoZ)) (* 1197 (* skoZ skoZ)) (* 1200 (* skoX skoX skoX)) (* 1600 (* skoX skoX skoY)) (* 1200 (* skoX skoY skoY)) (* 2100 (* skoX skoX skoZ)) (* 1800 (* skoX skoY skoZ)) (* 1800 (* skoY skoY skoZ)) (* 900 (* skoX skoZ skoZ)) (* 900 (* skoY skoZ skoZ)) (* 900 (* skoY skoY skoY)) (* 399 (* skoX skoX skoX skoX)) (* 532 (* skoX skoX skoX skoY)) (* 798 (* skoX skoX skoY skoY)) (* (- 1596) (* skoX skoX skoY skoZ)) (* (- 2394) (* skoX skoY skoY skoZ)) (* 798 (* skoX skoX skoX skoZ)) (* 399 (* skoX skoX skoZ skoZ)) (* (- 2394) (* skoX skoY skoZ skoZ)) (* 400 (* skoX skoX skoX skoY skoY)) (* 600 (* skoX skoX skoY skoY skoY)) (* (- 1800) (* skoX skoX skoX skoY skoZ)) (* (- 2100) (* skoX skoX skoY skoY skoZ)) (* (- 1800) (* skoX skoY skoY skoY skoZ)) (* (- 1500) (* skoX skoX skoY skoZ skoZ)) (* (- 1800) (* skoX skoY skoY skoZ skoZ)) (* 133 (* skoX skoX skoX skoX skoY skoY)) (* (- 798) (* skoX skoX skoX skoY skoY skoZ)) (* (- 798) (* skoX skoX skoX skoX skoY skoZ)) (* (- 798) (* skoX skoX skoX skoY skoZ skoZ)) (* 1197 (* skoX skoX skoY skoY skoZ skoZ)) (* 100 (* skoX skoX skoX skoX skoY skoY skoY)) (* (- 300) (* skoX skoX skoX skoX skoY skoY skoZ)) (* (- 600) (* skoX skoX skoX skoY skoY skoY skoZ)) (* 300 (* skoX skoX skoX skoY skoY skoZ skoZ)) (* 900 (* skoX skoX skoY skoY skoY skoZ skoZ)) (* 399 (* skoX skoX skoX skoX skoY skoY skoZ skoZ)) (* 300 (* skoX skoX skoX skoX skoY skoY skoY skoZ skoZ))) (- 399))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= (* (- 1) skoY) (- 1))) (not (<= (+ (* (- 1) skoX) skoY) 0)))))))))
(set-info :status sat)
(check-sat)