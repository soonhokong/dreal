(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSM () Real)
(declare-fun skoSP () Real)
(declare-fun skoS2 () Real)
(assert (and (not (<= (* skoSP (+ (/ (- 13.) 8.) (* skoS2 (/ (- 63.) 20.)))) (+ (/ 1. 5.) (* skoSM (+ (/ (- 61.) 40.) (* skoS2 (/ (- 63.) 20.))))))) (and (not (<= (* skoX (+ (+ (+ (- 8.) (* skoSM (- 2.))) (* skoSP (- 2.))) (* skoX (+ (+ (+ (/ (- 2.) 5.) (* skoSM (+ (/ 61. 20.) (* skoS2 (/ 63. 10.))))) (* skoSP (+ (/ (- 13.) 4.) (* skoS2 (/ (- 63.) 10.))))) (* skoX (+ (+ 4. skoSM) skoSP)))))) (+ (+ (/ (- 2.) 5.) (* skoSM (+ (/ 61. 20.) (* skoS2 (/ 63. 10.))))) (* skoSP (+ (/ (- 13.) 4.) (* skoS2 (/ (- 63.) 10.))))))) (and (not (<= (* skoX (+ (+ (+ 4. skoSM) skoSP) (* skoX (+ (+ (/ 1. 5.) (* skoSM (+ (/ (- 61.) 40.) (* skoS2 (/ (- 63.) 20.))))) (* skoSP (+ (/ 13. 8.) (* skoS2 (/ 63. 20.)))))))) (+ (+ (/ 1. 5.) (* skoSM (+ (/ (- 61.) 40.) (* skoS2 (/ (- 63.) 20.))))) (* skoSP (+ (/ 13. 8.) (* skoS2 (/ 63. 20.))))))) (and (not (<= skoX 0.)) (and (not (<= skoSP 0.)) (and (not (<= skoSM 0.)) (and (not (<= skoS2 0.)) (not (<= 1. skoX))))))))))
(set-info :status unsat)
(check-sat)