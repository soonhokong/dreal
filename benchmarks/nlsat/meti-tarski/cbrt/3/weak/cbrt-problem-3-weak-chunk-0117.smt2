(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoZ (+ (+ (+ (- 2.) (* skoX (+ (/ (- 130.) 3.) (* skoX (+ (/ (- 88.) 3.) (* skoX (/ 8. 3.))))))) (* skoY (+ (+ (/ (- 130.) 3.) (* skoX (+ (/ (- 668.) 3.) (* skoX (+ (/ (- 340.) 3.) (* skoX (/ 16. 3.))))))) (* skoY (+ (+ (/ (- 88.) 3.) (* skoX (+ (/ (- 340.) 3.) (* skoX (/ 32. 3.))))) (* skoY (+ (/ 8. 3.) (* skoX (/ 16. 3.))))))))) (* skoZ (+ (+ (+ (- 1.) (* skoX (+ (/ (- 88.) 3.) (* skoX (/ 16. 3.))))) (* skoY (+ (+ (/ (- 88.) 3.) (* skoX (+ (/ (- 340.) 3.) (* skoX (/ 32. 3.))))) (* skoY (+ (/ 16. 3.) (* skoX (/ 32. 3.))))))) (* skoZ (+ (+ (/ 4. 3.) (* skoX (/ 8. 3.))) (* skoY (+ (/ 8. 3.) (* skoX (/ 16. 3.)))))))))) (+ (+ (/ (- 5.) 3.) (* skoX (+ 2. (* skoX (+ 1. (* skoX (/ (- 4.) 3.))))))) (* skoY (+ (+ 2. (* skoX (+ (/ 130. 3.) (* skoX (+ (/ 88. 3.) (* skoX (/ (- 8.) 3.))))))) (* skoY (+ (+ 1. (* skoX (+ (/ 88. 3.) (* skoX (/ (- 16.) 3.))))) (* skoY (+ (/ (- 4.) 3.) (* skoX (/ (- 8.) 3.))))))))))) (and (not (<= (* skoZ (+ (+ (+ 13. (* skoX 10.)) (* skoY (+ (+ 36. (* skoX 20.)) (* skoY 20.)))) (* skoZ (+ 10. (* skoY 20.))))) (+ (+ (- 4.) (* skoX (- 5.))) (* skoY (+ (+ (- 13.) (* skoX (- 10.))) (* skoY (- 10.))))))) (and (not (<= skoZ (/ 1. 20.))) (and (not (<= skoY (/ 1. 20.))) (and (not (<= skoX (/ 1. 20.))) (and (not (<= 15. skoZ)) (and (not (<= 15. skoY)) (not (<= 15. skoX))))))))))
(set-info :status sat)
(check-sat)
