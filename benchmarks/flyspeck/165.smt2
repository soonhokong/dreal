(set-logic QF_NLR)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)
(declare-fun y5 () Real)
(declare-fun y6 () Real)
(assert
(and
(and (<= 2.0 y1) (<= y1 2.52))(and (<= 1.0 y2) (<= y2 1.0))(and (<= 1.0 y3) (<= y3 1.0))(and (<= 1.0 y4) (<= y4 1.0))(and (<= 1.0 y5) (<= y5 1.0))(and (<= 1.0 y6) (<= y6 1.0))(not (< (+ (+ (/ 3.14159265 2.0) (ite (< (ite (<= 0.0 (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) (- (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)))) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5)) (arctan (/ (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5))) (ite (< 0.0 (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))) (- (/ 3.14159265 2.0) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))))) (ite (< (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) 0.0) (- (- (/ 3.14159265 2.0)) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))))) 3.14159265)))) (+ (/ 3.14159265 2.0) (ite (< (ite (<= 0.0 (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) (- (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)))) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5)) (arctan (/ (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5))) (ite (< 0.0 (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))) (- (/ 3.14159265 2.0) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))))) (ite (< (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0)) 0.0) (- (- (/ 3.14159265 2.0)) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* 2.0 2.0) (* 2.0 2.0))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (* 2.0 (* (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))))))) 0.5) (- (- (* (* 2.0 1.26) (* 2.0 1.26)) (* y1 y1)) (* 2.0 2.0))))) 3.14159265))))) (+ (+ (/ 3.14159265 2.0) (ite (< (ite (<= 0.0 (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26)))) (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26))) (- (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26))))) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5)) (arctan (/ (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26))) (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5))) (ite (< 0.0 (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26)))) (- (/ 3.14159265 2.0) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5) (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26)))))) (ite (< (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26))) 0.0) (- (- (/ 3.14159265 2.0)) (arctan (/ (^ (+ (- (- (* (- (* y1 y1)) (* y1 y1)) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* 2.0 2.0))) (+ (* 2.0 (* (* y1 y1) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5) (- (- (* 2.0 2.0) (* y1 y1)) (* (* 2.0 1.26) (* 2.0 1.26)))))) 3.14159265)))) (+ (/ 3.14159265 3.0) (+ (/ 3.14159265 2.0) (ite (< (ite (<= 0.0 (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26)))) (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (- (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))))) (^ (+ (- (- (* (- (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5)) (arctan (/ (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (^ (+ (- (- (* (- (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5))) (ite (< 0.0 (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26)))) (- (/ 3.14159265 2.0) (arctan (/ (^ (+ (- (- (* (- (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5) (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26)))))) (ite (< (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) 0.0) (- (- (/ 3.14159265 2.0)) (arctan (/ (^ (+ (- (- (* (- (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* (* 2.0 2.0) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0))) (+ (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* (* 2.0 1.26) (* 2.0 1.26)))) (* 2.0 (* (* (* 2.0 1.26) (* 2.0 1.26)) (* 2.0 2.0)))))) 0.5) (- (- (* 2.0 2.0) (* (* 2.0 1.26) (* 2.0 1.26))) (* (* 2.0 1.26) (* 2.0 1.26)))))) 3.14159265)))))))))
)
(check-sat)
(exit)