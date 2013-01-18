(set-logic QF_NRA)
(declare-fun y1 () Real)
(declare-fun t3uscore0dollarsk!0 () Real)
(declare-fun e1 () Real)
(declare-fun x1 () Real)
(declare-fun t1uscore0dollarsk!1 () Real)
(declare-fun d1 () Real)
(declare-fun y2 () Real)
(declare-fun e2 () Real)
(declare-fun x2 () Real)
(declare-fun d2 () Real)
(declare-fun om () Real)
(assert (= (+ (* (- 1) y1) x1 (* t1uscore0dollarsk!1 d1) (* (- 1) (* t3uscore0dollarsk!0 e1))) 0))
(assert (= (+ (* (- 1) y2) x2 (* t1uscore0dollarsk!1 d2) (* (- 1) (* t3uscore0dollarsk!0 e2))) 0))
(assert (>= t3uscore0dollarsk!0 0))
(assert (>= t1uscore0dollarsk!1 0))
(assert (= (+ d1 (* x2 om)) 0))
(assert (= (+ d2 (* (- 1) (* x1 om))) 0))
(assert (= (+ e1 (* y2 om)) 0))
(assert (= (+ e2 (* (- 1) (* y1 om))) 0))
(assert (= (+ (* x1 x1) (* x2 x2) (* (- 1) (* y1 y1)) (* (- 1) (* y2 y2))) 0))
(assert (not (= (+ (* (- 1) y1) x1) 0)))
(check-sat)