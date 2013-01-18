(set-logic QF_NRA)
(set-info :source | KeYmaera example: nl36, node 51
Andre Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. In Renate A. Schmidt, editor, International Conference on Automated Deduction, CADE'09, Montreal, Canada, Proceedings, volume 5663 of LNCS, pages 485(- 501.) Springer, 2009.
 |)
(set-info :smt-lib-version 2.0)
(declare-fun x () Real)
(assert (not (implies (not (>= (* (- 1) x) (- 1))) (not (>= (+ x (* (- 1) (* x x))) 0)))))
(check-sat)