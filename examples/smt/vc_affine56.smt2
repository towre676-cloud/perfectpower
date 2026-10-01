(set-logic QF_NIA)
; Constructed: hypothesis m^2 = (3n+15)^3 - 56 (an affine disguise of y^2 = x^3 - 56).
; Goal: n = 1.
(declare-const n Int)
(declare-const m Int)
(assert (= (* m m) (- (* (+ (* 3 n) 15) (+ (* 3 n) 15) (+ (* 3 n) 15)) 56)))
; negated goal
(assert (not (= n 1)))
(check-sat)
