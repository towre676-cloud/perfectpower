(set-logic QF_NIA)
; Constructed: m^2 = (2n+1)^3 - 5 has no integer solution (y^2 = x^3 - 5, MordellMinus5).
; The verification condition is that this hypothesis is impossible (the task is unsat).
(declare-const n Int)
(declare-const m Int)
(assert (= (* m m) (- (* (+ (* 2 n) 1) (+ (* 2 n) 1) (+ (* 2 n) 1)) 5)))
(check-sat)
