(set-logic QF_NIA)
(declare-const _pp_integer_0 Int)
(assert (= (* (+ (- 1) (* 3 _pp_integer_0)) (+ (- 1) (* 3 _pp_integer_0))) 1))
(check-sat)
