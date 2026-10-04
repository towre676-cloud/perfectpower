(set-logic QF_LIA)
(declare-const _pp_integer_0 Int)
(assert (and (= (mod (+ 4 (* (- 1) _pp_integer_0)) 3) 1) (> _pp_integer_0 0)))
(check-sat)
