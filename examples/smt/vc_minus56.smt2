(set-logic QF_NIA)
(declare-const n Int)
(declare-const m Int)
(declare-const len Int)
; hypotheses of a verification condition
(assert (>= n 1))
(assert (= (* m m) (- (* n n n) 56)))
(assert (= len (+ (* 2 n) m)))
; negated goal: len <= 200
(assert (not (<= len 200)))
