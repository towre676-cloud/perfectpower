(set-logic QF_NIA)
; Hypothetical configuration check: N(N-1)/2 unordered pairs must equal a square S^2,
; with 2 <= N <= 10^9.  Goal: N mod 4 is 1 or 2 (true for every solution: 2, 9, 50, 289, ...).
(declare-const N Int)
(declare-const S Int)
(assert (>= N 2))
(assert (<= N 1000000000))
(assert (= (* N (- N 1)) (* 2 S S)))
; negated goal
(assert (or (= (mod N 4) 0) (= (mod N 4) 3)))
(check-sat)
