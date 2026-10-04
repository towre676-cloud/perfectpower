(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* (+ (* 1 y) 0) (+ (* 1 y) 0)) (+ (* (+ (* 6 x) 1) (+ (* 6 x) 1) (+ (* 6 x) 1)) 22)))

(check-sat)
