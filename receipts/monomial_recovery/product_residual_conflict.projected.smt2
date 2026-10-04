(set-logic QF_LIA)
(declare-const z Int)
(assert (or (and (= z 12) (> z 12)) (and (= z 12) (> z 12)) (and (= z 12) (> z 12)) (and (= z 12) (> z 12)) (and (= z 12) (> z 12)) (and (= z 12) (> z 12))))
(check-sat)
