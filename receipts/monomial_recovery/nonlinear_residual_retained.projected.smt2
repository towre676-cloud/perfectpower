(set-logic QF_NIA)
(declare-const z Int)
(assert (or (and (= (* z z) 1) (> z 1)) (and (= (* z z) 2) (> z 1)) (and (= (* z z) 3) (> z 1)) (and (= (* z z) 4) (> z 1)) (and (= (* z z) 6) (> z 1)) (and (= (* z z) 12) (> z 1))))
(check-sat)
