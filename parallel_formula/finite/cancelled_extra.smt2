(declare-const n Int)(declare-const m Int)(declare-const z Int)
(assert (= (* m m) (+ (* n n n) 2 (- z z))))
(assert (= z (+ n m)))(check-sat)
