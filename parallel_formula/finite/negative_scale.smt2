(declare-const n Int)(declare-const m Int)(assert (= (* m m) (- (* (+ (* (- 3) n) 1) (+ (* (- 3) n) 1) (+ (* (- 3) n) 1)) 1)))(assert (>= n 0))(check-sat)
