(declare-const n Int)(declare-const m Int)(assert (= (* m m) (+ (* (+ (* 2 n) 0) (+ (* 2 n) 0) (+ (* 2 n) 0)) 2)))(check-sat)
