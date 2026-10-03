(declare-const n Int)(declare-const m Int)(assert (= (* m m) (+ (* n n n) 5)))(assert (> n 0))(check-sat)
