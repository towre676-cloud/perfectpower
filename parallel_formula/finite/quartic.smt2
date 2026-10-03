(declare-const u Int)(declare-const v Int)(assert (= (* v v) (+ (* 3 u u u u) (* 3 u u) 1)))(assert (> u 0))(check-sat)
