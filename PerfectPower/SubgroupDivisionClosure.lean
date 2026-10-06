import PerfectPower.EllipticDivision

namespace PerfectPower.SubgroupDivisionClosure
variable {G : Type*} [AddCommGroup G]

def Closed (S : AddSubgroup G) (n : ℤ) : Prop := ∀ Q, n • Q ∈ S → Q ∈ S

theorem closed_one (S : AddSubgroup G) : Closed S 1 := by
  intro Q h; simpa using h

/-- Joint prime closure implies closure under their products, without rank information. -/
theorem closed_mul (S : AddSubgroup G) (m n : ℤ) (hm : Closed S m) (hn : Closed S n) :
    Closed S (m*n) := by
  intro Q h
  rw [mul_smul] at h
  exact hn Q (hm (n • Q) h)

theorem closed_pow (S : AddSubgroup G) (n : ℤ) (hn : Closed S n) (k : ℕ) :
    Closed S (n^k) := by
  induction k with
  | zero => simpa using closed_one S
  | succ k hk => rw [pow_succ]; exact closed_mul S (n^k) n hk hn

theorem closed_two_three (S : AddSubgroup G) (h2 : Closed S 2) (h3 : Closed S 3)
    (a b : ℕ) : Closed S (2^a*3^b) :=
  closed_mul S _ _ (closed_pow S 2 h2 a) (closed_pow S 3 h3 b)

end PerfectPower.SubgroupDivisionClosure
