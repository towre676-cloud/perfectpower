import PerfectPower.FactorialWindow

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
theorem factorial_window_not_power : ¬∃ a:ℕ, a≠0 ∧ PerfectPower.FactorialWindow.window 1000000000000000000000000000000 100000000000000000000=a^2 := by
  apply PerfectPower.FactorialWindow.not_power 2 1000000000000000000000000000000 100000000000000000000 2
  rw [PerfectPower.FactorialWindow.legendre_window 2 1000000000000000000000000000000 100000000000000000000 100
    (Nat.log_lt_of_lt_pow (by decide +kernel) (by decide +kernel)) (Nat.log_lt_of_lt_pow (by decide +kernel) (by decide +kernel))]
  decide +kernel
