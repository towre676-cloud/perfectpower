import PerfectPower.MordellMinus2Core
import PerfectPower.Basic

namespace PerfectPower.MordellMinus2

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 2` is a perfect square iff `n = 3`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 2) ↔ n = 3 := by
  constructor
  · rintro ⟨m, hm⟩
    have := ((points n m).mp hm.symm).1
    exact_mod_cast this
  · rintro rfl
    exact ⟨5, by norm_num⟩

end PerfectPower.MordellMinus2
