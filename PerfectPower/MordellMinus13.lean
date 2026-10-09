import PerfectPower.MordellMinus13Core
import PerfectPower.Basic

namespace PerfectPower.MordellMinus13

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 13` is a perfect square iff `n = 17`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 13) ↔ n = 17 := by
  constructor
  · rintro ⟨m, hm⟩
    have := ((points n m).mp hm.symm).1
    exact_mod_cast this
  · rintro rfl
    exact ⟨70, by norm_num⟩

end PerfectPower.MordellMinus13
