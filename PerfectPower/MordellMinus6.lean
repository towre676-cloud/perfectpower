import PerfectPower.MordellMinus6Core
import PerfectPower.Basic

namespace PerfectPower.MordellMinus6

/-- **Complete (empty) hit list.**  `n^3 - 6` is never a perfect square. -/
theorem not_isHit (n : ℤ) : ¬ IsHit 2 (n ^ 3 - 6) := by
  rintro ⟨m, hm⟩
  exact no_points n m hm.symm

end PerfectPower.MordellMinus6
