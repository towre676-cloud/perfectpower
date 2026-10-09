import PerfectPower.MordellMinus5Core
import PerfectPower.Basic

namespace PerfectPower.MordellMinus5

/-- **Complete (empty) hit list.**  `n^3 - 5` is never a perfect square. -/
theorem not_isHit (n : ℤ) : ¬ IsHit 2 (n ^ 3 - 5) := by
  rintro ⟨m, hm⟩
  exact no_points n m hm.symm

end PerfectPower.MordellMinus5
