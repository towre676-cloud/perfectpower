import PerfectPower.MordellMinus4Core
import PerfectPower.Basic

namespace PerfectPower.MordellMinus4

theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 4) ↔ n = 2 ∨ n = 5 := by
  constructor
  · rintro ⟨m, hm⟩
    rcases (points n m).mp hm.symm with ⟨h, -⟩ | ⟨h, -⟩
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨11, by norm_num⟩

end PerfectPower.MordellMinus4
