import PerfectPower.MordellDescentCore
import PerfectPower.Basic

namespace PerfectPower.MordellDescent

/-- The hit-list form: `n^3 + k` is never a square, for any integer `n`. -/
theorem not_isHit {D c b k : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2)
    (hb : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ b → good D (p % 8))
    {M : ℕ} (hM : 8 ∣ M) (hMpos : 0 < M) (hcong : CongOK D c b M) (hk : k = c ^ 3 - D * b ^ 2) (n : ℤ) :
    ¬ IsHit 2 (n ^ 3 + k) := by
  rintro ⟨m, hm⟩
  exact no_points hD hb hM hMpos hcong n m (by rw [← hk]; exact hm.symm)

end PerfectPower.MordellDescent
