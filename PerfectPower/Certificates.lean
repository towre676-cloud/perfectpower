import PerfectPower.RungeReduction

open Polynomial
open scoped Classical

namespace PerfectPower

/-! ### Support for machine-generated hit-set certificates

`python -m perfectpower lean` emits theorems in `PerfectPower/Generated/*.lean` that use only
the lemmas below and `runge_pointwise`. -/

/-- A value strictly between consecutive `d`-th powers (in absolute value) is not a hit. -/
lemma not_isHit_between {d : ℕ} {v a : ℤ} (ha : 0 ≤ a)
    (h1 : a ^ d < |v|) (h2 : |v| < (a + 1) ^ d) : ¬ IsHit d v := by
  rintro ⟨m, rfl⟩
  rw [abs_pow] at h1 h2
  have hm0 : 0 ≤ |m| := abs_nonneg m
  have hlo : a < |m| := by
    by_contra hc; push_neg at hc
    exact absurd (pow_le_pow_left₀ hm0 hc d) (not_le.mpr h1)
  have hhi : |m| < a + 1 := by
    by_contra hc; push_neg at hc
    exact absurd (pow_le_pow_left₀ (by linarith) hc d) (not_le.mpr h2)
  omega

/-- For even `d`, negative values are never hits. -/
lemma not_isHit_neg {d : ℕ} (hd : Even d) {v : ℤ} (hv : v < 0) : ¬ IsHit d v := by
  rintro ⟨m, rfl⟩
  exact absurd (hd.pow_nonneg m) (not_le.mpr hv)

/-- **Sandwich.**  If `a^d < D^d v < (a+1)^d` with `0 ≤ a`, then `v` is not a `d`-th
power: otherwise `D^d v = (D m)^d` would be a `d`-th power strictly between consecutive ones. -/
lemma no_hit_of_sandwich {d : ℕ} {v D a : ℤ} (ha : 0 ≤ a)
    (h1 : a ^ d < D ^ d * v) (h2 : D ^ d * v < (a + 1) ^ d) : ¬ IsHit d v := by
  rintro ⟨m, rfl⟩
  have hpos : 0 ≤ D ^ d * m ^ d := le_trans (pow_nonneg ha d) h1.le
  refine not_isHit_between (v := D ^ d * m ^ d) (a := a) ha ?_ ?_ ⟨D * m, by ring⟩
  · rwa [abs_of_nonneg hpos]
  · rwa [abs_of_nonneg hpos]

end PerfectPower
