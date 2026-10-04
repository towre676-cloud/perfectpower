import Mathlib

namespace PerfectPower.CanonicalMetric
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The Bergman curvature numerator is a Gram defect, hence nonnegative. -/
theorem gram_defect_nonnegative (u v : V) :
    0 ≤ ‖u‖^2*‖v‖^2-‖inner ℂ u v‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u v
  have hs := (sq_le_sq₀ (norm_nonneg (inner ℂ u v))
    (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mpr h
  nlinarith

theorem curvature_nonpositive (u v : V) :
    -2*(‖u‖^2*‖v‖^2-‖inner ℂ u v‖^2)/(‖u‖^2)^3 ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [gram_defect_nonnegative u v])
    (pow_nonneg (sq_nonneg _) _)

end PerfectPower.CanonicalMetric
