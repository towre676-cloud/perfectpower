import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PerfectPower.StructuralCertificates
open scoped BigOperators

/-- A checked LDL quadratic identity proves nonnegativity, including zero pivots. -/
theorem weighted_squares_nonnegative {ι : Type*} (s : Finset ι) (d z : ι → ℚ)
    (hd : ∀ i ∈ s, 0 ≤ d i) : 0 ≤ ∑ i ∈ s, d i * (z i)^2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hd i hi) (sq_nonneg _)

/-- The acceptance contract for rational Gram/LDL certificates. -/
theorem gram_sound {ι : Type*} (s : Finset ι) (d : ι → ℚ)
    (z : ι → ℚ) (value : ℚ) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hid : value = ∑ i ∈ s, d i * (z i)^2) : 0 ≤ value := by
  rw [hid]
  exact weighted_squares_nonnegative s d z hd

/-- Preordering products retain all supplied inequality hypotheses. -/
theorem constraint_product_nonnegative (g : List ℚ) (hg : ∀ x ∈ g, 0 ≤ x) :
    0 ≤ g.prod := by
  induction g with
  | nil => simp
  | cons a g ih =>
    simp only [List.prod_cons]
    exact mul_nonneg (hg a (by simp)) (ih (fun x hx => hg x (by simp [hx])))

/-- Domain-aware lower bounds: nonnegative preordering terms plus vanishing ideals. -/
theorem lower_bound_sound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (sigma constraint : ι → ℚ) (multiplier equation : κ → ℚ)
    (value lower : ℚ) (hs : ∀ i ∈ s, 0 ≤ sigma i)
    (hc : ∀ i ∈ s, 0 ≤ constraint i) (he : ∀ j ∈ t, equation j = 0)
    (hid : value-lower = (∑ i ∈ s, sigma i*constraint i) +
      (∑ j ∈ t, multiplier j*equation j)) : lower ≤ value := by
  have hzero : (∑ j ∈ t, multiplier j*equation j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [he j hj, mul_zero]
  have hnonneg : 0 ≤ ∑ i ∈ s, sigma i*constraint i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hs i hi) (hc i hi)
  rw [hzero, add_zero] at hid
  linarith

/-- The real-place exclusion used by the two-isogeny cover sieve. -/
theorem negative_quartic_of_nonpositive_middle (d a c u v : ℚ)
    (hd : d < 0) (hc : c < 0) (ha : a ≤ 0) (huv : u ≠ 0 ∨ v ≠ 0) :
    d*u^4+a*u^2*v^2+c*v^4 < 0 := by
  have hu : 0 ≤ u^4 := by positivity
  have hv : 0 ≤ v^4 := by positivity
  have hm : a*u^2*v^2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg _)) (sq_nonneg _)
  rcases huv with h | h
  · have hp : 0 < u^4 := by positivity
    have hn := mul_neg_of_neg_of_pos hd hp
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) hv
    linarith
  · have hp : 0 < v^4 := by positivity
    have hn := mul_neg_of_neg_of_pos hc hp
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hd) hu
    linarith

/-- Both rational cover maps are algebraic identities with explicit denominators. -/
theorem cover_to_curve (a d c u v w : ℚ) (hv : v ≠ 0)
    (hw : w^2=d*u^4+a*u^2*v^2+c*v^4) :
    (d*u*w/v^3)^2 = (d*u^2/v^2)*((d*u^2/v^2)^2+a*(d*u^2/v^2)+d*c) := by
  field_simp [hv]
  linear_combination d^2*u^2*v^8*hw

/-- Numerical rank bounds still retain the classical descent identity as a premise. -/
theorem rank_bound_from_image_sizes (r l m L M : ℕ)
    (hdescent : r+2=l+m) (hl : l ≤ L) (hm : m ≤ M) : r ≤ L+M-2 := by omega

end PerfectPower.StructuralCertificates
