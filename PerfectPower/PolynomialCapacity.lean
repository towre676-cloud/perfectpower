import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Certificate interpretation for polynomial transports and discrete optimization.
The certificate producer must discharge coverage and descent hypotheses. -/
namespace PerfectPower.PolynomialCapacity

/-- Scaling a rational-polynomial equation keeps the transformed witness image. -/
theorem denominator_transport (D N y : ℤ) (d : ℕ) (hD : D ≠ 0) (hd : d ≠ 0) :
    D * y ^ d = N ↔ (D * y) ^ d = D ^ (d - 1) * N := by
  have he : d = (d - 1) + 1 := by omega
  have hp : D ^ d = D ^ (d - 1) * D := by calc
    D ^ d = D ^ ((d - 1) + 1) := congrArg (D ^ ·) he
    _ = D ^ (d - 1) * D := pow_succ _ _
  rw [mul_pow, hp, mul_assoc]
  constructor
  · intro h; rw [h]
  · exact mul_left_cancel₀ (pow_ne_zero _ hD)

/-- Divisibility recovers exactly the original integer witnesses. -/
theorem witness_image (D z : ℤ) : D ∣ z ↔ ∃ y : ℤ, z = D * y := by
  rfl

/-- A shared outer polynomial can be cancelled only with injectivity. -/
theorem outer_cancel {α β : Type*} (H : α → β) (h : Function.Injective H)
    (u v : α) : H u = H v ↔ u = v := h.eq_iff

/-- A descent certificate forces every global minimizer into the candidate set.
Strict descent is essential: equal adjacent values must retain all ties. -/
theorem minimizers_in_candidates (f : ℤ → ℤ) (feasible candidate : ℤ → Prop)
    (descent : ∀ x, feasible x → ¬ candidate x →
      ∃ y, feasible y ∧ f y < f x) (x : ℤ)
    (hx : feasible x) (minimal : ∀ y, feasible y → f x ≤ f y) : candidate x := by
  by_contra hc
  obtain ⟨y, hy, hlt⟩ := descent x hx hc
  exact (not_lt_of_ge (minimal y hy)) hlt

/-- Finite-domain descent and a finite candidate comparison certify a global bound. -/
theorem candidate_lower_bound (f : ℤ → ℤ) (S C : Finset ℤ) (m : ℤ)
    (descent : ∀ x ∈ S, x ∉ C → ∃ y ∈ S, f y < f x)
    (checked : ∀ x ∈ S, x ∈ C → m ≤ f x) : ∀ x ∈ S, m ≤ f x := by
  intro x hx
  obtain ⟨y, hy, hmin⟩ := S.exists_min_image f ⟨x, hx⟩
  have hc : y ∈ C := minimizers_in_candidates f (· ∈ S) (· ∈ C)
    (by simpa using descent) y hy hmin
  exact le_trans (checked y hy hc) (hmin x hx)

/-- Exact optimizer membership, including every equal-value candidate. -/
theorem optimizer_iff (f : ℤ → ℤ) (S C : Finset ℤ) (m x : ℤ)
    (descent : ∀ x ∈ S, x ∉ C → ∃ y ∈ S, f y < f x)
    (checked : ∀ x ∈ S, x ∈ C → m ≤ f x)
    (attained : ∃ y ∈ S, f y = m) :
    (x ∈ S ∧ ∀ y ∈ S, f x ≤ f y) ↔ x ∈ S ∧ x ∈ C ∧ f x = m := by
  constructor
  · rintro ⟨hx, hm⟩
    obtain ⟨y, hy, he⟩ := attained
    have hlo := candidate_lower_bound f S C m descent checked x hx
    have hhi := hm y hy
    exact ⟨hx, minimizers_in_candidates f (· ∈ S) (· ∈ C)
      (by simpa using descent) x hx hm, by omega⟩
  · rintro ⟨hx, _, he⟩
    exact ⟨hx, fun y hy => he ▸ candidate_lower_bound f S C m descent checked y hy⟩

/-- A negative forward difference supplies the right-neighbor descent witness. -/
theorem right_descent (f : ℤ → ℤ) (x : ℤ) (h : f (x + 1) - f x < 0) :
    f (x + 1) < f x := by omega

/-- A positive preceding difference supplies the left-neighbor descent witness. -/
theorem left_descent (f : ℤ → ℤ) (x : ℤ) (h : 0 < f x - f (x - 1)) :
    f (x - 1) < f x := by omega

/-- Exact all-integer optimizer set for the tied quartic used by the new API. -/
theorem quartic_ties (x : ℤ) :
    (∀ y : ℤ, x ^ 2 * (x - 1) ^ 2 ≤ y ^ 2 * (y - 1) ^ 2) ↔ x = 0 ∨ x = 1 := by
  have hn : 0 ≤ x ^ 2 * (x - 1) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · intro h
    have hz := h 0
    have he : x ^ 2 * (x - 1) ^ 2 = 0 := by nlinarith
    rcases mul_eq_zero.mp he with ha | hb
    · left; nlinarith [sq_nonneg x]
    · right; nlinarith [sq_nonneg (x - 1)]
  · rintro (rfl | rfl) <;> intro y <;>
      simpa using mul_nonneg (sq_nonneg y) (sq_nonneg (y - 1))

/-- Natural-index fixed-width binomial numerator has both minimizers 0 and 1. -/
theorem binomial_two_ties (x : ℤ) (hx : 0 ≤ x) :
    (∀ y : ℤ, 0 ≤ y → x * (x - 1) ≤ y * (y - 1)) ↔ x = 0 ∨ x = 1 := by
  have nonneg : ∀ y : ℤ, 0 ≤ y → 0 ≤ y * (y - 1) := by
    intro y hy
    by_cases h : y = 0
    · simp [h]
    · have : 1 ≤ y := by omega
      exact mul_nonneg hy (by omega)
  constructor
  · intro h
    have hl := nonneg x hx
    have hu := h 0 (by omega)
    have he : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> intro y hy <;> simpa using nonneg y hy

/-- Positive denominators preserve the comparison of rational objectives. -/
theorem positive_denominator_order (D a b : ℚ) (hD : 0 < D) :
    a / D ≤ b / D ↔ a ≤ b := (div_le_div_iff_of_pos_right hD)

/-- Removing perfect-power coefficient content retains all integer witnesses. -/
theorem content_power (c N y : ℤ) (d : ℕ) (hc : c ≠ 0) (hd : d ≠ 0) :
    y ^ d = c ^ d * N ↔ ∃ v : ℤ, y = c * v ∧ v ^ d = N := by
  constructor
  · intro h
    have hv : c ^ d ∣ y ^ d := ⟨N, h⟩
    have hdiv : c ∣ y := (Int.pow_dvd_pow_iff hd).mp hv
    obtain ⟨v, he⟩ := hdiv
    refine ⟨v, he, ?_⟩
    rw [he, mul_pow] at h
    exact mul_left_cancel₀ (pow_ne_zero _ hc) h
  · rintro ⟨v, rfl, h⟩
    rw [mul_pow, h]

/-- Boolean predicates used to combine independently certified sign atoms. -/
inductive Formula (ι : Type*) where
  | atom : ι → Formula ι
  | constant : Bool → Formula ι
  | conj : Formula ι → Formula ι → Formula ι
  | disj : Formula ι → Formula ι → Formula ι
  | neg : Formula ι → Formula ι

def Formula.eval {ι : Type*} (v : ι → Bool) : Formula ι → Bool
  | .atom i => v i
  | .constant b => b
  | .conj a b => a.eval v && b.eval v
  | .disj a b => a.eval v || b.eval v
  | .neg a => !(a.eval v)

/-- Certified constant atom values make every Boolean combination constant. -/
theorem boolean_cell {ι : Type*} (F : Formula ι) (values : ℤ → ι → Bool)
    (cell : ℤ → Prop) (sample : ℤ)
    (atoms : ∀ x, cell x → ∀ i, values x i = values sample i) :
    ∀ x, cell x → F.eval (values x) = F.eval (values sample) := by
  intro x hx
  have he : values x = values sample := funext (atoms x hx)
  rw [he]

end PerfectPower.PolynomialCapacity
