import PerfectPower.MordellMinus1

/-! A complete genus-one even-quartic pilot, including its zero fibre. -/
namespace PerfectPower.QuarticPilot

theorem forward (u v : ℤ) (h : v ^ 2 = 3 * u ^ 4 + 3 * u ^ 2 + 1) :
    (3 * u * v) ^ 2 = (3 * u ^ 2 + 1) ^ 3 - 1 := by
  nlinarith [sq_nonneg u]

/-- All integral solutions, without a nonzero-coordinate assumption. -/
theorem complete (u v : ℤ) :
    v ^ 2 = 3 * u ^ 4 + 3 * u ^ 2 + 1 ↔ u = 0 ∧ (v = 1 ∨ v = -1) := by
  constructor
  · intro h
    obtain ⟨hx, _⟩ := (MordellMinus1.points_iff _ _).mp (forward u v h)
    have hu : u = 0 := by nlinarith [sq_nonneg u]
    subst u
    norm_num at h
    constructor
    · rfl
    · exact h
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

/-- A non-square value at every nonzero integer argument. This gives an exact
non-square count on any finite collection of nonzero arguments. -/
theorem nonzero_not_square (u : ℤ) (hu : u ≠ 0) :
    ¬ ∃ v : ℤ, v ^ 2 = 3*u^4+3*u^2+1 := by
  rintro ⟨v,hv⟩
  exact hu ((complete u v).mp hv).1

/-- Every positive even exponent is excluded at a nonzero argument. -/
theorem nonzero_not_even_power (u : ℤ) (hu : u ≠ 0) (d : ℕ) :
    ¬ ∃ v : ℤ, v^(2*d)=3*u^4+3*u^2+1 := by
  rintro ⟨v,hv⟩
  apply nonzero_not_square u hu
  refine ⟨v^d,?_⟩
  simpa only [← pow_mul, Nat.mul_comm] using hv

end PerfectPower.QuarticPilot
