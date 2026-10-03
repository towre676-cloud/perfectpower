import PerfectPower.FormulaTransport

/-! Exact affine pullback of complete lists, with both integer image constraints. -/
namespace PerfectPower.FormulaTransport

theorem affine_image (r s t : ℤ) :
    (∃ n : ℤ, r * n + s = t) ↔ r ∣ t - s := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  · intro h
    refine ⟨(t - s) / r, ?_⟩
    have he := Int.ediv_mul_cancel h
    nlinarith

/-- Eliminate an affine integer coordinate; division is used only on its image. -/
theorem affine_finite_exists (R : ℤ → ℤ → Prop) (L : List (ℤ × ℤ))
    (complete : ∀ x y, R x y ↔ (x, y) ∈ L)
    (r s : ℤ) (hr : r ≠ 0) (C : ℤ → ℤ → Prop) :
    (∃ n y : ℤ, R (r*n+s) y ∧ C n y) ↔
      ∃ p ∈ L, r ∣ p.1-s ∧ C ((p.1-s)/r) p.2 := by
  constructor
  · rintro ⟨n, y, hR, hC⟩
    refine ⟨(r*n+s, y), (complete _ _).mp hR, ?_, ?_⟩
    · exact ⟨n, by simp⟩
    · simpa [Int.mul_ediv_cancel_left n hr] using hC
  · rintro ⟨⟨x, y⟩, hp, hdiv, hC⟩
    refine ⟨(x-s)/r, y, ?_, hC⟩
    have he : r * ((x-s)/r) + s = x := by
      have := Int.ediv_mul_cancel hdiv
      nlinarith
    rw [he]
    exact (complete x y).mpr hp

/-- Both coordinates may be disguised; each image lattice is retained. -/
theorem affine_pair_finite_exists (R : ℤ → ℤ → Prop) (L : List (ℤ × ℤ))
    (complete : ∀ x y, R x y ↔ (x, y) ∈ L)
    (r s a b : ℤ) (hr : r ≠ 0) (ha : a ≠ 0) (C : ℤ → ℤ → Prop) :
    (∃ n m : ℤ, R (r*n+s) (a*m+b) ∧ C n m) ↔
      ∃ p ∈ L, r ∣ p.1-s ∧ a ∣ p.2-b ∧
        C ((p.1-s)/r) ((p.2-b)/a) := by
  constructor
  · rintro ⟨n, m, hR, hC⟩
    refine ⟨(r*n+s, a*m+b), (complete _ _).mp hR, ?_, ?_, ?_⟩
    · exact ⟨n, by simp⟩
    · exact ⟨m, by simp⟩
    · simpa [Int.mul_ediv_cancel_left n hr, Int.mul_ediv_cancel_left m ha] using hC
  · rintro ⟨⟨x, y⟩, hp, hx, hy, hC⟩
    refine ⟨(x-s)/r, (y-b)/a, ?_, hC⟩
    have hex : r * ((x-s)/r) + s = x := by
      have := Int.ediv_mul_cancel hx
      nlinarith
    have hey : a * ((y-b)/a) + b = y := by
      have := Int.ediv_mul_cancel hy
      nlinarith
    rw [hex, hey]
    exact (complete x y).mpr hp
end PerfectPower.FormulaTransport
