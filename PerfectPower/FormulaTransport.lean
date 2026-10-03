import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Exact arithmetic replacements inside surrounding formulas

The consumer supplies a complete relation theorem; these lemmas retain every
surrounding constraint, including variables not occurring in the relation.
The singular square/cube relation is parametrized over all integers.
-/
namespace PerfectPower.FormulaTransport

/-- Compose a complete finite list with an arbitrary consumer predicate. -/
theorem finite_relation {α β : Type*} (R : α → β → Prop)
    (L : List (α × β))
    (complete : ∀ x y, R x y ↔ (x, y) ∈ L)
    (C : α → β → Prop) (x : α) (y : β) :
    (R x y ∧ C x y) ↔
      ∃ p ∈ L, x = p.1 ∧ y = p.2 ∧ C p.1 p.2 := by
  constructor
  · rintro ⟨hR, hC⟩
    exact ⟨(x, y), (complete x y).mp hR, rfl, rfl, hC⟩
  · rintro ⟨⟨a, b⟩, hp, rfl, rfl, hC⟩
    exact ⟨(complete x y).mpr hp, hC⟩

/-- Eliminate both arithmetic unknowns while retaining a residual predicate. -/
theorem finite_exists {α β : Type*} (R : α → β → Prop)
    (L : List (α × β))
    (complete : ∀ x y, R x y ↔ (x, y) ∈ L)
    (C : α → β → Prop) :
    (∃ x y, R x y ∧ C x y) ↔ ∃ p ∈ L, C p.1 p.2 := by
  constructor
  · rintro ⟨x, y, hR, hC⟩
    exact ⟨(x, y), (complete x y).mp hR, hC⟩
  · rintro ⟨⟨x, y⟩, hp, hC⟩
    exact ⟨x, y, (complete x y).mpr hp, hC⟩

/-- The singular cubic has an exact one-parameter integer solution set. -/
theorem square_eq_cube (x y : ℤ) :
    x ^ 2 = y ^ 3 ↔ ∃ t : ℤ, x = t ^ 3 ∧ y = t ^ 2 := by
  constructor
  · intro h
    have hq : (x : ℚ) ^ 2 = (y : ℚ) ^ 3 := by exact_mod_cast h
    obtain ⟨c, hx, hy⟩ :=
      (pow_eq_pow_iff_of_coprime (by decide : Nat.Coprime 2 3)).mp hq
    have hden : (c ^ 3).den = 1 := by rw [← hx]; simp
    rw [Rat.den_pow] at hden
    have hc : c.den = 1 := (pow_eq_one_iff (by decide : (3 : ℕ) ≠ 0)).mp hden
    have he : c = (c.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hc).symm
    rw [he] at hx hy
    refine ⟨c.num, ?_, ?_⟩
    · exact_mod_cast hx
    · exact_mod_cast hy
  · rintro ⟨t, rfl, rfl⟩
    ring

/-- The parametrization remains equivalent under an arbitrary constraint. -/
theorem square_cube_context (C : ℤ → ℤ → Prop) (x y : ℤ) :
    (x ^ 2 = y ^ 3 ∧ C x y) ↔
      ∃ t : ℤ, x = t ^ 3 ∧ y = t ^ 2 ∧ C (t ^ 3) (t ^ 2) := by
  constructor
  · rintro ⟨h, hC⟩
    obtain ⟨t, rfl, rfl⟩ := (square_eq_cube x y).mp h
    exact ⟨t, rfl, rfl, hC⟩
  · rintro ⟨t, rfl, rfl, hC⟩
    exact ⟨(square_eq_cube _ _).mpr ⟨t, rfl, rfl⟩, hC⟩

theorem square_cube_exists (C : ℤ → ℤ → Prop) :
    (∃ x y : ℤ, x ^ 2 = y ^ 3 ∧ C x y) ↔
      ∃ t : ℤ, C (t ^ 3) (t ^ 2) := by
  constructor
  · rintro ⟨x, y, h, hC⟩
    obtain ⟨t, rfl, rfl⟩ := (square_eq_cube x y).mp h
    exact ⟨t, hC⟩
  · rintro ⟨t, hC⟩
    exact ⟨t ^ 3, t ^ 2, by ring, hC⟩

end PerfectPower.FormulaTransport
