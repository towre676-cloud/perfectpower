/-
Squareclass representative uniqueness for ℚ — the well-definedness half
of the squareclass quotient identification that PerfectPower's descent
programme names as open (README.md:134;
docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md:107).

PerfectPower's `TwoDescentBridges.rational_point_cover_complete` proves
*existence*: every nonzero rational x is `d * u^2 / v^2` with `d` a
squarefree integer (and, on a curve `y^2 = x * (x^2 + a * x + b)`,
additionally `d ∣ b`). What the squareclass *identification*
additionally needs is that the label `d` is unique — otherwise "the
squareclass of x" is not well defined, and no homomorphism into
ℚ*/ℚ*² can be assembled from the representative. That uniqueness is
what this file proves, against Mathlib (v4.20.0):

* `Int.eq_of_squarefree_of_isSquare_ratCast_div` — if `d₁, d₂` are
  nonzero squarefree integers and `d₁ / d₂` is a square in ℚ, then
  `d₁ = d₂`. (Equivalently: distinct signed squarefree integers lie in
  distinct squareclasses of ℚ*, so the squareclass group of ℚ is
  faithfully labelled by signed squarefree integers.)
* `squareclass_label_unique` — the corollary in the exact form the
  descent uses: a nonzero rational has at most one squarefree label.

This does NOT define the descent homomorphisms δ, δ′ for the 2-isogeny,
does NOT prove ker δ = range ψ, and does NOT touch Mordell–Weil rank.
It closes one named brick of the identification: the target
ℚ*/ℚ*², restricted to the representatives the descent produces, is
well defined.
-/

import Mathlib

namespace SquareclassIdentification

/-- Two nonzero squarefree integers in the same squareclass of ℚ* are
equal. I.e. the signed squarefree representative of a rational
squareclass is unique. -/
theorem Int.eq_of_squarefree_of_isSquare_ratCast_div {d₁ d₂ : ℤ}
    (h₁ : Squarefree d₁) (h₂ : Squarefree d₂) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₁ = d₂ := by
  obtain ⟨r, hr⟩ := h
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  -- `d₁ * d₂` is a square in ℚ: it equals `(r * d₂)^2`.
  have hsq : IsSquare ((d₁ * d₂ : ℤ) : ℚ) := by
    refine ⟨r * (d₂ : ℚ), ?_⟩
    push_cast
    have hrw : (r * (d₂ : ℚ)) * (r * (d₂ : ℚ)) = (r * r) * ((d₂ : ℚ) ^ 2) := by ring
    rw [hrw, ← hr]
    field_simp
    ring
  -- Hence `d₁ * d₂` is a square in ℤ, by Mathlib's `Rat.isSquare_intCast_iff`.
  obtain ⟨s, hs⟩ := Rat.isSquare_intCast_iff.mp hsq
  -- Take absolute values: `|d₁| * |d₂| = s^2` in ℕ.
  have hnat : d₁.natAbs * d₂.natAbs = s.natAbs ^ 2 := by
    have hcon := congrArg Int.natAbs hs
    rwa [Int.natAbs_mul, Int.natAbs_mul, ← pow_two] at hcon
  have hA : Squarefree d₁.natAbs := Int.squarefree_natAbs.mpr h₁
  have hB : Squarefree d₂.natAbs := Int.squarefree_natAbs.mpr h₂
  have hA0 : d₁.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd₁
  have hB0 : d₂.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd₂
  -- Prime-by-prime: the factorisations of `|d₁|` and `|d₂|` agree,
  -- since each exponent is ≤ 1 (squarefree) and their sum is even
  -- (it is the exponent of a square).
  have hfact : ∀ p : ℕ, d₁.natAbs.factorization p = d₂.natAbs.factorization p := by
    intro p
    have hmul : (d₁.natAbs * d₂.natAbs).factorization p
        = (s.natAbs ^ 2).factorization p := by rw [hnat]
    rw [Nat.factorization_mul hA0 hB0, Nat.factorization_pow] at hmul
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hmul
    have ha1 : d₁.natAbs.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hA0).mp hA p
    have hb1 : d₂.natAbs.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hB0).mp hB p
    omega
  have hAB : d₁.natAbs = d₂.natAbs := Nat.eq_of_factorization_eq hA0 hB0 hfact
  -- It remains to match the signs: `d₁ * d₂ = s^2 > 0`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact mul_ne_zero hd₁ hd₂ hs
  have hpos : 0 < d₁ * d₂ := by
    rw [hs]
    exact mul_self_pos.mpr hs0
  have hsq2 : d₁ * d₁ = d₂ * d₂ := Int.natAbs_eq_iff_mul_self_eq.mp hAB
  rcases mul_self_eq_mul_self_iff.mp hsq2 with h | h
  · exact h
  · exfalso
    have hneg : d₁ * d₂ = -(d₂ * d₂) := by rw [h]; ring
    have hdd : 0 < d₂ * d₂ := mul_self_pos.mpr hd₂
    omega

/-- The squarefree label of a nonzero rational is unique: if
`x = d₁ * w₁^2 = d₂ * w₂^2` with `d₁, d₂` squarefree integers and
`w₁, w₂` nonzero rationals, then `d₁ = d₂`. This is the
well-definedness statement behind PerfectPower's
`rational_primitive_squareclass` / `rational_point_cover_complete`
representatives (which are stated with a rational square
`(u / v)^2`, a special case of `w^2`). -/
theorem squareclass_label_unique {x : ℚ} (hx : x ≠ 0) {d₁ d₂ : ℤ}
    (h₁ : Squarefree d₁) (h₂ : Squarefree d₂)
    {w₁ w₂ : ℚ} (hw₁ : w₁ ≠ 0) (_hw₂ : w₂ ≠ 0)
    (hx₁ : x = (d₁ : ℚ) * w₁ ^ 2) (hx₂ : x = (d₂ : ℚ) * w₂ ^ 2) :
    d₁ = d₂ := by
  have hd₁ : d₁ ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at hx₁
    exact hx hx₁
  have hd₂ : d₂ ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at hx₂
    exact hx hx₂
  apply Int.eq_of_squarefree_of_isSquare_ratCast_div h₁ h₂ hd₁ hd₂
  refine ⟨w₂ / w₁, ?_⟩
  have hd₂q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂
  have hxx : (d₁ : ℚ) * w₁ ^ 2 = (d₂ : ℚ) * w₂ ^ 2 := by rw [← hx₁, ← hx₂]
  field_simp
  have hgoal : (d₁ : ℚ) * w₁ ^ 2 = d₂ * w₂ ^ 2 := hxx
  linear_combination hgoal

end SquareclassIdentification
