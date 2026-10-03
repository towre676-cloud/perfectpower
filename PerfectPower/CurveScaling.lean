import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Scaling a short Weierstrass curve: `(x, y) ↦ (Z²x, Z³y)`

For `E : y² = x³ + Ax + B` over a field and `Z ≠ 0`, `φ_Z(x, y) = (Z²x, Z³y)` maps `E` onto
`E' : y² = x³ + (AZ⁴)x + BZ⁶`. This is the transformation behind the Brainpool "twisted" curves
of RFC 5639: `Z` is chosen with `AZ⁴ = −3`. It is an isomorphism over the same field, not a
quadratic twist.
* `residual`: `(Z³y)² − (Z²x)³ − (AZ⁴)(Z²x) − BZ⁶ = Z⁶ (y² − x³ − Ax − B)`, in any commutative ring.
* `residual_zero_iff_of_isUnit`: curve-equation membership is preserved over any commutative ring
  when `Z` is invertible, even without a field or primality assumption.
* `equation_iff`, `nonsingular_iff`: membership and nonsingularity are preserved, for `Z ≠ 0`.
* `phi`: the map on Mathlib's points (`WeierstrassCurve.Affine.Point`), with `0 ↦ 0`.
* **`phi_add`**: `φ_Z(P + Q) = φ_Z(P) + φ_Z(Q)` for Mathlib's group law; so `phiHom` is an
  additive group homomorphism, and `φ_Z([n]P) = [n]φ_Z(P)` (`phi_zsmul`).
* `phi_inj`, and `phi` with `Z⁻¹` inverts it (`phi_inv_phi`): an isomorphism.

This is algebra only. It says nothing about constant-time behaviour or about a particular
implementation.
-/

namespace PerfectPower.CurveScaling

open WeierstrassCurve WeierstrassCurve.Affine

section Ring
variable {R : Type*} [CommRing R]

/-- **The residual identity.** -/
theorem residual (A B Z x y : R) :
    (Z ^ 3 * y) ^ 2 - (Z ^ 2 * x) ^ 3 - (A * Z ^ 4) * (Z ^ 2 * x) - B * Z ^ 6 =
      Z ^ 6 * (y ^ 2 - x ^ 3 - A * x - B) := by ring

/-- Curve-equation membership is preserved over any commutative ring when the
scale is a unit. This includes residue rings without a primality assumption;
nonzero alone is insufficient in a ring with zero divisors. -/
theorem residual_zero_iff_of_isUnit (A B Z x y : R) (hZ : IsUnit Z) :
    (Z ^ 3 * y) ^ 2 - (Z ^ 2 * x) ^ 3 - (A * Z ^ 4) * (Z ^ 2 * x) - B * Z ^ 6 = 0 ↔
      y ^ 2 - x ^ 3 - A * x - B = 0 := by
  rw [residual]
  exact (hZ.pow 6).mul_right_eq_zero

end Ring

variable {F : Type*} [Field F]

/-- The short Weierstrass curve `y² = x³ + Ax + B`. -/
def short (A B : F) : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩

/-- Its affine model. -/
abbrev Wa (A B : F) : Affine F := (short A B).toAffine

@[simp] lemma a₁_short (A B : F) : (Wa A B).a₁ = 0 := rfl
@[simp] lemma a₂_short (A B : F) : (Wa A B).a₂ = 0 := rfl
@[simp] lemma a₃_short (A B : F) : (Wa A B).a₃ = 0 := rfl
@[simp] lemma a₄_short (A B : F) : (Wa A B).a₄ = A := rfl
@[simp] lemma a₆_short (A B : F) : (Wa A B).a₆ = B := rfl

lemma equation_short (A B x y : F) : (Wa A B).Equation x y ↔ y ^ 2 - x ^ 3 - A * x - B = 0 := by
  rw [equation_iff']; simp only [a₁_short, a₂_short, a₃_short, a₄_short, a₆_short]
  constructor <;> intro h <;> linear_combination h

lemma negY_short (A B : F) (x y : F) : (Wa A B).negY x y = -y := by
  simp [negY]

theorem equation_iff {A B Z x y : F} (hZ : Z ≠ 0) :
    (Wa (A * Z ^ 4) (B * Z ^ 6)).Equation (Z ^ 2 * x) (Z ^ 3 * y) ↔ (Wa A B).Equation x y := by
  rw [equation_short, equation_short, residual, mul_eq_zero]
  simp [pow_ne_zero 6 hZ]

theorem nonsingular_iff {A B Z x y : F} (hZ : Z ≠ 0) :
    (Wa (A * Z ^ 4) (B * Z ^ 6)).Nonsingular (Z ^ 2 * x) (Z ^ 3 * y) ↔ (Wa A B).Nonsingular x y := by
  rw [nonsingular_iff', nonsingular_iff', equation_iff hZ]
  simp only [a₁_short, a₂_short, a₃_short, a₄_short]
  have h4 : Z ^ 4 ≠ 0 := pow_ne_zero 4 hZ
  have h3 : Z ^ 3 ≠ 0 := pow_ne_zero 3 hZ
  have e1 : (0 : F) * (Z ^ 3 * y) - (3 * (Z ^ 2 * x) ^ 2 + 2 * 0 * (Z ^ 2 * x) + A * Z ^ 4) =
      Z ^ 4 * (0 * y - (3 * x ^ 2 + 2 * 0 * x + A)) := by ring
  have e2 : 2 * (Z ^ 3 * y) + 0 * (Z ^ 2 * x) + 0 = Z ^ 3 * (2 * y + 0 * x + 0) := by ring
  rw [e1, e2]
  simp [h4, h3]

/-- **`φ_Z` on points.** -/
noncomputable def phi {A B Z : F} (hZ : Z ≠ 0) : (Wa A B).Point → (Wa (A * Z ^ 4) (B * Z ^ 6)).Point
  | 0 => 0
  | @Point.some _ _ _ _ _ h => Point.some ((nonsingular_iff hZ).mpr h)

lemma some_congr {W : Affine F} {x y x' y' : F} {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some h = Point.some h' := by
  subst hx; subst hy; rfl

/-- `(Z⁴a)/(Z³b) = Z (a/b)`, including `b = 0`. -/
lemma div_scale {Z : F} (hZ : Z ≠ 0) (a b : F) : (Z ^ 4 * a) / (Z ^ 3 * b) = Z * (a / b) := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  · field_simp; ring

/-- The slope scales by `Z`. -/
lemma slope_scale {A B Z : F} (hZ : Z ≠ 0) (x₁ x₂ y₁ y₂ : F) :
    (Wa (A * Z ^ 4) (B * Z ^ 6)).slope (Z ^ 2 * x₁) (Z ^ 2 * x₂) (Z ^ 3 * y₁) (Z ^ 3 * y₂) =
      Z * (Wa A B).slope x₁ x₂ y₁ y₂ := by
  have h2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  have h3 : Z ^ 3 ≠ 0 := pow_ne_zero 3 hZ
  rw [slope, slope]
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = (Wa A B).negY x₁ y₂
    · have hy' : Z ^ 3 * y₁ = (Wa (A * Z ^ 4) (B * Z ^ 6)).negY (Z ^ 2 * x₁) (Z ^ 3 * y₂) := by
        rw [negY_short] at hy ⊢; rw [hy]; ring
      rw [if_pos rfl, if_pos hy', if_pos rfl, if_pos hy, mul_zero]
    · have hy' : ¬ Z ^ 3 * y₁ = (Wa (A * Z ^ 4) (B * Z ^ 6)).negY (Z ^ 2 * x₁) (Z ^ 3 * y₂) := by
        rw [negY_short] at hy ⊢
        intro h; apply hy; apply mul_left_cancel₀ h3; linear_combination h
      rw [if_pos rfl, if_neg hy', if_pos rfl, if_neg hy]
      simp only [negY_short, a₁_short, a₂_short, a₄_short]
      rw [show 3 * (Z ^ 2 * x₁) ^ 2 + 2 * 0 * (Z ^ 2 * x₁) + A * Z ^ 4 - 0 * (Z ^ 3 * y₁) =
          Z ^ 4 * (3 * x₁ ^ 2 + 2 * 0 * x₁ + A - 0 * y₁) by ring,
        show Z ^ 3 * y₁ - -(Z ^ 3 * y₁) = Z ^ 3 * (y₁ - -y₁) by ring, div_scale hZ]
  · have hx' : Z ^ 2 * x₁ ≠ Z ^ 2 * x₂ := fun h => hx (mul_left_cancel₀ h2 h)
    rw [if_neg hx, if_neg hx']
    rw [show Z ^ 3 * y₁ - Z ^ 3 * y₂ = Z ^ 3 * (y₁ - y₂) by ring,
      show Z ^ 2 * x₁ - Z ^ 2 * x₂ = Z ^ 2 * (x₁ - x₂) by ring]
    rcases eq_or_ne (x₁ - x₂) 0 with hd | hd
    · simp [hd]
    · field_simp; ring

/-- **`φ_Z` respects Mathlib's group law.** -/
theorem phi_add {A B Z : F} (hZ : Z ≠ 0) (P Q : (Wa A B).Point) : phi hZ (P + Q) = phi hZ P + phi hZ Q := by
  have h3 : Z ^ 3 ≠ 0 := pow_ne_zero 3 hZ
  have h2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  rcases P with _ | @⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | @⟨x₂, y₂, h₂⟩
  · rfl
  · show phi hZ (0 + _) = 0 + _; rw [zero_add, zero_add]
  · show phi hZ (_ + 0) = _ + 0; rw [add_zero, add_zero]
  · by_cases hxy : x₁ = x₂ ∧ y₁ = (Wa A B).negY x₂ y₂
    · have hxy' : Z ^ 2 * x₁ = Z ^ 2 * x₂ ∧ Z ^ 3 * y₁ = (Wa (A * Z ^ 4) (B * Z ^ 6)).negY (Z ^ 2 * x₂) (Z ^ 3 * y₂) := by
        rw [negY_short] at hxy ⊢; exact ⟨by rw [hxy.1], by rw [hxy.2]; ring⟩
      rw [Point.add_of_Y_eq hxy.1 hxy.2]
      show 0 = Point.some _ + Point.some _
      rw [Point.add_of_Y_eq hxy'.1 hxy'.2]
    · have hxy' : ¬(Z ^ 2 * x₁ = Z ^ 2 * x₂ ∧ Z ^ 3 * y₁ = (Wa (A * Z ^ 4) (B * Z ^ 6)).negY (Z ^ 2 * x₂) (Z ^ 3 * y₂)) := by
        rw [negY_short] at hxy ⊢
        rintro ⟨e1, e2⟩
        exact hxy ⟨mul_left_cancel₀ h2 e1, mul_left_cancel₀ h3 (by linear_combination e2)⟩
      rw [Point.add_some hxy]
      show Point.some _ = Point.some _ + Point.some _
      rw [Point.add_some hxy']
      apply some_congr
      · simp only [addX, slope_scale hZ, a₁_short, a₂_short]; ring
      · simp only [addY, addX, negAddY, slope_scale hZ, negY_short, a₁_short, a₂_short, a₃_short]; ring

/-- `φ_Z` as an additive group homomorphism. -/
noncomputable def phiHom {A B Z : F} (hZ : Z ≠ 0) : (Wa A B).Point →+ (Wa (A * Z ^ 4) (B * Z ^ 6)).Point where
  toFun := phi hZ
  map_zero' := rfl
  map_add' := phi_add hZ

/-- **`φ_Z([n]P) = [n]φ_Z(P)`.** -/
theorem phi_zsmul {A B Z : F} (hZ : Z ≠ 0) (n : ℤ) (P : (Wa A B).Point) :
    phi hZ (n • P) = n • phi hZ P :=
  (phiHom hZ).map_zsmul P n

theorem phi_injective {A B Z : F} (hZ : Z ≠ 0) : Function.Injective (phi (A := A) (B := B) hZ) := by
  have h3 : Z ^ 3 ≠ 0 := pow_ne_zero 3 hZ
  have h2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · simp only [phi, Point.some.injEq] at h
    exact some_congr (mul_left_cancel₀ h2 h.1) (mul_left_cancel₀ h3 h.2)

theorem phi_surjective {A B Z : F} (hZ : Z ≠ 0) : Function.Surjective (phi (A := A) (B := B) hZ) := by
  rintro (_ | @⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have ex : x = Z ^ 2 * (Z⁻¹ ^ 2 * x) := by field_simp
    have ey : y = Z ^ 3 * (Z⁻¹ ^ 3 * y) := by field_simp
    rw [ex, ey] at h
    refine ⟨Point.some ((nonsingular_iff hZ).mp h), ?_⟩
    exact some_congr ex.symm ey.symm

/-- **`φ_Z` is a group isomorphism** `E(F) ≃ E'(F)`. -/
noncomputable def phiEquiv {A B Z : F} (hZ : Z ≠ 0) : (Wa A B).Point ≃+ (Wa (A * Z ^ 4) (B * Z ^ 6)).Point :=
  AddEquiv.ofBijective (phiHom hZ) ⟨phi_injective hZ, phi_surjective hZ⟩

end PerfectPower.CurveScaling
