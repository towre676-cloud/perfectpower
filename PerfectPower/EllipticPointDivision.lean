import PerfectPower.EllipticDivision
import PerfectPower.NativeRationalRoots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Connect completed-square coordinates to Mathlib's actual elliptic group.
No finite search, rank assumption or torsion classification is used here. -/
namespace PerfectPower.EllipticPointDivision
open WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F]

/-- The completed-square model y²=x³+Ax²+Bx+C. -/
def completed (A B C : F) : Affine F :=
  (⟨0, A, 0, B, C⟩ : WeierstrassCurve F).toAffine

/-- The completed model has the declared cubic equation. -/
theorem equation_completed (A B C x y : F) :
    (completed A B C).Equation x y ↔ y ^ 2 = EllipticDivision.cubic A B C x := by
  rw [equation_iff']
  simp [completed, EllipticDivision.cubic, sub_eq_zero]

/-- A point doubles to zero exactly when it equals its negation. -/
theorem double_eq_zero_iff {W : Affine F} (P : W.Point) :
    (2 : ℤ) • P = 0 ↔ P = -P := by
  rw [show (2 : ℤ) • P = P + P by simp [two_smul], add_eq_zero_iff_eq_neg]

/-- Branch points are exactly the nonzero two-torsion points when 2 is invertible. -/
theorem affine_two_torsion_iff (A B C x y : F)
    (h : (completed A B C).Nonsingular x y) (h2 : (2 : F) ≠ 0) :
    (2 : ℤ) • Point.some h = 0 ↔ y = 0 := by
  rw [double_eq_zero_iff, Point.neg_some, Point.some.injEq]
  simp only [completed, negY, zero_mul, sub_zero, neg_zero, zero_add, true_and]
  constructor
  · intro hy
    have hz : (2 : F) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro hy
    simp [hy]

/-- Every nonzero two-torsion point yields a rational cubic root in characteristic zero. -/
theorem two_torsion_root (A B C x y : F)
    (h : (completed A B C).Nonsingular x y) (h2 : (2 : F) ≠ 0)
    (ht : (2 : ℤ) • Point.some h = 0) : EllipticDivision.cubic A B C x = 0 := by
  have hy := (affine_two_torsion_iff A B C x y h h2).mp ht
  have he := (equation_completed A B C x y).mp h.1
  simpa [hy] using he.symm

/-- The x-coordinate in Mathlib's doubling formula is the halving quartic. -/
theorem actual_doubling_x_iff (A B C u x y : F)
    (h : (completed A B C).Nonsingular x y) (hden : 2 * y ≠ 0) :
    (completed A B C).addX x x ((completed A B C).slope x x y y) = u ↔
      EllipticDivision.halvingPolynomial A B C u x = 0 := by
  have hy : y ≠ (completed A B C).negY x y := by
    intro he
    apply hden
    simp only [completed, negY, zero_mul, sub_zero] at he
    linear_combination he
  rw [slope_of_Y_ne rfl hy]
  have hs : y - (completed A B C).negY x y = 2 * y := by
    simp [completed, negY]
    ring
  rw [hs]
  have he := (equation_completed A B C x y).mp h.1
  convert EllipticDivision.doubling_x_iff A B C u x y he hden using 1
  simp only [addX, completed, zero_mul, mul_zero, sub_zero, add_zero]
  ring_nf

/-- Construct the nonsingular branch point from a cubic root. -/
noncomputable def branchPoint (A B C x : ℚ)
    (hΔ : (completed A B C).Δ ≠ 0) (hx : EllipticDivision.cubic A B C x = 0) :
    (completed A B C).Point :=
  Point.some ((equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    ((equation_completed A B C x 0).mpr (by simpa using hx.symm)))

/-- Include infinity and every supplied branch coordinate. -/
noncomputable def torsionList (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (L : List ℚ) : List (completed A B C).Point :=
  0 :: L.map (fun x => if hx : EllipticDivision.cubic A B C x = 0
    then branchPoint A B C x hΔ hx else 0)

/-- A complete cubic-root list gives every rational two-torsion point, including infinity. -/
theorem torsion_list_complete (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (L : List ℚ) (hL : ∀ x, EllipticDivision.cubic A B C x = 0 ↔ x ∈ L)
    (P : (completed A B C).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ torsionList A B C hΔ L := by
  classical
  constructor
  · intro ht
    cases P with
    | zero => exact List.mem_cons.mpr (Or.inl rfl)
    | @some x y h =>
      have hy := (affine_two_torsion_iff A B C x y h (by norm_num)).mp ht
      subst y
      have hx := two_torsion_root A B C x 0 h (by norm_num) ht
      apply List.mem_cons.mpr
      right
      apply List.mem_map.mpr
      refine ⟨x, (hL x).mp hx, ?_⟩
      simp only [dif_pos hx]
      rfl
  · intro hm
    rcases List.mem_cons.mp hm with he | hm
    · rw [he]
      exact zsmul_zero _
    · obtain ⟨x, _, he⟩ := List.mem_map.mp hm
      rw [← he]
      split_ifs with hx
      · exact (affine_two_torsion_iff A B C x 0 _ (by norm_num)).mpr rfl
      · exact zsmul_zero _

/-- The monic polynomial of completed-square branch coordinates. -/
noncomputable def cubicPolynomial (A B C : ℚ) : Polynomial ℚ :=
  Polynomial.X^3 + Polynomial.C A * Polynomial.X^2 +
    Polynomial.C B * Polynomial.X + Polynomial.C C

/-- Evaluation of the native polynomial is the completed cubic. -/
@[simp] theorem eval_cubicPolynomial (A B C x : ℚ) :
    (cubicPolynomial A B C).eval x = EllipticDivision.cubic A B C x := by
  simp [cubicPolynomial, EllipticDivision.cubic]

/-- The torsion producer needs scaled coefficients, not a supplied completeness
claim about its root output. The signed-divisor search is proved complete. -/
theorem native_torsion_complete (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (as : List ℤ) (D : ℚ) (hD : D ≠ 0) (hv : NativePolynomialSquare.valid as)
    (hm : (NativePolynomialSquare.polynomial as).Monic)
    (hs : (NativePolynomialSquare.polynomial as).map (Int.castRingHom ℚ) =
      (cubicPolynomial A B C).scaleRoots D) (P : (completed A B C).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ torsionList A B C hΔ (NativeRationalRoots.roots as D).toList := by
  apply torsion_list_complete
  intro x
  rw [Finset.mem_toList, ← NativeRationalRoots.complete (cubicPolynomial A B C)
    as D hD hv hm hs x, eval_cubicPolynomial]

/-- An actual anchor and native cubic-root certificate enumerate every half. -/
theorem native_halves_complete (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (as : List ℤ) (D : ℚ) (hD : D ≠ 0) (hv : NativePolynomialSquare.valid as)
    (hm : (NativePolynomialSquare.polynomial as).Monic)
    (hs : (NativePolynomialSquare.polynomial as).map (Int.castRingHom ℚ) =
      (cubicPolynomial A B C).scaleRoots D)
    (P H Q : (completed A B C).Point) (hH : (2 : ℤ) • H = P) :
    (2 : ℤ) • Q = P ↔ Q ∈
      (torsionList A B C hΔ (NativeRationalRoots.roots as D).toList).map (fun T => H+T) :=
  EllipticDivision.fibre_list_complete 2 P H hH _
    (native_torsion_complete A B C hΔ as D hD hv hm hs) Q

/-- Every half of a nonzero affine target supplies a root of its halving quartic. -/
theorem half_supplies_quartic_root (A B C u v : ℚ)
    (hp : (completed A B C).Nonsingular u v)
    (Q : (completed A B C).Point) (hQ : (2 : ℤ) • Q = Point.some hp) :
    ∃ x, EllipticDivision.halvingPolynomial A B C u x = 0 := by
  cases Q with
  | zero =>
    change (2 : ℤ) • (0 : (completed A B C).Point) = Point.some hp at hQ
    rw [zsmul_zero] at hQ
    exact False.elim (Point.some_ne_zero hp hQ.symm)
  | @some x y h =>
    have hy : y ≠ 0 := by
      intro hy
      have ht := (affine_two_torsion_iff A B C x y h (by norm_num)).mpr hy
      rw [ht] at hQ
      exact Point.some_ne_zero hp hQ.symm
    have hn : y ≠ (completed A B C).negY x y := by
      simp only [completed, negY, zero_mul, sub_zero, neg_zero, zero_add]
      intro he
      apply hy
      linear_combination (1 / 2 : ℚ) * he
    rw [two_zsmul, Point.add_self_of_Y_ne hn, Point.some.injEq] at hQ
    exact ⟨x, (actual_doubling_x_iff A B C u x y h (mul_ne_zero (by norm_num) hy)).mp hQ.1⟩

/-- A root-free quartic proves an empty actual halving fibre, including branch targets. -/
theorem no_half_of_quartic_root_free (A B C u v : ℚ)
    (hp : (completed A B C).Nonsingular u v)
    (hroot : ∀ x, EllipticDivision.halvingPolynomial A B C u x ≠ 0)
    (Q : (completed A B C).Point) : (2 : ℤ) • Q ≠ Point.some hp := by
  intro hQ
  obtain ⟨x, hx⟩ := half_supplies_quartic_root A B C u v hp Q hQ
  exact hroot x hx

end PerfectPower.EllipticPointDivision
