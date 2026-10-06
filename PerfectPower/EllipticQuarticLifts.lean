import PerfectPower.EllipticSquareTransport
import Mathlib.Data.Rat.Sqrt

namespace PerfectPower.EllipticQuarticLifts
open WeierstrassCurve WeierstrassCurve.Affine
open PerfectPower.EllipticPointDivision

/-- Both signed lifts of a rational abscissa, or no lift when its cubic is nonsquare. -/
noncomputable def lifts (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0) (x : ℚ) :
    List (completed A B C).Point :=
  let s := Rat.sqrt (EllipticDivision.cubic A B C x)
  if h : s^2 = EllipticDivision.cubic A B C x then
    [Point.some ((equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
      ((equation_completed A B C x s).mpr h)),
     Point.some ((equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
      ((equation_completed A B C x (-s)).mpr (by simpa using h)))]
  else []

/-- Every actual affine point appears in the two signed lifts of its abscissa. -/
theorem mem_lifts (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0) (x y : ℚ)
    (h : (completed A B C).Nonsingular x y) : Point.some h ∈ lifts A B C hΔ x := by
  have he := (equation_completed A B C x y).mp h.1
  have hs : (Rat.sqrt (EllipticDivision.cubic A B C x))^2 = EllipticDivision.cubic A B C x := by
    rw [pow_two]
    exact (Rat.exists_mul_self _).mp ⟨y,by simpa [pow_two] using he⟩
  have hy : y = Rat.sqrt (EllipticDivision.cubic A B C x) ∨
      y = -Rat.sqrt (EllipticDivision.cubic A B C x) := by
    have hz : (y-Rat.sqrt (EllipticDivision.cubic A B C x)) *
        (y+Rat.sqrt (EllipticDivision.cubic A B C x)) = 0 := by linear_combination he-hs
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl (sub_eq_zero.mp hz)
    · right; linear_combination hz
  unfold lifts
  simp only [dif_pos hs, List.mem_cons, List.not_mem_nil, or_false, Point.some.injEq]
  rcases hy with hy | hy
  · exact Or.inl ⟨True.intro,hy⟩
  · exact Or.inr ⟨True.intro,hy⟩

/-- Complete signed lifts filtered by actual doubling, with no square or sign assumptions. -/
noncomputable def fibreList (A B C : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (P : (completed A B C).Point) (roots : List ℚ) : List (completed A B C).Point := by
  classical
  exact (roots.flatMap (lifts A B C hΔ)).filter (fun Q => decide ((2 : ℤ) • Q = P))

/-- A complete quartic root list gives the full actual affine-target fibre. -/
theorem fibre_complete (A B C u v : ℚ) (hΔ : (completed A B C).Δ ≠ 0)
    (hp : (completed A B C).Nonsingular u v) (roots : List ℚ)
    (hr : ∀ x, EllipticDivision.halvingPolynomial A B C u x = 0 ↔ x ∈ roots)
    (Q : (completed A B C).Point) :
    (2 : ℤ) • Q = Point.some hp ↔ Q ∈ fibreList A B C hΔ (Point.some hp) roots := by
  classical
  unfold fibreList
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · intro hQ
    refine ⟨?_,hQ⟩
    cases Q with
    | zero =>
      change (2 : ℤ) • (0 : (completed A B C).Point) = Point.some hp at hQ
      rw [zsmul_zero] at hQ
      exact False.elim (Point.some_ne_zero hp hQ.symm)
    | @some x y h =>
      have hy : y ≠ 0 := by
        intro hy
        rw [(affine_two_torsion_iff A B C x y h (by norm_num)).mpr hy] at hQ
        exact Point.some_ne_zero hp hQ.symm
      have hn : y ≠ (completed A B C).negY x y := by
        simp only [completed, negY, zero_mul, sub_zero, neg_zero, zero_add]
        intro he
        apply hy
        linear_combination (1/2:ℚ)*he
      have hc := hQ
      rw [two_zsmul, Point.add_self_of_Y_ne hn, Point.some.injEq] at hc
      have hx := (actual_doubling_x_iff A B C u x y h (mul_ne_zero (by norm_num) hy)).mp hc.1
      exact List.mem_flatMap.mpr ⟨x,(hr x).mp hx,mem_lifts A B C hΔ x y h⟩
  · exact fun h => h.2
end PerfectPower.EllipticQuarticLifts
