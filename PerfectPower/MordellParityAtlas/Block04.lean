import PerfectPower.MordellParity
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace PerfectPower.MordellParityAtlas
open Polynomial PerfectPower.MordellParity PerfectPower
namespace Curve_m4629
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4629)
private def branch_coefficients : List ℤ := [-4629, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4629) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4629)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4629) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4629)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(25945/1521 : ℚ))*X^3-C (-37032)*X-C (4*(25945/1521 : ℚ)*(-4629))
private def half0_coefficients : List ℤ := [1690396128174248820, 130306118957352, 0, -103780, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1521) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1521) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4629)).Nonsingular (25945/1521 : ℚ) (1084634/59319 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4629)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4629)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4629) (25945/1521 : ℚ) (1084634/59319 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4629) (25945/1521 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4629)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4629
#print axioms PerfectPower.MordellParityAtlas.Curve_m4629.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4629.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4629.no_half0
namespace Curve_m4698
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4698)
private def branch_coefficients : List ℤ := [-4698, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 19 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4698) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4698)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4698) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4698)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(571/25 : ℚ))*X^3-C (-37584)*X-C (4*(571/25 : ℚ)*(-4698))
private def half0_coefficients : List ℤ := [167659875000, 587250000, 0, -2284, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (25) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (25) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4698)).Nonsingular (571/25 : ℚ) (10619/125 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4698)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4698)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4698) (571/25 : ℚ) (10619/125 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4698) (571/25 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4698)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4698
#print axioms PerfectPower.MordellParityAtlas.Curve_m4698.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4698.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4698.no_half0
namespace Curve_m4781
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4781)
private def branch_coefficients : List ℤ := [-4781, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 13 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4781) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4781)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4781) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4781)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(325574214427141498494741/11929639242308195289025 : ℚ))*X^3-C (-38248)*X-C (4*(325574214427141498494741/11929639242308195289025 : ℚ)*(-4781))
private def half0_coefficients : List ℤ := [10570868448196401467625999508221280602509474474292493159561633604649135225557434085503362562500, 64936766978282914569961675120930916396277553644226099315538603832625000, 0, -1302296857708565993978964, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (11929639242308195289025) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (11929639242308195289025) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4781)).Nonsingular (325574214427141498494741/11929639242308195289025 : ℚ) (-162460164325903216149888147926364664/1302989649709717147516026651742625 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4781)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4781)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4781) (325574214427141498494741/11929639242308195289025 : ℚ) (-162460164325903216149888147926364664/1302989649709717147516026651742625 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4781) (325574214427141498494741/11929639242308195289025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4781)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4781
#print axioms PerfectPower.MordellParityAtlas.Curve_m4781.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4781.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4781.no_half0
namespace Curve_m4810
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4810)
private def branch_coefficients : List ℤ := [-4810, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 19 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4810) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4810)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4810) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4810)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(3778975224643001199167849/13023144098641513649296 : ℚ))*X^3-C (-38480)*X-C (4*(3778975224643001199167849/13023144098641513649296 : ℚ)*(-4810))
private def half0_coefficients : List ℤ := [160593014470034441823731400027304281119547023347445397077021146154053529104818952032340824719360, 84992890888934378704234618441268957542369830430758692539951019498209280, 0, -15115900898572004796671396, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (13023144098641513649296) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (13023144098641513649296) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4810)).Nonsingular (3778975224643001199167849/13023144098641513649296 : ℚ) (7345448427141509234028920940459716917/1486188063715740820819292888961344 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4810)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4810)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4810) (3778975224643001199167849/13023144098641513649296 : ℚ) (7345448427141509234028920940459716917/1486188063715740820819292888961344 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4810) (3778975224643001199167849/13023144098641513649296 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4810)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4810
#print axioms PerfectPower.MordellParityAtlas.Curve_m4810.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4810.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4810.no_half0
namespace Curve_m4817
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4817)
private def branch_coefficients : List ℤ := [-4817, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 13 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4817) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4817)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4817) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4817)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(6640593/73441 : ℚ))*X^3-C (-38536)*X-C (4*(6640593/73441 : ℚ)*(-4817))
private def half0_coefficients : List ℤ := [50682642038152999642476804, 15264492806034942856, 0, -26562372, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (73441) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (73441) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4817)).Nonsingular (6640593/73441 : ℚ) (17056533200/19902511 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4817)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4817)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4817) (6640593/73441 : ℚ) (17056533200/19902511 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4817) (6640593/73441 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4817)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4817
#print axioms PerfectPower.MordellParityAtlas.Curve_m4817.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4817.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4817.no_half0
namespace Curve_m4818
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4818)
private def branch_coefficients : List ℤ := [-4818, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4818) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4818)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4818) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4818)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(6667/81 : ℚ))*X^3-C (-38544)*X-C (4*(6667/81 : ℚ)*(-4818))
private def half0_coefficients : List ℤ := [68282953656984, 20483861904, 0, -26668, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (81) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (81) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4818)).Nonsingular (6667/81 : ℚ) (542015/729 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4818)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4818)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4818) (6667/81 : ℚ) (542015/729 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4818) (6667/81 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4818)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4818
#print axioms PerfectPower.MordellParityAtlas.Curve_m4818.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4818.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4818.no_half0
namespace Curve_m4854
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4854)
private def branch_coefficients : List ℤ := [-4854, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4854) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4854)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4854) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4854)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(43836260085883613528812376047/1671684250254842305682316081 : ℚ))*X^3-C (-38832)*X-C (4*(43836260085883613528812376047/1671684250254842305682316081 : ℚ)*(-4854))
private def half0_coefficients : List ℤ := [3976088209538175371637838873018970440651445499723864519966574223225983985427434916105208225267325083472953876059432, 181406360932627850762579188628323363214095929300829898351206278570873606982550245812912, 0, -175345040343534454115249504188, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1671684250254842305682316081) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1671684250254842305682316081) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4854)).Nonsingular (43836260085883613528812376047/1671684250254842305682316081 : ℚ) (7846065134351917379440609616593942485351797/68348875874051461174058449438026205266729 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4854)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4854)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4854) (43836260085883613528812376047/1671684250254842305682316081 : ℚ) (7846065134351917379440609616593942485351797/68348875874051461174058449438026205266729 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4854) (43836260085883613528812376047/1671684250254842305682316081 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4854)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4854
#print axioms PerfectPower.MordellParityAtlas.Curve_m4854.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4854.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4854.no_half0
namespace Curve_m4882
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4882)
private def branch_coefficients : List ℤ := [-4882, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4882) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4882)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4882) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4882)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(65414080882467602035638033673/1791873684611835862539087936 : ℚ))*X^3-C (-39056)*X-C (4*(65414080882467602035638033673/1791873684611835862539087936 : ℚ)*(-4882))
private def half0_coefficients : List ℤ := [7349388144561203169820955389963157596983367320738479839515982102960882291515665217495177691104165729871915294654464, 224703551449914179374601447706811537101739410766627821414231478425568350111876236967936, 0, -261656323529870408142552134692, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1791873684611835862539087936) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1791873684611835862539087936) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4882)).Nonsingular (65414080882467602035638033673/1791873684611835862539087936 : ℚ) (-15868807060839116748350064016182736495362715/75850960953696529276515514036325088738816 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4882)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4882)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4882) (65414080882467602035638033673/1791873684611835862539087936 : ℚ) (-15868807060839116748350064016182736495362715/75850960953696529276515514036325088738816 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4882) (65414080882467602035638033673/1791873684611835862539087936 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4882)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4882
#print axioms PerfectPower.MordellParityAtlas.Curve_m4882.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4882.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4882.no_half0
namespace Curve_m4986
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-4986)
private def branch_coefficients : List ℤ := [-4986, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-4986) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-4986)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-4986) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-4986)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(171/1 : ℚ))*X^3-C (-39888)*X-C (4*(171/1 : ℚ)*(-4986))
private def half0_coefficients : List ℤ := [3410424, 39888, 0, -684, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-4986)).Nonsingular (171/1 : ℚ) (2235/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-4986)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-4986)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-4986) (171/1 : ℚ) (2235/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-4986) (171/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-4986)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m4986
#print axioms PerfectPower.MordellParityAtlas.Curve_m4986.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m4986.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m4986.no_half0
namespace Curve_m506
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-506)
private def branch_coefficients : List ℤ := [-506, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-506) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-506)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-506) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-506)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(675/1 : ℚ))*X^3-C (-4048)*X-C (4*(675/1 : ℚ)*(-506))
private def half0_coefficients : List ℤ := [1366200, 4048, 0, -2700, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1) half0_monic half0_scale 19 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-506)).Nonsingular (675/1 : ℚ) (17537/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-506)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-506)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-506) (675/1 : ℚ) (17537/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-506) (675/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-506)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m506
#print axioms PerfectPower.MordellParityAtlas.Curve_m506.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m506.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m506.no_half0
namespace Curve_m5083
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5083)
private def branch_coefficients : List ℤ := [-5083, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 19 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5083) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5083)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5083) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5083)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(123523/3249 : ℚ))*X^3-C (-40664)*X-C (4*(123523/3249 : ℚ)*(-5083))
private def half0_coefficients : List ℤ := [86134485888539231364, 1394630730933336, 0, -494092, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (3249) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (3249) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5083)).Nonsingular (123523/3249 : ℚ) (41356700/185193 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5083)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5083)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5083) (123523/3249 : ℚ) (41356700/185193 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5083) (123523/3249 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5083)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5083
#print axioms PerfectPower.MordellParityAtlas.Curve_m5083.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5083.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5083.no_half0
namespace Curve_m5089
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5089)
private def branch_coefficients : List ℤ := [-5089, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 13 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5089) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5089)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5089) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5089)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(5209229685270694653876588465857/236436998874473483668100975236 : ℚ))*X^3-C (-40712)*X-C (4*(5209229685270694653876588465857/236436998874473483668100975236 : ℚ)*(-5089))
private def half0_coefficients : List ℤ := [1401561836380832198712383736853835926834598020665908348008283828107530987597639581492221361191777695282177539228673055031552, 538107137162258122274005296959854113056348858960837959117677377785310823249598917093218550272, 0, -20836918741082778615506353863428, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (236436998874473483668100975236) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (236436998874473483668100975236) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5089)).Nonsingular (5209229685270694653876588465857/236436998874473483668100975236 : ℚ) (-8607824906951440510852696702932321657823701503/114966988987040830961555400305822295620782984 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5089)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5089)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5089) (5209229685270694653876588465857/236436998874473483668100975236 : ℚ) (-8607824906951440510852696702932321657823701503/114966988987040830961555400305822295620782984 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5089) (5209229685270694653876588465857/236436998874473483668100975236 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5089)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5089
#print axioms PerfectPower.MordellParityAtlas.Curve_m5089.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5089.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5089.no_half0
namespace Curve_m5097
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5097)
private def branch_coefficients : List ℤ := [-5097, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 19 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5097) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5097)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5097) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5097)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(50983119609322313313530137/18585185472268377810849 : ℚ))*X^3-C (-40776)*X-C (4*(50983119609322313313530137/18585185472268377810849 : ℚ)*(-5097))
private def half0_coefficients : List ℤ := [6672701994477338902929945121876684533740305029026202959905927813028545196797417090828473384064644, 261761227857748775860228118490601114343550763621428838133666236168638024, 0, -203932478437289253254120548, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (18585185472268377810849) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (18585185472268377810849) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5097)).Nonsingular (50983119609322313313530137/18585185472268377810849 : ℚ) (364031994725133583179679675009259809960/2533671750867798730956521031114993 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5097)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5097)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5097) (50983119609322313313530137/18585185472268377810849 : ℚ) (364031994725133583179679675009259809960/2533671750867798730956521031114993 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5097) (50983119609322313313530137/18585185472268377810849 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5097)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5097
#print axioms PerfectPower.MordellParityAtlas.Curve_m5097.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5097.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5097.no_half0
namespace Curve_m5106
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5106)
private def branch_coefficients : List ℤ := [-5106, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5106) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5106)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5106) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5106)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(28595515/194481 : ℚ))*X^3-C (-40848)*X-C (4*(28595515/194481 : ℚ)*(-5106))
private def half0_coefficients : List ℤ := [4296059237383637480432708760, 300470842185121511568, 0, -114382060, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (194481) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (194481) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5106)).Nonsingular (28595515/194481 : ℚ) (152791011577/85766121 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5106)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5106)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5106) (28595515/194481 : ℚ) (152791011577/85766121 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5106) (28595515/194481 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5106)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5106
#print axioms PerfectPower.MordellParityAtlas.Curve_m5106.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5106.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5106.no_half0
namespace Curve_m5155
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5155)
private def branch_coefficients : List ℤ := [-5155, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5155) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5155)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5155) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5155)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(191846577298052379621539502101702449/1332109579551773773943852789117184 : ℚ))*X^3-C (-41240)*X-C (4*(191846577298052379621539502101702449/1332109579551773773943852789117184 : ℚ)*(-5155))
private def half0_coefficients : List ℤ := [9351097187059238927416038800400298721779186453408955643799708954939817012297796398023660042728816788934356875545664259860766112664277483520, 97485160473114898464060364603114924654538668456863593266090841746911704471106147571512510974685830184960, 0, -767386309192209518486158008406809796, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1332109579551773773943852789117184) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (1332109579551773773943852789117184) half0_monic half0_scale 23 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5155)).Nonsingular (191846577298052379621539502101702449/1332109579551773773943852789117184 : ℚ) (-83956825726479187929765821536898958911754227982187223/48619437183044360781969423753775553654095043530752 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5155)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5155)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5155) (191846577298052379621539502101702449/1332109579551773773943852789117184 : ℚ) (-83956825726479187929765821536898958911754227982187223/48619437183044360781969423753775553654095043530752 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5155) (191846577298052379621539502101702449/1332109579551773773943852789117184 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5155)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5155
#print axioms PerfectPower.MordellParityAtlas.Curve_m5155.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5155.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5155.no_half0
namespace Curve_m5161
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-5161)
private def branch_coefficients : List ℤ := [-5161, 0, 0, 1]
private noncomputable def branch_scaled := polynomial branch_coefficients
private theorem branch_degree : branch_source.natDegree=3 := by
  unfold branch_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem branch_monic : branch_scaled.Monic := by
  simp [branch_scaled,branch_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem branch_scale : branch_scaled.map (Int.castRingHom ℚ) = branch_source.scaleRoots (1) := by
  have hg : branch_scaled.natDegree=3 := by
    simp [branch_scaled,branch_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,branch_degree]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [branch_scaled,branch_coefficients,polynomial,branch_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [branch_degree]; exact hi')]
    simp
theorem branch_root_free (x : ℚ) : branch_source.eval x ≠ 0 :=
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 7 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-5161) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-5161)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-5161) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-5161)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(10937/529 : ℚ))*X^3-C (-41288)*X-C (4*(10937/529 : ℚ)*(-5161))
private def half0_coefficients : List ℤ := [33424050485447492, 6112105785032, 0, -43748, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (529) := by
  have hg : half0_scaled.natDegree=4 := by
    simp [half0_scaled,half0_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half0_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half0_scaled,half0_coefficients,polynomial,half0_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half0_degree]; exact hi')]
    simp
theorem half0_root_free (x : ℚ) : half0_source.eval x ≠ 0 :=
  rational_root_free half0_source half0_coefficients (529) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-5161)).Nonsingular (10937/529 : ℚ) (737732/12167 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-5161)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-5161)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-5161) (10937/529 : ℚ) (737732/12167 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-5161) (10937/529 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-5161)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m5161
#print axioms PerfectPower.MordellParityAtlas.Curve_m5161.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m5161.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m5161.no_half0
end PerfectPower.MordellParityAtlas
