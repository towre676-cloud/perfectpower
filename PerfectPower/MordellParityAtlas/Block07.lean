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
namespace Curve_m6282
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6282)
private def branch_coefficients : List ℤ := [-6282, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6282) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6282)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6282) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6282)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(3129/64 : ℚ))*X^3-C (-50256)*X-C (4*(3129/64 : ℚ)*(-6282))
private def half0_coefficients : List ℤ := [20611206217728, 13174308864, 0, -12516, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (64) := by
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
  rational_root_free half0_source half0_coefficients (64) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6282)).Nonsingular (3129/64 : ℚ) (170259/512 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6282)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6282)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6282) (3129/64 : ℚ) (170259/512 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6282) (3129/64 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6282)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6282
#print axioms PerfectPower.MordellParityAtlas.Curve_m6282.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6282.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6282.no_half0
namespace Curve_m6286
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6286)
private def branch_coefficients : List ℤ := [-6286, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6286) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6286)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6286) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6286)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(12895400360638326374334442936783/659767737992894990019552934881 : ℚ))*X^3-C (-50288)*X-C (4*(12895400360638326374334442936783/659767737992894990019552934881 : ℚ)*(-6286))
private def half0_coefficients : List ℤ := [93119883415521846062215683118199311786479205454146309083276396769504237695359834619933614326886513218391740945973440338831432, 14442340805448615407019978187580663386739245980007224597397165964698415110291847884581136964208, 0, -51581601442553305497337771747132, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (659767737992894990019552934881) := by
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
  rational_root_free half0_source half0_coefficients (659767737992894990019552934881) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6286)).Nonsingular (12895400360638326374334442936783/659767737992894990019552934881 : ℚ) (18414693590355637658136946832846075627992891631/535903523788519924260868896033917420852919471 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6286)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6286)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6286) (12895400360638326374334442936783/659767737992894990019552934881 : ℚ) (18414693590355637658136946832846075627992891631/535903523788519924260868896033917420852919471 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6286) (12895400360638326374334442936783/659767737992894990019552934881 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6286)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6286
#print axioms PerfectPower.MordellParityAtlas.Curve_m6286.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6286.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6286.no_half0
namespace Curve_m6315
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6315)
private def branch_coefficients : List ℤ := [-6315, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6315) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6315)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6315) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6315)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(170521/36 : ℚ))*X^3-C (-50520)*X-C (4*(170521/36 : ℚ)*(-6315))
private def half0_coefficients : List ℤ := [200964209621760, 2357061120, 0, -682084, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (36) := by
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
  rational_root_free half0_source half0_coefficients (36) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6315)).Nonsingular (170521/36 : ℚ) (70415261/216 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6315)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6315)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6315) (170521/36 : ℚ) (70415261/216 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6315) (170521/36 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6315)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6315
#print axioms PerfectPower.MordellParityAtlas.Curve_m6315.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6315.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6315.no_half0
namespace Curve_m6338
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6338)
private def branch_coefficients : List ℤ := [-6338, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6338) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6338)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6338) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6338)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1377131975492456584507990971691/74126395648073338803697475025 : ℚ))*X^3-C (-50704)*X-C (4*(1377131975492456584507990971691/74126395648073338803697475025 : ℚ)*(-6338))
private def half0_coefficients : List ℤ := [14220224028014819085804394921971139877869073408600451765587347805053529689646739313497261145997916091659897937781472375000, 20651940817697921750066187426748254075017425684982857119317358972146536292027495699042250000, 0, -5508527901969826338031963886764, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (74126395648073338803697475025) := by
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
  rational_root_free half0_source half0_coefficients (74126395648073338803697475025) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6338)).Nonsingular (1377131975492456584507990971691/74126395648073338803697475025 : ℚ) (173861526559173085596595080564896357143443239/20181773370214895131443039010741306597062375 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6338)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6338)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6338) (1377131975492456584507990971691/74126395648073338803697475025 : ℚ) (173861526559173085596595080564896357143443239/20181773370214895131443039010741306597062375 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6338) (1377131975492456584507990971691/74126395648073338803697475025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6338)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6338
#print axioms PerfectPower.MordellParityAtlas.Curve_m6338.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6338.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6338.no_half0
namespace Curve_m6415
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6415)
private def branch_coefficients : List ℤ := [-6415, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6415) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6415)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6415) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6415)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(14714/1 : ℚ))*X^3-C (-51320)*X-C (4*(14714/1 : ℚ)*(-6415))
private def half0_coefficients : List ℤ := [377561240, 51320, 0, -58856, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-6415)).Nonsingular (14714/1 : ℚ) (1784827/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6415)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6415)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6415) (14714/1 : ℚ) (1784827/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6415) (14714/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6415)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6415
#print axioms PerfectPower.MordellParityAtlas.Curve_m6415.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6415.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6415.no_half0
namespace Curve_m6420
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6420)
private def branch_coefficients : List ℤ := [-6420, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6420) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6420)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6420) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6420)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1654/81 : ℚ))*X^3-C (-51360)*X-C (4*(1654/81 : ℚ)*(-6420))
private def half0_coefficients : List ℤ := [22572807671520, 27294809760, 0, -6616, 1]
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
  rational_root_free half0_source half0_coefficients (81) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6420)).Nonsingular (1654/81 : ℚ) (33362/729 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6420)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6420)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6420) (1654/81 : ℚ) (33362/729 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6420) (1654/81 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6420)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6420
#print axioms PerfectPower.MordellParityAtlas.Curve_m6420.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6420.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6420.no_half0
namespace Curve_m6429
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6429)
private def branch_coefficients : List ℤ := [-6429, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6429) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6429)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6429) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6429)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(2130460263233533058911051846498052581/33124923521097820907494533566670225 : ℚ))*X^3-C (-51432)*X-C (4*(2130460263233533058911051846498052581/33124923521097820907494533566670225 : ℚ)*(-6429))
private def half0_coefficients : List ℤ := [1991322074590767016863070234895355612685699999355300509333575951983929827635286043871301407088280866956078994829163568383768683843469519757562500, 1869382038197147790722526976151129891067873743148630742761891468705028139826373563865445340181649863292625000, 0, -8521841052934132235644207385992210324, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (33124923521097820907494533566670225) := by
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
  rational_root_free half0_source half0_coefficients (33124923521097820907494533566670225) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6429)).Nonsingular (2130460263233533058911051846498052581/33124923521097820907494533566670225 : ℚ) (3071838228778893264704828153975718976874006535088912604/6028820123017027748455508803543769968156717972578375 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6429)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6429)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6429) (2130460263233533058911051846498052581/33124923521097820907494533566670225 : ℚ) (3071838228778893264704828153975718976874006535088912604/6028820123017027748455508803543769968156717972578375 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6429) (2130460263233533058911051846498052581/33124923521097820907494533566670225 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6429)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6429
#print axioms PerfectPower.MordellParityAtlas.Curve_m6429.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6429.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6429.no_half0
namespace Curve_m6458
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6458)
private def branch_coefficients : List ℤ := [-6458, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6458) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6458)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6458) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6458)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(27/1 : ℚ))*X^3-C (-51664)*X-C (4*(27/1 : ℚ)*(-6458))
private def half0_coefficients : List ℤ := [697464, 51664, 0, -108, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-6458)).Nonsingular (27/1 : ℚ) (115/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6458)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6458)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6458) (27/1 : ℚ) (115/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6458) (27/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
private noncomputable def half1_source : Polynomial ℚ := X^4-C (4*(10179648145510299/465655614693025 : ℚ))*X^3-C (-51664)*X-C (4*(10179648145510299/465655614693025 : ℚ)*(-6458))
private def half1_coefficients : List ℤ := [26551271934325076791352104827913190686520095892367572168878875000, 5216540209405062725808487710938366220184917250000, 0, -40718592582041196, 1]
private noncomputable def half1_scaled := polynomial half1_coefficients
private theorem half1_degree : half1_source.natDegree=4 := by
  unfold half1_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half1_monic : half1_scaled.Monic := by
  simp [half1_scaled,half1_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half1_scale : half1_scaled.map (Int.castRingHom ℚ) = half1_source.scaleRoots (465655614693025) := by
  have hg : half1_scaled.natDegree=4 := by
    simp [half1_scaled,half1_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half1_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half1_scaled,half1_coefficients,polynomial,half1_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half1_degree]; exact hi')]
    simp
theorem half1_root_free (x : ℚ) : half1_source.eval x ≠ 0 :=
  rational_root_free half1_source half1_coefficients (465655614693025) half1_monic half1_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve1 : (completed (0:ℚ) 0 (-6458)).Nonsingular (10179648145510299/465655614693025 : ℚ) (634665990131477299813907/10048408120519594591375 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P1 : (completed (0:ℚ) 0 (-6458)).Point := WeierstrassCurve.Affine.Point.some on_curve1
theorem no_half1 (Q : (completed (0:ℚ) 0 (-6458)).Point) : (2:ℤ) • Q ≠ P1 := by
  apply no_half_of_quartic_root_free 0 0 (-6458) (10179648145510299/465655614693025 : ℚ) (634665990131477299813907/10048408120519594591375 : ℚ) on_curve1
  intro x
  have he : half1_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6458) (10179648145510299/465655614693025 : ℚ) x := by
    simp only [half1_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half1_root_free x
private noncomputable def half2_source : Polynomial ℚ := X^4-C (4*(1301966807733498673/24616239340679424 : ℚ))*X^3-C (-51664)*X-C (4*(1301966807733498673/24616239340679424 : ℚ)*(-6458))
private def half2_coefficients : List ℤ := [501675696227019965619277792826098514999843829297357837006239648358334464, 770642835511838385933340352646663145595852508874407936, 0, -5207867230933994692, 1]
private noncomputable def half2_scaled := polynomial half2_coefficients
private theorem half2_degree : half2_source.natDegree=4 := by
  unfold half2_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half2_monic : half2_scaled.Monic := by
  simp [half2_scaled,half2_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half2_scale : half2_scaled.map (Int.castRingHom ℚ) = half2_source.scaleRoots (24616239340679424) := by
  have hg : half2_scaled.natDegree=4 := by
    simp [half2_scaled,half2_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half2_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half2_scaled,half2_coefficients,polynomial,half2_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half2_degree]; exact hi')]
    simp
theorem half2_root_free (x : ℚ) : half2_source.eval x ≠ 0 :=
  rational_root_free half2_source half2_coefficients (24616239340679424) half2_monic half2_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve2 : (completed (0:ℚ) 0 (-6458)).Nonsingular (1301966807733498673/24616239340679424 : ℚ) (-1452809848147892068835911465/3862180428819161537875968 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P2 : (completed (0:ℚ) 0 (-6458)).Point := WeierstrassCurve.Affine.Point.some on_curve2
theorem no_half2 (Q : (completed (0:ℚ) 0 (-6458)).Point) : (2:ℤ) • Q ≠ P2 := by
  apply no_half_of_quartic_root_free 0 0 (-6458) (1301966807733498673/24616239340679424 : ℚ) (-1452809848147892068835911465/3862180428819161537875968 : ℚ) on_curve2
  intro x
  have he : half2_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6458) (1301966807733498673/24616239340679424 : ℚ) x := by
    simp only [half2_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half2_root_free x
theorem sum_checked : P0+P1=P2 := by
  unfold P0 P1 P2
  rw [WeierstrassCurve.Affine.Point.add_some (by
    norm_num [completed,WeierstrassCurve.Affine.negY] : ¬((27/1 : ℚ)=(10179648145510299/465655614693025 : ℚ) ∧ (115/1 : ℚ)=(completed (0:ℚ) 0 (-6458)).negY (10179648145510299/465655614693025 : ℚ) (634665990131477299813907/10048408120519594591375 : ℚ)))]
  rw [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne (by norm_num : (27/1 : ℚ) ≠ (10179648145510299/465655614693025 : ℚ))]
  norm_num [completed,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY]
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6458)).Point) (m n : ℤ)
    (h : (2:ℤ) • Q=m • P0+n • P1) : ∃ a b : ℤ, Q=a • P0+b • P1 :=
  pair_two_saturated P0 P1 double_injective no_half0 no_half1 (by rw [sum_checked]; exact no_half2) Q m n h
end Curve_m6458
#print axioms PerfectPower.MordellParityAtlas.Curve_m6458.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6458.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6458.no_half0
#print axioms PerfectPower.MordellParityAtlas.Curve_m6458.no_half1
#print axioms PerfectPower.MordellParityAtlas.Curve_m6458.no_half2
namespace Curve_m6510
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6510)
private def branch_coefficients : List ℤ := [-6510, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6510) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6510)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6510) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6510)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(266995837486449703681936993380079/10802704540258556506807221429729 : ℚ))*X^3-C (-52080)*X-C (4*(266995837486449703681936993380079/10802704540258556506807221429729 : ℚ)*(-6510))
private def half0_coefficients : List ℤ := [8764819257631289803660536210779545100123512743648673691635320450260420266325743671800447935019045825120883659575833085658815671240, 65655100395159627432272838231544870260612533909369055116301512467987731528364835668444375508427120, 0, -1067983349945798814727747973520316, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (10802704540258556506807221429729) := by
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
  rational_root_free half0_source half0_coefficients (10802704540258556506807221429729) half0_monic half0_scale 29 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6510)).Nonsingular (266995837486449703681936993380079/10802704540258556506807221429729 : ℚ) (3290347282612893886354439032179867099416119551407/35505754600319200712564691911362423823387300433 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6510)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6510)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6510) (266995837486449703681936993380079/10802704540258556506807221429729 : ℚ) (3290347282612893886354439032179867099416119551407/35505754600319200712564691911362423823387300433 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6510) (266995837486449703681936993380079/10802704540258556506807221429729 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6510)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6510
#print axioms PerfectPower.MordellParityAtlas.Curve_m6510.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6510.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6510.no_half0
namespace Curve_m6545
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6545)
private def branch_coefficients : List ℤ := [-6545, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6545) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6545)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6545) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6545)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(39648207953457524582169447394629/600975186910901132796711961 : ℚ))*X^3-C (-52360)*X-C (4*(39648207953457524582169447394629/600975186910901132796711961 : ℚ)*(-6545))
private def half0_coefficients : List ℤ := [225300849057581428716059987587048000223580479600835004020887932345574229714015675609496830925956898145445019721816820, 11364995327004889428117511492573173009636188739487441912203346514841633552958994217160, 0, -158592831813830098328677789578516, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (600975186910901132796711961) := by
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
  rational_root_free half0_source half0_coefficients (600975186910901132796711961) half0_monic half0_scale 23 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6545)).Nonsingular (39648207953457524582169447394629/600975186910901132796711961 : ℚ) (-249652169138387213447647223214869393404513938362/14732783666784966891417659090606718716291 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6545)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6545)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6545) (39648207953457524582169447394629/600975186910901132796711961 : ℚ) (-249652169138387213447647223214869393404513938362/14732783666784966891417659090606718716291 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6545) (39648207953457524582169447394629/600975186910901132796711961 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6545)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6545
#print axioms PerfectPower.MordellParityAtlas.Curve_m6545.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6545.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6545.no_half0
namespace Curve_m6546
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6546)
private def branch_coefficients : List ℤ := [-6546, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6546) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6546)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6546) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6546)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(20707/1089 : ℚ))*X^3-C (-52368)*X-C (4*(20707/1089 : ℚ)*(-6546))
private def half0_coefficients : List ℤ := [700223714697229272, 67631594600592, 0, -82828, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1089) := by
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
  rational_root_free half0_source half0_coefficients (1089) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6546)).Nonsingular (20707/1089 : ℚ) (651763/35937 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6546)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6546)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6546) (20707/1089 : ℚ) (651763/35937 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6546) (20707/1089 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6546)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6546
#print axioms PerfectPower.MordellParityAtlas.Curve_m6546.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6546.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6546.no_half0
namespace Curve_m6553
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6553)
private def branch_coefficients : List ℤ := [-6553, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6553) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6553)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6553) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6553)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(37/1 : ℚ))*X^3-C (-52424)*X-C (4*(37/1 : ℚ)*(-6553))
private def half0_coefficients : List ℤ := [969844, 52424, 0, -148, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-6553)).Nonsingular (37/1 : ℚ) (210/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6553)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6553)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6553) (37/1 : ℚ) (210/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6553) (37/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
private noncomputable def half1_source : Polynomial ℚ := X^4-C (4*(3429989893064137/40197514702801 : ℚ))*X^3-C (-52424)*X-C (4*(3429989893064137/40197514702801 : ℚ)*(-6553))
private def half1_coefficients : List ℤ := [5839700953632370086700687490454868113767572049754773816408644, 3405083475867358287434367732240008144039294024, 0, -13719959572256548, 1]
private noncomputable def half1_scaled := polynomial half1_coefficients
private theorem half1_degree : half1_source.natDegree=4 := by
  unfold half1_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half1_monic : half1_scaled.Monic := by
  simp [half1_scaled,half1_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half1_scale : half1_scaled.map (Int.castRingHom ℚ) = half1_source.scaleRoots (40197514702801) := by
  have hg : half1_scaled.natDegree=4 := by
    simp [half1_scaled,half1_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half1_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half1_scaled,half1_coefficients,polynomial,half1_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half1_degree]; exact hi')]
    simp
theorem half1_root_free (x : ℚ) : half1_source.eval x ≠ 0 :=
  rational_root_free half1_source half1_coefficients (40197514702801) half1_monic half1_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve1 : (completed (0:ℚ) 0 (-6553)).Nonsingular (3429989893064137/40197514702801 : ℚ) (199818955170170230837740/254858313040478462951 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P1 : (completed (0:ℚ) 0 (-6553)).Point := WeierstrassCurve.Affine.Point.some on_curve1
theorem no_half1 (Q : (completed (0:ℚ) 0 (-6553)).Point) : (2:ℤ) • Q ≠ P1 := by
  apply no_half_of_quartic_root_free 0 0 (-6553) (3429989893064137/40197514702801 : ℚ) (199818955170170230837740/254858313040478462951 : ℚ) on_curve1
  intro x
  have he : half1_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6553) (3429989893064137/40197514702801 : ℚ) x := by
    simp only [half1_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half1_root_free x
private noncomputable def half2_source : Polynomial ℚ := X^4-C (4*(119300219865504689/6360708491402500 : ℚ))*X^3-C (-52424)*X-C (4*(119300219865504689/6360708491402500 : ℚ)*(-6553))
private def half2_coefficients : List ℤ := [804744247331582235177171493288863000947594830586478687323562500000000, 13491077354908910603248462532867295471249125000000000, 0, -477200879462018756, 1]
private noncomputable def half2_scaled := polynomial half2_coefficients
private theorem half2_degree : half2_source.natDegree=4 := by
  unfold half2_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half2_monic : half2_scaled.Monic := by
  simp [half2_scaled,half2_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half2_scale : half2_scaled.map (Int.castRingHom ℚ) = half2_source.scaleRoots (6360708491402500) := by
  have hg : half2_scaled.natDegree=4 := by
    simp [half2_scaled,half2_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,half2_degree]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [half2_scaled,half2_coefficients,polynomial,half2_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [half2_degree]; exact hi')]
    simp
theorem half2_root_free (x : ℚ) : half2_source.eval x ≠ 0 :=
  rational_root_free half2_source half2_coefficients (6360708491402500) half2_monic half2_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve2 : (completed (0:ℚ) 0 (-6553)).Nonsingular (119300219865504689/6360708491402500 : ℚ) (3400114020805459010615863/507292263058739555125000 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P2 : (completed (0:ℚ) 0 (-6553)).Point := WeierstrassCurve.Affine.Point.some on_curve2
theorem no_half2 (Q : (completed (0:ℚ) 0 (-6553)).Point) : (2:ℤ) • Q ≠ P2 := by
  apply no_half_of_quartic_root_free 0 0 (-6553) (119300219865504689/6360708491402500 : ℚ) (3400114020805459010615863/507292263058739555125000 : ℚ) on_curve2
  intro x
  have he : half2_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6553) (119300219865504689/6360708491402500 : ℚ) x := by
    simp only [half2_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half2_root_free x
theorem sum_checked : P0+P1=P2 := by
  unfold P0 P1 P2
  rw [WeierstrassCurve.Affine.Point.add_some (by
    norm_num [completed,WeierstrassCurve.Affine.negY] : ¬((37/1 : ℚ)=(3429989893064137/40197514702801 : ℚ) ∧ (210/1 : ℚ)=(completed (0:ℚ) 0 (-6553)).negY (3429989893064137/40197514702801 : ℚ) (199818955170170230837740/254858313040478462951 : ℚ)))]
  rw [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne (by norm_num : (37/1 : ℚ) ≠ (3429989893064137/40197514702801 : ℚ))]
  norm_num [completed,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY]
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6553)).Point) (m n : ℤ)
    (h : (2:ℤ) • Q=m • P0+n • P1) : ∃ a b : ℤ, Q=a • P0+b • P1 :=
  pair_two_saturated P0 P1 double_injective no_half0 no_half1 (by rw [sum_checked]; exact no_half2) Q m n h
end Curve_m6553
#print axioms PerfectPower.MordellParityAtlas.Curve_m6553.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6553.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6553.no_half0
#print axioms PerfectPower.MordellParityAtlas.Curve_m6553.no_half1
#print axioms PerfectPower.MordellParityAtlas.Curve_m6553.no_half2
namespace Curve_m6590
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6590)
private def branch_coefficients : List ℤ := [-6590, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6590) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6590)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6590) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6590)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(46537884020110360441024399317746311390359/853414554399497101501044653589971577769 : ℚ))*X^3-C (-52720)*X-C (4*(46537884020110360441024399317746311390359/853414554399497101501044653589971577769 : ℚ)*(-6590))
private def half0_coefficients : List ℤ := [762486527393962259482551619323184318804245376467471866239849002765293020696345757230376762184801185677877694586993151784974828160263163532303695026719908722993160, 32768422692551722539298195104623517836717458824974798163360724203552138887594249380765038717884633758810516943031261946480, 0, -186151536080441441764097597270985245561436, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (853414554399497101501044653589971577769) := by
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
  rational_root_free half0_source half0_coefficients (853414554399497101501044653589971577769) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6590)).Nonsingular (46537884020110360441024399317746311390359/853414554399497101501044653589971577769 : ℚ) (9833337002030932811798802073124557147513149903578562939603563/24931021186170362433317135057856099127947360144249424679147 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6590)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6590)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6590) (46537884020110360441024399317746311390359/853414554399497101501044653589971577769 : ℚ) (9833337002030932811798802073124557147513149903578562939603563/24931021186170362433317135057856099127947360144249424679147 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6590) (46537884020110360441024399317746311390359/853414554399497101501044653589971577769 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6590)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6590
#print axioms PerfectPower.MordellParityAtlas.Curve_m6590.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6590.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6590.no_half0
namespace Curve_m6609
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6609)
private def branch_coefficients : List ℤ := [-6609, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6609) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6609)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6609) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6609)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(5346937/236196 : ℚ))*X^3-C (-52872)*X-C (4*(5346937/236196 : ℚ)*(-6609))
private def half0_coefficients : List ℤ := [1862594970245984276712145152, 696696059910930043392, 0, -21387748, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (236196) := by
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
  rational_root_free half0_source half0_coefficients (236196) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6609)).Nonsingular (5346937/236196 : ℚ) (8110518227/114791256 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6609)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6609)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6609) (5346937/236196 : ℚ) (8110518227/114791256 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6609) (5346937/236196 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6609)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6609
#print axioms PerfectPower.MordellParityAtlas.Curve_m6609.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6609.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6609.no_half0
namespace Curve_m6611
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6611)
private def branch_coefficients : List ℤ := [-6611, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6611) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6611)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6611) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6611)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(42004349404159384528804345034256440346171961075/1110398170994669149287850004217375655191288969 : ℚ))*X^3-C (-52888)*X-C (4*(42004349404159384528804345034256440346171961075/1110398170994669149287850004217375655191288969 : ℚ)*(-6611))
private def half0_coefficients : List ℤ := [1520749296294839636463728314479672804366778645934473981686109958681106571081983712533434788305244545541621890948872142080919444388652949924918263312845026699111139304617624117201447565700, 72409134666623400634101784003711121824045442399142754630934614597354470692426377080901025381110292551470865655934200413732464962905618469592, 0, -168017397616637538115217380137025761384687844300, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1110398170994669149287850004217375655191288969) := by
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
  rational_root_free half0_source half0_coefficients (1110398170994669149287850004217375655191288969) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6611)).Nonsingular (42004349404159384528804345034256440346171961075/1110398170994669149287850004217375655191288969 : ℚ) (8065970344425257131148780343662826225244708878233203004521001485318724/37001395750017203617617704179857441128844889843769551323268546213797 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6611)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6611)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6611) (42004349404159384528804345034256440346171961075/1110398170994669149287850004217375655191288969 : ℚ) (8065970344425257131148780343662826225244708878233203004521001485318724/37001395750017203617617704179857441128844889843769551323268546213797 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6611) (42004349404159384528804345034256440346171961075/1110398170994669149287850004217375655191288969 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6611)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6611
#print axioms PerfectPower.MordellParityAtlas.Curve_m6611.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6611.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6611.no_half0
namespace Curve_m6631
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-6631)
private def branch_coefficients : List ℤ := [-6631, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-6631) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-6631)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-6631) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-6631)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(20/1 : ℚ))*X^3-C (-53048)*X-C (4*(20/1 : ℚ)*(-6631))
private def half0_coefficients : List ℤ := [530480, 53048, 0, -80, 1]
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
  rational_root_free half0_source half0_coefficients (1) half0_monic half0_scale 13 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-6631)).Nonsingular (20/1 : ℚ) (37/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-6631)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-6631)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-6631) (20/1 : ℚ) (37/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-6631) (20/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-6631)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m6631
#print axioms PerfectPower.MordellParityAtlas.Curve_m6631.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m6631.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m6631.no_half0
end PerfectPower.MordellParityAtlas
