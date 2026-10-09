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
namespace Curve_m8408
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8408)
private def branch_coefficients : List ℤ := [-8408, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8408) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8408)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8408) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8408)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(2886/25 : ℚ))*X^3-C (-67264)*X-C (4*(2886/25 : ℚ)*(-8408))
private def half0_coefficients : List ℤ := [1516593000000, 1051000000, 0, -11544, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-8408)).Nonsingular (2886/25 : ℚ) (154616/125 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8408)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8408)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8408) (2886/25 : ℚ) (154616/125 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8408) (2886/25 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8408)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8408
#print axioms PerfectPower.MordellParityAtlas.Curve_m8408.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8408.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8408.no_half0
namespace Curve_m8417
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8417)
private def branch_coefficients : List ℤ := [-8417, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8417) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8417)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8417) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8417)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(12814285925642095091367277624391093765095489632437721/627303858663826548317619410073675176670965381364025 : ℚ))*X^3-C (-67336)*X-C (4*(12814285925642095091367277624391093765095489632437721/627303858663826548317619410073675176670965381364025 : ℚ)*(-8417))
private def half0_coefficients : List ℤ := [106499018573459458136291249953106628083076271367276021943902222675316177200092831355443981854924415662077564903954191064871619040582308333192807934618720732040027383154830321498348155971396901294820243313562500, 16621920127495989438023903905408215349442405785160504299492957051709430523449104919383912778441255548749453051169045333171218462366824165441222475796072125000, 0, -51257143702568380365469110497564375060381958529750884, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (627303858663826548317619410073675176670965381364025) := by
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
  rational_root_free half0_source half0_coefficients (627303858663826548317619410073675176670965381364025) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8417)).Nonsingular (12814285925642095091367277624391093765095489632437721/627303858663826548317619410073675176670965381364025 : ℚ) (-162608862356173363733694191219195852784435208367008500060099029062117903609856/15711474267518769067007924795748190854018757581756504904896219851633264726125 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8417)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8417)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8417) (12814285925642095091367277624391093765095489632437721/627303858663826548317619410073675176670965381364025 : ℚ) (-162608862356173363733694191219195852784435208367008500060099029062117903609856/15711474267518769067007924795748190854018757581756504904896219851633264726125 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8417) (12814285925642095091367277624391093765095489632437721/627303858663826548317619410073675176670965381364025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8417)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8417
#print axioms PerfectPower.MordellParityAtlas.Curve_m8417.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8417.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8417.no_half0
namespace Curve_m8445
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8445)
private def branch_coefficients : List ℤ := [-8445, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8445) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8445)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8445) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8445)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(23618546587466781717623245526511721/1143162406831246493206828309290441 : ℚ))*X^3-C (-67560)*X-C (4*(23618546587466781717623245526511721/1143162406831246493206828309290441 : ℚ)*(-8445))
private def half0_coefficients : List ℤ := [1191891209106142627186489597822721689486242906662380462440744889769024304673824965001354688311433308668767496514895146343601905058207860980, 100928412736338445232329540301655082123278379951996023810087786538953604492997147148560122484196712334760, 0, -94474186349867126870492982106046884, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1143162406831246493206828309290441) := by
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
  rational_root_free half0_source half0_coefficients (1143162406831246493206828309290441) half0_monic half0_scale 13 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8445)).Nonsingular (23618546587466781717623245526511721/1143162406831246493206828309290441 : ℚ) (-747808725475947867405017448777089601628745618443246/38651103815730030397330953805744466952697469855739 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8445)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8445)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8445) (23618546587466781717623245526511721/1143162406831246493206828309290441 : ℚ) (-747808725475947867405017448777089601628745618443246/38651103815730030397330953805744466952697469855739 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8445) (23618546587466781717623245526511721/1143162406831246493206828309290441 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8445)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8445
#print axioms PerfectPower.MordellParityAtlas.Curve_m8445.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8445.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8445.no_half0
namespace Curve_m8473
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8473)
private def branch_coefficients : List ℤ := [-8473, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8473) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8473)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8473) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8473)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1748998673220104439628721650333117440826753961/8487535461836151216054321012565669260552100 : ℚ))*X^3-C (-67784)*X-C (4*(1748998673220104439628721650333117440826753961/8487535461836151216054321012565669260552100 : ℚ)*(-8473))
private def half0_coefficients : List ℤ := [36243612895863492656775789398213625806762908255559622957381640317916041835084252695952977586345244073717932058866071488817467158384502288196263539823766568414177877483387332000000, 41444986152144873503350910018464325795175388637480405527021774160792499366193652396285470295182408974528603917426079782899223624000000, 0, -6995994692880417758514886601332469763307015844, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (8487535461836151216054321012565669260552100) := by
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
  rational_root_free half0_source half0_coefficients (8487535461836151216054321012565669260552100) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8473)).Nonsingular (1748998673220104439628721650333117440826753961/8487535461836151216054321012565669260552100 : ℚ) (73109506562943895449117225122255639265780805850117792748418682830709/24727055449781786920038351178736970584104322727436228734075431000 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8473)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8473)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8473) (1748998673220104439628721650333117440826753961/8487535461836151216054321012565669260552100 : ℚ) (73109506562943895449117225122255639265780805850117792748418682830709/24727055449781786920038351178736970584104322727436228734075431000 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8473) (1748998673220104439628721650333117440826753961/8487535461836151216054321012565669260552100 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8473)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8473
#print axioms PerfectPower.MordellParityAtlas.Curve_m8473.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8473.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8473.no_half0
namespace Curve_m8555
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8555)
private def branch_coefficients : List ℤ := [-8555, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8555) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8555)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8555) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8555)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(21810724903522276802241042994481041/852148173185601327346408861851684 : ℚ))*X^3-C (-68440)*X-C (4*(21810724903522276802241042994481041/852148173185601327346408861851684 : ℚ)*(-8555))
private def half0_coefficients : List ℤ := [461844160887215049639087240505631033708380779384261794248533604818982421441808424511439397658538589597901156382272195495231525874267022080, 42350188994647354018563784067941985182983331680118687728204606836866267177231634672911187790586750133760, 0, -87242899614089107208964171977924164, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (852148173185601327346408861851684) := by
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
  rational_root_free half0_source half0_coefficients (852148173185601327346408861851684) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8555)).Nonsingular (21810724903522276802241042994481041/852148173185601327346408861851684 : ℚ) (2254275184819504579614531498993171126474148625887399/24875549092338527829264764576144245930684213420248 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8555)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8555)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8555) (21810724903522276802241042994481041/852148173185601327346408861851684 : ℚ) (2254275184819504579614531498993171126474148625887399/24875549092338527829264764576144245930684213420248 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8555) (21810724903522276802241042994481041/852148173185601327346408861851684 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8555)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8555
#print axioms PerfectPower.MordellParityAtlas.Curve_m8555.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8555.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8555.no_half0
namespace Curve_m857
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-857)
private def branch_coefficients : List ℤ := [-857, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-857) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-857)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-857) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-857)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1257/49 : ℚ))*X^3-C (-6856)*X-C (4*(1257/49 : ℚ)*(-857))
private def half0_coefficients : List ℤ := [506949070404, 806601544, 0, -5028, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (49) := by
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
  rational_root_free half0_source half0_coefficients (49) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-857)).Nonsingular (1257/49 : ℚ) (43420/343 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-857)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-857)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-857) (1257/49 : ℚ) (43420/343 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-857) (1257/49 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-857)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m857
#print axioms PerfectPower.MordellParityAtlas.Curve_m857.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m857.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m857.no_half0
namespace Curve_m8590
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8590)
private def branch_coefficients : List ℤ := [-8590, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8590) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8590)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8590) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8590)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(689433304868319814035509832535001/15472360525235363418558298237504 : ℚ))*X^3-C (-68720)*X-C (4*(689433304868319814035509832535001/15472360525235363418558298237504 : ℚ)*(-8590))
private def half0_coefficients : List ℤ := [87743538357074513020634945937783399393895999046398887387358457120206300969229454107466364814975802447766482734936328238844912599040, 254538148179056503121132226844566937176028181896785731815178294999033795484217648307933334292398080, 0, -2757733219473279256142039330140004, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (15472360525235363418558298237504) := by
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
  rational_root_free half0_source half0_coefficients (15472360525235363418558298237504) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8590)).Nonsingular (689433304868319814035509832535001/15472360525235363418558298237504 : ℚ) (17201249530363465453085513265413883538350275659421/60860408729195674292537586488525249879128724992 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8590)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8590)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8590) (689433304868319814035509832535001/15472360525235363418558298237504 : ℚ) (17201249530363465453085513265413883538350275659421/60860408729195674292537586488525249879128724992 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8590) (689433304868319814035509832535001/15472360525235363418558298237504 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8590)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8590
#print axioms PerfectPower.MordellParityAtlas.Curve_m8590.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8590.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8590.no_half0
namespace Curve_m8620
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8620)
private def branch_coefficients : List ℤ := [-8620, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8620) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8620)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8620) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8620)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(314081472529949128936129/3303723465269576572356 : ℚ))*X^3-C (-68960)*X-C (4*(314081472529949128936129/3303723465269576572356 : ℚ)*(-8620))
private def half0_coefficients : List ℤ := [390499641541869831300115679536777499552913771024603742227595409022176015706669000002388126720, 2486613669990571472449215567713632922541674476258058539525568723343360, 0, -1256325890119796515744516, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (3303723465269576572356) := by
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
  rational_root_free half0_source half0_coefficients (3303723465269576572356) half0_monic half0_scale 23 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8620)).Nonsingular (314081472529949128936129/3303723465269576572356 : ℚ) (-175135439421217264069996285738494113/189891503015529070527076995480504 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8620)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8620)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8620) (314081472529949128936129/3303723465269576572356 : ℚ) (-175135439421217264069996285738494113/189891503015529070527076995480504 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8620) (314081472529949128936129/3303723465269576572356 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8620)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8620
#print axioms PerfectPower.MordellParityAtlas.Curve_m8620.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8620.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8620.no_half0
namespace Curve_m8655
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8655)
private def branch_coefficients : List ℤ := [-8655, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8655) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8655)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8655) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8655)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1729/16 : ℚ))*X^3-C (-69240)*X-C (4*(1729/16 : ℚ)*(-8655))
private def half0_coefficients : List ℤ := [245178286080, 283607040, 0, -6916, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (16) := by
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
  rational_root_free half0_source half0_coefficients (16) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8655)).Nonsingular (1729/16 : ℚ) (71647/64 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8655)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8655)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8655) (1729/16 : ℚ) (71647/64 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8655) (1729/16 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8655)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8655
#print axioms PerfectPower.MordellParityAtlas.Curve_m8655.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8655.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8655.no_half0
namespace Curve_m8683
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8683)
private def branch_coefficients : List ℤ := [-8683, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8683) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8683)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8683) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8683)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(2352430584586659633529225366035191851/9729614854745430531991387342994025 : ℚ))*X^3-C (-69464)*X-C (4*(2352430584586659633529225366035191851/9729614854745430531991387342994025 : ℚ)*(-8683))
private def half0_coefficients : List ℤ := [75254687541332980365700222161008082844116151478786646281916946836110076382080106139527668277623739441486471795104716606594185297568574054562500, 63980368249255537370290924783931851003595188347321045911612405979888769486870403521897716355550783415375000, 0, -9409722338346638534116901464140767404, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (9729614854745430531991387342994025) := by
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
  rational_root_free half0_source half0_coefficients (9729614854745430531991387342994025) half0_monic half0_scale 29 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8683)).Nonsingular (2352430584586659633529225366035191851/9729614854745430531991387342994025 : ℚ) (-3606963796331298610302113024550304508496239385413952224/959717631845628868538155251287687293082728536748875 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8683)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8683)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8683) (2352430584586659633529225366035191851/9729614854745430531991387342994025 : ℚ) (-3606963796331298610302113024550304508496239385413952224/959717631845628868538155251287687293082728536748875 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8683) (2352430584586659633529225366035191851/9729614854745430531991387342994025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8683)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8683
#print axioms PerfectPower.MordellParityAtlas.Curve_m8683.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8683.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8683.no_half0
namespace Curve_m8778
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8778)
private def branch_coefficients : List ℤ := [-8778, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8778) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8778)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8778) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8778)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(68748333305829360033528577374553/3009057124210271135447128646544 : ℚ))*X^3-C (-70224)*X-C (4*(68748333305829360033528577374553/3009057124210271135447128646544 : ℚ)*(-8778))
private def half0_coefficients : List ℤ := [65767152567405104011165847066864086173488539416837328784729001906822368770589921480846618421907787549240686176689889404999860224, 1913272639638771474967200630472150851419489037559256597000325539952684430989480327946034897289216, 0, -274993333223317440134114309498212, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (3009057124210271135447128646544) := by
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
  rational_root_free half0_source half0_coefficients (3009057124210271135447128646544) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8778)).Nonsingular (68748333305829360033528577374553/3009057124210271135447128646544 : ℚ) (-292862526265459175040638056726063330997577958435/5219701273074680316087189178450732469305083072 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8778)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8778)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8778) (68748333305829360033528577374553/3009057124210271135447128646544 : ℚ) (-292862526265459175040638056726063330997577958435/5219701273074680316087189178450732469305083072 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8778) (68748333305829360033528577374553/3009057124210271135447128646544 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8778)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8778
#print axioms PerfectPower.MordellParityAtlas.Curve_m8778.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8778.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8778.no_half0
namespace Curve_m8793
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8793)
private def branch_coefficients : List ℤ := [-8793, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8793) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8793)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8793) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8793)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(57/1 : ℚ))*X^3-C (-70344)*X-C (4*(57/1 : ℚ)*(-8793))
private def half0_coefficients : List ℤ := [2004804, 70344, 0, -228, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-8793)).Nonsingular (57/1 : ℚ) (420/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8793)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8793)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8793) (57/1 : ℚ) (420/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8793) (57/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8793)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8793
#print axioms PerfectPower.MordellParityAtlas.Curve_m8793.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8793.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8793.no_half0
namespace Curve_m8814
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8814)
private def branch_coefficients : List ℤ := [-8814, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8814) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8814)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8814) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8814)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(100510928923239166015756585084214063568463/689453394378225298889668168962266697969 : ℚ))*X^3-C (-70512)*X-C (4*(100510928923239166015756585084214063568463/689453394378225298889668168962266697969 : ℚ)*(-8814))
private def half0_coefficients : List ℤ := [1161344497454874360669990586021893320775208482945343675316226930916865812606582507548946294232210292141244882588109141150731364758493173917872142910282745562401352, 23108820302353399202395633655567600836762718807876742102500277544208595127704988520036490259914865493751041609327466385008, 0, -402043715692956664063026340336856254273852, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (689453394378225298889668168962266697969) := by
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
  rational_root_free half0_source half0_coefficients (689453394378225298889668168962266697969) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8814)).Nonsingular (100510928923239166015756585084214063568463/689453394378225298889668168962266697969 : ℚ) (-31820083485841474851363712354904909398020766197642366796028561/18103284273770782697255256811419003590882023075457617333047 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8814)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8814)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8814) (100510928923239166015756585084214063568463/689453394378225298889668168962266697969 : ℚ) (-31820083485841474851363712354904909398020766197642366796028561/18103284273770782697255256811419003590882023075457617333047 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8814) (100510928923239166015756585084214063568463/689453394378225298889668168962266697969 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8814)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8814
#print axioms PerfectPower.MordellParityAtlas.Curve_m8814.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8814.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8814.no_half0
namespace Curve_m8835
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8835)
private def branch_coefficients : List ℤ := [-8835, 0, 0, 1]
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
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 43 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8835) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8835)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8835) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8835)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(631171722782578144749237601/74489827674245409075456 : ℚ))*X^3-C (-70680)*X-C (4*(631171722782578144749237601/74489827674245409075456 : ℚ)*(-8835))
private def half0_coefficients : List ℤ := [9219449454254054969556585172939440264767400469683141276363761898718848583476915385318226372528701440, 29213759493563084934103154120846198453279788989511866555863274428961914880, 0, -2524686891130312578996950404, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (74489827674245409075456) := by
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
  rational_root_free half0_source half0_coefficients (74489827674245409075456) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8835)).Nonsingular (631171722782578144749237601/74489827674245409075456 : ℚ) (15857009904770254198983012993518383459729/20330378040578152699426924815151104 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8835)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8835)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8835) (631171722782578144749237601/74489827674245409075456 : ℚ) (15857009904770254198983012993518383459729/20330378040578152699426924815151104 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8835) (631171722782578144749237601/74489827674245409075456 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8835)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8835
#print axioms PerfectPower.MordellParityAtlas.Curve_m8835.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8835.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8835.no_half0
namespace Curve_m8885
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8885)
private def branch_coefficients : List ℤ := [-8885, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8885) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8885)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8885) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8885)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(478616857985252410899819179891711318301/5907456347443137355372027170135216049 : ℚ))*X^3-C (-71080)*X-C (4*(478616857985252410899819179891711318301/5907456347443137355372027170135216049 : ℚ)*(-8885))
private def half0_coefficients : List ℤ := [3506767543106687756175952817695213838291974676503790662607597384640489102802990099971350008921691851142510658175270027654731872782603537907591122425083460, 14653756902205653395350259871690449321520301166560954021048342028480601200588500995597221164395974238492171998330920, 0, -1914467431941009643599276719566845273204, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (5907456347443137355372027170135216049) := by
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
  rational_root_free half0_source half0_coefficients (5907456347443137355372027170135216049) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8885)).Nonsingular (478616857985252410899819179891711318301/5907456347443137355372027170135216049 : ℚ) (-10383015208426036074760933262432311136573206140225785439256/14358225894831595414733016681494510153749081703347768343 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8885)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8885)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8885) (478616857985252410899819179891711318301/5907456347443137355372027170135216049 : ℚ) (-10383015208426036074760933262432311136573206140225785439256/14358225894831595414733016681494510153749081703347768343 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8885) (478616857985252410899819179891711318301/5907456347443137355372027170135216049 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8885)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8885
#print axioms PerfectPower.MordellParityAtlas.Curve_m8885.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8885.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8885.no_half0
namespace Curve_m8886
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-8886)
private def branch_coefficients : List ℤ := [-8886, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-8886) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-8886)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-8886) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-8886)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(48732698890608555725666873637603674147822562535/2352263038245344060645436093482693269573501521 : ℚ))*X^3-C (-71088)*X-C (4*(48732698890608555725666873637603674147822562535/2352263038245344060645436093482693269573501521 : ℚ)*(-8886))
private def half0_coefficients : List ℤ := [22544697763672303469840970326078385925359000621905449263942220481196205907380430735148082698517604107093341484289936156912500508295846000116877252016297377856437023581161412120002009934440, 925239039778154741645059427368049600826203558347527581783943487034129861183901210270227596511157742827533884699324508129872821515493120481968, 0, -194930795562434222902667494550414696591290250140, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (2352263038245344060645436093482693269573501521) := by
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
  rational_root_free half0_source half0_coefficients (2352263038245344060645436093482693269573501521) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-8886)).Nonsingular (48732698890608555725666873637603674147822562535/2352263038245344060645436093482693269573501521 : ℚ) (-281485649659284308816843978933959015606642377018115282667561623992623/114085073533663180035211272960089822476684840753729093896676299809319 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-8886)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-8886)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-8886) (48732698890608555725666873637603674147822562535/2352263038245344060645436093482693269573501521 : ℚ) (-281485649659284308816843978933959015606642377018115282667561623992623/114085073533663180035211272960089822476684840753729093896676299809319 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-8886) (48732698890608555725666873637603674147822562535/2352263038245344060645436093482693269573501521 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-8886)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m8886
#print axioms PerfectPower.MordellParityAtlas.Curve_m8886.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m8886.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m8886.no_half0
end PerfectPower.MordellParityAtlas
