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
namespace Curve_m7043
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7043)
private def branch_coefficients : List ℤ := [-7043, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7043) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7043)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7043) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7043)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(53369114773614832741746242383/2210610655857713222281080969 : ℚ))*X^3-C (-56344)*X-C (4*(53369114773614832741746242383/2210610655857713222281080969 : ℚ)*(-7043))
private def half0_coefficients : List ℤ := [16242185132992619951779374266812259357847779888038733025158167447097575379878270694523774355336093685658263695368084, 608673582160392028359839926415430247630329604980907529743683181730388149587962741367896, 0, -213476459094459330966984969532, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (2210610655857713222281080969) := by
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
  rational_root_free half0_source half0_coefficients (2210610655857713222281080969) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7043)).Nonsingular (53369114773614832741746242383/2210610655857713222281080969 : ℚ) (-8713497907635593300002845017517662180589430/103936571933956470842534191537699805651547 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7043)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7043)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7043) (53369114773614832741746242383/2210610655857713222281080969 : ℚ) (-8713497907635593300002845017517662180589430/103936571933956470842534191537699805651547 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7043) (53369114773614832741746242383/2210610655857713222281080969 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7043)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7043
#print axioms PerfectPower.MordellParityAtlas.Curve_m7043.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7043.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7043.no_half0
namespace Curve_m7049
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7049)
private def branch_coefficients : List ℤ := [-7049, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7049) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7049)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7049) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7049)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(5196463840661753695421568589849/245436039386176890812434640001 : ℚ))*X^3-C (-56392)*X-C (4*(5196463840661753695421568589849/245436039386176890812434640001 : ℚ)*(-7049))
private def half0_coefficients : List ℤ := [2166259168265847329089947825123541055488161398949947218276072947062689292467013025352361751498582090467282016596871383062404, 833743574357280963358917093831580535102020791392589456255206016299884847584978894452256696392, 0, -20785855362647014781686274359396, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (245436039386176890812434640001) := by
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
  rational_root_free half0_source half0_coefficients (245436039386176890812434640001) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7049)).Nonsingular (5196463840661753695421568589849/245436039386176890812434640001 : ℚ) (-6008610070939901567353313268727068989789556800/121592699703455271966465442224354192251960001 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7049)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7049)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7049) (5196463840661753695421568589849/245436039386176890812434640001 : ℚ) (-6008610070939901567353313268727068989789556800/121592699703455271966465442224354192251960001 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7049) (5196463840661753695421568589849/245436039386176890812434640001 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7049)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7049
#print axioms PerfectPower.MordellParityAtlas.Curve_m7049.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7049.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7049.no_half0
namespace Curve_m7077
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7077)
private def branch_coefficients : List ℤ := [-7077, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7077) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7077)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7077) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7077)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(9193/81 : ℚ))*X^3-C (-56616)*X-C (4*(9193/81 : ℚ)*(-7077))
private def half0_coefficients : List ℤ := [138299784594804, 30088063656, 0, -36772, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-7077)).Nonsingular (9193/81 : ℚ) (879290/729 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7077)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7077)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7077) (9193/81 : ℚ) (879290/729 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7077) (9193/81 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7077)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7077
#print axioms PerfectPower.MordellParityAtlas.Curve_m7077.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7077.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7077.no_half0
namespace Curve_m7085
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7085)
private def branch_coefficients : List ℤ := [-7085, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7085) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7085)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7085) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7085)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(33142888753707008431462278963782559841489/124452765946757723550809063982800509089 : ℚ))*X^3-C (-56680)*X-C (4*(33142888753707008431462278963782559841489/124452765946757723550809063982800509089 : ℚ)*(-7085))
private def half0_coefficients : List ℤ := [1810522242628146473258499296601306571376058941366977482115658310243818933488717761811755239226780984846366518681458479689502105471493168758795439838344312973940, 109255548367107309182157423537680919383295805435229382003941852371875894176105257130397073418593339606800573535719202920, 0, -132571555014828033725849115855130239365956, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (124452765946757723550809063982800509089) := by
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
  rational_root_free half0_source half0_coefficients (124452765946757723550809063982800509089) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7085)).Nonsingular (33142888753707008431462278963782559841489/124452765946757723550809063982800509089 : ℚ) (-6032593541305451475706617518751680633955697188856439766768202/1388375143573468172893714281810426647693758231003989900687 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7085)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7085)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7085) (33142888753707008431462278963782559841489/124452765946757723550809063982800509089 : ℚ) (-6032593541305451475706617518751680633955697188856439766768202/1388375143573468172893714281810426647693758231003989900687 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7085) (33142888753707008431462278963782559841489/124452765946757723550809063982800509089 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7085)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7085
#print axioms PerfectPower.MordellParityAtlas.Curve_m7085.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7085.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7085.no_half0
namespace Curve_m7099
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7099)
private def branch_coefficients : List ℤ := [-7099, 0, 0, 1]
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
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 37 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7099) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7099)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7099) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7099)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(928456106829181905791227111/47606264277422820179924025 : ℚ))*X^3-C (-56792)*X-C (4*(928456106829181905791227111/47606264277422820179924025 : ℚ)*(-7099))
private def half0_coefficients : List ℤ := [2844532198866141392029366291490381391569092513522521759933659963906908251278117931804420746282252148281812500, 6127445719713448321653278324064419744906842120778902508474247469347632510427375000, 0, -3713824427316727623164908444, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (47606264277422820179924025) := by
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
  rational_root_free half0_source half0_coefficients (47606264277422820179924025) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7099)).Nonsingular (928456106829181905791227111/47606264277422820179924025 : ℚ) (-5867451917702174335904806012358251030766/328470336029793889072825402395080473875 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7099)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7099)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7099) (928456106829181905791227111/47606264277422820179924025 : ℚ) (-5867451917702174335904806012358251030766/328470336029793889072825402395080473875 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7099) (928456106829181905791227111/47606264277422820179924025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7099)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7099
#print axioms PerfectPower.MordellParityAtlas.Curve_m7099.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7099.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7099.no_half0
namespace Curve_m7122
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7122)
private def branch_coefficients : List ℤ := [-7122, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7122) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7122)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7122) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7122)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(188116439149889251256581755762691/1157470009995179026341619400025 : ℚ))*X^3-C (-56976)*X-C (4*(188116439149889251256581755762691/1157470009995179026341619400025 : ℚ)*(-7122))
private def half0_coefficients : List ℤ := [8310323917375544727578476419391827420045958821300519985617487126414866030200944808751139512053956934147218573030285308831375000, 88352979196613048565565706478915957958274307183716217296526124683547631121661776752502890250000, 0, -752465756599557005026327023050764, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1157470009995179026341619400025) := by
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
  rational_root_free half0_source half0_coefficients (1157470009995179026341619400025) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7122)).Nonsingular (188116439149889251256581755762691/1157470009995179026341619400025 : ℚ) (-2577980178720314530509979981105709600825946098261/1245273140764888924626733983146089789145500125 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7122)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7122)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7122) (188116439149889251256581755762691/1157470009995179026341619400025 : ℚ) (-2577980178720314530509979981105709600825946098261/1245273140764888924626733983146089789145500125 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7122) (188116439149889251256581755762691/1157470009995179026341619400025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7122)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7122
#print axioms PerfectPower.MordellParityAtlas.Curve_m7122.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7122.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7122.no_half0
namespace Curve_m7171
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7171)
private def branch_coefficients : List ℤ := [-7171, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7171) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7171)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7171) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7171)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(680201894041302101862874327464823/13865545592633251480272123102561 : ℚ))*X^3-C (-57368)*X-C (4*(680201894041302101862874327464823/13865545592633251480272123102561 : ℚ)*(-7171))
private def half0_coefficients : List ℤ := [52010190009175753984376132908344737498286143287440990331835977796450160716491337943993616198064152791281813283943695891800916278292, 152925742973652104172175016982324574811534264632280103877555446225527043536679432365547938599306008, 0, -2720807576165208407451497309859292, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (13865545592633251480272123102561) := by
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
  rational_root_free half0_source half0_coefficients (13865545592633251480272123102561) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7171)).Nonsingular (680201894041302101862874327464823/13865545592633251480272123102561 : ℚ) (17192918097387458618314607429159880965886502116754/51630394665206356961718717222225394984594414191 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7171)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7171)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7171) (680201894041302101862874327464823/13865545592633251480272123102561 : ℚ) (17192918097387458618314607429159880965886502116754/51630394665206356961718717222225394984594414191 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7171) (680201894041302101862874327464823/13865545592633251480272123102561 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7171)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7171
#print axioms PerfectPower.MordellParityAtlas.Curve_m7171.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7171.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7171.no_half0
namespace Curve_m7238
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7238)
private def branch_coefficients : List ℤ := [-7238, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7238) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7238)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7238) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7238)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(15850927/549081 : ℚ))*X^3-C (-57904)*X-C (4*(15850927/549081 : ℚ)*(-7238))
private def half0_coefficients : List ℤ := [75970062526943405756643972264, 9585567144046957727664, 0, -63403708, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (549081) := by
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
  rational_root_free half0_source half0_coefficients (549081) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7238)).Nonsingular (15850927/549081 : ℚ) (52767219205/406869021 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7238)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7238)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7238) (15850927/549081 : ℚ) (52767219205/406869021 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7238) (15850927/549081 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7238)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7238
#print axioms PerfectPower.MordellParityAtlas.Curve_m7238.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7238.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7238.no_half0
namespace Curve_m7266
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7266)
private def branch_coefficients : List ℤ := [-7266, 0, 0, 1]
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
  rational_root_free branch_source branch_coefficients (1) branch_monic branch_scale 31 (by decide +kernel) (by decide +kernel) x
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7266) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7266)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7266) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7266)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(536371175303023048625426669209633/27491382634626060483336857169156 : ℚ))*X^3-C (-58128)*X-C (4*(536371175303023048625426669209633/27491382634626060483336857169156 : ℚ)*(-7266))
private def half0_coefficients : List ℤ := [323899712991477231863870335195535747029960766894098461129299718458656082974277952026684801573348494635450620293307081406596481556992, 1207744666027177901696688767907071098665045486849271071488837219965197461841341007090602140115125248, 0, -2145484701212092194501706676838532, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (27491382634626060483336857169156) := by
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
  rational_root_free half0_source half0_coefficients (27491382634626060483336857169156) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7266)).Nonsingular (536371175303023048625426669209633/27491382634626060483336857169156 : ℚ) (-1828306832358750137287729617262300938786623933809/144143437166019812914272127489299868885708392696 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7266)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7266)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7266) (536371175303023048625426669209633/27491382634626060483336857169156 : ℚ) (-1828306832358750137287729617262300938786623933809/144143437166019812914272127489299868885708392696 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7266) (536371175303023048625426669209633/27491382634626060483336857169156 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7266)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7266
#print axioms PerfectPower.MordellParityAtlas.Curve_m7266.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7266.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7266.no_half0
namespace Curve_m7365
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7365)
private def branch_coefficients : List ℤ := [-7365, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7365) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7365)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7365) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7365)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(49767793853829496168364984255047234929742727976545161/26946190756815843660002611805688344946164709009 : ℚ))*X^3-C (-58920)*X-C (4*(49767793853829496168364984255047234929742727976545161/26946190756815843660002611805688344946164709009 : ℚ)*(-7365))
private def half0_coefficients : List ℤ := [28686216490108422490883135732756860369270886724994823380488940546373276416153570347465460067697472168479552499434079784056887650312657857225257250223945158124221687047510630136469084905140721210740, 1152802415729388264773337575815778530935354611652578709729432287305890369702773017335417716408081406141725554759651295526407332652963393072992680, 0, -199071175415317984673459937020188939718970911906180644, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (26946190756815843660002611805688344946164709009) := by
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
  rational_root_free half0_source half0_coefficients (26946190756815843660002611805688344946164709009) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7365)).Nonsingular (49767793853829496168364984255047234929742727976545161/26946190756815843660002611805688344946164709009 : ℚ) (-11102546074544548368664684599551401577404717041573939878410384242505241628396986/4423296684551231744797679565522904616644413217494317748340084470846777 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7365)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7365)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7365) (49767793853829496168364984255047234929742727976545161/26946190756815843660002611805688344946164709009 : ℚ) (-11102546074544548368664684599551401577404717041573939878410384242505241628396986/4423296684551231744797679565522904616644413217494317748340084470846777 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7365) (49767793853829496168364984255047234929742727976545161/26946190756815843660002611805688344946164709009 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7365)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7365
#print axioms PerfectPower.MordellParityAtlas.Curve_m7365.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7365.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7365.no_half0
namespace Curve_m7409
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7409)
private def branch_coefficients : List ℤ := [-7409, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7409) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7409)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7409) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7409)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(7650453665857318761442727855713697937/384118365498331304034924621709236496 : ℚ))*X^3-C (-59272)*X-C (4*(7650453665857318761442727855713697937/384118365498331304034924621709236496 : ℚ)*(-7409))
private def half0_coefficients : List ℤ := [12849966394729467866147595923433104489027463001701460635697088484015765104427392139595593840539830006590803539407242859362812940882932629022008164352, 3359269124673402134378836759222945087453645579379197074253420111641056190004595917592981048254665655902691950592, 0, -30601814663429275045770911422854791748, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (384118365498331304034924621709236496) := by
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
  rational_root_free half0_source half0_coefficients (384118365498331304034924621709236496) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7409)).Nonsingular (7650453665857318761442727855713697937/384118365498331304034924621709236496 : ℚ) (5279028141592409788715136237064291399135098146560199623/238066127893900156427897500288548432812051712626987456 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7409)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7409)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7409) (7650453665857318761442727855713697937/384118365498331304034924621709236496 : ℚ) (5279028141592409788715136237064291399135098146560199623/238066127893900156427897500288548432812051712626987456 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7409) (7650453665857318761442727855713697937/384118365498331304034924621709236496 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7409)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7409
#print axioms PerfectPower.MordellParityAtlas.Curve_m7409.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7409.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7409.no_half0
namespace Curve_m7429
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7429)
private def branch_coefficients : List ℤ := [-7429, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7429) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7429)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7429) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7429)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(2707576823849667644447946904886561/3399523475099130482527006176400 : ℚ))*X^3-C (-59432)*X-C (4*(2707576823849667644447946904886561/3399523475099130482527006176400 : ℚ)*(-7429))
private def half0_coefficients : List ℤ := [3161005643259330139605852415962184103633630050841730357303784162467016701196803123358911353525353612987301959991365150962944000000, 2334933299336616090845186456424710439166111152991283537179271143806460783338466623855569408000000, 0, -10830307295398670577791787619546244, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (3399523475099130482527006176400) := by
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
  rational_root_free half0_source half0_coefficients (3399523475099130482527006176400) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7429)).Nonsingular (2707576823849667644447946904886561/3399523475099130482527006176400 : ℚ) (140886048680503639183106363522302465303716175451441/6267972274388635606722694799671923467395912000 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7429)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7429)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7429) (2707576823849667644447946904886561/3399523475099130482527006176400 : ℚ) (140886048680503639183106363522302465303716175451441/6267972274388635606722694799671923467395912000 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7429) (2707576823849667644447946904886561/3399523475099130482527006176400 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7429)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7429
#print axioms PerfectPower.MordellParityAtlas.Curve_m7429.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7429.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7429.no_half0
namespace Curve_m7437
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7437)
private def branch_coefficients : List ℤ := [-7437, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7437) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7437)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7437) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7437)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(6940201023740110925572981/320722466746260193409025 : ℚ))*X^3-C (-59496)*X-C (4*(6940201023740110925572981/320722466746260193409025 : ℚ)*(-7437))
private def half0_coefficients : List ℤ := [6811111241126951700411149264096245454677463611043028825322450088492502474212760735907863528378562500, 1962799411091527126787844104405030722386598175155047718462000287604124625000, 0, -27760804094960443702291924, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (320722466746260193409025) := by
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
  rational_root_free half0_source half0_coefficients (320722466746260193409025) half0_monic half0_scale 19 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7437)).Nonsingular (6940201023740110925572981/320722466746260193409025 : ℚ) (9430509240541699414671781537632909496/181632715228892746892223006986138625 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7437)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7437)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7437) (6940201023740110925572981/320722466746260193409025 : ℚ) (9430509240541699414671781537632909496/181632715228892746892223006986138625 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7437) (6940201023740110925572981/320722466746260193409025 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7437)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7437
#print axioms PerfectPower.MordellParityAtlas.Curve_m7437.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7437.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7437.no_half0
namespace Curve_m7456
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7456)
private def branch_coefficients : List ℤ := [-7456, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7456) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7456)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7456) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7456)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(49459727481257482889828105/209239782301010912355844 : ℚ))*X^3-C (-59648)*X-C (4*(49459727481257482889828105/209239782301010912355844 : ℚ)*(-7456))
private def half0_coefficients : List ℤ := [13512956797944882986039155401618743559262312606255280206997874019473154986567836121765706283087175680, 546422614360968753237138775021668027197488639676225191853172581009156882432, 0, -197838909925029931559312420, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (209239782301010912355844) := by
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
  rational_root_free half0_source half0_coefficients (209239782301010912355844) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7456)).Nonsingular (49459727481257482889828105/209239782301010912355844 : ℚ) (347740247511404020738828798013325173861/95711999538035022059375126079025672 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7456)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7456)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7456) (49459727481257482889828105/209239782301010912355844 : ℚ) (347740247511404020738828798013325173861/95711999538035022059375126079025672 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7456) (49459727481257482889828105/209239782301010912355844 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7456)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7456
#print axioms PerfectPower.MordellParityAtlas.Curve_m7456.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7456.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7456.no_half0
namespace Curve_m7465
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7465)
private def branch_coefficients : List ℤ := [-7465, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7465) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7465)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7465) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7465)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(12989854031445767596274451579140681/143257894738916637230366442115489 : ℚ))*X^3-C (-59720)*X-C (4*(12989854031445767596274451579140681/143257894738916637230366442115489 : ℚ)*(-7465))
private def half0_coefficients : List ℤ := [1140380462616354798467496082916752315001567401683303428246706955642364645469884845259906194653110817316394646213639085812721581119657540, 175580181248492556027431090884427321222931801477987073861025467480768042764438264857968724962801092680, 0, -51959416125783070385097806316562724, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (143257894738916637230366442115489) := by
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
  rational_root_free half0_source half0_coefficients (143257894738916637230366442115489) half0_monic half0_scale 23 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7465)).Nonsingular (12989854031445767596274451579140681/143257894738916637230366442115489 : ℚ) (-1473062281415469532721419665060676563043578079143284/1714659330117956270735732787967148538615318581263 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7465)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7465)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7465) (12989854031445767596274451579140681/143257894738916637230366442115489 : ℚ) (-1473062281415469532721419665060676563043578079143284/1714659330117956270735732787967148538615318581263 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7465) (12989854031445767596274451579140681/143257894738916637230366442115489 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7465)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7465
#print axioms PerfectPower.MordellParityAtlas.Curve_m7465.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7465.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7465.no_half0
namespace Curve_m7582
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7582)
private def branch_coefficients : List ℤ := [-7582, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7582) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7582)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7582) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7582)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(71890712807511456702538245161/703332871017309580578388900 : ℚ))*X^3-C (-60656)*X-C (4*(71890712807511456702538245161/703332871017309580578388900 : ℚ)*(-7582))
private def half0_coefficients : List ℤ := [758576363646470942264849770672464888271881469614491221855610844139599748610982758833491287272695135484788152000000, 21103598337592545324562633193652354331808993924279683715689353940506797935726064000000, 0, -287562851230045826810152980644, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (703332871017309580578388900) := by
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
  rational_root_free half0_source half0_coefficients (703332871017309580578388900) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7582)).Nonsingular (71890712807511456702538245161/703332871017309580578388900 : ℚ) (19207107911449401448129433080619422030949909/18652685712208619375716874468675464537000 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7582)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7582)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7582) (71890712807511456702538245161/703332871017309580578388900 : ℚ) (19207107911449401448129433080619422030949909/18652685712208619375716874468675464537000 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7582) (71890712807511456702538245161/703332871017309580578388900 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7582)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7582
#print axioms PerfectPower.MordellParityAtlas.Curve_m7582.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7582.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7582.no_half0
end PerfectPower.MordellParityAtlas
