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
namespace Curve_m7598
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7598)
private def branch_coefficients : List ℤ := [-7598, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7598) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7598)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7598) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7598)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1526044443813356943622615937725321/12386964819174266995125164294400 : ℚ))*X^3-C (-60784)*X-C (4*(1526044443813356943622615937725321/12386964819174266995125164294400 : ℚ)*(-7598))
private def half0_coefficients : List ℤ := [88149768268496523383224013493894344615566201780725047075464806017105266460391205558579688051467933143442319797391221994815488000000, 115527131107955715351988559550897139457100374941240448440104827882632320370784840329835053056000000, 0, -6104177775253427774490463750901284, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (12386964819174266995125164294400) := by
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
  rational_root_free half0_source half0_coefficients (12386964819174266995125164294400) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7598)).Nonsingular (1526044443813356943622615937725321/12386964819174266995125164294400 : ℚ) (59493101947863147705814329673623339108457746886619/43596071502450282394376910505104400897807872000 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7598)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7598)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7598) (1526044443813356943622615937725321/12386964819174266995125164294400 : ℚ) (59493101947863147705814329673623339108457746886619/43596071502450282394376910505104400897807872000 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7598) (1526044443813356943622615937725321/12386964819174266995125164294400 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7598)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7598
#print axioms PerfectPower.MordellParityAtlas.Curve_m7598.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7598.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7598.no_half0
namespace Curve_m7619
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7619)
private def branch_coefficients : List ℤ := [-7619, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7619) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7619)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7619) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7619)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(14057867442320105322500753111593/689932432624439531806533991044 : ℚ))*X^3-C (-60952)*X-C (4*(14057867442320105322500753111593/689932432624439531806533991044 : ℚ)*(-7619))
private def half0_coefficients : List ℤ := [140700970003674292277414766788419723154451249028957086323427075476254796653218664240130949379228857886145905481891852689005312, 20017398880872226439823170095009915196138996397792885488749664218657756842595975153159237191168, 0, -56231469769280421290003012446372, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (689932432624439531806533991044) := by
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
  rational_root_free half0_source half0_coefficients (689932432624439531806533991044) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7619)).Nonsingular (14057867442320105322500753111593/689932432624439531806533991044 : ℚ) (-16613007935634799055077132219869477617600052469/573072860086266440540697186031106900108417928 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7619)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7619)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7619) (14057867442320105322500753111593/689932432624439531806533991044 : ℚ) (-16613007935634799055077132219869477617600052469/573072860086266440540697186031106900108417928 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7619) (14057867442320105322500753111593/689932432624439531806533991044 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7619)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7619
#print axioms PerfectPower.MordellParityAtlas.Curve_m7619.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7619.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7619.no_half0
namespace Curve_m7625
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7625)
private def branch_coefficients : List ℤ := [-7625, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7625) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7625)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7625) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7625)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(405/1 : ℚ))*X^3-C (-61000)*X-C (4*(405/1 : ℚ)*(-7625))
private def half0_coefficients : List ℤ := [12352500, 61000, 0, -1620, 1]
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
  rational_root_free half0_source half0_coefficients (1) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7625)).Nonsingular (405/1 : ℚ) (8150/1 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7625)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7625)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7625) (405/1 : ℚ) (8150/1 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7625) (405/1 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7625)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7625
#print axioms PerfectPower.MordellParityAtlas.Curve_m7625.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7625.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7625.no_half0
namespace Curve_m7654
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7654)
private def branch_coefficients : List ℤ := [-7654, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7654) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7654)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7654) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7654)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(23888558645708376352553554950095467056599/1212051647151472090003995162164867640625 : ℚ))*X^3-C (-61232)*X-C (4*(23888558645708376352553554950095467056599/1212051647151472090003995162164867640625 : ℚ)*(-7654))
private def half0_coefficients : List ℤ := [1302272213660434092592034812763609871431782463790235984952250229364580441327017027606500659681925290408214589824719100073315462167796907930386653796295166015625000, 109028948374362443934376975597175038217040511362311020202484557533069692126470573396982211669118106638270153991699218750000, 0, -95554234582833505410214219800381868226396, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1212051647151472090003995162164867640625) := by
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
  rational_root_free half0_source half0_coefficients (1212051647151472090003995162164867640625) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7654)).Nonsingular (23888558645708376352553554950095467056599/1212051647151472090003995162164867640625 : ℚ) (-60857124572026930696256963044438433195160920535828101720257/42197011008111972127361884651003183728132992104205728515625 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7654)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7654)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7654) (23888558645708376352553554950095467056599/1212051647151472090003995162164867640625 : ℚ) (-60857124572026930696256963044438433195160920535828101720257/42197011008111972127361884651003183728132992104205728515625 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7654) (23888558645708376352553554950095467056599/1212051647151472090003995162164867640625 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7654)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7654
#print axioms PerfectPower.MordellParityAtlas.Curve_m7654.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7654.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7654.no_half0
namespace Curve_m7689
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7689)
private def branch_coefficients : List ℤ := [-7689, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7689) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7689)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7689) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7689)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(114620691272813547824059580037966553/1444465776937225169844294402326544 : ℚ))*X^3-C (-61512)*X-C (4*(114620691272813547824059580037966553/1444465776937225169844294402326544 : ℚ)*(-7689))
private def half0_coefficients : List ℤ := [10624650331420547259435265061299192092305424318843252342170095219592819338038895944097106452075070870216505896739422581692158587641098944512, 185387999556421594386287300188554516527041307705505013588432759843330418976893958606522251614957439582208, 0, -458482765091254191296238320151866212, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (1444465776937225169844294402326544) := by
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
  rational_root_free half0_source half0_coefficients (1444465776937225169844294402326544) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7689)).Nonsingular (114620691272813547824059580037966553/1444465776937225169844294402326544 : ℚ) (-38505869794673760865471994717160142927290030489777949/54898551426242494429195281806471067050720556843072 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7689)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7689)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7689) (114620691272813547824059580037966553/1444465776937225169844294402326544 : ℚ) (-38505869794673760865471994717160142927290030489777949/54898551426242494429195281806471067050720556843072 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7689) (114620691272813547824059580037966553/1444465776937225169844294402326544 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7689)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7689
#print axioms PerfectPower.MordellParityAtlas.Curve_m7689.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7689.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7689.no_half0
namespace Curve_m7717
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7717)
private def branch_coefficients : List ℤ := [-7717, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7717) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7717)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7717) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7717)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(114435482672761036043706741996617/348583221834496618153837160704 : ℚ))*X^3-C (-61736)*X-C (4*(114435482672761036043706741996617/348583221834496618153837160704 : ℚ)*(-7717))
private def half0_coefficients : List ℤ := [149619650586422591775805646084968739934834167713953553369455320191303560874108151909948120293683926766812113788912477283549184, 2614917105986680268971130518087570366042578381360358301553137306818398436189761743674570440704, 0, -457741930691044144174826967986468, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (348583221834496618153837160704) := by
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
  rational_root_free half0_source half0_coefficients (348583221834496618153837160704) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7717)).Nonsingular (114435482672761036043706741996617/348583221834496618153837160704 : ℚ) (1224034588987855940304333086679437994023903252795/205806799702350946424071145492634365727035392 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7717)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7717)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7717) (114435482672761036043706741996617/348583221834496618153837160704 : ℚ) (1224034588987855940304333086679437994023903252795/205806799702350946424071145492634365727035392 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7717) (114435482672761036043706741996617/348583221834496618153837160704 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7717)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7717
#print axioms PerfectPower.MordellParityAtlas.Curve_m7717.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7717.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7717.no_half0
namespace Curve_m7738
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7738)
private def branch_coefficients : List ℤ := [-7738, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7738) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7738)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7738) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7738)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(329/16 : ℚ))*X^3-C (-61904)*X-C (4*(329/16 : ℚ)*(-7738))
private def half0_coefficients : List ℤ := [41710419968, 253558784, 0, -1316, 1]
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
  rational_root_free half0_source half0_coefficients (16) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7738)).Nonsingular (329/16 : ℚ) (1979/64 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7738)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7738)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7738) (329/16 : ℚ) (1979/64 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7738) (329/16 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
private noncomputable def half1_source : Polynomial ℚ := X^4-C (4*(6435221886583446467/40794307403664049 : ℚ))*X^3-C (-61904)*X-C (4*(6435221886583446467/40794307403664049 : ℚ)*(-7738))
private def half1_coefficients : List ℤ := [13522311471981044510097884278531782508503887166958152174764808372242089016, 4202593697716377479237501795872665071971647741222911696, 0, -25740887546333785868, 1]
private noncomputable def half1_scaled := polynomial half1_coefficients
private theorem half1_degree : half1_source.natDegree=4 := by
  unfold half1_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half1_monic : half1_scaled.Monic := by
  simp [half1_scaled,half1_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half1_scale : half1_scaled.map (Int.castRingHom ℚ) = half1_source.scaleRoots (40794307403664049) := by
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
  rational_root_free half1_source half1_coefficients (40794307403664049) half1_monic half1_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve1 : (completed (0:ℚ) 0 (-7738)).Nonsingular (6435221886583446467/40794307403664049 : ℚ) (16308605215272928195076831551/8239471317722601786472343 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P1 : (completed (0:ℚ) 0 (-7738)).Point := WeierstrassCurve.Affine.Point.some on_curve1
theorem no_half1 (Q : (completed (0:ℚ) 0 (-7738)).Point) : (2:ℤ) • Q ≠ P1 := by
  apply no_half_of_quartic_root_free 0 0 (-7738) (6435221886583446467/40794307403664049 : ℚ) (16308605215272928195076831551/8239471317722601786472343 : ℚ) on_curve1
  intro x
  have he : half1_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7738) (6435221886583446467/40794307403664049 : ℚ) x := by
    simp only [half1_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half1_root_free x
private noncomputable def half2_source : Polynomial ℚ := X^4-C (4*(334306448234862400619/14282875678510101601 : ℚ))*X^3-C (-61904)*X-C (4*(334306448234862400619/14282875678510101601 : ℚ)*(-7738))
private def half2_coefficients : List ℤ := [30149522497774920273288094650900799940144064468007899240798073562205167905914781688, 180370571115001572489821854895488256020363327766120706035121104, 0, -1337225792939449602476, 1]
private noncomputable def half2_scaled := polynomial half2_coefficients
private theorem half2_degree : half2_source.natDegree=4 := by
  unfold half2_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half2_monic : half2_scaled.Monic := by
  simp [half2_scaled,half2_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half2_scale : half2_scaled.map (Int.castRingHom ℚ) = half2_source.scaleRoots (14282875678510101601) := by
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
  rational_root_free half2_source half2_coefficients (14282875678510101601) half2_monic half2_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve2 : (completed (0:ℚ) 0 (-7738)).Nonsingular (334306448234862400619/14282875678510101601 : ℚ) (-3849160318252558599063248338789/53978832124939453191019887599 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P2 : (completed (0:ℚ) 0 (-7738)).Point := WeierstrassCurve.Affine.Point.some on_curve2
theorem no_half2 (Q : (completed (0:ℚ) 0 (-7738)).Point) : (2:ℤ) • Q ≠ P2 := by
  apply no_half_of_quartic_root_free 0 0 (-7738) (334306448234862400619/14282875678510101601 : ℚ) (-3849160318252558599063248338789/53978832124939453191019887599 : ℚ) on_curve2
  intro x
  have he : half2_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7738) (334306448234862400619/14282875678510101601 : ℚ) x := by
    simp only [half2_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half2_root_free x
theorem sum_checked : P0+P1=P2 := by
  unfold P0 P1 P2
  rw [WeierstrassCurve.Affine.Point.add_some (by
    norm_num [completed,WeierstrassCurve.Affine.negY] : ¬((329/16 : ℚ)=(6435221886583446467/40794307403664049 : ℚ) ∧ (1979/64 : ℚ)=(completed (0:ℚ) 0 (-7738)).negY (6435221886583446467/40794307403664049 : ℚ) (16308605215272928195076831551/8239471317722601786472343 : ℚ)))]
  rw [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne (by norm_num : (329/16 : ℚ) ≠ (6435221886583446467/40794307403664049 : ℚ))]
  norm_num [completed,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY]
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7738)).Point) (m n : ℤ)
    (h : (2:ℤ) • Q=m • P0+n • P1) : ∃ a b : ℤ, Q=a • P0+b • P1 :=
  pair_two_saturated P0 P1 double_injective no_half0 no_half1 (by rw [sum_checked]; exact no_half2) Q m n h
end Curve_m7738
#print axioms PerfectPower.MordellParityAtlas.Curve_m7738.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7738.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7738.no_half0
#print axioms PerfectPower.MordellParityAtlas.Curve_m7738.no_half1
#print axioms PerfectPower.MordellParityAtlas.Curve_m7738.no_half2
namespace Curve_m7762
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7762)
private def branch_coefficients : List ℤ := [-7762, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7762) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7762)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7762) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7762)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(11987/289 : ℚ))*X^3-C (-62096)*X-C (4*(11987/289 : ℚ)*(-7762))
private def half0_coefficients : List ℤ := [8983336405593944, 1498846484624, 0, -47948, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (289) := by
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
  rational_root_free half0_source half0_coefficients (289) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7762)).Nonsingular (11987/289 : ℚ) (1238965/4913 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7762)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7762)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7762) (11987/289 : ℚ) (1238965/4913 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7762) (11987/289 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7762)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7762
#print axioms PerfectPower.MordellParityAtlas.Curve_m7762.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7762.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7762.no_half0
namespace Curve_m777
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-777)
private def branch_coefficients : List ℤ := [-777, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-777) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-777)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-777) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-777)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(793/81 : ℚ))*X^3-C (-6216)*X-C (4*(793/81 : ℚ)*(-777))
private def half0_coefficients : List ℤ := [1309812872004, 3303437256, 0, -3172, 1]
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
private theorem on_curve0 : (completed (0:ℚ) 0 (-777)).Nonsingular (793/81 : ℚ) (9260/729 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-777)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-777)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-777) (793/81 : ℚ) (9260/729 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-777) (793/81 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-777)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m777
#print axioms PerfectPower.MordellParityAtlas.Curve_m777.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m777.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m777.no_half0
namespace Curve_m7878
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7878)
private def branch_coefficients : List ℤ := [-7878, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7878) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7878)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7878) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7878)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(1769729167138411696755007160344862191/5230071391924711010645360435070225 : ℚ))*X^3-C (-63024)*X-C (4*(1769729167138411696755007160344862191/5230071391924711010645360435070225 : ℚ)*(-7878))
private def half0_coefficients : List ℤ := [7978213019488781128191328485260112213328514936889919599495691543515766607603284914182133072746324090323146999082100337245878702932970502625000, 9016309577345401546017384745941297989914945891808041322010552171512213016299278167060148254354571782750000, 0, -7078916668553646787020028641379448764, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (5230071391924711010645360435070225) := by
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
  rational_root_free half0_source half0_coefficients (5230071391924711010645360435070225) half0_monic half0_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7878)).Nonsingular (1769729167138411696755007160344862191/5230071391924711010645360435070225 : ℚ) (2354052011735846667073718530484624101642527720933954989/378234749075890101194933026207103409709122088421625 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7878)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7878)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7878) (1769729167138411696755007160344862191/5230071391924711010645360435070225 : ℚ) (2354052011735846667073718530484624101642527720933954989/378234749075890101194933026207103409709122088421625 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7878) (1769729167138411696755007160344862191/5230071391924711010645360435070225 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7878)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7878
#print axioms PerfectPower.MordellParityAtlas.Curve_m7878.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7878.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7878.no_half0
namespace Curve_m7897
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7897)
private def branch_coefficients : List ℤ := [-7897, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7897) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7897)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7897) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7897)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(103332283330934183956227922122503273782589/3840918942394395059167130633268197025625 : ℚ))*X^3-C (-63176)*X-C (4*(103332283330934183956227922122503273782589/3840918942394395059167130633268197025625 : ℚ)*(-7897))
private def half0_coefficients : List ℤ := [184953937530585584230264142120423782657685659501272629638444552786526646002354049101285968933614810297340341514472636257285471089169499969802677232684145012695312500, 3579790004992885760818296795618638687091729633335087548234989852445692837623797979929977475855318771198187547047533203125000, 0, -413329133323736735824911688490013095130356, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (3840918942394395059167130633268197025625) := by
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
  rational_root_free half0_source half0_coefficients (3840918942394395059167130633268197025625) half0_monic half0_scale 17 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7897)).Nonsingular (103332283330934183956227922122503273782589/3840918942394395059167130633268197025625 : ℚ) (-25609822041771049814892887995285392022618610659580783294142062/238041519067181664508324176817815757026284901472492727171875 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7897)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7897)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7897) (103332283330934183956227922122503273782589/3840918942394395059167130633268197025625 : ℚ) (-25609822041771049814892887995285392022618610659580783294142062/238041519067181664508324176817815757026284901472492727171875 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7897) (103332283330934183956227922122503273782589/3840918942394395059167130633268197025625 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7897)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7897
#print axioms PerfectPower.MordellParityAtlas.Curve_m7897.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7897.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7897.no_half0
namespace Curve_m7925
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7925)
private def branch_coefficients : List ℤ := [-7925, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7925) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7925)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7925) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7925)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(58801/2601 : ℚ))*X^3-C (-63400)*X-C (4*(58801/2601 : ℚ)*(-7925))
private def half0_coefficients : List ℤ := [32799334411875251700, 1115604646583400, 0, -235204, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (2601) := by
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
  rational_root_free half0_source half0_coefficients (2601) half0_monic half0_scale 7 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7925)).Nonsingular (58801/2601 : ℚ) (7991074/132651 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7925)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7925)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7925) (58801/2601 : ℚ) (7991074/132651 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7925) (58801/2601 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7925)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7925
#print axioms PerfectPower.MordellParityAtlas.Curve_m7925.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7925.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7925.no_half0
namespace Curve_m7941
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7941)
private def branch_coefficients : List ℤ := [-7941, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7941) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7941)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7941) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7941)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(16337330731710259711092265/88563948319863319331889 : ℚ))*X^3-C (-63528)*X-C (4*(16337330731710259711092265/88563948319863319331889 : ℚ)*(-7941))
private def half0_coefficients : List ℤ := [360484999694856815033058515670026876642141799507795195713206782347375528783208622396096271706394740, 44130219999178500609314892280590400788548307163842603936688834705131185832, 0, -65349322926841038844369060, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (88563948319863319331889) := by
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
  rational_root_free half0_source half0_coefficients (88563948319863319331889) half0_monic half0_scale 29 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7941)).Nonsingular (16337330731710259711092265/88563948319863319331889 : ℚ) (-65992833907042591969990895982751255414/26356361446122817538643294458309463 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7941)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7941)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7941) (16337330731710259711092265/88563948319863319331889 : ℚ) (-65992833907042591969990895982751255414/26356361446122817538643294458309463 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7941) (16337330731710259711092265/88563948319863319331889 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7941)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7941
#print axioms PerfectPower.MordellParityAtlas.Curve_m7941.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7941.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7941.no_half0
namespace Curve_m7954
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7954)
private def branch_coefficients : List ℤ := [-7954, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7954) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7954)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7954) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7954)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(185/4 : ℚ))*X^3-C (-63632)*X-C (4*(185/4 : ℚ)*(-7954))
private def half0_coefficients : List ℤ := [376701440, 4072448, 0, -740, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (4) := by
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
  rational_root_free half0_source half0_coefficients (4) half0_monic half0_scale 19 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7954)).Nonsingular (185/4 : ℚ) (2413/8 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7954)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7954)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7954) (185/4 : ℚ) (2413/8 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7954) (185/4 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
private noncomputable def half1_source : Polynomial ℚ := X^4-C (4*(1115/49 : ℚ))*X^3-C (-63632)*X-C (4*(1115/49 : ℚ)*(-7954))
private def half1_coefficients : List ℤ := [4173579451160, 7486241168, 0, -4460, 1]
private noncomputable def half1_scaled := polynomial half1_coefficients
private theorem half1_degree : half1_source.natDegree=4 := by
  unfold half1_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half1_monic : half1_scaled.Monic := by
  simp [half1_scaled,half1_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half1_scale : half1_scaled.map (Int.castRingHom ℚ) = half1_source.scaleRoots (49) := by
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
  rational_root_free half1_source half1_coefficients (49) half1_monic half1_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve1 : (completed (0:ℚ) 0 (-7954)).Nonsingular (1115/49 : ℚ) (21223/343 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P1 : (completed (0:ℚ) 0 (-7954)).Point := WeierstrassCurve.Affine.Point.some on_curve1
theorem no_half1 (Q : (completed (0:ℚ) 0 (-7954)).Point) : (2:ℤ) • Q ≠ P1 := by
  apply no_half_of_quartic_root_free 0 0 (-7954) (1115/49 : ℚ) (21223/343 : ℚ) on_curve1
  intro x
  have he : half1_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7954) (1115/49 : ℚ) x := by
    simp only [half1_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half1_root_free x
private noncomputable def half2_source : Polynomial ℚ := X^4-C (4*(29793475/848241 : ℚ))*X^3-C (-63632)*X-C (4*(29793475/848241 : ℚ)*(-7954))
private def half2_coefficients : List ℤ := [578528182149244136300330112600, 38835898272977162704272, 0, -119173900, 1]
private noncomputable def half2_scaled := polynomial half2_coefficients
private theorem half2_degree : half2_source.natDegree=4 := by
  unfold half2_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half2_monic : half2_scaled.Monic := by
  simp [half2_scaled,half2_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half2_scale : half2_scaled.map (Int.castRingHom ℚ) = half2_source.scaleRoots (848241) := by
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
  rational_root_free half2_source half2_coefficients (848241) half2_monic half2_scale 11 (by decide +kernel) (by decide +kernel) x
private theorem on_curve2 : (completed (0:ℚ) 0 (-7954)).Nonsingular (29793475/848241 : ℚ) (-146941230221/781229961 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P2 : (completed (0:ℚ) 0 (-7954)).Point := WeierstrassCurve.Affine.Point.some on_curve2
theorem no_half2 (Q : (completed (0:ℚ) 0 (-7954)).Point) : (2:ℤ) • Q ≠ P2 := by
  apply no_half_of_quartic_root_free 0 0 (-7954) (29793475/848241 : ℚ) (-146941230221/781229961 : ℚ) on_curve2
  intro x
  have he : half2_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7954) (29793475/848241 : ℚ) x := by
    simp only [half2_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half2_root_free x
theorem sum_checked : P0+P1=P2 := by
  unfold P0 P1 P2
  rw [WeierstrassCurve.Affine.Point.add_some (by
    norm_num [completed,WeierstrassCurve.Affine.negY] : ¬((185/4 : ℚ)=(1115/49 : ℚ) ∧ (2413/8 : ℚ)=(completed (0:ℚ) 0 (-7954)).negY (1115/49 : ℚ) (21223/343 : ℚ)))]
  rw [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne (by norm_num : (185/4 : ℚ) ≠ (1115/49 : ℚ))]
  norm_num [completed,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY]
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7954)).Point) (m n : ℤ)
    (h : (2:ℤ) • Q=m • P0+n • P1) : ∃ a b : ℤ, Q=a • P0+b • P1 :=
  pair_two_saturated P0 P1 double_injective no_half0 no_half1 (by rw [sum_checked]; exact no_half2) Q m n h
end Curve_m7954
#print axioms PerfectPower.MordellParityAtlas.Curve_m7954.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7954.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7954.no_half0
#print axioms PerfectPower.MordellParityAtlas.Curve_m7954.no_half1
#print axioms PerfectPower.MordellParityAtlas.Curve_m7954.no_half2
namespace Curve_m7969
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7969)
private def branch_coefficients : List ℤ := [-7969, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7969) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7969)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7969) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7969)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(2291157583928969147760088047142360067139443658017/92538079938280437635007977166081647057080271716 : ℚ))*X^3-C (-63752)*X-C (4*(2291157583928969147760088047142360067139443658017/92538079938280437635007977166081647057080271716 : ℚ)*(-7969))
private def half0_coefficients : List ℤ := [57873564406006832053132406837863811069716260487036633017990811221697763519010968235357481073865741624723622657384874719322914168614804770190617077911440883827446324988592264649601863444089112832, 50519060593608683022210047455618067315292139612075227575486444525458624173727694249445671544226474942716205288308190793303442436926036450571899392, 0, -9164630335715876591040352188569440268557774632068, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (92538079938280437635007977166081647057080271716) := by
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
  rational_root_free half0_source half0_coefficients (92538079938280437635007977166081647057080271716) half0_monic half0_scale 5 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7969)).Nonsingular (2291157583928969147760088047142360067139443658017/92538079938280437635007977166081647057080271716 : ℚ) (2390047508063301126770382344695936751703026382114575661401665649622076433/28150150832075955331459903893418198214687126982200365858063780675690264 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7969)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7969)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7969) (2291157583928969147760088047142360067139443658017/92538079938280437635007977166081647057080271716 : ℚ) (2390047508063301126770382344695936751703026382114575661401665649622076433/28150150832075955331459903893418198214687126982200365858063780675690264 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7969) (2291157583928969147760088047142360067139443658017/92538079938280437635007977166081647057080271716 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7969)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7969
#print axioms PerfectPower.MordellParityAtlas.Curve_m7969.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7969.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7969.no_half0
namespace Curve_m7985
private noncomputable def branch_source : Polynomial ℚ := X^3+C (-7985)
private def branch_coefficients : List ℤ := [-7985, 0, 0, 1]
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
theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 (-7985) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 (-7985)).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 (-7985) branch_free
private theorem smooth : (completed (0:ℚ) 0 (-7985)).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
private noncomputable def half0_source : Polynomial ℚ := X^4-C (4*(9009/289 : ℚ))*X^3-C (-63880)*X-C (4*(9009/289 : ℚ)*(-7985))
private def half0_coefficients : List ℤ := [6945524170324740, 1541907907720, 0, -36036, 1]
private noncomputable def half0_scaled := polynomial half0_coefficients
private theorem half0_degree : half0_source.natDegree=4 := by
  unfold half0_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem half0_monic : half0_scaled.Monic := by
  simp [half0_scaled,half0_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem half0_scale : half0_scaled.map (Int.castRingHom ℚ) = half0_source.scaleRoots (289) := by
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
  rational_root_free half0_source half0_coefficients (289) half0_monic half0_scale 29 (by decide +kernel) (by decide +kernel) x
private theorem on_curve0 : (completed (0:ℚ) 0 (-7985)).Nonsingular (9009/289 : ℚ) (733792/4913 : ℚ) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P0 : (completed (0:ℚ) 0 (-7985)).Point := WeierstrassCurve.Affine.Point.some on_curve0
theorem no_half0 (Q : (completed (0:ℚ) 0 (-7985)).Point) : (2:ℤ) • Q ≠ P0 := by
  apply no_half_of_quartic_root_free 0 0 (-7985) (9009/289 : ℚ) (733792/4913 : ℚ) on_curve0
  intro x
  have he : half0_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 (-7985) (9009/289 : ℚ) x := by
    simp only [half0_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half0_root_free x
theorem two_saturated (Q : (completed (0:ℚ) 0 (-7985)).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
end Curve_m7985
#print axioms PerfectPower.MordellParityAtlas.Curve_m7985.double_injective
#print axioms PerfectPower.MordellParityAtlas.Curve_m7985.two_saturated
#print axioms PerfectPower.MordellParityAtlas.Curve_m7985.no_half0
end PerfectPower.MordellParityAtlas
