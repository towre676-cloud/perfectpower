import PerfectPower.EllipticQuarticLifts
import Mathlib.Tactic.Linter.Lint
namespace PerfectPower.HalvesPacket_02eb92c8942723eb
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-1) * X + X^3
private def coefficients : List ℤ := [0,-1,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-1) * X + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1) * X + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-1),(0),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(0),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_02eb92c8942723eb
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.native_roots_checked
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.source_complete

namespace PerfectPower.HalvesPacket_02eb92c8942723eb
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0)
      smooth_checked ([(-1),(0),(1)] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-1) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_02eb92c8942723eb
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.smooth_checked
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_02eb92c8942723eb
open PerfectPower
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := 0
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point :=
  EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0) smooth_checked ([(-1),(0),(1)] : List ℚ)
 theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_02eb92c8942723eb
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.actual_halves_complete

namespace PerfectPower.HalvesPacket_02eb92c8942723eb
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([none,some ((-1),(0)),some ((0),(0)),some ((1),(0))] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(-1),(0)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (-1) (0) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([none,some ((-1),(0)),some ((0),(0)),some ((1),(0))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([none,some ((-1),(0)),some ((0),(0)),some ((1),(0))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    none := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_02eb92c8942723eb
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.original_target_checked
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.original_halves_complete
#print axioms PerfectPower.HalvesPacket_02eb92c8942723eb.original_json_list_checked
namespace PerfectPower.HalvesPacket_e4d4f24b1f7c7496
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-2) + X^3
private def coefficients : List ℤ := [-2,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-2) + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-2) + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_e4d4f24b1f7c7496
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.native_roots_checked
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.source_complete

namespace PerfectPower.HalvesPacket_e4d4f24b1f7c7496
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked ([] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_e4d4f24b1f7c7496
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.smooth_checked
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (24) + C (16) * X + C (-12) * X^3 + X^4
private def coefficients : List ℤ := [24,16,0,-12,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 4 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (24) + C (16) * X + C (-12) * X^3 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (24) + C (16) * X + C (-12) * X^3 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 4 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496
#print axioms PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496.native_roots_checked
#print axioms PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496.source_complete
namespace PerfectPower.HalvesPacket_e4d4f24b1f7c7496
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (3) (5) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
theorem quartic_root_free (x : ℚ) : EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-2) (3) x ≠ 0 := by
  have hc := PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496.source_complete x
  have he : PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-2) (3) x := by
    norm_num [PerfectPower.RationalPacket_c09040e3a484be22_e4d4f24b1f7c7496.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := []
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := by
  have hn := EllipticPointDivision.no_half_of_quartic_root_free ((0) : ℚ) (0) (-2) (3) (5) target_on_curve quartic_root_free Q
  simpa [target, halves] using hn
end PerfectPower.HalvesPacket_e4d4f24b1f7c7496
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.quartic_root_free

namespace PerfectPower.HalvesPacket_e4d4f24b1f7c7496
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(0),(-2)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (0) (-2) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((3),(5)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_e4d4f24b1f7c7496
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.original_target_checked
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.original_halves_complete
#print axioms PerfectPower.HalvesPacket_e4d4f24b1f7c7496.original_json_list_checked
namespace PerfectPower.HalvesPacket_3ad187ec1fe02953
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-1) * X + X^3
private def coefficients : List ℤ := [0,-1,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-1) * X + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1) * X + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-1),(0),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(0),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.native_roots_checked
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.source_complete

namespace PerfectPower.HalvesPacket_3ad187ec1fe02953
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0)
      smooth_checked ([(-1),(0),(1)] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-1) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.smooth_checked
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (1) + C (2) * X^2 + X^4
private def coefficients : List ℤ := [1,0,2,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 4 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (1) + C (2) * X^2 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1) + C (2) * X^2 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 4 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.native_roots_checked
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.source_complete
namespace PerfectPower.HalvesPacket_3ad187ec1fe02953
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Nonsingular (0) (0) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
theorem quartic_root_free (x : ℚ) : EllipticDivision.halvingPolynomial ((0) : ℚ) (-1) (0) (0) x ≠ 0 := by
  have hc := PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.source_complete x
  have he : PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (-1) (0) (0) x := by
    norm_num [PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := []
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := by
  have hn := EllipticPointDivision.no_half_of_quartic_root_free ((0) : ℚ) (-1) (0) (0) (0) target_on_curve quartic_root_free Q
  simpa [target, halves] using hn
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.quartic_root_free

namespace PerfectPower.HalvesPacket_3ad187ec1fe02953
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(-1),(0)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (-1) (0) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((0),(0)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.original_target_checked
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.original_halves_complete
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.original_json_list_checked
namespace PerfectPower.HalvesPacket_ea1d3ebedd649b4b
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := X + X^3
private def coefficients : List ℤ := [0,1,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (X + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (X + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(0)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(0)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_ea1d3ebedd649b4b
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.native_roots_checked
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.source_complete

namespace PerfectPower.HalvesPacket_ea1d3ebedd649b4b
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (1) (0)
      smooth_checked ([(0)] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (1) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_ea1d3ebedd649b4b
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.smooth_checked
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (1) + C (-2) * X^2 + X^4
private def coefficients : List ℤ := [1,0,-2,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 4 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (1) + C (-2) * X^2 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1) + C (-2) * X^2 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 4 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-1),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b
#print axioms PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b.native_roots_checked
#print axioms PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b.source_complete
namespace PerfectPower.HalvesPacket_ea1d3ebedd649b4b
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Nonsingular (0) (0) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem quartic_complete (x : ℚ) :
    EllipticDivision.halvingPolynomial ((0) : ℚ) (1) (0) (0) x = 0 ↔ x ∈ ([(-1),(1)] : List ℚ) := by
  have hc := PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b.source_complete x
  have he : PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (1) (0) (0) x := by
    norm_num [PerfectPower.RationalPacket_cf2eed598d0899b5_ea1d3ebedd649b4b.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point :=
  EllipticQuarticLifts.fibreList ((0) : ℚ) (1) (0) smooth_checked target ([(-1),(1)] : List ℚ)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticQuarticLifts.fibre_complete ((0) : ℚ) (1) (0) (0) (0) smooth_checked target_on_curve ([(-1),(1)] : List ℚ) quartic_complete Q
end PerfectPower.HalvesPacket_ea1d3ebedd649b4b
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.actual_halves_complete

namespace PerfectPower.HalvesPacket_ea1d3ebedd649b4b
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine
private theorem lift_sqrt_0 : Rat.sqrt (EllipticDivision.cubic ((0) : ℚ) (1) (0) (-1)) = (0) := by decide +kernel
private theorem lift_sqrt_1 : Rat.sqrt (EllipticDivision.cubic ((0) : ℚ) (1) (0) (1)) = (1) := by decide +kernel
/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  classical
  simp only [halves, EllipticQuarticLifts.fibreList, List.flatMap_cons, List.flatMap_nil, EllipticQuarticLifts.lifts]
  simp only [lift_sqrt_0,lift_sqrt_1]
  norm_num [target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(1),(0)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (1) (0) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (1) (0)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((0),(0)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_ea1d3ebedd649b4b
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.original_target_checked
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.original_halves_complete
#print axioms PerfectPower.HalvesPacket_ea1d3ebedd649b4b.original_json_list_checked
namespace PerfectPower.HalvesPacket_ab9bab34cbf77424
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-2) + X^3
private def coefficients : List ℤ := [-2,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-2) + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-2) + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_ab9bab34cbf77424
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.native_roots_checked
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.source_complete

namespace PerfectPower.HalvesPacket_ab9bab34cbf77424
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked ([] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_ab9bab34cbf77424
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.smooth_checked
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_ab9bab34cbf77424
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (129/100) (-383/1000) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem anchor_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (3) (5) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual anchor on the completed model. -/
noncomputable def anchor : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some anchor_on_curve
theorem anchor_checked : (2 : ℤ) • anchor = target := by
  unfold anchor target
  rw [two_zsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by
    norm_num [EllipticPointDivision.completed, WeierstrassCurve.Affine.negY] :
      ((5) : ℚ) ≠ (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).negY (3) (5))]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope,
    EllipticPointDivision.completed, WeierstrassCurve.Affine.negY]
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point :=
  (EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2) smooth_checked ([] : List ℚ)).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_ab9bab34cbf77424
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.anchor_checked

namespace PerfectPower.HalvesPacket_ab9bab34cbf77424
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([some ((3),(5))] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, anchor, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(0),(-2)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (0) (-2) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([some ((3),(5))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([some ((3),(5))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((129/100),(-383/1000)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_ab9bab34cbf77424
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.original_target_checked
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.original_halves_complete
#print axioms PerfectPower.HalvesPacket_ab9bab34cbf77424.original_json_list_checked
namespace PerfectPower.HalvesPacket_ef03987420ff1381
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-25) * X + X^3
private def coefficients : List ℤ := [0,-25,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-25) * X + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-25) * X + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-5),(0),(5)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-5),(0),(5)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_ef03987420ff1381
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.native_roots_checked
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.source_complete

namespace PerfectPower.HalvesPacket_ef03987420ff1381
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-25) (0)
      smooth_checked ([(-5),(0),(5)] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-25) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_ef03987420ff1381
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.smooth_checked
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_ef03987420ff1381
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Nonsingular (1681/144) (-62279/1728) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem anchor_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Nonsingular (25/4) (75/8) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual anchor on the completed model. -/
noncomputable def anchor : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point := WeierstrassCurve.Affine.Point.some anchor_on_curve
theorem anchor_checked : (2 : ℤ) • anchor = target := by
  unfold anchor target
  rw [two_zsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by
    norm_num [EllipticPointDivision.completed, WeierstrassCurve.Affine.negY] :
      ((75/8) : ℚ) ≠ (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).negY (25/4) (75/8))]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope,
    EllipticPointDivision.completed, WeierstrassCurve.Affine.negY]
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point :=
  (EllipticPointDivision.torsionList ((0) : ℚ) (-25) (0) smooth_checked ([(-5),(0),(5)] : List ℚ)).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_ef03987420ff1381
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.anchor_checked

namespace PerfectPower.HalvesPacket_ef03987420ff1381
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([some ((25/4),(75/8)),some ((-5/9),(-100/27)),some ((-4),(6)),some ((45),(-300))] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, anchor, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(-25),(0)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (-25) (0) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([some ((25/4),(75/8)),some ((-5/9),(-100/27)),some ((-4),(6)),some ((45),(-300))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([some ((25/4),(75/8)),some ((-5/9),(-100/27)),some ((-4),(6)),some ((45),(-300))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((1681/144),(-62279/1728)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_ef03987420ff1381
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.original_target_checked
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.original_halves_complete
#print axioms PerfectPower.HalvesPacket_ef03987420ff1381.original_json_list_checked
namespace PerfectPower.HalvesPacket_891d0881c02bd0e5
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-2) + X^3
private def coefficients : List ℤ := [-2,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-2) + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-2) + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_891d0881c02bd0e5
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.native_roots_checked
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.source_complete

namespace PerfectPower.HalvesPacket_891d0881c02bd0e5
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked ([] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_891d0881c02bd0e5
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.smooth_checked
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_891d0881c02bd0e5
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (129/100) (-383/1000) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem anchor_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (3) (5) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual anchor on the completed model. -/
noncomputable def anchor : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some anchor_on_curve
theorem anchor_checked : (2 : ℤ) • anchor = target := by
  unfold anchor target
  rw [two_zsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by
    norm_num [EllipticPointDivision.completed, WeierstrassCurve.Affine.negY] :
      ((5) : ℚ) ≠ (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).negY (3) (5))]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope,
    EllipticPointDivision.completed, WeierstrassCurve.Affine.negY]
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point :=
  (EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2) smooth_checked ([] : List ℚ)).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_891d0881c02bd0e5
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.anchor_checked

namespace PerfectPower.HalvesPacket_891d0881c02bd0e5
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine

/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([some ((3),(5))] : List (Option (ℚ × ℚ))) := by
  classical
  norm_num [halves, anchor, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(1),(-1/4),(1),(-1/2),(-9/4)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (0) (-2) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([some ((3),(3))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([some ((3),(3))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((129/100),(-191/125)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_891d0881c02bd0e5
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.original_target_checked
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.original_halves_complete
#print axioms PerfectPower.HalvesPacket_891d0881c02bd0e5.original_json_list_checked
namespace PerfectPower.HalvesPacket_ae6d1916e52accd5
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-7) + X^3
private def coefficients : List ℤ := [-7,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-7) + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-7) + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_ae6d1916e52accd5
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.native_roots_checked
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.source_complete

namespace PerfectPower.HalvesPacket_ae6d1916e52accd5
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-7)
      smooth_checked ([] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-7) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_ae6d1916e52accd5
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.smooth_checked
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (896) + C (56) * X + C (-128) * X^3 + X^4
private def coefficients : List ℤ := [896,56,0,-128,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 4 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (896) + C (56) * X + C (-128) * X^3 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (896) + C (56) * X + C (-128) * X^3 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 4 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(2)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(2)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5
#print axioms PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5.native_roots_checked
#print axioms PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5.source_complete
namespace PerfectPower.HalvesPacket_ae6d1916e52accd5
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Nonsingular (32) (-181) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem quartic_complete (x : ℚ) :
    EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-7) (32) x = 0 ↔ x ∈ ([(2)] : List ℚ) := by
  have hc := PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5.source_complete x
  have he : PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-7) (32) x := by
    norm_num [PerfectPower.RationalPacket_4fde3f08e93ebee3_ae6d1916e52accd5.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point :=
  EllipticQuarticLifts.fibreList ((0) : ℚ) (0) (-7) smooth_checked target ([(2)] : List ℚ)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticQuarticLifts.fibre_complete ((0) : ℚ) (0) (-7) (32) (-181) smooth_checked target_on_curve ([(2)] : List ℚ) quartic_complete Q
end PerfectPower.HalvesPacket_ae6d1916e52accd5
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.actual_halves_complete

namespace PerfectPower.HalvesPacket_ae6d1916e52accd5
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine
private theorem lift_sqrt_0 : Rat.sqrt (EllipticDivision.cubic ((0) : ℚ) (0) (-7) (2)) = (1) := by decide +kernel
/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([some ((2),(1))] : List (Option (ℚ × ℚ))) := by
  classical
  simp only [halves, EllipticQuarticLifts.fibreList, List.flatMap_cons, List.flatMap_nil, EllipticQuarticLifts.lifts]
  simp only [lift_sqrt_0]
  norm_num [target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(0),(-7)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (0) (-7) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([some ((2),(1))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([some ((2),(1))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((32),(-181)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_ae6d1916e52accd5
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.original_target_checked
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.original_halves_complete
#print axioms PerfectPower.HalvesPacket_ae6d1916e52accd5.original_json_list_checked
namespace PerfectPower.HalvesPacket_ac59f25f4db29d67
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (-7) + X^3
private def coefficients : List ℤ := [-7,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 3 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (-7) + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-7) + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 3 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 3
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 3 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_ac59f25f4db29d67
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.native_roots_checked
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.source_complete

namespace PerfectPower.HalvesPacket_ac59f25f4db29d67
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-7)
      smooth_checked ([] : List ℚ) := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-7) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa using h
end PerfectPower.HalvesPacket_ac59f25f4db29d67
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.smooth_checked
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67
open Polynomial PerfectPower
/-- The original rational polynomial bound to this packet. -/
noncomputable def source : Polynomial ℚ := C (896) + C (56) * X + C (-128) * X^3 + X^4
private def coefficients : List ℤ := [896,56,0,-128,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 4 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (1) := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots (1) := by
  have hn : NativeRationalRoots.normalize source = (C (896) + C (56) * X + C (-128) * X^3 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (896) + C (56) * X + C (-128) * X^3 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 4 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 4 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(2)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(2)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67
#print axioms PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67.native_roots_checked
#print axioms PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67.source_complete
namespace PerfectPower.HalvesPacket_ac59f25f4db29d67
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Nonsingular (32) (181) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
private theorem quartic_complete (x : ℚ) :
    EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-7) (32) x = 0 ↔ x ∈ ([(2)] : List ℚ) := by
  have hc := PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67.source_complete x
  have he : PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-7) (32) x := by
    norm_num [PerfectPower.RationalPacket_4fde3f08e93ebee3_ac59f25f4db29d67.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point :=
  EllipticQuarticLifts.fibreList ((0) : ℚ) (0) (-7) smooth_checked target ([(2)] : List ℚ)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticQuarticLifts.fibre_complete ((0) : ℚ) (0) (-7) (32) (181) smooth_checked target_on_curve ([(2)] : List ℚ) quartic_complete Q
end PerfectPower.HalvesPacket_ac59f25f4db29d67
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.actual_halves_complete

namespace PerfectPower.HalvesPacket_ac59f25f4db29d67
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine
private theorem lift_sqrt_0 : Rat.sqrt (EllipticDivision.cubic ((0) : ℚ) (0) (-7) (2)) = (1) := by decide +kernel
/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = ([some ((2),(-1))] : List (Option (ℚ × ℚ))) := by
  classical
  simp only [halves, EllipticQuarticLifts.fibreList, List.flatMap_cons, List.flatMap_nil, EllipticQuarticLifts.lifts]
  simp only [lift_sqrt_0]
  norm_num [target, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := (⟨(0),(0),(0),(0),(-7)⟩ : WeierstrassCurve ℚ).toAffine
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed ((0) : ℚ) (0) (-7) := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-7)).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = ([some ((2),(-1))] : List (Option (ℚ × ℚ))) := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ ([some ((2),(-1))] : List (Option (ℚ × ℚ))) := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    some ((32),(181)) := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end PerfectPower.HalvesPacket_ac59f25f4db29d67
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.literal_fibre_complete
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.original_target_checked
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.completed_json_list_checked
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.original_halves_complete
#print axioms PerfectPower.HalvesPacket_ac59f25f4db29d67.original_json_list_checked
#print axioms PerfectPower.EllipticSquareTransport.discriminant
#print axioms PerfectPower.EllipticSquareTransport.equation
#print axioms PerfectPower.EllipticSquareTransport.nonsingular
#print axioms PerfectPower.EllipticSquareTransport.vertical
#print axioms PerfectPower.EllipticSquareTransport.slope_shift
#print axioms PerfectPower.EllipticSquareTransport.same_x
#print axioms PerfectPower.EllipticSquareTransport.addX_shift
#print axioms PerfectPower.EllipticSquareTransport.addY_shift
#print axioms PerfectPower.EllipticSquareTransport.forward_add
#print axioms PerfectPower.EllipticSquareTransport.fibre
#print axioms PerfectPower.EllipticSquareTransport.coordinates_injective
#print axioms PerfectPower.EllipticSquareTransport.coordinates_cast
#print axioms PerfectPower.EllipticSquareTransport.coordinates_backward
#print axioms PerfectPower.EllipticSquareTransport.list_transport
#print axioms PerfectPower.EllipticQuarticLifts.mem_lifts
#print axioms PerfectPower.EllipticQuarticLifts.fibre_complete
#lint in PerfectPower.EllipticSquareTransport
#lint in PerfectPower.EllipticQuarticLifts
