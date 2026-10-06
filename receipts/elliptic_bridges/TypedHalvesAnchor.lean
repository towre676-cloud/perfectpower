import PerfectPower.EllipticQuarticLifts
import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.TypedDivisionPackets
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

noncomputable def typedPacket : TypedDivisionPackets.RationalPacket
    (NativeRationalRoots.normalize source) where
  coefficients := coefficients
  scale := (1)
  scale_ne_zero := by norm_num
  valid := by decide +kernel
  monic := scaled_monic
  scaling := scaling

theorem typed_roots_complete (r : ℚ) :
    (NativeRationalRoots.normalize source).eval r=0 ↔ r ∈ typedPacket.interpret :=
  typedPacket.complete r

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(0),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.native_roots_checked
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.source_complete
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.typed_roots_complete

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

noncomputable def typedPacket : TypedDivisionPackets.RationalPacket
    (NativeRationalRoots.normalize source) where
  coefficients := coefficients
  scale := (1)
  scale_ne_zero := by norm_num
  valid := by decide +kernel
  monic := scaled_monic
  scaling := scaling

theorem typed_roots_complete (r : ℚ) :
    (NativeRationalRoots.normalize source).eval r=0 ↔ r ∈ typedPacket.interpret :=
  typedPacket.complete r

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.native_roots_checked
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.source_complete
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa_3ad187ec1fe02953.typed_roots_complete
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

noncomputable def typedFibre : TypedDivisionPackets.FibrePacket 2 target where
  points := halves
  sound_complete := actual_halves_complete

theorem typed_fibre_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • Q=target ↔ Q ∈ typedFibre.points := typedFibre.sound_complete Q

end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.typed_fibre_complete
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

namespace PerfectPower.HalvesPacket_3ad187ec1fe02953
noncomputable def typedOriginalFibre : PerfectPower.TypedDivisionPackets.FibrePacket 2 originalTarget where
  points := originalHalves
  sound_complete := original_halves_complete
end PerfectPower.HalvesPacket_3ad187ec1fe02953
#print axioms PerfectPower.HalvesPacket_3ad187ec1fe02953.typedOriginalFibre
