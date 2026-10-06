import PerfectPower.EllipticPointDivision
import Mathlib.Tactic.Linter.Lint
namespace PerfectPower.HalvesPacket_548e5e066286c8c8
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
end PerfectPower.HalvesPacket_548e5e066286c8c8
#print axioms PerfectPower.HalvesPacket_548e5e066286c8c8.native_roots_checked
#print axioms PerfectPower.HalvesPacket_548e5e066286c8c8.source_complete

namespace PerfectPower.HalvesPacket_548e5e066286c8c8
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0)
      smooth_checked ({(-1),(0),(1)} : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-1) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_548e5e066286c8c8
#print axioms PerfectPower.HalvesPacket_548e5e066286c8c8.smooth_checked
#print axioms PerfectPower.HalvesPacket_548e5e066286c8c8.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_548e5e066286c8c8
open PerfectPower
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := 0
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point :=
  EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0) smooth_checked ({(-1),(0),(1)} : Finset ℚ).toList
 theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_548e5e066286c8c8
#print axioms PerfectPower.HalvesPacket_548e5e066286c8c8.actual_halves_complete
namespace PerfectPower.HalvesPacket_b7abc0fe272e0d02
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
end PerfectPower.HalvesPacket_b7abc0fe272e0d02
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.native_roots_checked
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.source_complete

namespace PerfectPower.HalvesPacket_b7abc0fe272e0d02
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked (∅ : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_b7abc0fe272e0d02
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.smooth_checked
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_c09040e3a484be22
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
end PerfectPower.RationalPacket_c09040e3a484be22
#print axioms PerfectPower.RationalPacket_c09040e3a484be22.native_roots_checked
#print axioms PerfectPower.RationalPacket_c09040e3a484be22.source_complete
namespace PerfectPower.HalvesPacket_b7abc0fe272e0d02
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Nonsingular (3) (5) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
theorem quartic_root_free (x : ℚ) : EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-2) (3) x ≠ 0 := by
  have hc := PerfectPower.RationalPacket_c09040e3a484be22.source_complete x
  have he : PerfectPower.RationalPacket_c09040e3a484be22.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (0) (-2) (3) x := by
    norm_num [PerfectPower.RationalPacket_c09040e3a484be22.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point := []
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := by
  have hn := EllipticPointDivision.no_half_of_quartic_root_free ((0) : ℚ) (0) (-2) (3) (5) target_on_curve quartic_root_free Q
  simpa [target, halves] using hn
end PerfectPower.HalvesPacket_b7abc0fe272e0d02
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_b7abc0fe272e0d02.quartic_root_free
namespace PerfectPower.HalvesPacket_be67fab9d866a948
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
end PerfectPower.HalvesPacket_be67fab9d866a948
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.native_roots_checked
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.source_complete

namespace PerfectPower.HalvesPacket_be67fab9d866a948
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-1) (0)
      smooth_checked ({(-1),(0),(1)} : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-1) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_be67fab9d866a948
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.smooth_checked
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.actual_two_torsion_complete

namespace PerfectPower.RationalPacket_ac68ffb54d1621fa
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
end PerfectPower.RationalPacket_ac68ffb54d1621fa
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa.native_roots_checked
#print axioms PerfectPower.RationalPacket_ac68ffb54d1621fa.source_complete
namespace PerfectPower.HalvesPacket_be67fab9d866a948
open PerfectPower
private theorem target_on_curve : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Nonsingular (0) (0) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
/-- The checked actual target on the completed model. -/
noncomputable def target : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := WeierstrassCurve.Affine.Point.some target_on_curve
theorem quartic_root_free (x : ℚ) : EllipticDivision.halvingPolynomial ((0) : ℚ) (-1) (0) (0) x ≠ 0 := by
  have hc := PerfectPower.RationalPacket_ac68ffb54d1621fa.source_complete x
  have he : PerfectPower.RationalPacket_ac68ffb54d1621fa.source.eval x = EllipticDivision.halvingPolynomial ((0) : ℚ) (-1) (0) (0) x := by
    norm_num [PerfectPower.RationalPacket_ac68ffb54d1621fa.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
/-- The complete native halving fibre list. -/
noncomputable def halves : List (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point := []
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-1) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := by
  have hn := EllipticPointDivision.no_half_of_quartic_root_free ((0) : ℚ) (-1) (0) (0) (0) target_on_curve quartic_root_free Q
  simpa [target, halves] using hn
end PerfectPower.HalvesPacket_be67fab9d866a948
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_be67fab9d866a948.quartic_root_free
namespace PerfectPower.HalvesPacket_d603a7ed1257d631
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
end PerfectPower.HalvesPacket_d603a7ed1257d631
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.native_roots_checked
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.source_complete

namespace PerfectPower.HalvesPacket_d603a7ed1257d631
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked (∅ : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_d603a7ed1257d631
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.smooth_checked
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_d603a7ed1257d631
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
  (EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2) smooth_checked (∅ : Finset ℚ).toList).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_d603a7ed1257d631
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_d603a7ed1257d631.anchor_checked
namespace PerfectPower.HalvesPacket_6a98c972a12840fe
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
end PerfectPower.HalvesPacket_6a98c972a12840fe
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.native_roots_checked
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.source_complete

namespace PerfectPower.HalvesPacket_6a98c972a12840fe
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (-25) (0)
      smooth_checked ({(-5),(0),(5)} : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (-25) (0) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_6a98c972a12840fe
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.smooth_checked
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_6a98c972a12840fe
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
  (EllipticPointDivision.torsionList ((0) : ℚ) (-25) (0) smooth_checked ({(-5),(0),(5)} : Finset ℚ).toList).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (-25) (0)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_6a98c972a12840fe
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_6a98c972a12840fe.anchor_checked
namespace PerfectPower.HalvesPacket_3153a664e7850c18
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
end PerfectPower.HalvesPacket_3153a664e7850c18
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.native_roots_checked
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.source_complete

namespace PerfectPower.HalvesPacket_3153a664e7850c18
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2)
      smooth_checked (∅ : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((0) : ℚ) (0) (-2) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.HalvesPacket_3153a664e7850c18
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.smooth_checked
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.actual_two_torsion_complete

namespace PerfectPower.HalvesPacket_3153a664e7850c18
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
  (EllipticPointDivision.torsionList ((0) : ℚ) (0) (-2) smooth_checked (∅ : Finset ℚ).toList).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed ((0) : ℚ) (0) (-2)).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q
end PerfectPower.HalvesPacket_3153a664e7850c18
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.actual_halves_complete
#print axioms PerfectPower.HalvesPacket_3153a664e7850c18.anchor_checked
#print axioms PerfectPower.EllipticPointDivision.half_supplies_quartic_root
#print axioms PerfectPower.EllipticPointDivision.no_half_of_quartic_root_free
#lint in PerfectPower.EllipticPointDivision
