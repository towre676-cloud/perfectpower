import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.ResiduePopulation
import PerfectPower.PicardLefschetz
namespace PerfectPower.RationalPacket_7da4dfe32819e3cc
open Polynomial PerfectPower
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
end PerfectPower.RationalPacket_7da4dfe32819e3cc
#print axioms PerfectPower.RationalPacket_7da4dfe32819e3cc.native_roots_checked
#print axioms PerfectPower.RationalPacket_7da4dfe32819e3cc.source_complete

namespace PerfectPower.RationalPacket_7da4dfe32819e3cc
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
end PerfectPower.RationalPacket_7da4dfe32819e3cc
#print axioms PerfectPower.RationalPacket_7da4dfe32819e3cc.smooth_checked
#print axioms PerfectPower.RationalPacket_7da4dfe32819e3cc.actual_two_torsion_complete
namespace PerfectPower.RationalPacket_dbd5d8ec75600244
open Polynomial PerfectPower
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
end PerfectPower.RationalPacket_dbd5d8ec75600244
#print axioms PerfectPower.RationalPacket_dbd5d8ec75600244.native_roots_checked
#print axioms PerfectPower.RationalPacket_dbd5d8ec75600244.source_complete

namespace PerfectPower.RationalPacket_dbd5d8ec75600244
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
end PerfectPower.RationalPacket_dbd5d8ec75600244
#print axioms PerfectPower.RationalPacket_dbd5d8ec75600244.smooth_checked
#print axioms PerfectPower.RationalPacket_dbd5d8ec75600244.actual_two_torsion_complete
namespace PerfectPower.RationalPacket_7ec2af249a5afc27
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (29/4) + C (-5/2) * X + C (9/4) * X^2 + X^3
private def coefficients : List ℤ := [464,-40,9,1]
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
    (NativeRationalRoots.normalize source).scaleRoots (4) := by
  have hn : NativeRationalRoots.normalize source = (C (29/4) + C (-5/2) * X + C (9/4) * X^2 + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (29/4) + C (-5/2) * X + C (9/4) * X^2 + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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

theorem native_roots_checked : NativeRationalRoots.roots coefficients (4) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (4)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_7ec2af249a5afc27
#print axioms PerfectPower.RationalPacket_7ec2af249a5afc27.native_roots_checked
#print axioms PerfectPower.RationalPacket_7ec2af249a5afc27.source_complete

namespace PerfectPower.RationalPacket_7ec2af249a5afc27
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed ((9/4) : ℚ) (-5/2) (29/4)).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed ((9/4) : ℚ) (-5/2) (29/4)).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList ((9/4) : ℚ) (-5/2) (29/4)
      smooth_checked (∅ : Finset ℚ).toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic ((9/4) : ℚ) (-5/2) (29/4) x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end PerfectPower.RationalPacket_7ec2af249a5afc27
#print axioms PerfectPower.RationalPacket_7ec2af249a5afc27.smooth_checked
#print axioms PerfectPower.RationalPacket_7ec2af249a5afc27.actual_two_torsion_complete
