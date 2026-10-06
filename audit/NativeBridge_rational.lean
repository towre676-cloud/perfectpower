import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.ResiduePopulation
import PerfectPower.PicardLefschetz
namespace PerfectPower.RationalPacket_c8717b1530123a75
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (-3/2) + C (6) * X^2
private def coefficients : List ℤ := [-4,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 2 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (6) := by
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
  have hn : NativeRationalRoots.normalize source = (C (-1/4) + X^2 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1/4) + X^2 : Polynomial ℚ).natDegree = 2 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 2 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 2
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 2 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (4) = ({(-1/2),(1/2)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1/2),(1/2)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (4)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_c8717b1530123a75
#print axioms PerfectPower.RationalPacket_c8717b1530123a75.native_roots_checked
#print axioms PerfectPower.RationalPacket_c8717b1530123a75.source_complete
namespace PerfectPower.RationalPacket_6c82bbb1f983c0d6
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (-1) * X^2 + X^4
private def coefficients : List ℤ := [0,0,-1,0,1]
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
  have hn : NativeRationalRoots.normalize source = (C (-1) * X^2 + X^4 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1) * X^2 + X^4 : Polynomial ℚ).natDegree = 4 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-1),(0),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(0),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_6c82bbb1f983c0d6
#print axioms PerfectPower.RationalPacket_6c82bbb1f983c0d6.native_roots_checked
#print axioms PerfectPower.RationalPacket_6c82bbb1f983c0d6.source_complete
namespace PerfectPower.RationalPacket_68a90152c04505f5
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (2)
private def coefficients : List ℤ := [1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 0 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (2) := by
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
  have hn : NativeRationalRoots.normalize source = (C (1) : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1) : Polynomial ℚ).natDegree = 0 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 0 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 0
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 0 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_68a90152c04505f5
#print axioms PerfectPower.RationalPacket_68a90152c04505f5.native_roots_checked
#print axioms PerfectPower.RationalPacket_68a90152c04505f5.source_complete
namespace PerfectPower.RationalPacket_93938bee38185b2d
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (1) + X^2
private def coefficients : List ℤ := [1,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 2 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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
  have hn : NativeRationalRoots.normalize source = (C (1) + X^2 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1) + X^2 : Polynomial ℚ).natDegree = 2 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 2 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 2
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 2 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = (∅ : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ (∅ : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_93938bee38185b2d
#print axioms PerfectPower.RationalPacket_93938bee38185b2d.native_roots_checked
#print axioms PerfectPower.RationalPacket_93938bee38185b2d.source_complete
namespace PerfectPower.RationalPacket_c1119b20b8a3acf4
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (-1) + C (3) * X + C (-3) * X^2 + X^3
private def coefficients : List ℤ := [-1,3,-3,1]
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
  have hn : NativeRationalRoots.normalize source = (C (-1) + C (3) * X + C (-3) * X^2 + X^3 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1) + C (3) * X + C (-3) * X^2 + X^3 : Polynomial ℚ).natDegree = 3 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_c1119b20b8a3acf4
#print axioms PerfectPower.RationalPacket_c1119b20b8a3acf4.native_roots_checked
#print axioms PerfectPower.RationalPacket_c1119b20b8a3acf4.source_complete
namespace PerfectPower.RationalPacket_6e54adb2f5a6689c
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (-2) + C (-4) * X
private def coefficients : List ℤ := [1,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 1 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = (-4) := by
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
    (NativeRationalRoots.normalize source).scaleRoots (2) := by
  have hn : NativeRationalRoots.normalize source = (C (1/2) + X : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1/2) + X : Polynomial ℚ).natDegree = 1 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 1 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 1
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 1 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (2) = ({(-1/2)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1/2)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (2)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_6e54adb2f5a6689c
#print axioms PerfectPower.RationalPacket_6e54adb2f5a6689c.native_roots_checked
#print axioms PerfectPower.RationalPacket_6e54adb2f5a6689c.source_complete
namespace PerfectPower.RationalPacket_8917093f60850a1e
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (1/2) + C (-3/2) * X + X^2
private def coefficients : List ℤ := [2,-3,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 2 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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
    (NativeRationalRoots.normalize source).scaleRoots (2) := by
  have hn : NativeRationalRoots.normalize source = (C (1/2) + C (-3/2) * X + X^2 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (1/2) + C (-3/2) * X + X^2 : Polynomial ℚ).natDegree = 2 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 2 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 2
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 2 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (2) = ({(1/2),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(1/2),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (2)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_8917093f60850a1e
#print axioms PerfectPower.RationalPacket_8917093f60850a1e.native_roots_checked
#print axioms PerfectPower.RationalPacket_8917093f60850a1e.source_complete
namespace PerfectPower.RationalPacket_fff8a185ca722a1c
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := C (-1) + X^8
private def coefficients : List ℤ := [-1,0,0,0,0,0,0,0,1]
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = 8 := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
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
  have hn : NativeRationalRoots.normalize source = (C (-1) + X^8 : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : (C (-1) + X^8 : Polynomial ℚ).natDegree = 8 := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = 8 := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ 8
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : 8 < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients (1) = ({(-1),(1)} : Finset ℚ) := by
  decide +kernel

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(-1),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (1)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_fff8a185ca722a1c
#print axioms PerfectPower.RationalPacket_fff8a185ca722a1c.native_roots_checked
#print axioms PerfectPower.RationalPacket_fff8a185ca722a1c.source_complete
