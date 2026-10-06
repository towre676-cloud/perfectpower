import PerfectPower.NativeRationalRoots
import PerfectPower.TypedDivisionPackets
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

noncomputable def typedPacket : TypedDivisionPackets.RationalPacket
    (NativeRationalRoots.normalize source) where
  coefficients := coefficients
  scale := (2)
  scale_ne_zero := by norm_num
  valid := by decide +kernel
  monic := scaled_monic
  scaling := scaling

theorem typed_roots_complete (r : ℚ) :
    (NativeRationalRoots.normalize source).eval r=0 ↔ r ∈ typedPacket.interpret :=
  typedPacket.complete r

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ ({(1/2),(1)} : Finset ℚ) := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients (2)
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end PerfectPower.RationalPacket_8917093f60850a1e
#print axioms PerfectPower.RationalPacket_8917093f60850a1e.native_roots_checked
#print axioms PerfectPower.RationalPacket_8917093f60850a1e.source_complete
#print axioms PerfectPower.RationalPacket_8917093f60850a1e.typed_roots_complete
