import PerfectPower.IntegerValuedPowerCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace PowerCharts_4a0c07cf3871071c
open Polynomial PerfectPower.IntegerValuedPolynomial PerfectPower.IntegerValuedPowerCharts
noncomputable def source : Polynomial ℤ := C (7) + C (1) * X^2
theorem source_checked : source = PerfectPower.NativePolynomialSquare.polynomial [7, 0, 1] := by
  norm_num [source, PerfectPower.NativePolynomialSquare.polynomial] <;> ring
theorem denominator_clearing (x y : ℤ) : PowerAt source 2 0 2 x y ↔
    source.eval x + (2 : ℤ)*(0) = (2 : ℤ)*y^2 :=
  cleared_power_iff source 2 0 2 (by norm_num) x y
noncomputable def rationalSource : Polynomial ℚ := C ((7 : ℚ)/2) + C ((1 : ℚ)/2)*X^2
theorem rational_identity : rationalSource*C (2 : ℚ)=source.map (Int.castRingHom ℚ) := by
  simp only [rationalSource,source,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow] <;> ring
theorem rational_equation (x y : ℤ) : rationalSource.eval (x : ℚ)+(0 : ℚ)=(y : ℚ)^2 ↔ PowerAt source 2 0 2 x y :=
  rational_power_iff source rationalSource 2 0 2 (by norm_num) rational_identity x y
#print axioms rational_identity
#print axioms rational_equation
theorem residues_checked : PerfectPower.PowerFreeLocal.rootResidues [7, 0, 1] 2 = ({1} : Finset ℕ) := by decide +kernel
theorem integral_domain (x : ℤ) : IntegralAt source 2 x ↔
    ∃ r ∈ ({1} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+2*n := by
  rw [source_checked]
  simpa only [residues_checked] using integer_domain_cover [7, 0, 1] 2 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (4) + C (2) * X + C (2) * X^2
theorem chart0_identity : source.comp (C (1 : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*chart0 := by
  norm_num [source,chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring
theorem chart0_power (n y : ℤ) : PowerAt source 2 0 2 (1+2*n) y ↔
    chart0.eval n + (0) = y^2 := chart_power_iff source chart0 2 1 0 2 (by norm_num) chart0_identity n y
#print axioms source_checked
#print axioms denominator_clearing
#print axioms residues_checked
#print axioms integral_domain
#print axioms chart0_identity
#print axioms chart0_power
end PowerCharts_4a0c07cf3871071c
