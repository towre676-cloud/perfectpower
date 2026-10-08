import PerfectPower.IntegerValuedPowerCharts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace PowerCharts_dace7e525e5bdfea
open Polynomial PerfectPower.IntegerValuedPolynomial PerfectPower.IntegerValuedPowerCharts
noncomputable def source : Polynomial ℤ := C (1) * X + C (1) * X^2
theorem source_checked : source = PerfectPower.NativePolynomialSquare.polynomial [0, 1, 1] := by
  norm_num [source, PerfectPower.NativePolynomialSquare.polynomial] <;> ring
theorem denominator_clearing (x y : ℤ) : PowerAt source 6 0 3 x y ↔
    source.eval x + (6 : ℤ)*(0) = (6 : ℤ)*y^3 :=
  cleared_power_iff source 6 0 3 (by norm_num) x y
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/6)*X^1 + C ((1 : ℚ)/6)*X^2
theorem rational_identity : rationalSource*C (6 : ℚ)=source.map (Int.castRingHom ℚ) := by
  simp only [rationalSource,source,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow] <;> ring
theorem rational_equation (x y : ℤ) : rationalSource.eval (x : ℚ)+(0 : ℚ)=(y : ℚ)^3 ↔ PowerAt source 6 0 3 x y :=
  rational_power_iff source rationalSource 6 0 3 (by norm_num) rational_identity x y
#print axioms rational_identity
#print axioms rational_equation
theorem residues_checked : PerfectPower.PowerFreeLocal.rootResidues [0, 1, 1] 6 = ({0,2,3,5} : Finset ℕ) := by decide +kernel
theorem integral_domain (x : ℤ) : IntegralAt source 6 x ↔
    ∃ r ∈ ({0,2,3,5} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+6*n := by
  rw [source_checked]
  simpa only [residues_checked] using integer_domain_cover [0, 1, 1] 6 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (1) * X + C (6) * X^2
theorem chart0_identity : source.comp (C (0 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart0 := by
  norm_num [source,chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring
theorem chart0_power (n y : ℤ) : PowerAt source 6 0 3 (0+6*n) y ↔
    chart0.eval n + (0) = y^3 := chart_power_iff source chart0 6 0 0 3 (by norm_num) chart0_identity n y
noncomputable def chart1 : Polynomial ℤ := C (1) + C (5) * X + C (6) * X^2
theorem chart1_identity : source.comp (C (2 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart1 := by
  norm_num [source,chart1,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring
theorem chart1_power (n y : ℤ) : PowerAt source 6 0 3 (2+6*n) y ↔
    chart1.eval n + (0) = y^3 := chart_power_iff source chart1 6 2 0 3 (by norm_num) chart1_identity n y
noncomputable def chart2 : Polynomial ℤ := C (2) + C (7) * X + C (6) * X^2
theorem chart2_identity : source.comp (C (3 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart2 := by
  norm_num [source,chart2,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring
theorem chart2_power (n y : ℤ) : PowerAt source 6 0 3 (3+6*n) y ↔
    chart2.eval n + (0) = y^3 := chart_power_iff source chart2 6 3 0 3 (by norm_num) chart2_identity n y
noncomputable def chart3 : Polynomial ℤ := C (5) + C (11) * X + C (6) * X^2
theorem chart3_identity : source.comp (C (5 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart3 := by
  norm_num [source,chart3,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring
theorem chart3_power (n y : ℤ) : PowerAt source 6 0 3 (5+6*n) y ↔
    chart3.eval n + (0) = y^3 := chart_power_iff source chart3 6 5 0 3 (by norm_num) chart3_identity n y
#print axioms source_checked
#print axioms denominator_clearing
#print axioms residues_checked
#print axioms integral_domain
#print axioms chart0_identity
#print axioms chart0_power
#print axioms chart1_identity
#print axioms chart1_power
#print axioms chart2_identity
#print axioms chart2_power
#print axioms chart3_identity
#print axioms chart3_power
end PowerCharts_dace7e525e5bdfea
