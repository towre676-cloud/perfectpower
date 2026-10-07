import PerfectPower.IntegerValuedPolynomial
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_7a9cbb462a38d9f6
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, -1, 1]
theorem source_checked : source = C (-1) * X + C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 2 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((-1 : ℚ)/2) * X + C ((1 : ℚ)/2) * X^2
theorem rational_source_checked : rationalSource * C (2 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 2 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (2 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 2 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 2 x := by
  apply (integral_everywhere_iff source 2).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 2 x := by
  have hL : 2 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 2 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 2 n := by
  have hL : 2 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 2 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 2 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 2 x → (p : ℤ)^2 ∣ quotientValue source 2 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by intro x; simpa only [Nat.cast_pow] using hu x (integral_checked x))
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_7a9cbb462a38d9f6
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_57491d3f649219ed
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [1, 0, 1]
theorem source_checked : source = C (1) + C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/2) + C ((1 : ℚ)/2) * X^2
theorem rational_source_checked : rationalSource * C (2 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 2 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (2 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 2 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [1, 0, 1] 2 = ({1} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 2 x ↔
    ∃ r ∈ ({1} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+2*n := by
  simpa only [source, residues_checked] using integer_domain_cover [1, 0, 1] 2 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (1) + C (2) * X + C (2) * X^2
theorem chart0_checked : source.comp (C (1 : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 2 (1+2*n) = chart0.eval n :=
  chart_quotient source chart0 2 1 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 1 := by
  have hd : chart0.natDegree ≤ 2 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 2 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 1 then chart0 else (0)
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [1, 0, 1] 2) :
    source.comp (C (r : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl
  · simpa [charts] using chart0_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [1, 0, 1] 2).toList.map charts) ↔ f ∈ [chart0] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [1, 0, 1] 2).toList.map charts) = 1 := by
  rw [familyGcd_congr _ [chart0] family_members_checked]
  norm_num [familyGcd,chart0_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, IntegralAt source 2 x →
    (q : ℤ) ∣ quotientValue source 2 x := by
  have h := domain_divisors_iff [1, 0, 1] 2 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 2 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 2 x → (p : ℤ)^2 ∣ quotientValue source 2 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by simpa only [Nat.cast_pow] using hu)
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_57491d3f649219ed
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_d2c4a662dd8986a0
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [7, 0, 1]
theorem source_checked : source = C (7) + C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((7 : ℚ)/2) + C ((1 : ℚ)/2) * X^2
theorem rational_source_checked : rationalSource * C (2 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 2 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (2 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 2 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [7, 0, 1] 2 = ({1} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 2 x ↔
    ∃ r ∈ ({1} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+2*n := by
  simpa only [source, residues_checked] using integer_domain_cover [7, 0, 1] 2 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (4) + C (2) * X + C (2) * X^2
theorem chart0_checked : source.comp (C (1 : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 2 (1+2*n) = chart0.eval n :=
  chart_quotient source chart0 2 1 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 4 := by
  have hd : chart0.natDegree ≤ 2 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 2 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 1 then chart0 else (0)
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [7, 0, 1] 2) :
    source.comp (C (r : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl
  · simpa [charts] using chart0_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [7, 0, 1] 2).toList.map charts) ↔ f ∈ [chart0] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [7, 0, 1] 2).toList.map charts) = 4 := by
  rw [familyGcd_congr _ [chart0] family_members_checked]
  norm_num [familyGcd,chart0_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 4 ↔ ∀ x : ℤ, IntegralAt source 2 x →
    (q : ℤ) ∣ quotientValue source 2 x := by
  have h := domain_divisors_iff [7, 0, 1] 2 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem obstruction_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    ¬ PowerFree 2 (quotientValue source 2 x) := by
  intro h
  apply h 2 (by norm_num)
  have hd := (domain_gcd_checked (2^2)).mp (by norm_num : 2^2 ∣ 4)
  simpa only [Nat.cast_pow] using hd x hx
end IntegerValued_d2c4a662dd8986a0
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_656db630d4da80c7
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, 1, 1]
theorem source_checked : source = C (1) * X + C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 2 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/6) * X + C ((1 : ℚ)/6) * X^2
theorem rational_source_checked : rationalSource * C (6 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 6 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 6 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (6 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 6 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [0, 1, 1] 6 = ({0,2,3,5} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 6 x ↔
    ∃ r ∈ ({0,2,3,5} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+6*n := by
  simpa only [source, residues_checked] using integer_domain_cover [0, 1, 1] 6 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (1) * X + C (6) * X^2
theorem chart0_checked : source.comp (C (0 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 6 (0+6*n) = chart0.eval n :=
  chart_quotient source chart0 6 0 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 1 := by
  have hd : chart0.natDegree ≤ 2 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 2 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def chart1 : Polynomial ℤ := C (1) + C (5) * X + C (6) * X^2
theorem chart1_checked : source.comp (C (2 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart1 := by
  rw [source_checked]
  norm_num [chart1,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart1_quotient (n : ℤ) : quotientValue source 6 (2+6*n) = chart1.eval n :=
  chart_quotient source chart1 6 2 (by norm_num) chart1_checked n
theorem chart1_gcd : fixedDivisor chart1 = 1 := by
  have hd : chart1.natDegree ≤ 2 := by unfold chart1; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart1 2 hd]
  norm_num [windowGcd,chart1,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def chart2 : Polynomial ℤ := C (2) + C (7) * X + C (6) * X^2
theorem chart2_checked : source.comp (C (3 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart2 := by
  rw [source_checked]
  norm_num [chart2,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart2_quotient (n : ℤ) : quotientValue source 6 (3+6*n) = chart2.eval n :=
  chart_quotient source chart2 6 3 (by norm_num) chart2_checked n
theorem chart2_gcd : fixedDivisor chart2 = 1 := by
  have hd : chart2.natDegree ≤ 2 := by unfold chart2; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart2 2 hd]
  norm_num [windowGcd,chart2,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def chart3 : Polynomial ℤ := C (5) + C (11) * X + C (6) * X^2
theorem chart3_checked : source.comp (C (5 : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*chart3 := by
  rw [source_checked]
  norm_num [chart3,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart3_quotient (n : ℤ) : quotientValue source 6 (5+6*n) = chart3.eval n :=
  chart_quotient source chart3 6 5 (by norm_num) chart3_checked n
theorem chart3_gcd : fixedDivisor chart3 = 1 := by
  have hd : chart3.natDegree ≤ 2 := by unfold chart3; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart3 2 hd]
  norm_num [windowGcd,chart3,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 0 then chart0 else (if r = 2 then chart1 else (if r = 3 then chart2 else (if r = 5 then chart3 else (0))))
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [0, 1, 1] 6) :
    source.comp (C (r : ℤ)+C (6 : ℤ)*X) = C (6 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa [charts] using chart0_checked
  · simpa [charts] using chart1_checked
  · simpa [charts] using chart2_checked
  · simpa [charts] using chart3_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [0, 1, 1] 6).toList.map charts) ↔ f ∈ [chart0,chart1,chart2,chart3] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [0, 1, 1] 6).toList.map charts) = 1 := by
  rw [familyGcd_congr _ [chart0,chart1,chart2,chart3] family_members_checked]
  norm_num [familyGcd,chart0_gcd,chart1_gcd,chart2_gcd,chart3_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, IntegralAt source 6 x →
    (q : ℤ) ∣ quotientValue source 6 x := by
  have h := domain_divisors_iff [0, 1, 1] 6 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 6 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 6 x → (p : ℤ)^2 ∣ quotientValue source 6 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by simpa only [Nat.cast_pow] using hu)
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_656db630d4da80c7
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_0425aa5cdbec4806
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, 0, 1]
theorem source_checked : source = C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/3) * X^2
theorem rational_source_checked : rationalSource * C (3 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 3 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 3 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (3 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 3 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [0, 0, 1] 3 = ({0} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 3 x ↔
    ∃ r ∈ ({0} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+3*n := by
  simpa only [source, residues_checked] using integer_domain_cover [0, 0, 1] 3 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (3) * X^2
theorem chart0_checked : source.comp (C (0 : ℤ)+C (3 : ℤ)*X) = C (3 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 3 (0+3*n) = chart0.eval n :=
  chart_quotient source chart0 3 0 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 3 := by
  have hd : chart0.natDegree ≤ 2 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 2 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 0 then chart0 else (0)
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [0, 0, 1] 3) :
    source.comp (C (r : ℤ)+C (3 : ℤ)*X) = C (3 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl
  · simpa [charts] using chart0_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [0, 0, 1] 3).toList.map charts) ↔ f ∈ [chart0] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [0, 0, 1] 3).toList.map charts) = 3 := by
  rw [familyGcd_congr _ [chart0] family_members_checked]
  norm_num [familyGcd,chart0_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 3 ↔ ∀ x : ℤ, IntegralAt source 3 x →
    (q : ℤ) ∣ quotientValue source 3 x := by
  have h := domain_divisors_iff [0, 0, 1] 3 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem power_free_gcd_checked : PowerFree 2 (3 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 3 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (3 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 3 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([3] : List ℕ).Perm (3 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 3 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  all_goals norm_num at hd
theorem admissible_checked : QuotientAdmissible source 3 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 3 x → (p : ℤ)^2 ∣ quotientValue source 3 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by simpa only [Nat.cast_pow] using hu)
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_0425aa5cdbec4806
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_9163a87c6a6bca50
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, 0, 1]
theorem source_checked : source = C (1) * X^2 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 2 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/3) * X^2
theorem rational_source_checked : rationalSource * C (3 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 3 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 3 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (3 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 3 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [0, 0, 1] 3 = ({0} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 3 x ↔
    ∃ r ∈ ({0} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+3*n := by
  simpa only [source, residues_checked] using integer_domain_cover [0, 0, 1] 3 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (3) * X^2
theorem chart0_checked : source.comp (C (0 : ℤ)+C (3 : ℤ)*X) = C (3 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 3 (0+3*n) = chart0.eval n :=
  chart_quotient source chart0 3 0 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 3 := by
  have hd : chart0.natDegree ≤ 2 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 2 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 0 then chart0 else (0)
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [0, 0, 1] 3) :
    source.comp (C (r : ℤ)+C (3 : ℤ)*X) = C (3 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl
  · simpa [charts] using chart0_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [0, 0, 1] 3).toList.map charts) ↔ f ∈ [chart0] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [0, 0, 1] 3).toList.map charts) = 3 := by
  rw [familyGcd_congr _ [chart0] family_members_checked]
  norm_num [familyGcd,chart0_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 3 ↔ ∀ x : ℤ, IntegralAt source 3 x →
    (q : ℤ) ∣ quotientValue source 3 x := by
  have h := domain_divisors_iff [0, 0, 1] 3 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem obstruction_checked (x : ℤ) (hx : IntegralAt source 3 x) :
    ¬ PowerFree 1 (quotientValue source 3 x) := by
  intro h
  apply h 3 (by norm_num)
  have hd := (domain_gcd_checked (3^1)).mp (by norm_num : 3^1 ∣ 3)
  simpa only [Nat.cast_pow] using hd x hx
end IntegerValued_9163a87c6a6bca50
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_817cd37305b375fe
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, 1]
theorem source_checked : source = C (1) * X := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 1 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 1 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/2) * X
theorem rational_source_checked : rationalSource * C (2 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 2 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (2 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 2 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [0, 1] 2 = ({0} : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 2 x ↔
    ∃ r ∈ ({0} : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+2*n := by
  simpa only [source, residues_checked] using integer_domain_cover [0, 1] 2 (by norm_num) x
noncomputable def chart0 : Polynomial ℤ := C (1) * X
theorem chart0_checked : source.comp (C (0 : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*chart0 := by
  rw [source_checked]
  norm_num [chart0,Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart0_quotient (n : ℤ) : quotientValue source 2 (0+2*n) = chart0.eval n :=
  chart_quotient source chart0 2 0 (by norm_num) chart0_checked n
theorem chart0_gcd : fixedDivisor chart0 = 1 := by
  have hd : chart0.natDegree ≤ 1 := by unfold chart0; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart0 1 hd]
  norm_num [windowGcd,chart0,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def charts (r : ℕ) : Polynomial ℤ := if r = 0 then chart0 else (0)
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [0, 1] 2) :
    source.comp (C (r : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
  rcases hr with rfl
  · simpa [charts] using chart0_checked
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [0, 1] 2).toList.map charts) ↔ f ∈ [chart0] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [0, 1] 2).toList.map charts) = 1 := by
  rw [familyGcd_congr _ [chart0] family_members_checked]
  norm_num [familyGcd,chart0_gcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, IntegralAt source 2 x →
    (q : ℤ) ∣ quotientValue source 2 x := by
  have h := domain_divisors_iff [0, 1] 2 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 2 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 2 x → (p : ℤ)^2 ∣ quotientValue source 2 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by simpa only [Nat.cast_pow] using hu)
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_817cd37305b375fe
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_ef8a3818a93cb190
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [1]
theorem source_checked : source = C (1) := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 0 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((1 : ℚ)/2)
theorem rational_source_checked : rationalSource * C (2 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 2 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (2 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 2 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr h
theorem residues_checked : rootResidues [1] 2 = (∅ : Finset ℕ) := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source 2 x ↔
    ∃ r ∈ (∅ : Finset ℕ), ∃ n : ℤ, x = (r : ℤ)+2*n := by
  simpa only [source, residues_checked] using integer_domain_cover [1] 2 (by norm_num) x
noncomputable def charts (r : ℕ) : Polynomial ℤ := 0
theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues [1] 2) :
    source.comp (C (r : ℤ)+C (2 : ℤ)*X) = C (2 : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues [1] 2).toList.map charts) ↔ f ∈ [] := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues [1] 2).toList.map charts) = 0 := by
  rw [familyGcd_congr _ [] family_members_checked]
  norm_num [familyGcd]
theorem domain_gcd_checked (q : ℕ) : q ∣ 0 ↔ ∀ x : ℤ, IntegralAt source 2 x →
    (q : ℤ) ∣ quotientValue source 2 x := by
  have h := domain_divisors_iff [1] 2 q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
theorem obstruction_checked (x : ℤ) (hx : IntegralAt source 2 x) :
    ¬ PowerFree 2 (quotientValue source 2 x) := by
  intro h
  apply h 2 (by norm_num)
  have hd := (domain_gcd_checked (2^2)).mp (by norm_num : 2^2 ∣ 0)
  simpa only [Nat.cast_pow] using hd x hx
end IntegerValued_ef8a3818a93cb190
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_ba5ee6bd518c9734
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0]
theorem source_checked : source = 0 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 0 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 0 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := 0
theorem rational_source_checked : rationalSource * C (1 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 1 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 1 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (1 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 1 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (1 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 1 x := by
  apply (integral_everywhere_iff source 1).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 0 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 1 x := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 0 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 1 n := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem obstruction_checked (x : ℤ) (hx : IntegralAt source 1 x) :
    ¬ PowerFree 2 (quotientValue source 1 x) := by
  intro h
  apply h 2 (by norm_num)
  have hd := (domain_gcd_checked (2^2)).mp (by norm_num : 2^2 ∣ 0)
  simpa only [Nat.cast_pow] using hd x
end IntegerValued_ba5ee6bd518c9734
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_ab809885b2bb7446
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [-12]
theorem source_checked : source = C (-12) := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 0 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 12 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((-12 : ℚ)/1)
theorem rational_source_checked : rationalSource * C (1 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 1 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 1 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (1 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 1 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (1 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 1 x := by
  apply (integral_everywhere_iff source 1).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 12 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 1 x := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 12 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 1 n := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem obstruction_checked (x : ℤ) (hx : IntegralAt source 1 x) :
    ¬ PowerFree 2 (quotientValue source 1 x) := by
  intro h
  apply h 2 (by norm_num)
  have hd := (domain_gcd_checked (2^2)).mp (by norm_num : 2^2 ∣ 12)
  simpa only [Nat.cast_pow] using hd x
end IntegerValued_ab809885b2bb7446
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_69ad59ef09c6b25b
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [-12]
theorem source_checked : source = C (-12) := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 0 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 12 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((-12 : ℚ)/1)
theorem rational_source_checked : rationalSource * C (1 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 1 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 1 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (1 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 1 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (1 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 1 x := by
  apply (integral_everywhere_iff source 1).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 12 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 1 x := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 12 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 1 n := by
  have hL : 1 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 1 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem power_free_gcd_checked : PowerFree 3 (12 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 12 := by
    have hc : ((p^3 : ℕ) : ℤ) ∣ (12 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 12 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hd'
  have hf : ([2, 2, 3] : List ℕ).Perm (12 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 12 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  all_goals norm_num at hd
theorem admissible_checked : QuotientAdmissible source 1 3 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 1 x → (p : ℤ)^3 ∣ quotientValue source 1 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^3)).mpr (by intro x; simpa only [Nat.cast_pow] using hu x (integral_checked x))
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_69ad59ef09c6b25b
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_f4759b5897be50d9
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, -5040, 13068, -13132, 6769, -1960, 322, -28, 1]
theorem source_checked : source = C (-5040) * X + C (13068) * X^2 + C (-13132) * X^3 + C (6769) * X^4 + C (-1960) * X^5 + C (322) * X^6 + C (-28) * X^7 + C (1) * X^8 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 8 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 40320 := by
  rw [← windowGcd_eq_fixedDivisor source 8 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((-1 : ℚ)/8) * X + C ((363 : ℚ)/1120) * X^2 + C ((-469 : ℚ)/1440) * X^3 + C ((967 : ℚ)/5760) * X^4 + C ((-7 : ℚ)/144) * X^5 + C ((23 : ℚ)/2880) * X^6 + C ((-1 : ℚ)/1440) * X^7 + C ((1 : ℚ)/40320) * X^8
theorem rational_source_checked : rationalSource * C (40320 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 40320 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 40320 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (40320 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 40320 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (40320 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 40320 x := by
  apply (integral_everywhere_iff source 40320).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 40320 x := by
  have hL : 40320 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 40320 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 40320 n := by
  have hL : 40320 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 40320 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 40320 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 40320 x → (p : ℤ)^2 ∣ quotientValue source 40320 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by intro x; simpa only [Nat.cast_pow] using hu x (integral_checked x))
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_f4759b5897be50d9
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace IntegerValued_b2c9dc5143e0caad
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial [0, -1307674368000, 4339163001600, -6165817614720, 5056995703824, -2706813345600, 1009672107080, -272803210680, 54631129553, -8207628000, 928095740, -78558480, 4899622, -218400, 6580, -120, 1]
theorem source_checked : source = C (-1307674368000) * X + C (4339163001600) * X^2 + C (-6165817614720) * X^3 + C (5056995703824) * X^4 + C (-2706813345600) * X^5 + C (1009672107080) * X^6 + C (-272803210680) * X^7 + C (54631129553) * X^8 + C (-8207628000) * X^9 + C (928095740) * X^10 + C (-78558480) * X^11 + C (4899622) * X^12 + C (-218400) * X^13 + C (6580) * X^14 + C (-120) * X^15 + C (1) * X^16 := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ 16 := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = 20922789888000 := by
  rw [← windowGcd_eq_fixedDivisor source 16 degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
noncomputable def rationalSource : Polynomial ℚ := C ((-1 : ℚ)/16) * X + C ((1195757 : ℚ)/5765760) * X^2 + C ((-13215487 : ℚ)/44844800) * X^3 + C ((35118025721 : ℚ)/145297152000) * X^4 + C ((-2065639 : ℚ)/15966720) * X^5 + C ((277382447 : ℚ)/5748019200) * X^6 + C ((-2271089 : ℚ)/174182400) * X^7 + C ((54576553 : ℚ)/20901888000) * X^8 + C ((-4783 : ℚ)/12192768) * X^9 + C ((324509 : ℚ)/7315660800) * X^10 + C ((-109 : ℚ)/29030400) * X^11 + C ((26921 : ℚ)/114960384000) * X^12 + C ((-1 : ℚ)/95800320) * X^13 + C ((47 : ℚ)/149448499200) * X^14 + C ((-1 : ℚ)/174356582400) * X^15 + C ((1 : ℚ)/20922789888000) * X^16
theorem rational_source_checked : rationalSource * C (20922789888000 : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source 20922789888000 x) :
    rationalSource.eval (x : ℚ) = (quotientValue source 20922789888000 x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * (20922789888000 : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source 20922789888000 (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : (20922789888000 : ℚ) ≠ 0)).mpr h
theorem integral_checked (x : ℤ) : IntegralAt source 20922789888000 x := by
  apply (integral_everywhere_iff source 20922789888000).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source 20922789888000 x := by
  have hL : 20922789888000 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source 20922789888000 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem natural_gcd_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source 20922789888000 n := by
  have hL : 20922789888000 ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source 20922789888000 q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
theorem power_free_gcd_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : QuotientAdmissible source 20922789888000 2 := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source 20922789888000 x → (p : ℤ)^2 ∣ quotientValue source 20922789888000 x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  have hd := (domain_gcd_checked (p^2)).mpr (by intro x; simpa only [Nat.cast_pow] using hu x (integral_checked x))
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
end IntegerValued_b2c9dc5143e0caad

#print axioms IntegerValued_7a9cbb462a38d9f6.source_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.degree_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.numerator_gcd_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.rational_source_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.rational_value_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.integral_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.domain_gcd_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.natural_gcd_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.power_free_gcd_checked
#print axioms IntegerValued_7a9cbb462a38d9f6.admissible_checked
#print axioms IntegerValued_57491d3f649219ed.source_checked
#print axioms IntegerValued_57491d3f649219ed.degree_checked
#print axioms IntegerValued_57491d3f649219ed.numerator_gcd_checked
#print axioms IntegerValued_57491d3f649219ed.rational_source_checked
#print axioms IntegerValued_57491d3f649219ed.rational_value_checked
#print axioms IntegerValued_57491d3f649219ed.residues_checked
#print axioms IntegerValued_57491d3f649219ed.domain_checked
#print axioms IntegerValued_57491d3f649219ed.chart0_checked
#print axioms IntegerValued_57491d3f649219ed.chart0_quotient
#print axioms IntegerValued_57491d3f649219ed.chart0_gcd
#print axioms IntegerValued_57491d3f649219ed.charts_checked
#print axioms IntegerValued_57491d3f649219ed.family_members_checked
#print axioms IntegerValued_57491d3f649219ed.family_gcd_checked
#print axioms IntegerValued_57491d3f649219ed.domain_gcd_checked
#print axioms IntegerValued_57491d3f649219ed.power_free_gcd_checked
#print axioms IntegerValued_57491d3f649219ed.admissible_checked
#print axioms IntegerValued_d2c4a662dd8986a0.source_checked
#print axioms IntegerValued_d2c4a662dd8986a0.degree_checked
#print axioms IntegerValued_d2c4a662dd8986a0.numerator_gcd_checked
#print axioms IntegerValued_d2c4a662dd8986a0.rational_source_checked
#print axioms IntegerValued_d2c4a662dd8986a0.rational_value_checked
#print axioms IntegerValued_d2c4a662dd8986a0.residues_checked
#print axioms IntegerValued_d2c4a662dd8986a0.domain_checked
#print axioms IntegerValued_d2c4a662dd8986a0.chart0_checked
#print axioms IntegerValued_d2c4a662dd8986a0.chart0_quotient
#print axioms IntegerValued_d2c4a662dd8986a0.chart0_gcd
#print axioms IntegerValued_d2c4a662dd8986a0.charts_checked
#print axioms IntegerValued_d2c4a662dd8986a0.family_members_checked
#print axioms IntegerValued_d2c4a662dd8986a0.family_gcd_checked
#print axioms IntegerValued_d2c4a662dd8986a0.domain_gcd_checked
#print axioms IntegerValued_d2c4a662dd8986a0.obstruction_checked
#print axioms IntegerValued_656db630d4da80c7.source_checked
#print axioms IntegerValued_656db630d4da80c7.degree_checked
#print axioms IntegerValued_656db630d4da80c7.numerator_gcd_checked
#print axioms IntegerValued_656db630d4da80c7.rational_source_checked
#print axioms IntegerValued_656db630d4da80c7.rational_value_checked
#print axioms IntegerValued_656db630d4da80c7.residues_checked
#print axioms IntegerValued_656db630d4da80c7.domain_checked
#print axioms IntegerValued_656db630d4da80c7.chart0_checked
#print axioms IntegerValued_656db630d4da80c7.chart0_quotient
#print axioms IntegerValued_656db630d4da80c7.chart0_gcd
#print axioms IntegerValued_656db630d4da80c7.chart1_checked
#print axioms IntegerValued_656db630d4da80c7.chart1_quotient
#print axioms IntegerValued_656db630d4da80c7.chart1_gcd
#print axioms IntegerValued_656db630d4da80c7.chart2_checked
#print axioms IntegerValued_656db630d4da80c7.chart2_quotient
#print axioms IntegerValued_656db630d4da80c7.chart2_gcd
#print axioms IntegerValued_656db630d4da80c7.chart3_checked
#print axioms IntegerValued_656db630d4da80c7.chart3_quotient
#print axioms IntegerValued_656db630d4da80c7.chart3_gcd
#print axioms IntegerValued_656db630d4da80c7.charts_checked
#print axioms IntegerValued_656db630d4da80c7.family_members_checked
#print axioms IntegerValued_656db630d4da80c7.family_gcd_checked
#print axioms IntegerValued_656db630d4da80c7.domain_gcd_checked
#print axioms IntegerValued_656db630d4da80c7.power_free_gcd_checked
#print axioms IntegerValued_656db630d4da80c7.admissible_checked
#print axioms IntegerValued_0425aa5cdbec4806.source_checked
#print axioms IntegerValued_0425aa5cdbec4806.degree_checked
#print axioms IntegerValued_0425aa5cdbec4806.numerator_gcd_checked
#print axioms IntegerValued_0425aa5cdbec4806.rational_source_checked
#print axioms IntegerValued_0425aa5cdbec4806.rational_value_checked
#print axioms IntegerValued_0425aa5cdbec4806.residues_checked
#print axioms IntegerValued_0425aa5cdbec4806.domain_checked
#print axioms IntegerValued_0425aa5cdbec4806.chart0_checked
#print axioms IntegerValued_0425aa5cdbec4806.chart0_quotient
#print axioms IntegerValued_0425aa5cdbec4806.chart0_gcd
#print axioms IntegerValued_0425aa5cdbec4806.charts_checked
#print axioms IntegerValued_0425aa5cdbec4806.family_members_checked
#print axioms IntegerValued_0425aa5cdbec4806.family_gcd_checked
#print axioms IntegerValued_0425aa5cdbec4806.domain_gcd_checked
#print axioms IntegerValued_0425aa5cdbec4806.power_free_gcd_checked
#print axioms IntegerValued_0425aa5cdbec4806.admissible_checked
#print axioms IntegerValued_9163a87c6a6bca50.source_checked
#print axioms IntegerValued_9163a87c6a6bca50.degree_checked
#print axioms IntegerValued_9163a87c6a6bca50.numerator_gcd_checked
#print axioms IntegerValued_9163a87c6a6bca50.rational_source_checked
#print axioms IntegerValued_9163a87c6a6bca50.rational_value_checked
#print axioms IntegerValued_9163a87c6a6bca50.residues_checked
#print axioms IntegerValued_9163a87c6a6bca50.domain_checked
#print axioms IntegerValued_9163a87c6a6bca50.chart0_checked
#print axioms IntegerValued_9163a87c6a6bca50.chart0_quotient
#print axioms IntegerValued_9163a87c6a6bca50.chart0_gcd
#print axioms IntegerValued_9163a87c6a6bca50.charts_checked
#print axioms IntegerValued_9163a87c6a6bca50.family_members_checked
#print axioms IntegerValued_9163a87c6a6bca50.family_gcd_checked
#print axioms IntegerValued_9163a87c6a6bca50.domain_gcd_checked
#print axioms IntegerValued_9163a87c6a6bca50.obstruction_checked
#print axioms IntegerValued_817cd37305b375fe.source_checked
#print axioms IntegerValued_817cd37305b375fe.degree_checked
#print axioms IntegerValued_817cd37305b375fe.numerator_gcd_checked
#print axioms IntegerValued_817cd37305b375fe.rational_source_checked
#print axioms IntegerValued_817cd37305b375fe.rational_value_checked
#print axioms IntegerValued_817cd37305b375fe.residues_checked
#print axioms IntegerValued_817cd37305b375fe.domain_checked
#print axioms IntegerValued_817cd37305b375fe.chart0_checked
#print axioms IntegerValued_817cd37305b375fe.chart0_quotient
#print axioms IntegerValued_817cd37305b375fe.chart0_gcd
#print axioms IntegerValued_817cd37305b375fe.charts_checked
#print axioms IntegerValued_817cd37305b375fe.family_members_checked
#print axioms IntegerValued_817cd37305b375fe.family_gcd_checked
#print axioms IntegerValued_817cd37305b375fe.domain_gcd_checked
#print axioms IntegerValued_817cd37305b375fe.power_free_gcd_checked
#print axioms IntegerValued_817cd37305b375fe.admissible_checked
#print axioms IntegerValued_ef8a3818a93cb190.source_checked
#print axioms IntegerValued_ef8a3818a93cb190.degree_checked
#print axioms IntegerValued_ef8a3818a93cb190.numerator_gcd_checked
#print axioms IntegerValued_ef8a3818a93cb190.rational_source_checked
#print axioms IntegerValued_ef8a3818a93cb190.rational_value_checked
#print axioms IntegerValued_ef8a3818a93cb190.residues_checked
#print axioms IntegerValued_ef8a3818a93cb190.domain_checked
#print axioms IntegerValued_ef8a3818a93cb190.charts_checked
#print axioms IntegerValued_ef8a3818a93cb190.family_members_checked
#print axioms IntegerValued_ef8a3818a93cb190.family_gcd_checked
#print axioms IntegerValued_ef8a3818a93cb190.domain_gcd_checked
#print axioms IntegerValued_ef8a3818a93cb190.obstruction_checked
#print axioms IntegerValued_ba5ee6bd518c9734.source_checked
#print axioms IntegerValued_ba5ee6bd518c9734.degree_checked
#print axioms IntegerValued_ba5ee6bd518c9734.numerator_gcd_checked
#print axioms IntegerValued_ba5ee6bd518c9734.rational_source_checked
#print axioms IntegerValued_ba5ee6bd518c9734.rational_value_checked
#print axioms IntegerValued_ba5ee6bd518c9734.integral_checked
#print axioms IntegerValued_ba5ee6bd518c9734.domain_gcd_checked
#print axioms IntegerValued_ba5ee6bd518c9734.natural_gcd_checked
#print axioms IntegerValued_ba5ee6bd518c9734.obstruction_checked
#print axioms IntegerValued_ab809885b2bb7446.source_checked
#print axioms IntegerValued_ab809885b2bb7446.degree_checked
#print axioms IntegerValued_ab809885b2bb7446.numerator_gcd_checked
#print axioms IntegerValued_ab809885b2bb7446.rational_source_checked
#print axioms IntegerValued_ab809885b2bb7446.rational_value_checked
#print axioms IntegerValued_ab809885b2bb7446.integral_checked
#print axioms IntegerValued_ab809885b2bb7446.domain_gcd_checked
#print axioms IntegerValued_ab809885b2bb7446.natural_gcd_checked
#print axioms IntegerValued_ab809885b2bb7446.obstruction_checked
#print axioms IntegerValued_69ad59ef09c6b25b.source_checked
#print axioms IntegerValued_69ad59ef09c6b25b.degree_checked
#print axioms IntegerValued_69ad59ef09c6b25b.numerator_gcd_checked
#print axioms IntegerValued_69ad59ef09c6b25b.rational_source_checked
#print axioms IntegerValued_69ad59ef09c6b25b.rational_value_checked
#print axioms IntegerValued_69ad59ef09c6b25b.integral_checked
#print axioms IntegerValued_69ad59ef09c6b25b.domain_gcd_checked
#print axioms IntegerValued_69ad59ef09c6b25b.natural_gcd_checked
#print axioms IntegerValued_69ad59ef09c6b25b.power_free_gcd_checked
#print axioms IntegerValued_69ad59ef09c6b25b.admissible_checked
#print axioms IntegerValued_f4759b5897be50d9.source_checked
#print axioms IntegerValued_f4759b5897be50d9.degree_checked
#print axioms IntegerValued_f4759b5897be50d9.numerator_gcd_checked
#print axioms IntegerValued_f4759b5897be50d9.rational_source_checked
#print axioms IntegerValued_f4759b5897be50d9.rational_value_checked
#print axioms IntegerValued_f4759b5897be50d9.integral_checked
#print axioms IntegerValued_f4759b5897be50d9.domain_gcd_checked
#print axioms IntegerValued_f4759b5897be50d9.natural_gcd_checked
#print axioms IntegerValued_f4759b5897be50d9.power_free_gcd_checked
#print axioms IntegerValued_f4759b5897be50d9.admissible_checked
#print axioms IntegerValued_b2c9dc5143e0caad.source_checked
#print axioms IntegerValued_b2c9dc5143e0caad.degree_checked
#print axioms IntegerValued_b2c9dc5143e0caad.numerator_gcd_checked
#print axioms IntegerValued_b2c9dc5143e0caad.rational_source_checked
#print axioms IntegerValued_b2c9dc5143e0caad.rational_value_checked
#print axioms IntegerValued_b2c9dc5143e0caad.integral_checked
#print axioms IntegerValued_b2c9dc5143e0caad.domain_gcd_checked
#print axioms IntegerValued_b2c9dc5143e0caad.natural_gcd_checked
#print axioms IntegerValued_b2c9dc5143e0caad.power_free_gcd_checked
#print axioms IntegerValued_b2c9dc5143e0caad.admissible_checked
