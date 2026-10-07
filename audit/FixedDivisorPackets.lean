import PerfectPower.FixedDivisor
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_ac20984701b4a871
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (1) + C (2) * X^2 + C (1) * X^4
noncomputable def source : Polynomial ℤ := C (1) + C (2) * X^2 + C (1) * X^4
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 4 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 4 = 1 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 4 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (1 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 1).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 4 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by exact_mod_cast hd
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : LocallyAdmissible source 2 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_ac20984701b4a871
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_e573d0970a80d916
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (4) + C (4) * X^2 + C (1) * X^4
noncomputable def source : Polynomial ℤ := C (4) + C (4) * X^2 + C (1) * X^4
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 4 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 4 = 1 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 4 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (1 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 1).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 4 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by exact_mod_cast hd
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : LocallyAdmissible source 2 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_e573d0970a80d916
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_ed7d46027038d140
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (1) * X^2 + C (-2) * X^3 + C (1) * X^4
noncomputable def source : Polynomial ℤ := C (1) * X^2 + C (-2) * X^3 + C (1) * X^4
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 4 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 4 = 4 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 4 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 4 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (4 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 4).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (0+1*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^2 ∣ 4).trans (universal_checked n)
end FixedDivisor_ed7d46027038d140
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_6e61471d0236089c
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (1) * X^2 + C (-2) * X^3 + C (1) * X^4
noncomputable def source : Polynomial ℤ := C (1) * X^2 + C (-2) * X^3 + C (1) * X^4
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 4 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 4 = 4 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 4 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 4 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (4 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 4).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 4 := by
  rw [← windowGcd_eq_fixedDivisor source 4 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 3 (4 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 4 := by exact_mod_cast hd
  have hpd : p ∣ 4 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hd'
  have hf : ([2, 2] : List ℕ).Perm (4 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 4 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  all_goals norm_num at hd
theorem admissible_checked : LocallyAdmissible source 3 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_6e61471d0236089c
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_81fcf57f2037334a
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-5040) * X + C (13068) * X^2 + C (-13132) * X^3 + C (6769) * X^4 + C (-1960) * X^5 + C (322) * X^6 + C (-28) * X^7 + C (1) * X^8
noncomputable def source : Polynomial ℤ := C (-5040) * X + C (13068) * X^2 + C (-13132) * X^3 + C (6769) * X^4 + C (-1960) * X^5 + C (322) * X^6 + C (-28) * X^7 + C (1) * X^8
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 8 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 8 = 40320 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 40320 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 8 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (40320 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 40320).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 40320 := by
  rw [← windowGcd_eq_fixedDivisor source 8 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 8 (40320 : ℤ) := by
  intro p hp hd
  have hd' : p^8 ∣ 40320 := by exact_mod_cast hd
  have hpd : p ∣ 40320 := (dvd_pow_self p (by norm_num : 8 ≠ 0)).trans hd'
  have hf : ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7] : List ℕ).Perm (40320 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 40320 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hd
theorem admissible_checked : LocallyAdmissible source 8 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_81fcf57f2037334a
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_378be3568e03ce3a
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-1307674368000) * X + C (4339163001600) * X^2 + C (-6165817614720) * X^3 + C (5056995703824) * X^4 + C (-2706813345600) * X^5 + C (1009672107080) * X^6 + C (-272803210680) * X^7 + C (54631129553) * X^8 + C (-8207628000) * X^9 + C (928095740) * X^10 + C (-78558480) * X^11 + C (4899622) * X^12 + C (-218400) * X^13 + C (6580) * X^14 + C (-120) * X^15 + C (1) * X^16
noncomputable def source : Polynomial ℤ := C (-1307674368000) * X + C (4339163001600) * X^2 + C (-6165817614720) * X^3 + C (5056995703824) * X^4 + C (-2706813345600) * X^5 + C (1009672107080) * X^6 + C (-272803210680) * X^7 + C (54631129553) * X^8 + C (-8207628000) * X^9 + C (928095740) * X^10 + C (-78558480) * X^11 + C (4899622) * X^12 + C (-218400) * X^13 + C (6580) * X^14 + C (-120) * X^15 + C (1) * X^16
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 16 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 16 = 20922789888000 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 20922789888000 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 16 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (20922789888000 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 20922789888000).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (0+1*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^2 ∣ 20922789888000).trans (universal_checked n)
end FixedDivisor_378be3568e03ce3a
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_f53fcc18cc212cad
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (1) + C (1) * X^2
noncomputable def source : Polynomial ℤ := C (2) + C (4) * X + C (4) * X^2
theorem pullback_checked : source = original.comp (C (1 : ℤ) + C (2 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 2 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 2 = 2 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 2 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (1+2*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 2 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (2 : ℤ) ∣ original.eval (1+2*n) :=
  (all_divisors_checked 2).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 2 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 2 (2 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 2 := by exact_mod_cast hd
  have hpd : p ∣ 2 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([2] : List ℕ).Perm (2 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 2 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  all_goals norm_num at hd
theorem admissible_checked : LocallyAdmissible source 2 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_f53fcc18cc212cad
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_4d6945cb5de019d2
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (1) + C (1) * X^2
noncomputable def source : Polynomial ℤ := C (2) + C (4) * X + C (4) * X^2
theorem pullback_checked : source = original.comp (C (1 : ℤ) + C (2 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 2 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 2 = 2 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 2 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (1+2*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 2 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (2 : ℤ) ∣ original.eval (1+2*n) :=
  (all_divisors_checked 2).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 1 (original.eval (1+2*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^1 ∣ 2).trans (universal_checked n)
end FixedDivisor_4d6945cb5de019d2
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_1c0f3704ad533d4b
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-3) + C (2) * X^2
noncomputable def source : Polynomial ℤ := C (47) + C (40) * X + C (8) * X^2
theorem pullback_checked : source = original.comp (C (-5 : ℤ) + C (-2 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 2 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 2 = 1 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 1 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (-5+-2*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 2 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (1 : ℤ) ∣ original.eval (-5+-2*n) :=
  (all_divisors_checked 1).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 1 := by
  rw [← windowGcd_eq_fixedDivisor source 2 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 2 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by exact_mod_cast hd
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem admissible_checked : LocallyAdmissible source 2 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_1c0f3704ad533d4b
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_3d284b924a11d4e5
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := 0
noncomputable def source : Polynomial ℤ := 0
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 0 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 0 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (0 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 0).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (0+1*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^2 ∣ 0).trans (universal_checked n)
end FixedDivisor_3d284b924a11d4e5
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_0c9ba219fc8dcf5c
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-12)
noncomputable def source : Polynomial ℤ := C (-12)
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 12 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 12 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (12 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 12).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (0+1*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^2 ∣ 12).trans (universal_checked n)
end FixedDivisor_0c9ba219fc8dcf5c
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_e0d47cc7af3c6d45
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-12)
noncomputable def source : Polynomial ℤ := C (-12)
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 12 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 12 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (12 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 12).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 12 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 3 (12 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 12 := by exact_mod_cast hd
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
theorem admissible_checked : LocallyAdmissible source 3 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_e0d47cc7af3c6d45
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_e6c2279d4aa22682
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (100140049)
noncomputable def source : Polynomial ℤ := C (100140049)
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 100140049 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 100140049 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (100140049 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 100140049).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (0+1*n)) := by
  intro h
  apply h 10007 (by norm_num)
  exact (by norm_num : (10007 : ℤ)^2 ∣ 100140049).trans (universal_checked n)
end FixedDivisor_e6c2279d4aa22682
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_0aa4dacafbf5cd4a
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (100140049)
noncomputable def source : Polynomial ℤ := C (100140049)
theorem pullback_checked : source = original.comp (C (0 : ℤ) + C (1 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 100140049 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 100140049 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (0+1*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (100140049 : ℤ) ∣ original.eval (0+1*n) :=
  (all_divisors_checked 100140049).mp (dvd_refl _) n
theorem fixed_divisor_checked : fixedDivisor source = 100140049 := by
  rw [← windowGcd_eq_fixedDivisor source 0 degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree 3 (100140049 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 100140049 := by exact_mod_cast hd
  have hpd : p ∣ 100140049 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hd'
  have hf : ([10007, 10007] : List ℕ).Perm (100140049 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 100140049 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  all_goals norm_num at hd
theorem admissible_checked : LocallyAdmissible source 3 := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
end FixedDivisor_0aa4dacafbf5cd4a
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FixedDivisor_ec5c7757b84e19c7
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := C (-4) + C (1) * X^2
noncomputable def source : Polynomial ℤ := 0
theorem pullback_checked : source = original.comp (C (2 : ℤ) + C (0 : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ 0 := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source 0 = 0 := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ 0 ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval (2+0*n) := by
  rw [← window_checked, dvd_windowGcd_iff source 0 q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : (0 : ℤ) ∣ original.eval (2+0*n) :=
  (all_divisors_checked 0).mp (dvd_refl _) n
theorem obstruction_checked (n : ℤ) : ¬ PowerFree 2 (original.eval (2+0*n)) := by
  intro h
  apply h 2 (by norm_num)
  exact (by norm_num : (2 : ℤ)^2 ∣ 0).trans (universal_checked n)
end FixedDivisor_ec5c7757b84e19c7
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_f53e12f0aff14419
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (4) + C (4) * X^2 + C (1) * X^4
noncomputable def repeated : Polynomial ℤ := C (2) + C (1) * X^2
noncomputable def cofactor : Polynomial ℤ := C (1)
def coefficients : List ℤ := [2, 0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = (∅ : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ (∅ : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ (∅ : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
end RepeatedPowerFree_f53e12f0aff14419
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_65e78396986ffc37
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (1) + C (2) * X^2 + C (1) * X^4
noncomputable def repeated : Polynomial ℤ := C (1) + C (1) * X^2
noncomputable def cofactor : Polynomial ℤ := C (1)
def coefficients : List ℤ := [1, 0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({0} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({0} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem constant_0_checked : PowerFree 2 (1 : ℤ) := by
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
theorem candidate_0_checked : PowerFree 2 (source.eval (0 : ℤ)) := by
  have he : source.eval (0 : ℤ) = 1 := by norm_num [source]
  rw [he]
  exact constant_0_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ ({0} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl
    · exact candidate_0_checked
end RepeatedPowerFree_65e78396986ffc37
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_687538ae9b1de318
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (1) * X^2
noncomputable def repeated : Polynomial ℤ := C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (1)
def coefficients : List ℤ := [0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({-1,1} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({-1,1} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem constant_0_checked : PowerFree 2 (1 : ℤ) := by
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
theorem candidate_0_checked : PowerFree 2 (source.eval (-1 : ℤ)) := by
  have he : source.eval (-1 : ℤ) = 1 := by norm_num [source]
  rw [he]
  exact constant_0_checked
theorem constant_1_checked : PowerFree 2 (1 : ℤ) := by
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
theorem candidate_1_checked : PowerFree 2 (source.eval (1 : ℤ)) := by
  have he : source.eval (1 : ℤ) = 1 := by norm_num [source]
  rw [he]
  exact constant_1_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ ({-1,1} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · decide
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl | rfl
    · exact candidate_0_checked
    · exact candidate_1_checked
end RepeatedPowerFree_687538ae9b1de318
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_6138797e80d4e3ce
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (-1) * X^2
noncomputable def repeated : Polynomial ℤ := C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (-1)
def coefficients : List ℤ := [0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({-1,1} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({-1,1} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem constant_0_checked : PowerFree 2 (-1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (-1 : ℤ) := by simpa only [Nat.cast_pow] using hd
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
theorem candidate_0_checked : PowerFree 2 (source.eval (-1 : ℤ)) := by
  have he : source.eval (-1 : ℤ) = -1 := by norm_num [source]
  rw [he]
  exact constant_0_checked
theorem constant_1_checked : PowerFree 2 (-1 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 1 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (-1 : ℤ) := by simpa only [Nat.cast_pow] using hd
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
theorem candidate_1_checked : PowerFree 2 (source.eval (1 : ℤ)) := by
  have he : source.eval (1 : ℤ) = -1 := by norm_num [source]
  rw [he]
  exact constant_1_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ ({-1,1} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · decide
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl | rfl
    · exact candidate_0_checked
    · exact candidate_1_checked
end RepeatedPowerFree_6138797e80d4e3ce
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_2b3c1063d250b06f
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (3) * X^2
noncomputable def repeated : Polynomial ℤ := C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (3)
def coefficients : List ℤ := [0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({-1,1} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({-1,1} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem constant_0_checked : PowerFree 2 (3 : ℤ) := by
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
theorem candidate_0_checked : PowerFree 2 (source.eval (-1 : ℤ)) := by
  have he : source.eval (-1 : ℤ) = 3 := by norm_num [source]
  rw [he]
  exact constant_0_checked
theorem constant_1_checked : PowerFree 2 (3 : ℤ) := by
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
theorem candidate_1_checked : PowerFree 2 (source.eval (1 : ℤ)) := by
  have he : source.eval (1 : ℤ) = 3 := by norm_num [source]
  rw [he]
  exact constant_1_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ ({-1,1} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · decide
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl | rfl
    · exact candidate_0_checked
    · exact candidate_1_checked
end RepeatedPowerFree_2b3c1063d250b06f
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_1501d126df4bd327
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (12) * X^2
noncomputable def repeated : Polynomial ℤ := C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (12)
def coefficients : List ℤ := [0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({-1,1} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({-1,1} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem candidate_0_checked : ¬ PowerFree 2 (source.eval (-1 : ℤ)) := by
  intro hx
  apply hx 2 (by norm_num)
  norm_num [source]
theorem candidate_1_checked : ¬ PowerFree 2 (source.eval (1 : ℤ)) := by
  intro hx
  apply hx 2 (by norm_num)
  norm_num [source]
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ (∅ : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · exact False.elim (candidate_0_checked hx)
    · exact False.elim (candidate_1_checked hx)
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
end RepeatedPowerFree_1501d126df4bd327
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_9d217fd78a01ba32
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (1) * X^2 + C (1) * X^3
noncomputable def repeated : Polynomial ℤ := C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (1) + C (1) * X
def coefficients : List ℤ := [0, 1]
theorem factorization_checked : source = repeated^2*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({-1,1} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 2 (source.eval x)) : x ∈ ({-1,1} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 2 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem candidate_0_checked : ¬ PowerFree 2 (source.eval (-1 : ℤ)) := by
  intro hx
  apply hx 2 (by norm_num)
  norm_num [source]
theorem constant_1_checked : PowerFree 2 (2 : ℤ) := by
  intro p hp hd
  have hd' : p^2 ∣ 2 := by
    have hc : ((p^2 : ℕ) : ℤ) ∣ (2 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 2 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hd'
  have hf : ([2] : List ℕ).Perm (2 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      all_goals norm_num
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 2 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  all_goals norm_num at hd
theorem candidate_1_checked : PowerFree 2 (source.eval (1 : ℤ)) := by
  have he : source.eval (1 : ℤ) = 2 := by norm_num [source]
  rw [he]
  exact constant_1_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 2 (source.eval x) ↔ x ∈ ({1} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · exact False.elim (candidate_0_checked hx)
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl
    · exact candidate_1_checked
end RepeatedPowerFree_9d217fd78a01ba32
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RepeatedPowerFree_c7b4c8ae24fc4a6b
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := C (-8) + C (12) * X + C (-6) * X^2 + C (1) * X^3
noncomputable def repeated : Polynomial ℤ := C (-2) + C (1) * X
noncomputable def cofactor : Polynomial ℤ := C (1)
def coefficients : List ℤ := [-2, 1]
theorem factorization_checked : source = repeated^3*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = ({1,3} : Finset ℤ) := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree 3 (source.eval x)) : x ∈ ({1,3} : Finset ℤ) := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients 3 factorization_checked factor_source_checked (by decide) (by decide) x hx
theorem constant_0_checked : PowerFree 3 (-1 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 1 := by
    have hc : ((p^3 : ℕ) : ℤ) ∣ (-1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem candidate_0_checked : PowerFree 3 (source.eval (1 : ℤ)) := by
  have he : source.eval (1 : ℤ) = -1 := by norm_num [source]
  rw [he]
  exact constant_0_checked
theorem constant_1_checked : PowerFree 3 (1 : ℤ) := by
  intro p hp hd
  have hd' : p^3 ∣ 1 := by
    have hc : ((p^3 : ℕ) : ℤ) ∣ (1 : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ 1 := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hd'
  have hf : ([] : List ℕ).Perm (1 : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : 1 ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
theorem candidate_1_checked : PowerFree 3 (source.eval (3 : ℤ)) := by
  have he : source.eval (3 : ℤ) = 1 := by norm_num [source]
  rw [he]
  exact constant_1_checked
theorem all_solutions_checked (x : ℤ) : PowerFree 3 (source.eval x) ↔ x ∈ ({1,3} : Finset ℤ) := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
    rcases hc with rfl | rfl
    · decide
    · decide
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx
    rcases hx with rfl | rfl
    · exact candidate_0_checked
    · exact candidate_1_checked
end RepeatedPowerFree_c7b4c8ae24fc4a6b

#print axioms FixedDivisor_ac20984701b4a871.pullback_checked
#print axioms FixedDivisor_ac20984701b4a871.degree_bound_checked
#print axioms FixedDivisor_ac20984701b4a871.window_checked
#print axioms FixedDivisor_ac20984701b4a871.all_divisors_checked
#print axioms FixedDivisor_ac20984701b4a871.universal_checked
#print axioms FixedDivisor_ac20984701b4a871.fixed_divisor_checked
#print axioms FixedDivisor_ac20984701b4a871.power_free_checked
#print axioms FixedDivisor_ac20984701b4a871.admissible_checked
#print axioms FixedDivisor_e573d0970a80d916.pullback_checked
#print axioms FixedDivisor_e573d0970a80d916.degree_bound_checked
#print axioms FixedDivisor_e573d0970a80d916.window_checked
#print axioms FixedDivisor_e573d0970a80d916.all_divisors_checked
#print axioms FixedDivisor_e573d0970a80d916.universal_checked
#print axioms FixedDivisor_e573d0970a80d916.fixed_divisor_checked
#print axioms FixedDivisor_e573d0970a80d916.power_free_checked
#print axioms FixedDivisor_e573d0970a80d916.admissible_checked
#print axioms FixedDivisor_ed7d46027038d140.pullback_checked
#print axioms FixedDivisor_ed7d46027038d140.degree_bound_checked
#print axioms FixedDivisor_ed7d46027038d140.window_checked
#print axioms FixedDivisor_ed7d46027038d140.all_divisors_checked
#print axioms FixedDivisor_ed7d46027038d140.universal_checked
#print axioms FixedDivisor_ed7d46027038d140.obstruction_checked
#print axioms FixedDivisor_6e61471d0236089c.pullback_checked
#print axioms FixedDivisor_6e61471d0236089c.degree_bound_checked
#print axioms FixedDivisor_6e61471d0236089c.window_checked
#print axioms FixedDivisor_6e61471d0236089c.all_divisors_checked
#print axioms FixedDivisor_6e61471d0236089c.universal_checked
#print axioms FixedDivisor_6e61471d0236089c.fixed_divisor_checked
#print axioms FixedDivisor_6e61471d0236089c.power_free_checked
#print axioms FixedDivisor_6e61471d0236089c.admissible_checked
#print axioms FixedDivisor_81fcf57f2037334a.pullback_checked
#print axioms FixedDivisor_81fcf57f2037334a.degree_bound_checked
#print axioms FixedDivisor_81fcf57f2037334a.window_checked
#print axioms FixedDivisor_81fcf57f2037334a.all_divisors_checked
#print axioms FixedDivisor_81fcf57f2037334a.universal_checked
#print axioms FixedDivisor_81fcf57f2037334a.fixed_divisor_checked
#print axioms FixedDivisor_81fcf57f2037334a.power_free_checked
#print axioms FixedDivisor_81fcf57f2037334a.admissible_checked
#print axioms FixedDivisor_378be3568e03ce3a.pullback_checked
#print axioms FixedDivisor_378be3568e03ce3a.degree_bound_checked
#print axioms FixedDivisor_378be3568e03ce3a.window_checked
#print axioms FixedDivisor_378be3568e03ce3a.all_divisors_checked
#print axioms FixedDivisor_378be3568e03ce3a.universal_checked
#print axioms FixedDivisor_378be3568e03ce3a.obstruction_checked
#print axioms FixedDivisor_f53fcc18cc212cad.pullback_checked
#print axioms FixedDivisor_f53fcc18cc212cad.degree_bound_checked
#print axioms FixedDivisor_f53fcc18cc212cad.window_checked
#print axioms FixedDivisor_f53fcc18cc212cad.all_divisors_checked
#print axioms FixedDivisor_f53fcc18cc212cad.universal_checked
#print axioms FixedDivisor_f53fcc18cc212cad.fixed_divisor_checked
#print axioms FixedDivisor_f53fcc18cc212cad.power_free_checked
#print axioms FixedDivisor_f53fcc18cc212cad.admissible_checked
#print axioms FixedDivisor_4d6945cb5de019d2.pullback_checked
#print axioms FixedDivisor_4d6945cb5de019d2.degree_bound_checked
#print axioms FixedDivisor_4d6945cb5de019d2.window_checked
#print axioms FixedDivisor_4d6945cb5de019d2.all_divisors_checked
#print axioms FixedDivisor_4d6945cb5de019d2.universal_checked
#print axioms FixedDivisor_4d6945cb5de019d2.obstruction_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.pullback_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.degree_bound_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.window_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.all_divisors_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.universal_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.fixed_divisor_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.power_free_checked
#print axioms FixedDivisor_1c0f3704ad533d4b.admissible_checked
#print axioms FixedDivisor_3d284b924a11d4e5.pullback_checked
#print axioms FixedDivisor_3d284b924a11d4e5.degree_bound_checked
#print axioms FixedDivisor_3d284b924a11d4e5.window_checked
#print axioms FixedDivisor_3d284b924a11d4e5.all_divisors_checked
#print axioms FixedDivisor_3d284b924a11d4e5.universal_checked
#print axioms FixedDivisor_3d284b924a11d4e5.obstruction_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.pullback_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.degree_bound_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.window_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.all_divisors_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.universal_checked
#print axioms FixedDivisor_0c9ba219fc8dcf5c.obstruction_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.pullback_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.degree_bound_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.window_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.all_divisors_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.universal_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.fixed_divisor_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.power_free_checked
#print axioms FixedDivisor_e0d47cc7af3c6d45.admissible_checked
#print axioms FixedDivisor_e6c2279d4aa22682.pullback_checked
#print axioms FixedDivisor_e6c2279d4aa22682.degree_bound_checked
#print axioms FixedDivisor_e6c2279d4aa22682.window_checked
#print axioms FixedDivisor_e6c2279d4aa22682.all_divisors_checked
#print axioms FixedDivisor_e6c2279d4aa22682.universal_checked
#print axioms FixedDivisor_e6c2279d4aa22682.obstruction_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.pullback_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.degree_bound_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.window_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.all_divisors_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.universal_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.fixed_divisor_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.power_free_checked
#print axioms FixedDivisor_0aa4dacafbf5cd4a.admissible_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.pullback_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.degree_bound_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.window_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.all_divisors_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.universal_checked
#print axioms FixedDivisor_ec5c7757b84e19c7.obstruction_checked
#print axioms RepeatedPowerFree_f53e12f0aff14419.factorization_checked
#print axioms RepeatedPowerFree_f53e12f0aff14419.factor_source_checked
#print axioms RepeatedPowerFree_f53e12f0aff14419.candidates_checked
#print axioms RepeatedPowerFree_f53e12f0aff14419.finite_reduction_checked
#print axioms RepeatedPowerFree_f53e12f0aff14419.all_solutions_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.factorization_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.factor_source_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.candidates_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.finite_reduction_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.candidate_0_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.constant_0_checked
#print axioms RepeatedPowerFree_65e78396986ffc37.all_solutions_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.factorization_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.factor_source_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.candidates_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.finite_reduction_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.candidate_0_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.constant_0_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.candidate_1_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.constant_1_checked
#print axioms RepeatedPowerFree_687538ae9b1de318.all_solutions_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.factorization_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.factor_source_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.candidates_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.finite_reduction_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.candidate_0_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.constant_0_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.candidate_1_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.constant_1_checked
#print axioms RepeatedPowerFree_6138797e80d4e3ce.all_solutions_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.factorization_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.factor_source_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.candidates_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.finite_reduction_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.candidate_0_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.constant_0_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.candidate_1_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.constant_1_checked
#print axioms RepeatedPowerFree_2b3c1063d250b06f.all_solutions_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.factorization_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.factor_source_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.candidates_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.finite_reduction_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.candidate_0_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.candidate_1_checked
#print axioms RepeatedPowerFree_1501d126df4bd327.all_solutions_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.factorization_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.factor_source_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.candidates_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.finite_reduction_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.candidate_0_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.candidate_1_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.constant_1_checked
#print axioms RepeatedPowerFree_9d217fd78a01ba32.all_solutions_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.factorization_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.factor_source_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.candidates_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.finite_reduction_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.candidate_0_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.constant_0_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.candidate_1_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.constant_1_checked
#print axioms RepeatedPowerFree_c7b4c8ae24fc4a6b.all_solutions_checked
