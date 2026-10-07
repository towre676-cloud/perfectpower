import PerfectPower.PowerFreeLocal
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_5ee301b35fb707b0
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [1, 0, 0, 0, 1]
noncomputable def source : Polynomial ℤ := C (1) + C (1) * X^4
noncomputable def u : Polynomial ℤ := C (4)
noncomputable def v : Polynomial ℤ := C (-1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 4 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 4 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([2, 2] : List ℕ).Perm (4 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 4 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_5ee301b35fb707b0

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_11a40050adb1e00f
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [4, 0, 0, 0, 1]
noncomputable def source : Polynomial ℤ := C (4) + C (1) * X^4
noncomputable def u : Polynomial ℤ := C (4)
noncomputable def v : Polynomial ℤ := C (-1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 16 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 16 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([2, 2, 2, 2] : List ℕ).Perm (16 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = ({0,2} : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 2 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ ({0,2} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 16 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_11a40050adb1e00f

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_6239627b605a24fb
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [4, 0, 0, 0, 4]
noncomputable def source : Polynomial ℤ := C (4) + C (4) * X^4
noncomputable def u : Polynomial ℤ := C (4)
noncomputable def v : Polynomial ℤ := C (-1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 16 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 16 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([2, 2, 2, 2] : List ℕ).Perm (16 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = ({0,1,2,3} : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 4 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ ({0,1,2,3} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem fixed_divisor_checked (x : ℤ) : ¬ PowerFree 2 (source.eval x) := by
  apply fixed_divisor_obstruction source 2 2 (by norm_num)
  rw [rho_2_checked]
  norm_num

end PerfectPower.PowerFreePacket_6239627b605a24fb

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_1af481b1a9bd3100
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [-3, 0, 2]
noncomputable def source : Polynomial ℤ := C (-3) + C (2) * X^2
noncomputable def u : Polynomial ℤ := C (-2)
noncomputable def v : Polynomial ℤ := C (1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 2 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 6 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 6 2 = ({0,1,2,3} : Finset ℕ) := by
  have hf : ([2, 3] : List ℕ).Perm (6 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 6 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num

end PerfectPower.PowerFreePacket_1af481b1a9bd3100

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_a53eb5427555aa7b
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [3, -3, 0, 1]
noncomputable def source : Polynomial ℤ := C (3) + C (-3) * X + C (1) * X^3
noncomputable def u : Polynomial ℤ := C (9) + C (6) * X
noncomputable def v : Polynomial ℤ := C (4) + C (-3) * X + C (-2) * X^2
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 3 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 15 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 15 3 = ({0,1,2,3,5} : Finset ℕ) := by
  have hf : ([3, 5] : List ℕ).Perm (15 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h
theorem roots_5_checked : rootResidues coefficients 25 = ({7} : Finset ℕ) := by decide
theorem rho_5_checked : rho source (5^2) = 1 := by
  rw [source_polynomial, rho_coefficients, show (5^2 : ℕ) = 25 by norm_num, roots_5_checked]
  decide
theorem roots_5_complete (x : ℤ) : (25 : ℤ) ∣ source.eval x ↔
    (x % 25).toNat ∈ ({7} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 25 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_5_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 15 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · rw [rho_5_checked]; norm_num

end PerfectPower.PowerFreePacket_a53eb5427555aa7b

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_5bbb619f6074e5fa
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [0, -1, 0, 0, 1]
noncomputable def source : Polynomial ℤ := C (-1) * X + C (1) * X^4
noncomputable def u : Polynomial ℤ := C (-16) * X^2
noncomputable def v : Polynomial ℤ := C (-3) + C (4) * X^3
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 3 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 3 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([3] : List ℕ).Perm (3 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = ({0,1} : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 2 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ ({0,1} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = ({0,1,4,7} : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 4 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ ({0,1,4,7} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 3 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_5bbb619f6074e5fa

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_da7536019496d7b4
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [-1, 0, 0, 0, -1]
noncomputable def source : Polynomial ℤ := C (-1) + C (-1) * X^4
noncomputable def u : Polynomial ℤ := C (-4)
noncomputable def v : Polynomial ℤ := C (1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 4 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 4 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([2, 2] : List ℕ).Perm (4 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 4 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_da7536019496d7b4

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_e7bc42e201c1b877
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0, 1]
noncomputable def source : Polynomial ℤ := C (1) + C (1) * X^8
noncomputable def u : Polynomial ℤ := C (8)
noncomputable def v : Polynomial ℤ := C (-1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 8 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 8 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 8 8 = ({0,1,2,3,4,5,6,7,8} : Finset ℕ) := by
  have hf : ([2, 2, 2] : List ℕ).Perm (8 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 4 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^2 : ℕ) = 4 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (4 : ℤ) ∣ source.eval x ↔
    (x % 4).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 4 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 9 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^2 : ℕ) = 9 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (9 : ℤ) ∣ source.eval x ↔
    (x % 9).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 9 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h
theorem roots_5_checked : rootResidues coefficients 25 = (∅ : Finset ℕ) := by decide
theorem rho_5_checked : rho source (5^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (5^2 : ℕ) = 25 by norm_num, roots_5_checked]
  decide
theorem roots_5_complete (x : ℤ) : (25 : ℤ) ∣ source.eval x ↔
    (x % 25).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 25 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_5_checked] at h
theorem roots_7_checked : rootResidues coefficients 49 = (∅ : Finset ℕ) := by decide
theorem rho_7_checked : rho source (7^2) = 0 := by
  rw [source_polynomial, rho_coefficients, show (7^2 : ℕ) = 49 by norm_num, roots_7_checked]
  decide
theorem roots_7_complete (x : ℤ) : (49 : ℤ) ∣ source.eval x ↔
    (x % 49).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 49 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_7_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 8 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime
  · rw [rho_5_checked]; norm_num
  · norm_num at hprime
  · rw [rho_7_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_e7bc42e201c1b877

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_f6da4881d5ba7c10
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [4, 0, 0, 0, 1]
noncomputable def source : Polynomial ℤ := C (4) + C (1) * X^4
noncomputable def u : Polynomial ℤ := C (4)
noncomputable def v : Polynomial ℤ := C (-1) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 4 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 16 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 16 4 = ({0,1,2,3,4} : Finset ℕ) := by
  have hf : ([2, 2, 2, 2] : List ℕ).Perm (16 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      all_goals norm_num
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 8 = (∅ : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^3) = 0 := by
  rw [source_polynomial, rho_coefficients, show (2^3 : ℕ) = 8 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (8 : ℤ) ∣ source.eval x ↔
    (x % 8).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 8 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h
theorem roots_3_checked : rootResidues coefficients 27 = (∅ : Finset ℕ) := by decide
theorem rho_3_checked : rho source (3^3) = 0 := by
  rw [source_polynomial, rho_coefficients, show (3^3 : ℕ) = 27 by norm_num, roots_3_checked]
  decide
theorem roots_3_complete (x : ℤ) : (27 : ℤ) ∣ source.eval x ↔
    (x % 27).toNat ∈ (∅ : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 27 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_3_checked] at h

theorem locally_admissible_checked : LocallyAdmissible source 3 := by
  apply (admissible_iff_finite source u v 16 3 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · norm_num at hprime
  · norm_num at hprime
  · rw [rho_2_checked]; norm_num
  · rw [rho_3_checked]; norm_num
  · norm_num at hprime

end PerfectPower.PowerFreePacket_f6da4881d5ba7c10

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_13063aae1cb59d5d
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [0, 1, 1]
noncomputable def source : Polynomial ℤ := C (1) * X + C (1) * X^2
noncomputable def u : Polynomial ℤ := C (-4)
noncomputable def v : Polynomial ℤ := C (1) + C (2) * X
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 2 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 1 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 1 2 = ({0,1,2} : Finset ℕ) := by
  have hf : ([] : List ℕ).Perm (1 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp


  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
theorem roots_2_checked : rootResidues coefficients 2 = ({0,1} : Finset ℕ) := by decide
theorem rho_2_checked : rho source (2^1) = 2 := by
  rw [source_polynomial, rho_coefficients, show (2^1 : ℕ) = 2 by norm_num, roots_2_checked]
  decide
theorem roots_2_complete (x : ℤ) : (2 : ℤ) ∣ source.eval x ↔
    (x % 2).toNat ∈ ({0,1} : Finset ℕ) := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients 2 (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_2_checked] at h

theorem fixed_divisor_checked (x : ℤ) : ¬ PowerFree 1 (source.eval x) := by
  apply fixed_divisor_obstruction source 2 1 (by norm_num)
  rw [rho_2_checked]
  norm_num

end PerfectPower.PowerFreePacket_13063aae1cb59d5d

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace PerfectPower.PowerFreePacket_211bd412a3bac54a
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := [-1, 1]
noncomputable def source : Polynomial ℤ := C (-1) + C (1) * X
noncomputable def u : Polynomial ℤ := 0
noncomputable def v : Polynomial ℤ := C (1)
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = 1 := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v 1 := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional 1 1 = ({0,1} : Finset ℕ) := by
  have hf : ([] : List ℕ).Perm (1 : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp


  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide

theorem locally_admissible_checked : LocallyAdmissible source 2 := by
  apply (admissible_iff_finite source u v 1 2 bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · norm_num at hprime
  · norm_num at hprime

end PerfectPower.PowerFreePacket_211bd412a3bac54a

#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.source_polynomial
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.degree_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.bezout_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_5ee301b35fb707b0.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.source_polynomial
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.degree_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.bezout_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_11a40050adb1e00f.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.source_polynomial
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.degree_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.bezout_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_6239627b605a24fb.fixed_divisor_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.source_polynomial
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.degree_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.bezout_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_1af481b1a9bd3100.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_5_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.rho_5_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.roots_5_complete
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.source_polynomial
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.degree_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.bezout_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_a53eb5427555aa7b.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.source_polynomial
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.degree_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.bezout_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_5bbb619f6074e5fa.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.source_polynomial
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.degree_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.bezout_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_da7536019496d7b4.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_5_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.rho_5_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_5_complete
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_7_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.rho_7_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.roots_7_complete
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.source_polynomial
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.degree_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.bezout_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_e7bc42e201c1b877.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.roots_3_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.rho_3_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.roots_3_complete
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.source_polynomial
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.degree_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.bezout_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_f6da4881d5ba7c10.locally_admissible_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.roots_2_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.rho_2_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.roots_2_complete
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.source_polynomial
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.degree_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.bezout_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_13063aae1cb59d5d.fixed_divisor_checked
#print axioms PerfectPower.PowerFreePacket_211bd412a3bac54a.source_polynomial
#print axioms PerfectPower.PowerFreePacket_211bd412a3bac54a.degree_checked
#print axioms PerfectPower.PowerFreePacket_211bd412a3bac54a.bezout_checked
#print axioms PerfectPower.PowerFreePacket_211bd412a3bac54a.exceptional_checked
#print axioms PerfectPower.PowerFreePacket_211bd412a3bac54a.locally_admissible_checked
