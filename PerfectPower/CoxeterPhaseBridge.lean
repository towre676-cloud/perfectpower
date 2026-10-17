import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring

/-!
# The integral Coxeter--cyclotomic bridge

The displayed E₈ Cartan lattice is *integrally* conjugate to the
multiplication-by-X companion module for
`Phi30 = X^8 + X^7 - X^5 - X^4 - X^3 + X + 1`.
The certificate supplies both integral inverse matrices, intertwines the
operators in every power, and transports the actual Cartan bilinear form.
Thus it does not identify unrelated sets merely because their cardinalities
agree. All concrete certificates are reduced by Lean's kernel; no native
oracle, admitted proof, or new axiom is used.

The reflection convention agrees with `python/perfectpower/e8_periods.py`:
`s_1` acts first, followed successively by `s_2,...,s_8`.
-/

namespace PerfectPower.CoxeterPhaseBridge

open Matrix

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev M8 := Matrix (Fin 8) (Fin 8) ℤ

/-- The E₈ Cartan form in the supplied simple-root basis. -/
def cartan : M8 :=
![
  ![2, 0, -1, 0, 0, 0, 0, 0],
  ![0, 2, 0, -1, 0, 0, 0, 0],
  ![-1, 0, 2, -1, 0, 0, 0, 0],
  ![0, -1, -1, 2, -1, 0, 0, 0],
  ![0, 0, 0, -1, 2, -1, 0, 0],
  ![0, 0, 0, 0, -1, 2, -1, 0],
  ![0, 0, 0, 0, 0, -1, 2, -1],
  ![0, 0, 0, 0, 0, 0, -1, 2]]

/-- The concrete E₈ Coxeter operator in the simple-root basis. -/
def coxeter : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![-1, -1, 0, 1, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 1, 0, 0],
  ![-1, -1, 0, 1, 0, 0, 1, 0],
  ![-1, -1, 0, 1, 0, 0, 0, 1],
  ![-1, -1, 0, 1, 0, 0, 0, 0]]

/-- Integral two-sided inverse of the Coxeter operator. -/
def coxeterInverse : M8 :=
![
  ![0, 1, 0, 0, 0, 0, 0, -1],
  ![0, 0, 1, 0, 0, 0, 0, -1],
  ![1, 1, 0, 0, 0, 0, 0, -1],
  ![0, 1, 1, 0, 0, 0, 0, -1],
  ![0, 0, 0, 1, 0, 0, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 1, 0, -1],
  ![0, 0, 0, 0, 0, 0, 1, -1]]

/-- Multiplication by X modulo Phi30, in the coefficient basis 1,X,...,X^7. -/
def cyclotomic : M8 :=
![
  ![0, 0, 0, 0, 0, 0, 0, -1],
  ![1, 0, 0, 0, 0, 0, 0, -1],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1],
  ![0, 0, 0, 1, 0, 0, 0, 1],
  ![0, 0, 0, 0, 1, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, -1]]

/-- Integral inverse of multiplication by X modulo Phi30. -/
def cyclotomicInverse : M8 :=
![
  ![-1, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![1, 0, 0, 1, 0, 0, 0, 0],
  ![1, 0, 0, 0, 1, 0, 0, 0],
  ![1, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![-1, 0, 0, 0, 0, 0, 0, 1],
  ![-1, 0, 0, 0, 0, 0, 0, 0]]

/-- Columns are v,Cv,...,C^7v, where v is the eighth simple root. -/
def bridge : M8 :=
![
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 0, 1, 0, 1, 1, 1],
  ![0, 0, 1, 0, 0, 1, 1, 1],
  ![0, 1, 0, 0, 0, 1, 1, 0],
  ![1, 0, 0, 0, 0, 1, 0, 0]]

/-- The integral inverse of bridge; no denominators are required. -/
def bridgeInverse : M8 :=
![
  ![1, 0, -1, 0, 0, 0, 0, 1],
  ![0, 0, -1, 0, 0, 0, 1, 0],
  ![-1, -1, 0, 0, 0, 1, 0, 0],
  ![-1, -1, 0, 0, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, -1, 0, 0, 0, 0, 0]]

/-- The E₈ Cartan form transported to the cyclotomic coefficient basis. -/
def cyclotomicGram : M8 :=
![
  ![2, -1, 0, 0, 0, 1, -1, 0],
  ![-1, 2, -1, 0, 0, 0, 1, -1],
  ![0, -1, 2, -1, 0, 0, 0, 1],
  ![0, 0, -1, 2, -1, 0, 0, 0],
  ![0, 0, 0, -1, 2, -1, 0, 0],
  ![1, 0, 0, 0, -1, 2, -1, 0],
  ![-1, 1, 0, 0, 0, -1, 2, -1],
  ![0, -1, 1, 0, 0, 0, -1, 2]]

/-- The exact operator 2I-C-C⁻¹ used for the inverse-binomial moment bridge. -/
def angleLaplacian : M8 :=
![
  ![3, -1, -1, 0, 0, 0, 0, 1],
  ![0, 3, -1, -1, 0, 0, 0, 1],
  ![0, -1, 2, -1, 0, 0, 0, 1],
  ![1, 0, -1, 1, -1, 0, 0, 1],
  ![1, 1, 0, -2, 2, -1, 0, 1],
  ![1, 1, 0, -1, -1, 2, -1, 1],
  ![1, 1, 0, -1, 0, -1, 2, 0],
  ![1, 1, 0, -1, 0, 0, -1, 3]]

/-- The same operator in cyclotomic coefficient coordinates. -/
def cyclotomicLaplacian : M8 :=
![
  ![3, -1, 0, 0, 0, 0, 0, 1],
  ![-1, 2, -1, 0, 0, 0, 0, 1],
  ![-1, -1, 2, -1, 0, 0, 0, 0],
  ![-1, 0, -1, 2, -1, 0, 0, -1],
  ![-1, 0, 0, -1, 2, -1, 0, -1],
  ![0, 0, 0, 0, -1, 2, -1, -1],
  ![1, 0, 0, 0, 0, -1, 2, -1],
  ![1, 0, 0, 0, 0, 0, -1, 3]]

/-- Both inverse equations prove that the bridge is an integral lattice isomorphism. -/
theorem bridge_inverse_left : bridgeInverse * bridge = 1 := by decide +kernel

theorem bridge_inverse_right : bridge * bridgeInverse = 1 := by decide +kernel

theorem coxeter_inverse_left : coxeterInverse * coxeter = 1 := by decide +kernel

theorem coxeter_inverse_right : coxeter * coxeterInverse = 1 := by decide +kernel

theorem cyclotomic_inverse_left : cyclotomicInverse * cyclotomic = 1 := by decide +kernel

theorem cyclotomic_inverse_right : cyclotomic * cyclotomicInverse = 1 := by decide +kernel

/-- This intertwiner is the substantive representation bridge. -/
theorem coxeter_intertwining : coxeter * bridge = bridge * cyclotomic := by decide +kernel

theorem inverse_intertwining :
    coxeterInverse * bridge = bridge * cyclotomicInverse := by decide +kernel

/-- A generic intertwiner transports every natural power, not only sample traces. -/
theorem powers_intertwine {A B P : M8} (h : A * P = P * B) (n : ℕ) :
    A ^ n * P = P * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      A ^ (n + 1) * P = A * (A ^ n * P) := by rw [pow_succ', mul_assoc]
      _ = A * (P * B ^ n) := by rw [ih]
      _ = P * B ^ (n + 1) := by rw [← mul_assoc, h, mul_assoc, ← pow_succ']

/-- In particular all Coxeter iterates are transported integrally. -/
theorem coxeter_powers_intertwining (n : ℕ) :
    coxeter ^ n * bridge = bridge * cyclotomic ^ n :=
  powers_intertwine coxeter_intertwining n

/-- Every integral vector is preserved by the two mutually inverse coordinate maps. -/
theorem coordinates_round_trip (v : Fin 8 → ℤ) :
    bridgeInverse.mulVec (bridge.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, bridge_inverse_left, Matrix.one_mulVec]

theorem lattice_round_trip (v : Fin 8 → ℤ) :
    bridge.mulVec (bridgeInverse.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, bridge_inverse_right, Matrix.one_mulVec]

/-- A concrete integral linear equivalence, not merely an agreement of character values. -/
def integralBridge : (Fin 8 → ℤ) ≃ₗ[ℤ] (Fin 8 → ℤ) where
  toFun := bridge.mulVec
  invFun := bridgeInverse.mulVec
  left_inv := coordinates_round_trip
  right_inv := lattice_round_trip
  map_add' := Matrix.mulVec_add bridge
  map_smul' := Matrix.mulVec_smul bridge

/-- The bridge preserves the full bilinear form, not merely dimensions. -/
theorem transported_cartan : bridge.transpose * cartan * bridge = cyclotomicGram := by
  decide +kernel

theorem coxeter_preserves_cartan : coxeter.transpose * cartan * coxeter = cartan := by
  decide +kernel

theorem cyclotomic_preserves_gram :
    cyclotomic.transpose * cyclotomicGram * cyclotomic = cyclotomicGram := by
  decide +kernel

/-- The discrete angle operator is obtained from actual Coxeter and inverse matrices. -/
theorem angle_laplacian_definition :
    angleLaplacian = 2 • (1 : M8) - coxeter - coxeterInverse := by decide +kernel

theorem cyclotomic_laplacian_definition :
    cyclotomicLaplacian = 2 • (1 : M8) - cyclotomic - cyclotomicInverse := by decide +kernel

/-- The same bridge transports the operator whose eigenvalues are 4 sin²(theta/2). -/
theorem angle_laplacian_intertwining :
    angleLaplacian * bridge = bridge * cyclotomicLaplacian := by decide +kernel

theorem angle_laplacian_powers_intertwining (n : ℕ) :
    angleLaplacian ^ n * bridge = bridge * cyclotomicLaplacian ^ n :=
  powers_intertwine angle_laplacian_intertwining n

/-- Every bilinear lattice pairing, and hence every norm, is transported exactly. -/
theorem bridge_preserves_bilinear (u v : Fin 8 → ℤ) :
    (bridge.mulVec u) ⬝ᵥ (cartan.mulVec (bridge.mulVec v)) =
      u ⬝ᵥ (cyclotomicGram.mulVec v) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, transported_cartan, ← Matrix.dotProduct_mulVec]

/-- Norm-two vectors correspond under the integral bridge; this is a root-lattice statement. -/
theorem norm_two_iff (v : Fin 8 → ℤ) :
    (bridge.mulVec v) ⬝ᵥ (cartan.mulVec (bridge.mulVec v)) = 2 ↔
      v ⬝ᵥ (cyclotomicGram.mulVec v) = 2 := by
  rw [bridge_preserves_bilinear]

/-- Self-adjointness is in the E₈ Cartan metric, not in arbitrary coordinates. -/
theorem angle_laplacian_cartan_selfAdjoint :
    angleLaplacian.transpose * cartan = cartan * angleLaplacian := by decide +kernel

/-- Reflection in the i-th displayed simple root, acting on simple-root coefficients. -/
def simpleReflection (i : Fin 8) : M8 := fun j k =>
  if j = i then (if j = k then 1 else 0) - cartan i k
  else if j = k then 1 else 0

/-- Integral certificate after the first 1 simple reflections. -/
def partial1 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 2 simple reflections. -/
def partial2 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 3 simple reflections. -/
def partial3 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 4 simple reflections. -/
def partial4 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![-1, -1, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 5 simple reflections. -/
def partial5 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![-1, -1, 0, 1, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 6 simple reflections. -/
def partial6 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![-1, -1, 0, 1, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 1, 0, 0],
  ![-1, -1, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Integral certificate after the first 7 simple reflections. -/
def partial7 : M8 :=
![
  ![-1, 0, 1, 0, 0, 0, 0, 0],
  ![0, -1, 0, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 1, 0, 0, 0, 0],
  ![-1, -1, 0, 1, 1, 0, 0, 0],
  ![-1, -1, 0, 1, 0, 1, 0, 0],
  ![-1, -1, 0, 1, 0, 0, 1, 0],
  ![-1, -1, 0, 1, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1]]

theorem reflection_step_1 : partial1 = simpleReflection 0 * (1 : M8) := by decide +kernel

theorem reflection_step_2 : partial2 = simpleReflection 1 * partial1 := by decide +kernel

theorem reflection_step_3 : partial3 = simpleReflection 2 * partial2 := by decide +kernel

theorem reflection_step_4 : partial4 = simpleReflection 3 * partial3 := by decide +kernel

theorem reflection_step_5 : partial5 = simpleReflection 4 * partial4 := by decide +kernel

theorem reflection_step_6 : partial6 = simpleReflection 5 * partial5 := by decide +kernel

theorem reflection_step_7 : partial7 = simpleReflection 6 * partial6 := by decide +kernel

theorem reflection_step_8 : coxeter = simpleReflection 7 * partial7 := by decide +kernel

/-- Therefore the concrete matrix is the actual product of the eight E₈ reflections. -/
theorem coxeter_reflection_product : coxeter =
    simpleReflection 7 * (simpleReflection 6 * (simpleReflection 5 *
    (simpleReflection 4 * (simpleReflection 3 * (simpleReflection 2 *
    (simpleReflection 1 * simpleReflection 0)))))) := by
  rw [reflection_step_8, reflection_step_7, reflection_step_6, reflection_step_5,
      reflection_step_4, reflection_step_3, reflection_step_2, reflection_step_1, mul_one]

/-- Finite addition-chain certificate for C^2. -/
def power2 : M8 :=
![
  ![0, 0, -1, 1, 0, 0, 0, 0],
  ![-1, 0, 0, 0, 1, 0, 0, 0],
  ![0, -1, -1, 1, 1, 0, 0, 0],
  ![-1, -1, -1, 1, 1, 1, 0, 0],
  ![-1, -1, -1, 1, 1, 0, 1, 0],
  ![-1, -1, -1, 1, 1, 0, 0, 1],
  ![-1, -1, -1, 1, 1, 0, 0, 0],
  ![0, 0, -1, 0, 1, 0, 0, 0]]

/-- Finite addition-chain certificate for C^4. -/
def power4 : M8 :=
![
  ![-1, 0, 0, 0, 0, 1, 0, 0],
  ![-1, -1, 0, 0, 1, 0, 1, 0],
  ![-1, -1, -1, 1, 0, 1, 1, 0],
  ![-2, -2, -1, 1, 1, 1, 1, 1],
  ![-2, -2, -1, 1, 1, 1, 1, 0],
  ![-1, -1, -1, 0, 1, 1, 1, 0],
  ![-1, -1, 0, 0, 0, 1, 1, 0],
  ![-1, 0, 0, 0, 0, 0, 1, 0]]

/-- Finite addition-chain certificate for C^5. -/
def power5 : M8 :=
![
  ![0, -1, -1, 1, 0, 0, 1, 0],
  ![-1, -1, -1, 1, 0, 1, 0, 1],
  ![-1, -2, -1, 1, 1, 0, 1, 1],
  ![-2, -3, -2, 2, 1, 1, 1, 1],
  ![-1, -2, -2, 1, 1, 1, 1, 1],
  ![-1, -2, -1, 1, 0, 1, 1, 1],
  ![-1, -1, -1, 1, 0, 0, 1, 1],
  ![0, -1, -1, 1, 0, 0, 0, 1]]

/-- Finite addition-chain certificate for C^6. -/
def power6 : M8 :=
![
  ![-1, -1, 0, 0, 1, 0, 0, 1],
  ![-1, -2, -1, 1, 1, 0, 1, 0],
  ![-2, -2, -1, 1, 1, 1, 0, 1],
  ![-2, -3, -2, 1, 2, 1, 1, 1],
  ![-2, -3, -1, 1, 1, 1, 1, 1],
  ![-2, -2, -1, 1, 1, 0, 1, 1],
  ![-1, -2, -1, 1, 1, 0, 0, 1],
  ![-1, -1, 0, 0, 1, 0, 0, 0]]

/-- Finite addition-chain certificate for C^10. -/
def power10 : M8 :=
![
  ![-1, -1, -1, 1, 0, 0, 1, 0],
  ![-1, -2, -1, 1, 0, 1, 0, 1],
  ![-1, -2, -2, 1, 1, 0, 1, 1],
  ![-2, -3, -2, 1, 1, 1, 1, 1],
  ![-1, -2, -2, 1, 0, 1, 1, 1],
  ![-1, -2, -1, 1, 0, 0, 1, 1],
  ![-1, -1, -1, 1, 0, 0, 0, 1],
  ![0, -1, -1, 1, 0, 0, 0, 0]]

theorem coxeter_power_two : coxeter ^ 2 = power2 := by decide +kernel

theorem coxeter_power_four : coxeter ^ 4 = power4 := by
  calc
    coxeter ^ 4 = (coxeter ^ 2) ^ 2 := by rw [← pow_mul]
    _ = power4 := by rw [coxeter_power_two]; decide +kernel

theorem coxeter_power_five : coxeter ^ 5 = power5 := by
  calc
    coxeter ^ 5 = coxeter ^ 4 * coxeter := pow_succ _ _
    _ = power5 := by rw [coxeter_power_four]; decide +kernel

theorem coxeter_power_six : coxeter ^ 6 = power6 := by
  calc
    coxeter ^ 6 = coxeter ^ 5 * coxeter := pow_succ _ _
    _ = power6 := by rw [coxeter_power_five]; decide +kernel

theorem coxeter_power_ten : coxeter ^ 10 = power10 := by
  calc
    coxeter ^ 10 = (coxeter ^ 5) ^ 2 := by rw [← pow_mul]
    _ = power10 := by rw [coxeter_power_five]; decide +kernel

theorem coxeter_power_fifteen : coxeter ^ 15 = -(1 : M8) := by
  calc
    coxeter ^ 15 = coxeter ^ 10 * coxeter ^ 5 := by
      simpa using (pow_add coxeter 10 5)
    _ = -(1 : M8) := by rw [coxeter_power_ten, coxeter_power_five]; decide +kernel

theorem coxeter_power_thirty : coxeter ^ 30 = 1 := by
  calc
    coxeter ^ 30 = (coxeter ^ 15) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [coxeter_power_fifteen]; simp

/-- The prime-divisor certificate establishes exact order, not merely order dividing 30. -/
theorem coxeter_order : orderOf coxeter = 30 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) coxeter_power_thirty
  intro p hp hdiv
  have hle : p ≤ 30 := Nat.le_of_dvd (by decide) hdiv
  have cases : p = 2 ∨ p = 3 ∨ p = 5 := by
    have finite : ∀ q : Fin 31, q.val.Prime → q.val ∣ 30 →
        q.val = 2 ∨ q.val = 3 ∨ q.val = 5 := by decide +kernel
    exact finite ⟨p, Nat.lt_succ_iff.mpr hle⟩ hp hdiv
  rcases cases with rfl | rfl | rfl
  · change coxeter ^ 15 ≠ 1
    rw [coxeter_power_fifteen]
    decide +kernel
  · change coxeter ^ 10 ≠ 1
    rw [coxeter_power_ten]
    decide +kernel
  · change coxeter ^ 6 ≠ 1
    rw [coxeter_power_six]
    decide +kernel

/-- Matrix conjugacy of every iterate, as an explicit integral identity. -/
theorem all_power_conjugacy (n : ℕ) :
    coxeter ^ n = bridge * cyclotomic ^ n * bridgeInverse := by
  calc
    coxeter ^ n = coxeter ^ n * (bridge * bridgeInverse) := by
      rw [bridge_inverse_right, mul_one]
    _ = bridge * cyclotomic ^ n * bridgeInverse := by
      rw [← mul_assoc, coxeter_powers_intertwining]

/-- Every power trace is therefore the same in both realizations. -/
theorem all_power_trace (n : ℕ) :
    Matrix.trace (coxeter ^ n) = Matrix.trace (cyclotomic ^ n) := by
  rw [all_power_conjugacy, Matrix.trace_mul_cycle, bridge_inverse_left, one_mul]

/-- The moment traces likewise depend on the same operator in either lattice realization. -/
theorem all_angle_moment_traces (n : ℕ) :
    Matrix.trace (angleLaplacian ^ n) = Matrix.trace (cyclotomicLaplacian ^ n) := by
  have hc : angleLaplacian ^ n =
      bridge * cyclotomicLaplacian ^ n * bridgeInverse := by
    calc
      angleLaplacian ^ n = angleLaplacian ^ n * (bridge * bridgeInverse) := by
        rw [bridge_inverse_right, mul_one]
      _ = bridge * cyclotomicLaplacian ^ n * bridgeInverse := by
        rw [← mul_assoc, angle_laplacian_powers_intertwining]
  rw [hc, Matrix.trace_mul_cycle, bridge_inverse_left, one_mul]

/-- The plus operator 2I+C+C⁻¹, with eigenvalues 4cos²(pi*m/30). -/
def raghavaOperator : M8 :=
![
  ![1, 1, 1, 0, 0, 0, 0, -1],
  ![0, 1, 1, 1, 0, 0, 0, -1],
  ![0, 1, 2, 1, 0, 0, 0, -1],
  ![-1, 0, 1, 3, 1, 0, 0, -1],
  ![-1, -1, 0, 2, 2, 1, 0, -1],
  ![-1, -1, 0, 1, 1, 2, 1, -1],
  ![-1, -1, 0, 1, 0, 1, 2, 0],
  ![-1, -1, 0, 1, 0, 0, 1, 1]]

/-- The same plus operator in the integral cyclotomic coordinates. -/
def raghavaCyclotomicOperator : M8 :=
![
  ![1, 1, 0, 0, 0, 0, 0, -1],
  ![1, 2, 1, 0, 0, 0, 0, -1],
  ![1, 1, 2, 1, 0, 0, 0, 0],
  ![1, 0, 1, 2, 1, 0, 0, 1],
  ![1, 0, 0, 1, 2, 1, 0, 1],
  ![0, 0, 0, 0, 1, 2, 1, 1],
  ![-1, 0, 0, 0, 0, 1, 2, 1],
  ![-1, 0, 0, 0, 0, 0, 1, 1]]

/-- Exact certificate for the plus operator raised to power 2. -/
def raghavaPower2 : M8 :=
![
  ![2, 4, 4, 1, 0, 0, -1, -4],
  ![0, 3, 4, 4, 1, 0, -1, -4],
  ![0, 4, 6, 5, 1, 0, -1, -5],
  ![-4, 0, 4, 11, 5, 1, -1, -5],
  ![-5, -4, 0, 9, 7, 4, 0, -4],
  ![-5, -5, -1, 6, 5, 6, 3, -3],
  ![-5, -5, -1, 5, 2, 4, 5, 0],
  ![-4, -4, -1, 4, 1, 1, 3, 2]]

/-- Exact certificate for the plus operator raised to power 3. -/
def raghavaPower3 : M8 :=
![
  ![6, 15, 15, 6, 1, -1, -6, -15],
  ![0, 11, 15, 16, 6, 0, -6, -16],
  ![0, 15, 21, 21, 7, 0, -7, -21],
  ![-15, 0, 15, 42, 22, 6, -6, -22],
  ![-21, -16, 0, 37, 27, 15, 0, -15],
  ![-22, -22, -6, 28, 22, 20, 9, -9],
  ![-21, -22, -7, 22, 13, 15, 14, 0],
  ![-15, -16, -6, 15, 7, 6, 9, 5]]

/-- Exact certificate for the plus operator raised to power 4. -/
def raghavaPower4 : M8 :=
![
  ![21, 57, 57, 28, 7, -7, -28, -57],
  ![0, 42, 57, 64, 28, 0, -28, -64],
  ![0, 57, 78, 85, 35, 0, -35, -85],
  ![-57, 0, 57, 163, 92, 28, -28, -92],
  ![-85, -64, 0, 149, 106, 57, 0, -57],
  ![-92, -92, -28, 120, 92, 71, 29, -29],
  ![-85, -92, -35, 92, 63, 57, 43, 0],
  ![-57, -64, -28, 57, 35, 28, 29, 14]]

theorem raghava_operator_definition :
    raghavaOperator = 2 • (1 : M8) + coxeter + coxeterInverse := by decide +kernel

theorem raghava_cyclotomic_operator_definition :
    raghavaCyclotomicOperator = 2 • (1 : M8) + cyclotomic + cyclotomicInverse := by
  decide +kernel

theorem raghava_operator_intertwining :
    raghavaOperator * bridge = bridge * raghavaCyclotomicOperator := by decide +kernel

theorem raghava_powers_intertwining (n : ℕ) :
    raghavaOperator ^ n * bridge = bridge * raghavaCyclotomicOperator ^ n :=
  powers_intertwine raghava_operator_intertwining n

theorem raghava_operator_cartan_selfAdjoint :
    raghavaOperator.transpose * cartan = cartan * raghavaOperator := by decide +kernel

theorem raghava_power_two : raghavaOperator ^ 2 = raghavaPower2 := by decide +kernel

theorem raghava_power_three : raghavaOperator ^ 3 = raghavaPower3 := by
  rw [pow_succ, raghava_power_two]
  decide +kernel

theorem raghava_power_four : raghavaOperator ^ 4 = raghavaPower4 := by
  rw [pow_succ, raghava_power_three]
  decide +kernel

/-- An exact quartic identity reduces every higher operator moment to four initial ones. -/
theorem raghava_operator_annihilator :
    raghavaOperator ^ 4 + (14 : ℤ) • raghavaOperator ^ 2 + 1 =
      (7 : ℤ) • raghavaOperator ^ 3 + (8 : ℤ) • raghavaOperator := by
  rw [raghava_power_four, raghava_power_three, raghava_power_two]
  decide +kernel

/-- All higher operator powers obey the same exact recurrence. -/
theorem raghava_operator_recurrence (n : ℕ) :
    raghavaOperator ^ (n + 4) + (14 : ℤ) • raghavaOperator ^ (n + 2) +
      raghavaOperator ^ n =
    (7 : ℤ) • raghavaOperator ^ (n + 3) + (8 : ℤ) • raghavaOperator ^ (n + 1) := by
  have h := congrArg (fun M : M8 => raghavaOperator ^ n * M) raghava_operator_annihilator
  simpa only [mul_add, mul_smul_comm, mul_one, ← pow_add, ← pow_succ] using h

/-- Exact integer traces of the actual E₈-derived plus operator. -/
def raghavaTrace (n : ℕ) : ℤ := Matrix.trace (raghavaOperator ^ n)

theorem raghava_trace_initial :
    raghavaTrace 0 = 8 ∧ raghavaTrace 1 = 14 ∧
    raghavaTrace 2 = 42 ∧ raghavaTrace 3 = 146 := by
  unfold raghavaTrace
  rw [raghava_power_two, raghava_power_three]
  decide +kernel

/-- This four-term recurrence computes all inverse-binomial trace coefficients exactly. -/
theorem raghava_trace_recurrence (n : ℕ) :
    raghavaTrace (n + 4) + 14 * raghavaTrace (n + 2) + raghavaTrace n =
    7 * raghavaTrace (n + 3) + 8 * raghavaTrace (n + 1) := by
  have h := congrArg Matrix.trace (raghava_operator_recurrence n)
  simpa only [raghavaTrace, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] using h

theorem all_raghava_moment_traces (n : ℕ) :
    raghavaTrace n = Matrix.trace (raghavaCyclotomicOperator ^ n) := by
  have hc : raghavaOperator ^ n =
      bridge * raghavaCyclotomicOperator ^ n * bridgeInverse := by
    calc
      raghavaOperator ^ n = raghavaOperator ^ n * (bridge * bridgeInverse) := by
        rw [bridge_inverse_right, mul_one]
      _ = bridge * raghavaCyclotomicOperator ^ n * bridgeInverse := by
        rw [← mul_assoc, raghava_powers_intertwining]
  unfold raghavaTrace
  rw [hc, Matrix.trace_mul_cycle, bridge_inverse_left, one_mul]

/-- Every finite weighted trace functional is transported, including rational series truncations. -/
theorem raghava_weighted_trace_transport {R : Type*} [Ring R]
    (weight : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.range N, weight n * (raghavaTrace n : R)) =
      ∑ n ∈ Finset.range N,
        weight n * ((Matrix.trace (raghavaCyclotomicOperator ^ n) : ℤ) : R) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [all_raghava_moment_traces]

/-- The actual polynomial value defining the order-30 cyclotomic relation. -/
def phi30Value {R : Type*} [CommRing R] (z : R) : R :=
  z ^ 8 + z ^ 7 - z ^ 5 - z ^ 4 - z ^ 3 + z + 1

/-- Evaluate an integral coefficient vector as a polynomial of degree at most seven. -/
def evaluateCoefficients {R : Type*} [CommRing R] (v : Fin 8 → ℤ) (z : R) : R :=
  ∑ i : Fin 8, (v i : R) * z ^ i.val

/-- The companion action really is polynomial multiplication modulo Phi30. -/
theorem companion_evaluation {R : Type*} [CommRing R] (v : Fin 8 → ℤ) (z : R) :
    evaluateCoefficients (cyclotomic.mulVec v) z =
      z * evaluateCoefficients v z - (v 7 : R) * phi30Value z := by
  simp [evaluateCoefficients, phi30Value, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, cyclotomic]
  ring

/-- At every actual root of Phi30, the integral lattice bridge intertwines multiplication by z. -/
theorem companion_at_cyclotomic_root {R : Type*} [CommRing R]
    (v : Fin 8 → ℤ) (z : R) (hz : phi30Value z = 0) :
    evaluateCoefficients (cyclotomic.mulVec v) z = z * evaluateCoefficients v z := by
  rw [companion_evaluation, hz, mul_zero, sub_zero]

/-- Evaluation after inverse lattice coordinates yields an actual Coxeter eigenfunctional. -/
theorem coxeter_eigenfunctional {R : Type*} [CommRing R]
    (v : Fin 8 → ℤ) (z : R) (hz : phi30Value z = 0) :
    evaluateCoefficients (bridgeInverse.mulVec (coxeter.mulVec v)) z =
      z * evaluateCoefficients (bridgeInverse.mulVec v) z := by
  have h : bridgeInverse * coxeter = cyclotomic * bridgeInverse := by decide +kernel
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  exact companion_at_cyclotomic_root _ z hz

/-- The explicit Phi30 relation holds at every primitive 30th root in any integral domain. -/
theorem phi30_at_primitive {R : Type*} [CommRing R] [IsDomain R]
    (z : R) (h : IsPrimitiveRoot z 30) : phi30Value z = 0 := by
  have h15ne : z ^ 15 - 1 ≠ 0 :=
    sub_ne_zero.mpr (h.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have hprod : (z ^ 15 - 1) * (z ^ 15 + 1) = 0 := by
    calc
      (z ^ 15 - 1) * (z ^ 15 + 1) = z ^ 30 - 1 := by ring
      _ = 0 := by rw [h.pow_eq_one]; ring
  have h15 : z ^ 15 + 1 = 0 := (mul_eq_zero.mp hprod).resolve_left h15ne
  have h5 : z ^ 5 + 1 ≠ 0 := by
    intro hz
    have hz5 : z ^ 5 = -1 := eq_neg_of_add_eq_zero_left hz
    have h10 : z ^ 10 = 1 := by
      calc
        z ^ 10 = (z ^ 5) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hz5]; ring
    exact h.pow_ne_one_of_pos_of_lt (by decide) (by decide) h10
  have h3 : z ^ 3 + 1 ≠ 0 := by
    intro hz
    have hz3 : z ^ 3 = -1 := eq_neg_of_add_eq_zero_left hz
    have h6 : z ^ 6 = 1 := by
      calc
        z ^ 6 = (z ^ 3) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hz3]; ring
    exact h.pow_ne_one_of_pos_of_lt (by decide) (by decide) h6
  have hfactor : phi30Value z * (z ^ 5 + 1) * (z ^ 3 + 1) = 0 := by
    calc
      phi30Value z * (z ^ 5 + 1) * (z ^ 3 + 1) = (z ^ 15 + 1) * (z + 1) := by
        unfold phi30Value
        ring
      _ = 0 := by rw [h15, zero_mul]
  have hp0 : phi30Value z * (z ^ 5 + 1) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right h3
  exact (mul_eq_zero.mp hp0).resolve_right h5

/-- The actual E₈ Coxeter action has an explicit eigenfunctional for every primitive 30th phase. -/
theorem coxeter_primitive_eigenfunctional {R : Type*} [CommRing R] [IsDomain R]
    (v : Fin 8 → ℤ) (z : R) (h : IsPrimitiveRoot z 30) :
    evaluateCoefficients (bridgeInverse.mulVec (coxeter.mulVec v)) z =
      z * evaluateCoefficients (bridgeInverse.mulVec v) z :=
  coxeter_eigenfunctional v z (phi30_at_primitive z h)

end PerfectPower.CoxeterPhaseBridge
