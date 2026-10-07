import PerfectPower.IntegralKernelWitness
import PerfectPower.ResidueDeterminantCertificate
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Kernel_209bd2bd5a8e4172
open Matrix
def A : Matrix (Fin 1) (Fin 3) ℤ := !![(0), (0), (0)]
def K : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (0), (0); (0), (1), (0); (0), (0), (1)]
theorem annihilates : A * K = 0 := by decide +kernel
def c0 : Fin 3 → ℤ := ![(1), (0), (0)]
theorem relation0 : c0 ≠ 0 ∧ A *ᵥ c0 = 0 := by decide +kernel
#print axioms relation0
def c1 : Fin 3 → ℤ := ![(0), (1), (0)]
theorem relation1 : c1 ≠ 0 ∧ A *ᵥ c1 = 0 := by decide +kernel
#print axioms relation1
def c2 : Fin 3 → ℤ := ![(0), (0), (1)]
theorem relation2 : c2 ≠ 0 ∧ A *ᵥ c2 = 0 := by decide +kernel
#print axioms relation2
#print axioms annihilates
end Kernel_209bd2bd5a8e4172
