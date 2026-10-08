import PerfectPower.UnorderedWeightedDeterminant
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Weighted_75859b42c7e3f41f
open Matrix
open scoped BigOperators
def C : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (0), (0); (0), (0), (1); (0), (1), (0)]
def V : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (1), (1); (0), (0), (1); (0), (1), (0)]
def w : Fin 3 → ℕ := ![(0), (1), (1)]
def A : Matrix (Fin 3) (Fin 3) ℤ := !![(1), (1), (1); (0), (8), (0); (0), (0), (8)]
theorem assembly_checked : A = Matrix.of (fun i j => ∑ a, C i a * ((8 : ℤ)^w a * V a j)) := by decide +kernel
theorem determinant_checked : A.det = (64 : ℤ) := by decide +kernel
def indices0 : Fin 3 → Fin 3 := ![0,1,2]
theorem minor0_checked : (C.submatrix id indices0).det * (V.submatrix indices0 id).det =
    (1 : ℤ) := by decide +kernel
#print axioms minor0_checked
theorem unordered_checked : A.det = (8 : ℤ)^2*((C.submatrix id indices0).det*(V.submatrix indices0 id).det) := by decide +kernel
theorem divisor_checked : (64 : ℤ) ∣ A.det := by decide +kernel
#print axioms assembly_checked
#print axioms determinant_checked
#print axioms unordered_checked
#print axioms divisor_checked
end Weighted_75859b42c7e3f41f
