import PerfectPower.UnorderedWeightedDeterminant
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Weighted_6f53556e370035de
open Matrix
open scoped BigOperators
def C : Matrix (Fin 2) (Fin 3) ℤ := !![(1), (2), (3); (2), (4), (6)]
def V : Matrix (Fin 3) (Fin 2) ℤ := !![(1), (0); (0), (1); (1), (1)]
def w : Fin 3 → ℕ := ![(0), (2), (1)]
def A : Matrix (Fin 2) (Fin 2) ℤ := !![(10), (27); (20), (54)]
theorem assembly_checked : A = Matrix.of (fun i j => ∑ a, C i a * ((3 : ℤ)^w a * V a j)) := by decide +kernel
theorem determinant_checked : A.det = (0 : ℤ) := by decide +kernel
def indices0 : Fin 2 → Fin 3 := ![0,1]
theorem minor0_checked : (C.submatrix id indices0).det * (V.submatrix indices0 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor0_checked
def indices1 : Fin 2 → Fin 3 := ![0,2]
theorem minor1_checked : (C.submatrix id indices1).det * (V.submatrix indices1 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor1_checked
def indices2 : Fin 2 → Fin 3 := ![1,2]
theorem minor2_checked : (C.submatrix id indices2).det * (V.submatrix indices2 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor2_checked
theorem unordered_checked : A.det = (3 : ℤ)^2*((C.submatrix id indices0).det*(V.submatrix indices0 id).det) + (3 : ℤ)^1*((C.submatrix id indices1).det*(V.submatrix indices1 id).det) + (3 : ℤ)^3*((C.submatrix id indices2).det*(V.submatrix indices2 id).det) := by decide +kernel
theorem divisor_checked : (1 : ℤ) ∣ A.det := by decide +kernel
#print axioms assembly_checked
#print axioms determinant_checked
#print axioms unordered_checked
#print axioms divisor_checked
theorem zero_checked : A.det=0 := by decide +kernel
#print axioms zero_checked
end Weighted_6f53556e370035de
