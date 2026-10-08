import PerfectPower.UnorderedWeightedDeterminant
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Weighted_ababba182c5432b0
open Matrix
open scoped BigOperators
def C : Matrix (Fin 3) (Fin 5) ℤ := !![(1), (2), (0), (-1), (1); (0), (1), (2), (1), (-2); (1), (0), (1), (2), (1)]
def V : Matrix (Fin 5) (Fin 3) ℤ := !![(1), (0), (1); (0), (1), (2); (1), (1), (0); (2), (1), (1); (1), (-1), (2)]
def w : Fin 5 → ℕ := ![(0), (1), (1), (2), (3)]
def A : Matrix (Fin 3) (Fin 3) ℤ := !![(10), (-30), (58); (-30), (72), (-93); (67), (-6), (73)]
theorem assembly_checked : A = Matrix.of (fun i j => ∑ a, C i a * ((3 : ℤ)^w a * V a j)) := by decide +kernel
theorem determinant_checked : A.det = (-101142 : ℤ) := by decide +kernel
def indices0 : Fin 3 → Fin 5 := ![0,1,2]
theorem minor0_checked : (C.submatrix id indices0).det * (V.submatrix indices0 id).det =
    (-15 : ℤ) := by decide +kernel
#print axioms minor0_checked
def indices1 : Fin 3 → Fin 5 := ![0,1,3]
theorem minor1_checked : (C.submatrix id indices1).det * (V.submatrix indices1 id).det =
    (-15 : ℤ) := by decide +kernel
#print axioms minor1_checked
def indices2 : Fin 3 → Fin 5 := ![0,1,4]
theorem minor2_checked : (C.submatrix id indices2).det * (V.submatrix indices2 id).det =
    (-12 : ℤ) := by decide +kernel
#print axioms minor2_checked
def indices3 : Fin 3 → Fin 5 := ![0,2,3]
theorem minor3_checked : (C.submatrix id indices3).det * (V.submatrix indices3 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor3_checked
def indices4 : Fin 3 → Fin 5 := ![0,2,4]
theorem minor4_checked : (C.submatrix id indices4).det * (V.submatrix indices4 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor4_checked
def indices5 : Fin 3 → Fin 5 := ![0,3,4]
theorem minor5_checked : (C.submatrix id indices5).det * (V.submatrix indices5 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor5_checked
def indices6 : Fin 3 → Fin 5 := ![1,2,3]
theorem minor6_checked : (C.submatrix id indices6).det * (V.submatrix indices6 id).det =
    (-15 : ℤ) := by decide +kernel
#print axioms minor6_checked
def indices7 : Fin 3 → Fin 5 := ![1,2,4]
theorem minor7_checked : (C.submatrix id indices7).det * (V.submatrix indices7 id).det =
    (-54 : ℤ) := by decide +kernel
#print axioms minor7_checked
def indices8 : Fin 3 → Fin 5 := ![1,3,4]
theorem minor8_checked : (C.submatrix id indices8).det * (V.submatrix indices8 id).det =
    (-117 : ℤ) := by decide +kernel
#print axioms minor8_checked
def indices9 : Fin 3 → Fin 5 := ![2,3,4]
theorem minor9_checked : (C.submatrix id indices9).det * (V.submatrix indices9 id).det =
    (0 : ℤ) := by decide +kernel
#print axioms minor9_checked
theorem unordered_checked : A.det = (3 : ℤ)^2*((C.submatrix id indices0).det*(V.submatrix indices0 id).det) + (3 : ℤ)^3*((C.submatrix id indices1).det*(V.submatrix indices1 id).det) + (3 : ℤ)^4*((C.submatrix id indices2).det*(V.submatrix indices2 id).det) + (3 : ℤ)^3*((C.submatrix id indices3).det*(V.submatrix indices3 id).det) + (3 : ℤ)^4*((C.submatrix id indices4).det*(V.submatrix indices4 id).det) + (3 : ℤ)^5*((C.submatrix id indices5).det*(V.submatrix indices5 id).det) + (3 : ℤ)^4*((C.submatrix id indices6).det*(V.submatrix indices6 id).det) + (3 : ℤ)^5*((C.submatrix id indices7).det*(V.submatrix indices7 id).det) + (3 : ℤ)^6*((C.submatrix id indices8).det*(V.submatrix indices8 id).det) + (3 : ℤ)^6*((C.submatrix id indices9).det*(V.submatrix indices9 id).det) := by decide +kernel
theorem divisor_checked : (9 : ℤ) ∣ A.det := by decide +kernel
#print axioms assembly_checked
#print axioms determinant_checked
#print axioms unordered_checked
#print axioms divisor_checked
end Weighted_ababba182c5432b0
