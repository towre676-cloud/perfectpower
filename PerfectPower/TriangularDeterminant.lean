import Mathlib
namespace PerfectPower.TriangularDeterminant
open Matrix
open scoped BigOperators

/-- A unit-lower-triangular elimination witness reduces determinant checking to multiplication. -/
theorem checked {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {R : Type*} [CommRing R] (A E U : Matrix n n R)
    (hE : E.BlockTriangular (OrderDual.toDual : n ≃ OrderDual n)) (hdiag : ∀ i,E i i=1)
    (hmul : E*A=U) (hU : U.BlockTriangular id) (v : R)
    (hprod : ∏ i,U i i=v) : det A=v := by
  have he : det E=1 := by rw [det_of_lowerTriangular E hE];simp [hdiag]
  calc det A = det E * det A := by rw [he,one_mul]
       _ = det (E*A) := (det_mul E A).symm
       _ = det U := congrArg det hmul
       _ = ∏ i,U i i := det_of_upperTriangular hU
       _ = v := hprod
end PerfectPower.TriangularDeterminant
