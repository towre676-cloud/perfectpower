import Mathlib
namespace PerfectPower.IntegerOptimization
open Matrix
variable {ι : Type*} [Fintype ι]

/-- A symmetric quadratic form has symmetric cross terms. -/
theorem cross_symmetry (G : Matrix ι ι ℚ) (hG : G.transpose=G) (u v : ι → ℚ) :
    dotProduct u (G*ᵥ v)=dotProduct v (G*ᵥ u) := by
  rw [dotProduct_mulVec]
  have hv : u ᵥ*G=G*ᵥ u := by simpa only [hG] using vecMul_transpose G u
  rw [hv,dotProduct_comm]

/-- Exact completion of the square used by the integer-fibre optimizer. -/
theorem complete_square (G : Matrix ι ι ℚ) (hG : G.transpose=G)
    (h c z : ι → ℚ) (hc : G*ᵥ c= -h) :
    dotProduct z (G*ᵥ z)+2*dotProduct h z =
      -dotProduct c (G*ᵥ c)+dotProduct (z-c) (G*ᵥ (z-c)) := by
  simp only [mulVec_sub,sub_dotProduct,dotProduct_sub]
  rw [cross_symmetry G hG c z]
  simp only [hc,dotProduct_neg]
  rw [dotProduct_comm z h]
  ring

/-- The claimed continuous minimum is a proved lower bound when the Gram energy is nonnegative. -/
theorem continuous_lower_bound (G : Matrix ι ι ℚ) (hG : G.transpose=G)
    (h c z : ι → ℚ) (hc : G*ᵥ c= -h)
    (hpos : ∀ v,0 ≤ dotProduct v (G*ᵥ v)) :
    -dotProduct c (G*ᵥ c) ≤ dotProduct z (G*ᵥ z)+2*dotProduct h z := by
  rw [complete_square G hG h c z hc]
  exact le_add_of_nonneg_right (hpos (z-c))

/-- The stored tied example has exactly both integer minimizers. -/
theorem tied_minimizers (x y : ℤ) (h : x+y=1) :
    x^2+y^2=1 ↔ (x=0 ∧ y=1) ∨ (x=1 ∧ y=0) := by
  constructor
  · intro he
    have hx : x ≤ 0 ∨ 1 ≤ x := by omega
    rcases hx with hx | hx
    · have hz : x=0 := by nlinarith [sq_nonneg x]
      left;constructor <;> omega
    · have hz : x=1 := by nlinarith [sq_nonneg (x-1)]
      right;constructor <;> omega
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num

theorem tied_lower_bound (x y : ℤ) (h : x+y=1) : 1 ≤ x^2+y^2 := by
  have hx : x ≤ 0 ∨ 1 ≤ x := by omega
  rcases hx with hx | hx <;> nlinarith

end PerfectPower.IntegerOptimization
