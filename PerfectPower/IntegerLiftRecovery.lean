import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace PerfectPower.IntegerLiftRecovery
open Matrix
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- Replayable rectangular integer change of coordinates; no rational division. -/
theorem transformed_fibre (A : Matrix m n ℤ) (U Ui : Matrix m m ℤ)
    (V Vi : Matrix n n ℤ) (D : Matrix m n ℤ)
    (hD : U*A*V=D) (hU : Ui*U=1) (hV : V*Vi=1)
    (x : n → ℤ) (b : m → ℤ) :
    A *ᵥ x=b ↔ D *ᵥ (Vi *ᵥ x)=U *ᵥ b := by
  have ht : D *ᵥ (Vi *ᵥ x)=U *ᵥ (A *ᵥ x) := by
    rw [← hD, mulVec_mulVec, Matrix.mul_assoc (U*A) V Vi, hV, Matrix.mul_one, ← mulVec_mulVec]
  rw [ht]
  constructor
  · intro h; rw [h]
  · intro h
    have he := congrArg (fun y => Ui *ᵥ y) h
    simpa only [mulVec_mulVec,← Matrix.mul_assoc,hU,Matrix.one_mul,one_mulVec] using he

/-- Transport every parameterized diagonal solution back to original coordinates. -/
theorem lift_transformed (A : Matrix m n ℤ) (U Ui : Matrix m m ℤ)
    (V : Matrix n n ℤ) (D : Matrix m n ℤ)
    (hD : U*A*V=D) (hU : Ui*U=1) (z : n → ℤ) (b : m → ℤ)
    (hz : D *ᵥ z=U *ᵥ b) : A *ᵥ (V *ᵥ z)=b := by
  have ht : U *ᵥ (A *ᵥ (V *ᵥ z))=U *ᵥ b := by
    rw [mulVec_mulVec,mulVec_mulVec,hD]; exact hz
  have he := congrArg (fun y => Ui *ᵥ y) ht
  simpa only [mulVec_mulVec,← Matrix.mul_assoc,hU,Matrix.one_mul,one_mulVec] using he

/-- A complete kernel parameterization gives the complete affine fibre. -/
theorem affine_fibre (A : Matrix m n ℤ) (K : Matrix n p ℤ)
    (x0 : n → ℤ) (b : m → ℤ) (hx0 : A *ᵥ x0=b)
    (hk : ∀ z : n → ℤ, A *ᵥ z=0 ↔ ∃ t : p → ℤ, K *ᵥ t=z)
    (x : n → ℤ) : A *ᵥ x=b ↔ ∃ t : p → ℤ, x=x0+K *ᵥ t := by
  constructor
  · intro hx
    have hz : A *ᵥ (x-x0)=0 := by rw [mulVec_sub,hx,hx0,sub_self]
    obtain ⟨t,ht⟩ := (hk (x-x0)).mp hz
    refine ⟨t,?_⟩
    rw [ht]; abel
  · rintro ⟨t,rfl⟩
    have hz : A *ᵥ (K *ᵥ t)=0 := (hk _).mpr ⟨t,rfl⟩
    rw [mulVec_add,hx0,hz,add_zero]

/-- Concrete saturated integer fibre recovered in the latest Python push. -/
theorem two_three (x y : ℤ) :
    2*x+3*y=1 ↔ ∃ t : ℤ, x = -1+3*t ∧ y=1-2*t := by
  constructor
  · intro h
    refine ⟨(x+1)/3,?_,?_⟩ <;> omega
  · rintro ⟨t,hx,hy⟩; rw [hx,hy]; ring

 theorem four_six_no_point (x y : ℤ) : 4*x+6*y ≠ 1 := by omega
end PerfectPower.IntegerLiftRecovery
