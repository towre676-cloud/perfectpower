import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Integral transvections for marked vanishing cycles. Geometric identification
of a supplied vanishing cycle is separate from these universal algebraic laws. -/
namespace PerfectPower.PicardLefschetz
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
open LinearMap (BilinForm)

/-- The integral Picard–Lefschetz transvection in a declared cycle. -/
def twist (B : BilinForm R V) (d x : V) : V := x + B d x • d

/-- Opposite orientation gives the inverse transvection. -/
def untwist (B : BilinForm R V) (d x : V) : V := x - B d x • d

/-- Alternation implies skew symmetry without dividing by two. -/
theorem skew (B : BilinForm R V) (h : ∀ x, B x x = 0) (x y : V) :
    B x y = - B y x := by
  have he := h (x+y)
  rw [BilinForm.add_left, BilinForm.add_right, BilinForm.add_right, h x, h y] at he
  simp only [add_zero, zero_add] at he
  linear_combination he

/-- The transvection preserves the integral intersection form. -/
theorem preserves (B : BilinForm R V) (h : ∀ x, B x x = 0) (d x y : V) :
    B (twist B d x) (twist B d y) = B x y := by
  simp only [twist, BilinForm.add_left, BilinForm.add_right,
    BilinForm.smul_left, BilinForm.smul_right, h, mul_zero, add_zero]
  rw [skew B h x d]
  ring

/-- The inverse identity is integral and needs only an isotropic cycle. -/
theorem untwist_twist (B : BilinForm R V) (d : V) (hd : B d d = 0) (x : V) :
    untwist B d (twist B d x) = x := by
  simp [untwist, twist, BilinForm.add_right, BilinForm.smul_right, hd]

/-- The reverse inverse identity. -/
theorem twist_untwist (B : BilinForm R V) (d : V) (hd : B d d = 0) (x : V) :
    twist B d (untwist B d x) = x := by
  simp [untwist, twist, BilinForm.sub_right, BilinForm.smul_right, hd]

/-- Disjoint marked cycles have commuting transvections. -/
theorem commute (B : BilinForm R V) (h : ∀ x, B x x = 0) (d e : V)
    (hde : B d e = 0) (x : V) :
    twist B d (twist B e x) = twist B e (twist B d x) := by
  have hed : B e d = 0 := by rw [skew B h e d, hde, neg_zero]
  simp only [twist, BilinForm.add_right, BilinForm.smul_right, hde, hed,
    mul_zero, add_zero]
  abel

/-- Adjacent cycles intersecting once satisfy the braid relation. -/
theorem braid (B : BilinForm R V) (h : ∀ x, B x x = 0) (d e : V)
    (hde : B d e = 1) (x : V) :
    twist B d (twist B e (twist B d x)) =
      twist B e (twist B d (twist B e x)) := by
  have hed : B e d = -1 := by rw [skew B h e d, hde]
  simp only [twist, BilinForm.add_right, BilinForm.smul_right,
    h d, h e, hde, hed, mul_zero, add_zero, mul_one, mul_neg_one]
  module

section Matrix
open scoped BigOperators Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact rank-one matrix used by marked branch-braid execution. -/
def twistMatrix (J : Matrix n n R) (d : n → R) : Matrix n n R :=
  1 + Matrix.of (fun i j => d i * ∑ k, d k * J k j)

/-- Matrix action agrees with the bilinear transvection formula. -/
theorem twistMatrix_action (J : Matrix n n R) (d x : n → R) :
    (twistMatrix J d).mulVec x = twist (Matrix.toBilin' J) d x := by
  rw [twistMatrix, Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  simp only [twist, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.toBilin'_apply]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Native execution of a signed word of declared cycles. -/
def wordMatrix (J : Matrix n n R) (steps : List ((n → R) × R)) : Matrix n n R :=
  steps.foldl (fun M step => M *
    (1 + Matrix.of (fun i j => step.2 * step.1 i * ∑ k, step.1 k * J k j))) 1

end Matrix
end PerfectPower.PicardLefschetz
