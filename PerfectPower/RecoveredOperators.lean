import Mathlib
namespace PerfectPower.RecoveredOperators

/-- The coefficient relation implies the formal hypergeometric annihilator at
all positive indices, not merely a tested prefix. -/
theorem hypergeometric_coefficient (n a previous : ℚ)
    (h : (4*n-3)*(4*n-1)*a=16*n^2*previous) :
    n*(n-1/4)*(n-3/4)*a-n^3*previous=0 := by
  linear_combination (n/16)*h

/-- Vanishing of every formal coefficient from a proved sequence recurrence. -/
theorem hypergeometric_all (a : ℕ → ℚ)
    (h : ∀ n : ℕ, (4*(n+1 : ℚ)-3)*(4*(n+1 : ℚ)-1)*a (n+1)=
      16*(n+1 : ℚ)^2*a n) :
    ∀ n : ℕ, (n : ℚ)*((n : ℚ)-1/4)*((n : ℚ)-3/4)*a n-
      (n : ℚ)^3*a (n-1)=0 := by
  intro n
  cases n with
  | zero => norm_num
  | succ n =>
    simpa using hypergeometric_coefficient (n+1) (a (n+1)) (a n) (h n)

section Projectors
variable {R : Type*} [CommRing R] [Algebra ℚ R]
def stationary (q : R) : R := 1+algebraMap ℚ R (1/11)*q^2
def moving (q : R) : R := -algebraMap ℚ R (1/11)*q^2

theorem wilson_projectors (q : R) (h : q^3 = -algebraMap ℚ R 11*q) :
    stationary q+moving q=1 ∧
    stationary q*stationary q=stationary q ∧
    moving q*moving q=moving q ∧ stationary q*moving q=0 := by
  have hinv : algebraMap ℚ R (1/11)*algebraMap ℚ R 11=1 := by
    rw [← map_mul]; norm_num
  have h4 : q^4 = -algebraMap ℚ R 11*q^2 := by
    calc q^4 = q^3*q := by ring
         _ = -algebraMap ℚ R 11*q^2 := by rw [h]; ring
  have hz : (algebraMap ℚ R (1/11))^2*q^4 = -algebraMap ℚ R (1/11)*q^2 := by
    rw [h4]
    calc
      algebraMap ℚ R (1/11)^2 * (-algebraMap ℚ R 11*q^2) =
        -algebraMap ℚ R (1/11)*(algebraMap ℚ R (1/11)*algebraMap ℚ R 11)*q^2 := by ring
      _ = -algebraMap ℚ R (1/11)*q^2 := by rw [hinv]; ring
  unfold stationary moving
  constructor
  · ring
  constructor
  · linear_combination hz
  constructor
  · linear_combination hz
  · linear_combination -hz
end Projectors
end PerfectPower.RecoveredOperators
