import Mathlib

noncomputable section
namespace PerfectPower.DivisorCoordinates
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Divisor-incidence congruence, equally valid for any supplied integral unimodular carrier. -/
def raw (D : Matrix ι ι ℤ) (g : ι → ℤ) := D*diagonal g*D.transpose

theorem coordinate_iff (D E : Matrix ι ι ℤ) (g b x : ι → ℤ)
    (hED : E*D=1) (hDE : D*E=1) :
    raw D g*ᵥ x=b ↔ ∀ i, g i*(D.transpose*ᵥ x) i=(E*ᵥ b) i := by
  have hid : E*raw D g=diagonal g*D.transpose := by
    simp only [raw,← Matrix.mul_assoc,hED,one_mul]
  constructor
  · intro h
    have he := congrArg (fun v => E*ᵥ v) h
    change E*ᵥ (raw D g*ᵥ x)=E*ᵥ b at he
    rw [mulVec_mulVec,hid,← mulVec_mulVec] at he
    intro i
    simpa only [mulVec_diagonal] using congrFun he i
  · intro h
    have he : (diagonal g*D.transpose)*ᵥ x=E*ᵥ b := by
      ext i
      simpa only [← mulVec_mulVec,mulVec_diagonal,Pi.mul_apply] using h i
    have hm := congrArg (fun v => D*ᵥ v) he
    simpa only [mulVec_mulVec,← Matrix.mul_assoc,hDE,one_mulVec,raw] using hm

/-- Integral image membership is exactly coordinatewise divisibility, including zero coefficients. -/
theorem integer_image_iff (D E : Matrix ι ι ℤ) (g b : ι → ℤ)
    (hED : E*D=1) (hDE : D*E=1) :
    (∃ x,raw D g*ᵥ x=b) ↔ ∀ i,g i ∣ (E*ᵥ b) i := by
  constructor
  · rintro ⟨x,hx⟩ i
    exact ⟨(D.transpose*ᵥ x) i,((coordinate_iff D E g b x hED hDE).mp hx i).symm⟩
  · intro h
    choose u hu using h
    refine ⟨E.transpose*ᵥ u,(coordinate_iff D E g b _ hED hDE).mpr ?_⟩
    have ht : D.transpose*E.transpose=1 := by rw [← transpose_mul,hED,transpose_one]
    intro i
    simpa only [mulVec_mulVec,ht,one_mulVec] using (hu i).symm

/-- Every prescribed free-coordinate solution lifts; this describes the entire fibre. -/
theorem family_iff (D E : Matrix ι ι ℤ) (g b u : ι → ℤ)
    (hED : E*D=1) (hDE : D*E=1) :
    raw D g*ᵥ (E.transpose*ᵥ u)=b ↔ ∀ i,g i*u i=(E*ᵥ b) i := by
  rw [coordinate_iff D E g b _ hED hDE,mulVec_mulVec,← transpose_mul,hED,transpose_one,one_mulVec]

/-- The energy of a divisor Gram matrix is diagonal in shared-divisor coordinates. -/
theorem gram_energy (D : Matrix ι ι ℝ) (g x : ι → ℝ) :
    dotProduct x ((D*diagonal g*D.transpose)*ᵥ x)=
      ∑ i,g i*((D.transpose*ᵥ x) i)^2 := by
  rw [← mulVec_mulVec,← mulVec_mulVec,dotProduct_mulVec]
  have hv : x ᵥ* D=D.transpose*ᵥ x := by simpa using vecMul_transpose D.transpose x
  rw [hv]
  simp only [mulVec_diagonal,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gram_nonnegative (D : Matrix ι ι ℝ) (g x : ι → ℝ) (hg : ∀ i,0 ≤ g i) :
    0 ≤ dotProduct x ((D*diagonal g*D.transpose)*ᵥ x) := by
  rw [gram_energy]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (sq_nonneg _)

/-- Positive weights alone do not guarantee positivity of the normalized kernel. -/
theorem positive_weight_counterexample :
    (1:ℚ)^2+2*(1/2)*(1:ℚ)*(-2)+(1/20)*(-2:ℚ)^2= -4/5 := by norm_num

/-- A GCD kernel expands over precisely the common divisor coordinates. -/
theorem shared_divisor_sum (g : ℕ → ℤ) (i j : ℕ) (hi : i ≠ 0) :
    (∑ d ∈ (Nat.gcd i j).divisors, g d) = ∑ d ∈ i.divisors, if d ∣ j then g d else 0 := by
  have hg : Nat.gcd i j ≠ 0 := by
    intro h
    exact hi (Nat.gcd_eq_zero_iff.mp h).1
  have hs : (Nat.gcd i j).divisors = i.divisors.filter (fun d => d ∣ j) := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hg, hi]
  rw [hs, Finset.sum_filter]

end PerfectPower.DivisorCoordinates
