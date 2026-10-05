import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PerfectPower.BernsteinBoxes
open scoped BigOperators

noncomputable def basis (n : ℕ) (i : Fin (n+1)) (s : ℝ) : ℝ :=
  s^i.val*(1-s)^(n-i.val)

noncomputable def tensor (m n : ℕ) (c : Fin (m+1) → Fin (n+1) → ℚ) (s t : ℝ) : ℝ :=
  ∑ i, ∑ j, (c i j : ℝ)*basis m i s*basis n j t

theorem basis_nonnegative (n : ℕ) (i : Fin (n+1)) (s : ℝ)
    (h0 : 0 ≤ s) (h1 : s ≤ 1) : 0 ≤ basis n i s :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)

theorem basis_positive_somewhere (n : ℕ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ i : Fin (n+1), 0 < basis n i s := by
  by_cases hs : s < 1
  · refine ⟨0,?_⟩
    simpa [basis] using pow_pos (sub_pos.mpr hs) n
  · have he : s=1 := by linarith
    refine ⟨Fin.last n,?_⟩
    simp [basis,he]

/-- Strict coefficient positivity certifies the entire closed rectangle. -/
theorem tensor_positive (m n : ℕ) (c : Fin (m+1) → Fin (n+1) → ℚ)
    (hc : ∀ i j, 0 < c i j) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < tensor m n c s t := by
  obtain ⟨i,hi⟩ := basis_positive_somewhere m s hs0 hs1
  obtain ⟨j,hj⟩ := basis_positive_somewhere n t ht0 ht1
  have hnon : ∀ i j, 0 ≤ (c i j : ℝ)*basis m i s*basis n j t := by
    intro i j
    have hcoef : 0 ≤ (c i j : ℝ) := by exact_mod_cast (hc i j).le
    exact mul_nonneg (mul_nonneg hcoef (basis_nonnegative m i s hs0 hs1))
      (basis_nonnegative n j t ht0 ht1)
  unfold tensor
  apply Finset.sum_pos'
  · intro i _; exact Finset.sum_nonneg (fun j _ => hnon i j)
  · refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.sum_pos'
    · intro j _; exact hnon i j
    · refine ⟨j,Finset.mem_univ _,?_⟩
      have hcoef : 0 < (c i j : ℝ) := by exact_mod_cast hc i j
      exact mul_pos (mul_pos hcoef hi) hj

/-- Pull a verified tensor identity back to a physical rational rectangle. -/
theorem rectangle_positive (F : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (m n : ℕ)
    (coeff : Fin (m+1) → Fin (n+1) → ℚ)
    (hc : ∀ i j, 0 < coeff i j)
    (hid : ∀ s t, F (a+(b-a)*s) (c+(d-c)*t)=tensor m n coeff s t)
    (x y : ℝ) (hx0 : a ≤ x) (hx1 : x ≤ b) (hy0 : c ≤ y) (hy1 : y ≤ d) :
    0 < F x y := by
  let s := (x-a)/(b-a)
  let t := (y-c)/(d-c)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hx0) (sub_pos.mpr hab).le
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy0) (sub_pos.mpr hcd).le
  have hs1 : s ≤ 1 := by
    apply (div_le_one (sub_pos.mpr hab)).mpr; linarith
  have ht1 : t ≤ 1 := by
    apply (div_le_one (sub_pos.mpr hcd)).mpr; linarith
  have hx : a+(b-a)*s=x := by dsimp [s]; rw [mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))]; ring
  have hy : c+(d-c)*t=y := by dsimp [t]; rw [mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hcd))]; ring
  have hp := tensor_positive m n coeff hc s t hs0 hs1 ht0 ht1
  rw [← hid s t,hx,hy] at hp
  exact hp

/-- A weighted common-zero constraint can be excluded without solving either curve. -/
theorem joint_exclusion (F G : ℝ → ℝ → ℝ) (a b : ℝ) (x y : ℝ)
    (hpositive : 0 < a*F x y+b*G x y) : ¬(F x y=0 ∧ G x y=0) := by
  rintro ⟨hF,hG⟩
  simp [hF,hG] at hpositive

/-- Squared polynomial inequalities enclose a smooth chart density N/|D|.
The supplied N and D are the exact chart expressions, not quadrature estimates. -/
theorem density_comparison (N D r l u : ℝ) (hN : 0 < N) (hD : 0 < D)
    (hr : 0 < r) (_hl : 0 < l) (_hu : 0 < u)
    (hlo : 0 < N^2-l^4*r^2*D) (hup : 0 < u^4*r^2*D-N^2) :
    l^2*r < N/Real.sqrt D ∧ N/Real.sqrt D < u^2*r := by
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have he (a : ℝ) : (a^2*r*Real.sqrt D)^2=a^4*r^2*D := by
    calc
      _ = a^4*r^2*(Real.sqrt D)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hD.le]
  have hbaseL : 0 ≤ l^2*r*Real.sqrt D :=
    mul_nonneg (mul_nonneg (sq_nonneg l) hr.le) hs.le
  have hbaseU : 0 ≤ u^2*r*Real.sqrt D :=
    mul_nonneg (mul_nonneg (sq_nonneg u) hr.le) hs.le
  constructor
  · apply (lt_div_iff₀ hs).mpr
    nlinarith [he l]
  · apply (div_lt_iff₀ hs).mpr
    nlinarith [he u]

/-- Branch chart x=b+t² removes the simple-root denominator. -/
theorem branch_equation {R : Type*} [CommRing R] (b t h : R) (Q : R → R)
    (P : R → R) (hf : ∀ x, P x=(x-b)*Q x) (hh : h^2=Q (b+t^2)) :
    (t*h)^2=P (b+t^2) := by rw [hf]; linear_combination t^2*hh

/-- Infinity chart on y²=x^(2g+1)-x; the equation extends through t=0. -/
theorem reciprocal_odd {R : Type*} [CommRing R] (g : ℕ) (t y : R)
    (h : y^2=1-t^(4*g)) : y^2+t^(4*g)=1 := by linear_combination h

/-- A positive density bracket controls the squared norm of every tangent vector. -/
theorem tangent_comparison (ρ r l u a b : ℝ) (hlo : l^2*r ≤ ρ)
    (hup : ρ ≤ u^2*r) :
    l^2*r*(a^2+b^2) ≤ ρ*(a^2+b^2) ∧ ρ*(a^2+b^2) ≤ u^2*r*(a^2+b^2) := by
  have hv := add_nonneg (sq_nonneg a) (sq_nonneg b)
  exact ⟨mul_le_mul_of_nonneg_right hlo hv,mul_le_mul_of_nonneg_right hup hv⟩

theorem sqrt_scaled (l a : ℝ) (hl : 0 ≤ l) :
    Real.sqrt (l^2*a)=l*Real.sqrt a := by
  rw [Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq_eq_abs, abs_of_nonneg hl]

/-- Chart density bounds give actual tangent-speed bounds. -/
theorem speed_comparison (ρ r l u a b : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l^2*r ≤ ρ) (hup : ρ ≤ u^2*r) :
    l*Real.sqrt (r*(a^2+b^2)) ≤ Real.sqrt (ρ*(a^2+b^2)) ∧
      Real.sqrt (ρ*(a^2+b^2)) ≤ u*Real.sqrt (r*(a^2+b^2)) := by
  obtain ⟨h1,h2⟩ := tangent_comparison ρ r l u a b hlo hup
  have h1' := Real.sqrt_le_sqrt h1
  have h2' := Real.sqrt_le_sqrt h2
  rw [mul_assoc, sqrt_scaled l _ hl] at h1'
  rw [mul_assoc, sqrt_scaled u _ hu] at h2'
  exact ⟨h1',h2'⟩

/-- Integrable chart speeds transfer along entire contained paths.
This compares those paths; it does not identify unrestricted global geodesics. -/
theorem path_length_comparison (f g : ℝ → ℝ) (a b l u : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hlo : ∀ x ∈ Set.Icc a b, l*g x ≤ f x)
    (hup : ∀ x ∈ Set.Icc a b, f x ≤ u*g x) :
    l*(∫ x in a..b, g x) ≤ (∫ x in a..b, f x) ∧
      (∫ x in a..b, f x) ≤ u*(∫ x in a..b, g x) := by
  have h1 := intervalIntegral.integral_mono_on hab (hg.const_mul l) hf hlo
  have h2 := intervalIntegral.integral_mono_on hab hf (hg.const_mul u) hup
  rw [intervalIntegral.integral_const_mul] at h1 h2
  exact ⟨h1,h2⟩

/-- Reciprocal symmetry of the whole family y²=x^(2g+1)-x.
The square root of -1 is explicit; this is an algebraic identity over any field. -/
theorem reciprocal_family {K : Type*} [Field K] (g : ℕ) (x y i : K)
    (hx : x ≠ 0) (hi : i^2 = -1) (hy : y^2=x^(2*g+1)-x) :
    (i*y/x^(g+1))^2=(1/x)^(2*g+1)-1/x := by
  rw [div_pow,mul_pow,hi,hy,← pow_mul]
  have hp : x^((g+1)*2)=x^(2*g+1)*x := by
    rw [show (g+1)*2=(2*g+1)+1 by omega, pow_succ]
  rw [hp,one_div_pow]
  field_simp [hx] <;> ring

theorem branch_family {R : Type*} [CommRing R] (g : ℕ) (t y : R)
    (hy : y^2=t^(4*g)-1) : (t*y)^2=(t^2)^(2*g+1)-t^2 := by
  have hp : (t^2)^(2*g+1)=t^2*t^(4*g) := by
    rw [← pow_mul, show 2*(2*g+1)=2+4*g by omega, pow_add]
  rw [mul_pow,hy,hp]
  ring

theorem basis_positive (n : ℕ) (i : Fin (n+1)) (s : ℝ)
    (h0 : 0 < s) (h1 : s < 1) : 0 < basis n i s :=
  mul_pos (pow_pos h0 _) (pow_pos (sub_pos.mpr h1) _)

/-- Positive tensor support excludes the interior even with zero coefficients.
This is the basis of exact boundary-stratum localization. -/
theorem tensor_positive_support (m n : ℕ) (c : Fin (m+1) → Fin (n+1) → ℚ)
    (hc : ∀ i j, 0 ≤ c i j) (i : Fin (m+1)) (j : Fin (n+1))
    (hpos : 0 < c i j) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hi : 0 < basis m i s) (hj : 0 < basis n j t) : 0 < tensor m n c s t := by
  have hnon : ∀ i j, 0 ≤ (c i j : ℝ)*basis m i s*basis n j t := by
    intro i j
    have hcoef : 0 ≤ (c i j : ℝ) := by exact_mod_cast hc i j
    exact mul_nonneg (mul_nonneg hcoef (basis_nonnegative m i s hs0 hs1))
      (basis_nonnegative n j t ht0 ht1)
  unfold tensor
  apply Finset.sum_pos'
  · intro i _; exact Finset.sum_nonneg (fun j _ => hnon i j)
  · refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.sum_pos'
    · intro j _; exact hnon i j
    · refine ⟨j,Finset.mem_univ _,?_⟩
      have hcoef : 0 < (c i j : ℝ) := by exact_mod_cast hpos
      exact mul_pos (mul_pos hcoef hi) hj

/-- For a weak-sign tensor, its zero set is determined exactly by active support. -/
theorem tensor_zero_iff (m n : ℕ) (c : Fin (m+1) → Fin (n+1) → ℚ)
    (hc : ∀ i j, 0 ≤ c i j) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tensor m n c s t=0 ↔ ∀ i j, (c i j : ℝ)*basis m i s*basis n j t=0 := by
  have hnon : ∀ i j, 0 ≤ (c i j : ℝ)*basis m i s*basis n j t := by
    intro i j
    have hcoef : 0 ≤ (c i j : ℝ) := by exact_mod_cast hc i j
    exact mul_nonneg (mul_nonneg hcoef (basis_nonnegative m i s hs0 hs1))
      (basis_nonnegative n j t ht0 ht1)
  unfold tensor
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j))]
  simp only [Finset.mem_univ,forall_true_left]
  constructor
  · intro h i
    have hi := h i
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon i j)] at hi
    simpa using hi
  · intro h i
    exact Finset.sum_eq_zero (fun j _ => h i j)

end PerfectPower.BernsteinBoxes
