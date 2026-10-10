import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Weighted recurrence majorants and signed/positive infinite-series tails. -/
noncomputable section
namespace PerfectPower.CertifiedSeriesBounds
open scoped BigOperators

/-- A uniform weighted recurrence bound is proved by strong induction. -/
theorem recurrence_majorant (a q : ℕ → ℝ) (P δ : ℝ)
    (hP : 0 ≤ P) (_hd : 0 ≤ δ) (hu : δ < 1)
    (hq : ∀ j, 0 ≤ q j)
    (hweights : ∀ n, (∑ j ∈ Finset.range n, q (j+1)) ≤ δ)
    (ha : ∀ n, |a n| ≤ P+∑ j ∈ Finset.range n, q (j+1)*|a (n-(j+1))|) :
    ∀ n, |a n| ≤ P/(1-δ) := by
  have hden : 0 < 1-δ := by linarith
  have hM : 0 ≤ P/(1-δ) := div_nonneg hP hden.le
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    calc
      |a n| ≤ P+∑ j ∈ Finset.range n, q (j+1)*|a (n-(j+1))| := ha n
      _ ≤ P+∑ j ∈ Finset.range n, q (j+1)*(P/(1-δ)) := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        exact mul_le_mul_of_nonneg_left (ih _ (by omega)) (hq _)
      _ = P+(∑ j ∈ Finset.range n, q (j+1))*(P/(1-δ)) := by rw [Finset.sum_mul]
      _ ≤ P+δ*(P/(1-δ)) := add_le_add_left (mul_le_mul_of_nonneg_right (hweights n) hM) P
      _ = P/(1-δ) := by field_simp; ring

/-- The coefficient majorant is derived from the normalized source recurrence. -/
theorem source_coefficient_majorant (a p q : ℕ → ℝ) (R P δ : ℝ)
    (hR : 0≤R) (hP : 0≤P) (hd : 0≤δ) (hu : δ<1)
    (hsource : ∀ n, a n=p n-∑ j ∈ Finset.range n, q (j+1)*a (n-(j+1)))
    (hp : ∀ n, |p n| * R^n≤P)
    (hq : ∀ n, (∑ j ∈ Finset.range n, |q (j+1)| * R^(j+1))≤δ) :
    ∀ n, |a n| * R^n≤P/(1-δ) := by
  have hb := recurrence_majorant (fun n => a n*R^n) (fun j => |q j| * R^j)
    P δ hP hd hu (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg hR _)) hq
  have hineq : ∀ n, |a n*R^n| ≤ P+
      ∑ j ∈ Finset.range n, (|q (j+1)| * R^(j+1))*|a (n-(j+1))*R^(n-(j+1))| := by
    intro n
    have hsum := Finset.abs_sum_le_sum_abs (fun j => q (j+1)*a (n-(j+1))) (Finset.range n)
    have ha := abs_add_le (p n) (-(∑ j ∈ Finset.range n, q (j+1)*a (n-(j+1))))
    simp only [← sub_eq_add_neg, abs_neg] at ha
    rw [← hsource] at ha
    have hterm : ∀ j∈Finset.range n,
        |q (j+1)*a (n-(j+1))| * R^n =
        (|q (j+1)| * R^(j+1))*|a (n-(j+1))*R^(n-(j+1))| := by
      intro j hj
      have hi := Finset.mem_range.mp hj
      have he : n=(j+1)+(n-(j+1)) := by omega
      rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hR _)]
      have hpow : R^n=R^(j+1)*R^(n-(j+1)) := by rw [← pow_add, ← he]
      rw [hpow]
      ring
    rw [abs_mul,abs_of_nonneg (pow_nonneg hR _)]
    calc
      |a n| * R^n ≤ (|p n|+∑ j ∈ Finset.range n, |q (j+1)*a (n-(j+1))|)*R^n :=
        mul_le_mul_of_nonneg_right (ha.trans (add_le_add_left hsum _)) (pow_nonneg hR _)
      _ = |p n| * R^n+∑ j ∈ Finset.range n, |q (j+1)*a (n-(j+1))| * R^n := by
        rw [add_mul,Finset.sum_mul]
      _ ≤ P+∑ j ∈ Finset.range n, |q (j+1)*a (n-(j+1))| * R^n := add_le_add_right (hp n) _
      _ = P+∑ j ∈ Finset.range n, (|q (j+1)| * R^(j+1))*|a (n-(j+1))*R^(n-(j+1))| := by
        congr 1
        exact Finset.sum_congr rfl hterm
  have h := hb hineq
  intro n
  simpa only [abs_mul,abs_of_nonneg (pow_nonneg hR _)] using h n

/-- Signed terms bounded by a geometric envelope have an absolute remainder. -/
theorem absolute_tail (a : ℕ → ℝ) (M ρ : ℝ)
    (_hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hu : ρ < 1)
    (ha : ∀ n, |a n| ≤ M*ρ^n) (N : ℕ) :
    Summable a ∧ |(∑' n, a n)-∑ n ∈ Finset.range N, a n| ≤ M*ρ^N/(1-ρ) := by
  have habs : |ρ|<1 := by rwa [abs_of_nonneg hρ]
  have hg := summable_geometric_of_abs_lt_one habs
  have hs : Summable a := .of_norm_bounded (fun n => M*ρ^n) (hg.mul_left M)
    (fun n => by simpa only [Real.norm_eq_abs] using ha n)
  refine ⟨hs,?_⟩
  have htail : (∑' n, a n)-∑ n ∈ Finset.range N, a n = ∑' i, a (i+N) := by
    have h := hs.sum_add_tsum_nat_add N
    linarith
  rw [htail]
  have hmajor := hg.mul_left (M*ρ^N)
  have hgeom := tsum_geometric_of_abs_lt_one habs
  have hb : HasSum (fun i => M*ρ^N*ρ^i) (M*ρ^N/(1-ρ)) := by
    convert hmajor.hasSum using 1
    rw [tsum_mul_left,hgeom,div_eq_mul_inv]
  have h := tsum_of_norm_bounded hb (fun i => show ‖a (i+N)‖ ≤ M*ρ^N*ρ^i from by
    rw [Real.norm_eq_abs]
    calc
      |a (i+N)| ≤ M*ρ^(i+N) := ha _
      _ = M*ρ^N*ρ^i := by rw [pow_add]; ring)
  simpa only [Real.norm_eq_abs] using h

/-- The rational-GF remainder follows from a coefficient disk majorant. -/
theorem coefficient_disk_tail (a : ℕ → ℝ) (M R z : ℝ)
    (hM : 0 ≤ M) (hR : 0 < R) (hz : |z|<R)
    (ha : ∀ n, |a n| * R^n ≤ M) (N : ℕ) :
    Summable (fun n => a n*z^n) ∧
      |(∑' n, a n*z^n)-∑ n ∈ Finset.range N, a n*z^n|
      ≤ M*(|z|/R)^N/(1-|z|/R) := by
  apply absolute_tail _ M (|z|/R) hM (div_nonneg (abs_nonneg _) hR.le)
    ((div_lt_one hR).mpr hz) _ N
  intro n
  rw [abs_mul,abs_pow]
  have hp : 0<R^n := pow_pos hR n
  calc
    |a n| * |z|^n = (|a n| * R^n)*(|z|/R)^n := by rw [div_pow]; field_simp; ring
    _ ≤ M*(|z|/R)^n := mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (by positivity) _)

/-- The binomial branch uses this explicit eventual ratio bound. -/
theorem binomial_ratio_bound (α x : ℝ) (hx : 0 ≤ x) (N n : ℕ) (hn : N ≤ n) :
    x*((n:ℝ)+α)/((n:ℝ)+1) ≤ x*max 1 (((N:ℝ)+α)/((N:ℝ)+1)) := by
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hle : (N:ℝ)≤n := by exact_mod_cast hn
  have hnpos : 0<(n:ℝ)+1 := by positivity
  have hNpos : 0<(N:ℝ)+1 := by positivity
  have hb : ((n:ℝ)+α)/((n:ℝ)+1) ≤ max 1 (((N:ℝ)+α)/((N:ℝ)+1)) := by
    by_cases hα : α≤1
    · exact le_trans ((div_le_one hnpos).mpr (by linarith)) (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      apply (div_le_div_iff₀ hnpos hNpos).mpr
      have hprod := mul_nonneg (show 0≤α-1 by linarith) (show 0≤(n:ℝ)-N by linarith)
      nlinarith
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb hx

/-- Positive eventual ratio envelopes bound all future terms and the actual sum. -/
theorem positive_ratio_tail (a : ℕ → ℝ) (N : ℕ) (ρ : ℝ)
    (ha : ∀ n, 0≤a n) (hρ : 0≤ρ) (hu : ρ<1)
    (hstep : ∀ n, N≤n → a (n+1) ≤ ρ*a n) :
    Summable a ∧ 0≤(∑' n, a n)-∑ n ∈ Finset.range N, a n ∧
      (∑' n, a n)-∑ n ∈ Finset.range N, a n ≤ a N/(1-ρ) := by
  have henv : ∀ i, a (i+N) ≤ a N*ρ^i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        a (i+1+N) = a ((i+N)+1) := by congr 1; omega
        _ ≤ ρ*a (i+N) := hstep _ (by omega)
        _ ≤ ρ*(a N*ρ^i) := mul_le_mul_of_nonneg_left ih hρ
        _ = a N*ρ^(i+1) := by rw [pow_succ]; ring
  have hg := summable_geometric_of_abs_lt_one (show |ρ|<1 by rwa [abs_of_nonneg hρ])
  have ht : Summable (fun i => a (i+N)) := Summable.of_nonneg_of_le (fun i => ha _)
    henv (hg.mul_left (a N))
  have hs : Summable a := (summable_nat_add_iff N).mp ht
  have htail : (∑' n, a n)-∑ n ∈ Finset.range N, a n = ∑' i, a (i+N) := by
    have h := hs.sum_add_tsum_nat_add N
    linarith
  refine ⟨hs,?_,?_⟩
  · rw [htail]; exact tsum_nonneg (fun i => ha _)
  · rw [htail]
    calc
      (∑' i, a (i+N)) ≤ ∑' i, a N*ρ^i := ht.tsum_le_tsum henv (hg.mul_left _)
      _ = a N/(1-ρ) := by
        rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (show |ρ|<1 by rwa [abs_of_nonneg hρ]),div_eq_mul_inv]

def binomialTerm (α x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => binomialTerm α x n*(x*((n:ℝ)+α)/((n:ℝ)+1))

theorem binomialTerm_nonnegative (α x : ℝ) (hα : 0<α) (hx : 0≤x) :
    ∀ n, 0≤binomialTerm α x n := by
  intro n
  induction n with
  | zero => norm_num [binomialTerm]
  | succ n ih => simp only [binomialTerm]; positivity

/-- Exact bounds for the actual recursively defined binomial series. -/
theorem binomial_series_interval (α x : ℝ) (N : ℕ)
    (hα : 0<α) (hx : 0≤x)
    (hρ : x*max 1 (((N:ℝ)+α)/((N:ℝ)+1))<1) :
    Summable (binomialTerm α x) ∧
      0≤(∑' n, binomialTerm α x n)-∑ n ∈ Finset.range N, binomialTerm α x n ∧
      (∑' n, binomialTerm α x n)-∑ n ∈ Finset.range N, binomialTerm α x n
        ≤ binomialTerm α x N/(1-x*max 1 (((N:ℝ)+α)/((N:ℝ)+1))) := by
  apply positive_ratio_tail _ N _ (binomialTerm_nonnegative α x hα hx) (by positivity) hρ
  intro n hn
  simp only [binomialTerm]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (binomial_ratio_bound α x hx N n hn)
    (binomialTerm_nonnegative α x hα hx n)

/-- Rational endpoint witnesses enclose the nonnegative square-root branch. -/
theorem square_root_interval (l u v y : ℝ) (_hl : 0≤l) (hu : 0≤u) (hy : 0≤y)
    (hlo : l^2≤v) (hhi : v≤u^2) (hsquare : y^2=v) : l≤y ∧ y≤u := by
  constructor <;> nlinarith

end PerfectPower.CertifiedSeriesBounds
