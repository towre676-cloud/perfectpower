import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Kernel-proved Legendre-series recurrence and real geometric-tail bounds.
Identification of this series with analytic curve periods is a separate theorem. -/
noncomputable section

namespace PerfectPower.LegendreBounds
open scoped BigOperators

def coefficient : ℕ → ℝ
  | 0 => 1
  | n+1 => coefficient n * (2*(n:ℝ)+1)^2 / (4*((n:ℝ)+1)^2)

theorem coefficient_positive (n : ℕ) : 0 < coefficient n := by
  induction n with
  | zero => norm_num [coefficient]
  | succ n ih => simp only [coefficient]; positivity

theorem coefficient_step_le (n : ℕ) : coefficient (n+1) ≤ coefficient n := by
  rw [coefficient, div_le_iff₀ (by positivity)]
  have hp := coefficient_positive n
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith

theorem coefficient_antitone : Antitone coefficient :=
  antitone_nat_of_succ_le coefficient_step_le

theorem legendre_formal_period_recurrence (n : ℕ) :
    ((n:ℝ)+1)^2 * coefficient (n+1) = ((n:ℝ)+1/2)^2 * coefficient n := by
  rw [coefficient]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

def series (lambda : ℝ) : ℝ := ∑' n : ℕ, coefficient n * lambda^n
def partialSum (lambda : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, coefficient n * lambda^n

/-- A generic decreasing positive coefficient sequence has the claimed tail. -/
theorem geometric_tail (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hm : Antitone a)
    (lambda : ℝ) (hl : 0 ≤ lambda) (hu : lambda < 1) (N : ℕ) :
    Summable (fun n => a n * lambda^n) ∧
      0 ≤ (∑' n, a n * lambda^n) - ∑ n ∈ Finset.range N, a n * lambda^n ∧
      (∑' n, a n * lambda^n) - ∑ n ∈ Finset.range N, a n * lambda^n ≤
        a N * lambda^N / (1-lambda) := by
  have habs : |lambda| < 1 := by rwa [abs_of_nonneg hl]
  have hg := summable_geometric_of_abs_lt_one habs
  have hs : Summable (fun n => a n * lambda^n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha n) (pow_nonneg hl n))
      (fun n => mul_le_mul_of_nonneg_right (hm (Nat.zero_le n)) (pow_nonneg hl n))
      (hg.mul_left (a 0))
  have htail : (∑' n, a n * lambda^n) - ∑ n ∈ Finset.range N, a n * lambda^n =
      ∑' i, a (i+N) * lambda^(i+N) := by
    have h := hs.sum_add_tsum_nat_add N
    linarith
  refine ⟨hs, ?_, ?_⟩
  · rw [htail]
    exact tsum_nonneg (fun n => mul_nonneg (ha _) (pow_nonneg hl _))
  · rw [htail]
    have hb : Summable (fun i => a N * lambda^N * lambda^i) := hg.mul_left _
    have ht : Summable (fun i => a (i+N) * lambda^(i+N)) := hs.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
    calc
      (∑' i, a (i+N) * lambda^(i+N)) ≤ ∑' i, a N * lambda^N * lambda^i := by
        apply ht.tsum_le_tsum _ hb
        intro i
        have hcoef := hm (show N ≤ i+N by omega)
        rw [pow_add]
        nlinarith [pow_nonneg hl i, pow_nonneg hl N,
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg hl i) (pow_nonneg hl N))]
      _ = a N * lambda^N / (1-lambda) := by
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one habs, div_eq_mul_inv]

theorem series_interval (lambda : ℝ) (hl : 0 ≤ lambda) (hu : lambda < 1) (N : ℕ) :
    partialSum lambda N ≤ series lambda ∧
    series lambda ≤ partialSum lambda N + coefficient N * lambda^N/(1-lambda) := by
  obtain ⟨_, hlo, hhi⟩ := geometric_tail coefficient
    (fun n => (coefficient_positive n).le) coefficient_antitone lambda hl hu N
  unfold partialSum series
  constructor <;> linarith

noncomputable def formalSeries : PowerSeries ℝ := PowerSeries.mk coefficient

/-- The actual formal power series satisfies the Picard–Fuchs operator.
This is an identity of power series, without an analytic period premise. -/
theorem legendre_formal_ode :
    PowerSeries.X^1 * (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ formalSeries)) -
    PowerSeries.X^2 * (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ formalSeries)) +
    PowerSeries.derivative ℝ formalSeries -
    PowerSeries.C ℝ 2 * (PowerSeries.X^1 * (PowerSeries.derivative ℝ formalSeries)) -
    PowerSeries.C ℝ (1/4) * formalSeries = 0 := by
  ext n
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_derivative,
    formalSeries, PowerSeries.coeff_mk]
  cases n with
  | zero => norm_num [coefficient]
  | succ n =>
    cases n with
    | zero => norm_num [coefficient]
    | succ n =>
      have h := legendre_formal_period_recurrence (n+2)
      simp only [Nat.succ_eq_add_one] at *
      simp only [show 1 ≤ n+1+1 by omega, show 2 ≤ n+1+1 by omega,
        ite_true, Nat.add_sub_cancel] at *
      push_cast at *
      ring_nf at h ⊢
      linarith

end PerfectPower.LegendreBounds
