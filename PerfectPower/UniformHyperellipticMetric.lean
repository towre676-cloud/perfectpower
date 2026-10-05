import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GeomSum

namespace PerfectPower.UniformHyperellipticMetric
open scoped BigOperators

/-- Common branch/infinity chart metric for y²=x^(2g+1)-x. -/
noncomputable def density (g : ℕ) (t : ℂ) : ℝ :=
  4*(∑ k ∈ Finset.range g, (‖t‖^4)^k)/‖1-t^(4*g)‖

theorem small_power (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (g : ℕ) (hg : 1 ≤ g) : q^g ≤ q := by
  have aux : ∀ k : ℕ, q^(k+1) ≤ q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul_of_nonneg_right ih h0).trans (by nlinarith)
  cases g with
  | zero => omega
  | succ k => exact aux k

/-- A genus-independent envelope: high-degree monomials never need expansion. -/
theorem disk_bounds (g : ℕ) (hg : 1 ≤ g) (t : ℂ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : ‖t‖^4 ≤ r) :
    4/(1+r) ≤ density g t ∧ density g t ≤ 4/(1-r)^2 := by
  let q := ‖t‖^4
  let S := ∑ k ∈ Finset.range g, q^k
  let D := ‖1-t^(4*g)‖
  have hq0 : 0 ≤ q := pow_nonneg (norm_nonneg t) _
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hq : q ≤ r := ht
  have hz : ‖t^(4*g)‖ ≤ r := by
    rw [norm_pow,pow_mul]
    exact (small_power q hq0 hq1 g hg).trans hq
  have hDhi : D ≤ 1+r := by
    have h := norm_sub_le (1:ℂ) (t^(4*g))
    rw [norm_one] at h
    exact h.trans (by linarith)
  have hDlo : 1-r ≤ D := by
    have h := norm_add_le (1-t^(4*g)) (t^(4*g))
    have he : (1-t^(4*g))+t^(4*g)=(1:ℂ) := by ring
    rw [he,norm_one] at h
    change 1 ≤ D+‖t^(4*g)‖ at h
    linarith
  have hDpos : 0 < D := by linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k)
  have hSlo : 1 ≤ S := by
    have h := Finset.single_le_sum (s := Finset.range g) (f := fun k => q^k)
      (fun k _ => pow_nonneg hq0 k) (Finset.mem_range.mpr (by omega : 0<g))
    simpa [S] using h
  have hgeom : S*(1-q)=1-q^g := geom_sum_mul_neg q g
  have hmul : S*(1-r) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show 1-r ≤ 1-q by linarith) hS0
    have hp := pow_nonneg hq0 g
    nlinarith
  have hrpos : 0 < 1-r := by linarith
  change 4/(1+r) ≤ 4*S/D ∧ 4*S/D ≤ 4/(1-r)^2
  constructor
  · apply (div_le_div_iff₀ (by linarith : 0<1+r) hDpos).mpr
    have hs := mul_le_mul_of_nonneg_right hSlo (show 0 ≤ 1+r by linarith)
    nlinarith
  · apply (div_le_div_iff₀ hDpos (sq_pos_of_pos hrpos)).mpr
    have hm := mul_le_mul_of_nonneg_right hmul hrpos.le
    nlinarith

/-- The same one-percent/three-percent bracket works at every positive genus. -/
theorem uniform_small_disk (g : ℕ) (hg : 1 ≤ g) (t : ℂ) (ht : ‖t‖^2 ≤ 1/8) :
    (99/100:ℝ)^2*4 < density g t ∧ density g t < (103/100:ℝ)^2*4 := by
  have hsq := (sq_le_sq₀ (sq_nonneg ‖t‖) (by norm_num : (0:ℝ)≤1/8)).mpr ht
  have hp : ‖t‖^4 ≤ (1/64:ℝ) := by nlinarith
  obtain ⟨hlo,hup⟩ := disk_bounds g hg t (1/64) (by norm_num) (by norm_num) hp
  constructor <;> norm_num at hlo hup ⊢ <;> linarith

end PerfectPower.UniformHyperellipticMetric
