import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import PerfectPower.BernsteinBoxes

/-! Conformal algebra and the missing common-path smooth-distance bridge.
The path family is explicit: this never identifies an arbitrary mesh with a
smooth curve, and never extends a contained chart domain to unrestricted paths. -/
namespace PerfectPower.MichorGeometry
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem factor_clears (a b n d f : ℝ) (hb : b=d*f) (ha : a=n*f) : n*b=d*a := by
  rw [hb,ha]
  ring

/-- Factor a tensor proof into small univariate row identities. -/
theorem tensor_rows (m n : ℕ) (c : Fin (m+1) → Fin (n+1) → ℚ)
    (r : Fin (m+1) → ℝ → ℝ)
    (hr : ∀ i t, (∑ j, (c i j : ℝ)*PerfectPower.BernsteinBoxes.basis n j t)=r i t)
    (s t : ℝ) : PerfectPower.BernsteinBoxes.tensor m n c s t =
      ∑ i, r i t*PerfectPower.BernsteinBoxes.basis m i s := by
  unfold PerfectPower.BernsteinBoxes.tensor
  apply Finset.sum_congr rfl
  intro i _
  rw [← hr i t, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

def accelX (gx gy u v : ℝ) := (v*v-u*u)*gx/2-u*v*gy
def accelY (gx gy u v : ℝ) := (u*u-v*v)*gy/2-u*v*gx

theorem geodesic_energy_rate (gx gy u v : ℝ) :
    (gx*u+gy*v)*(u*u+v*v)+2*(u*accelX gx gy u v+v*accelY gx gy u v)=0 := by
  unfold accelX accelY; ring

def transportX (gx gy u v zx zy : ℝ) :=
  -((gx*u+gy*v)*zx+(gx*zx+gy*zy)*u-(u*zx+v*zy)*gx)/2
def transportY (gx gy u v zx zy : ℝ) :=
  -((gx*u+gy*v)*zy+(gx*zx+gy*zy)*v-(u*zx+v*zy)*gy)/2

theorem parallel_norm_rate (gx gy u v zx zy : ℝ) :
    (gx*u+gy*v)*(zx*zx+zy*zy)+
      2*(zx*transportX gx gy u v zx zy+zy*transportY gx gy u v zx zy)=0 := by
  unfold transportX transportY; ring

theorem hamiltonian_energy_rate (rho gx gy px py : ℝ) :
    -((px*px+py*py)/(2*rho))*(gx*(px/rho)+gy*(py/rho))+
    (px/rho)*((px*px+py*py)*gx/(2*rho))+
    (py/rho)*((px*px+py*py)*gy/(2*rho))=0 := by ring

theorem conformal_speed_bounds (rho l u speed : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hs : 0 ≤ speed) (hlo : l^2 ≤ rho) (hup : rho ≤ u^2) :
    l*speed ≤ Real.sqrt rho*speed ∧ Real.sqrt rho*speed ≤ u*speed := by
  have h1 : l ≤ Real.sqrt rho := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg hl] using Real.sqrt_le_sqrt hlo
  have h2 : Real.sqrt rho ≤ u := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg hu] using Real.sqrt_le_sqrt hup
  exact ⟨mul_le_mul_of_nonneg_right h1 hs,mul_le_mul_of_nonneg_right h2 hs⟩

theorem integrated_length_bounds (f g : ℝ → ℝ) (l u : ℝ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (h : ∀ t ∈ Icc (0:ℝ) 1, l*f t ≤ g t ∧ g t ≤ u*f t) :
    l*(∫ t in (0:ℝ)..1, f t) ≤ (∫ t in (0:ℝ)..1, g t) ∧
      (∫ t in (0:ℝ)..1, g t) ≤ u*(∫ t in (0:ℝ)..1, f t) := by
  constructor
  · have hb := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (hf.const_mul l) hg (fun t ht => (h t ht).1)
    simpa only [intervalIntegral.integral_const_mul] using hb
  · have hb := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      hg (hf.const_mul u) (fun t ht => (h t ht).2)
    simpa only [intervalIntegral.integral_const_mul] using hb

/-- The infima range over the SAME nonempty path family. -/
theorem common_path_distance_bounds {P : Type*} [Nonempty P]
    (base smooth : P → ℝ) (l u : ℝ) (hl : 0 ≤ l) (hu : 0 < u)
    (hb : ∀ p, 0 ≤ base p) (hs : ∀ p, 0 ≤ smooth p)
    (hlo : ∀ p, l*base p ≤ smooth p) (hup : ∀ p, smooth p ≤ u*base p) :
    l*sInf (range base) ≤ sInf (range smooth) ∧
      sInf (range smooth) ≤ u*sInf (range base) := by
  have bb : BddBelow (range base) := ⟨0, by rintro _ ⟨p,rfl⟩; exact hb p⟩
  have bs : BddBelow (range smooth) := ⟨0, by rintro _ ⟨p,rfl⟩; exact hs p⟩
  constructor
  · apply le_csInf (range_nonempty smooth)
    rintro _ ⟨p,rfl⟩
    exact (mul_le_mul_of_nonneg_left (csInf_le bb (mem_range_self p)) hl).trans (hlo p)
  · have hd : sInf (range smooth)/u ≤ sInf (range base) := by
      apply le_csInf (range_nonempty base)
      rintro _ ⟨p,rfl⟩
      apply (div_le_iff₀ hu).mpr
      simpa only [mul_comm] using (csInf_le bs (mem_range_self p)).trans (hup p)
    simpa only [mul_comm] using (div_le_iff₀ hu).mp hd

/-- Explicit smooth whole-plane metric, not a statement about a compact curve. -/
def planeDensity (x y : ℝ) := (1+2*x*x+2*y*y)/(1+x*x+y*y)
theorem plane_density_bounds (x y : ℝ) : 1 ≤ planeDensity x y ∧ planeDensity x y ≤ 2 := by
  have hd : 0 < 1+x*x+y*y := by nlinarith [sq_nonneg x,sq_nonneg y]
  unfold planeDensity
  constructor
  · apply (le_div_iff₀ hd).mpr; nlinarith [sq_nonneg x,sq_nonneg y]
  · apply (div_le_iff₀ hd).mpr; nlinarith

theorem plane_rational_scale_bounds (x y : ℝ) :
    (1:ℝ)^2 ≤ planeDensity x y ∧ planeDensity x y ≤ (3/2:ℝ)^2 := by
  have h := plane_density_bounds x y
  constructor <;> nlinarith

/-- Stereographic coordinates actually lie on the unit sphere. -/
theorem stereographic_unit_sphere (x y : ℝ) :
    (2*x/(1+x^2+y^2))^2+(2*y/(1+x^2+y^2))^2+
      ((x^2+y^2-1)/(1+x^2+y^2))^2=1 := by
  have hd : 1+x^2+y^2 ≠ 0 := by nlinarith [sq_nonneg x,sq_nonneg y]
  field_simp
  <;> ring

theorem complex_chart_norm (x y : ℝ) : ‖(⟨x,y⟩ : ℂ)‖^2=x*x+y*y := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]

theorem finite_norm_density (z : ℂ) (hlo : 2 ≤ ‖z‖) (hhi : ‖z‖ ≤ (23/10:ℝ)) :
    (1/4:ℝ)^2 < (1+‖z‖^2)/‖z^5-z‖ ∧ (1+‖z‖^2)/‖z^5-z‖ < 1 := by
  have low5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlo 5
  have high5 := pow_le_pow_left₀ (norm_nonneg z) hhi 5
  have low := norm_sub_norm_le (z^5) z
  have high := norm_sub_le (z^5) z
  rw [norm_pow] at low high
  norm_num at low5 high5
  have hp : 0 < ‖z^5-z‖ := by linarith
  have hn0 : 5 ≤ 1+‖z‖^2 := by nlinarith [norm_nonneg z]
  have hn1 : 1+‖z‖^2 < 7 := by nlinarith [norm_nonneg z]
  constructor
  · apply (lt_div_iff₀ hp).mpr
    norm_num
    nlinarith
  · apply (div_lt_iff₀ hp).mpr
    norm_num
    linarith

theorem branch_norm_density (z : ℂ) (hhi : ‖z‖ ≤ (1/2:ℝ)) :
    1 < (4*(1+‖z‖^4))/‖z^8-1‖ ∧ (4*(1+‖z‖^4))/‖z^8-1‖ < 9 := by
  have high8 := pow_le_pow_left₀ (norm_nonneg z) hhi 8
  have high4 := pow_le_pow_left₀ (norm_nonneg z) hhi 4
  have low := norm_sub_norm_le (1:ℂ) (z^8)
  have high := norm_sub_le (z^8) (1:ℂ)
  rw [norm_one,norm_pow,norm_sub_rev] at low
  rw [norm_pow,norm_one] at high
  norm_num at high8 high4
  have hp : 0 < ‖z^8-1‖ := by linarith
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (‖z‖^2)]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith

#print axioms finite_norm_density
#print axioms branch_norm_density
#print axioms geodesic_energy_rate
#print axioms parallel_norm_rate
#print axioms hamiltonian_energy_rate
#print axioms conformal_speed_bounds
#print axioms integrated_length_bounds
#print axioms common_path_distance_bounds
#print axioms plane_density_bounds
#print axioms stereographic_unit_sphere
end
end PerfectPower.MichorGeometry
