import Mathlib.Tactic

/-! # Exact phase-moment induction and preservation of the weight-two zero

The definitions here are finite rational spectral data. Their analytic
identification with inverse-binomial arcsine series and normalized Mellin
values is given separately in the mathematical account. In particular,
the infinite-series identity is not assumed as a new Lean axiom.
-/

namespace PerfectPower.RaghavaInduction

open scoped BigOperators
open Finset

/-- The quadratic moment of a fiber before division by its conductor. -/
theorem centered_square_sum (d : ℕ) (x : ℚ) :
    (∑ j ∈ range d, (x + (j : ℚ) - ((d : ℚ) - 1) / 2) ^ 2) =
      d * x ^ 2 + d * ((d : ℚ) ^ 2 - 1) / 12 := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hshift :
        (∑ j ∈ range d, (x + (j : ℚ) - ((↑(d + 1) : ℚ) - 1) / 2) ^ 2) =
        ∑ j ∈ range d, ((x - 1 / 2) + (j : ℚ) - ((d : ℚ) - 1) / 2) ^ 2 := by
      apply sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hshift, ih]
    push_cast
    ring

/-- Twice the centered square is the first normalized arcsine moment. -/
def fiberMoment (d : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ range d, 2 * (((q + (j : ℚ)) / d) - 1 / 2) ^ 2

/-- The complete fiber formula, valid for every positive conductor ratio. -/
theorem fiberMoment_eq (d : ℕ) (hd : 0 < d) (q : ℚ) :
    fiberMoment d q = 2 * (q - 1 / 2) ^ 2 / d + ((d : ℚ) ^ 2 - 1) / (6 * d) := by
  have hne : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hterm (j : ℕ) :
      2 * (((q + (j : ℚ)) / d) - 1 / 2) ^ 2 =
      (2 / (d : ℚ) ^ 2) * ((q - 1 / 2) + j - ((d : ℚ) - 1) / 2) ^ 2 := by
    field_simp [hne]
    ring
  unfold fiberMoment
  simp_rw [hterm]
  rw [← mul_sum, centered_square_sum]
  field_simp [hne]
  ring

/-- Every branch stays in the principal phase interval needed by the arcsine formula. -/
theorem branch_phase_bounds (d j : ℕ) (hd : 0 < d) (hj : j < d)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (q + j) / d ∧ (q + j) / d ≤ 1 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hjq : (j : ℚ) + 1 ≤ d := by exact_mod_cast (Nat.succ_le_iff.mpr hj)
  constructor
  · positivity
  · apply (div_le_iff₀ hdq).mpr
    linarith

section FiniteProfile

variable {ι : Type*}

def mass (s : Finset ι) (w : ι → ℚ) : ℚ := ∑ i ∈ s, w i

def moment (s : Finset ι) (w q : ι → ℚ) : ℚ :=
  ∑ i ∈ s, w i * (2 * (q i - 1 / 2) ^ 2)

def inducedMass (d : ℕ) (s : Finset ι) (w : ι → ℚ) : ℚ :=
  ∑ i ∈ s, ∑ _j ∈ range d, w i

def inducedMoment (d : ℕ) (s : Finset ι) (w q : ι → ℚ) : ℚ :=
  ∑ i ∈ s, ∑ j ∈ range d, w i * (2 * (((q i + j) / d) - 1 / 2) ^ 2)

/-- The first moment's defect from its weight-two cancellation value. -/
def defect (s : Finset ι) (w q : ι → ℚ) : ℚ := moment s w q - mass s w / 6

/-- The second Bernoulli polynomial, with its usual normalization. -/
def bernoulliTwo (q : ℚ) : ℚ := q ^ 2 - q + 1 / 6

/-- The invariant is twice the weighted Bernoulli moment, not an arbitrary subtraction. -/
theorem defect_eq_bernoulli (s : Finset ι) (w q : ι → ℚ) :
    defect s w q = 2 * (∑ i ∈ s, w i * bernoulliTwo (q i)) := by
  unfold defect moment mass
  rw [sum_div, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro i _
  unfold bernoulliTwo
  ring

theorem inducedMass_eq (d : ℕ) (s : Finset ι) (w : ι → ℚ) :
    inducedMass d s w = d * mass s w := by
  simp [inducedMass, mass, mul_sum, sum_mul, mul_comm]

theorem inducedMoment_eq (d : ℕ) (hd : 0 < d) (s : Finset ι) (w q : ι → ℚ) :
    inducedMoment d s w q =
      moment s w q / d + ((d : ℚ) ^ 2 - 1) * mass s w / (6 * d) := by
  unfold inducedMoment
  have hinner (i : ι) :
      (∑ j ∈ range d, w i * (2 * (((q i + j) / d) - 1 / 2) ^ 2)) =
        w i * fiberMoment d (q i) := by
    rw [fiberMoment, mul_sum]
  simp_rw [hinner, fiberMoment_eq d hd]
  unfold moment mass
  simp_rw [mul_add, ← mul_div_assoc]
  rw [sum_add_distrib, ← sum_div, ← sum_div, ← sum_mul]
  ring

/-- Induction transports the cancellation defect by exactly 1/d. -/
theorem induction_defect (d : ℕ) (hd : 0 < d) (s : Finset ι) (w q : ι → ℚ) :
    inducedMoment d s w q - inducedMass d s w / 6 = defect s w q / d := by
  rw [inducedMoment_eq d hd, inducedMass_eq]
  unfold defect
  have hne : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hne]
  ring

/-- A zero is preserved and reflected; induction cannot fabricate a zero. -/
theorem induction_zero_iff (d : ℕ) (hd : 0 < d) (s : Finset ι) (w q : ι → ℚ) :
    inducedMoment d s w q - inducedMass d s w / 6 = 0 ↔ defect s w q = 0 := by
  rw [induction_defect d hd]
  have hne : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [div_eq_zero_iff, hne, or_false]

/-- Induction is an actual finite profile, with one point for every branch. -/
def inducedSet (d : ℕ) (s : Finset ι) : Finset (ι × ℕ) := s ×ˢ range d

def inducedWeight (w : ι → ℚ) (p : ι × ℕ) : ℚ := w p.1

def inducedPhase (d : ℕ) (q : ι → ℚ) (p : ι × ℕ) : ℚ := (q p.1 + p.2) / d

theorem mass_induced_profile (d : ℕ) (s : Finset ι) (w : ι → ℚ) :
    mass (inducedSet d s) (inducedWeight w) = inducedMass d s w := by
  simp [mass, inducedSet, inducedWeight, inducedMass, sum_product]

theorem moment_induced_profile (d : ℕ) (s : Finset ι) (w q : ι → ℚ) :
    moment (inducedSet d s) (inducedWeight w) (inducedPhase d q) =
      inducedMoment d s w q := by
  simp [moment, inducedSet, inducedWeight, inducedPhase, inducedMoment, sum_product]

theorem defect_induced_profile (d : ℕ) (hd : 0 < d) (s : Finset ι) (w q : ι → ℚ) :
    defect (inducedSet d s) (inducedWeight w) (inducedPhase d q) =
      defect s w q / d := by
  unfold defect
  rw [moment_induced_profile, mass_induced_profile]
  exact induction_defect d hd s w q

/-- A two-stage tower preserves the same defect as a single refinement by d*e. -/
theorem tower_defect (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (s : Finset ι) (w q : ι → ℚ) :
    defect (inducedSet e (inducedSet d s)) (inducedWeight (inducedWeight w))
        (inducedPhase e (inducedPhase d q)) = defect s w q / (d * e) := by
  rw [defect_induced_profile e he, defect_induced_profile d hd, div_div]

theorem tower_mass (d e : ℕ) (s : Finset ι) (w : ι → ℚ) :
    mass (inducedSet e (inducedSet d s)) (inducedWeight (inducedWeight w)) =
      (d * e : ℕ) * mass s w := by
  rw [mass_induced_profile, inducedMass_eq, mass_induced_profile, inducedMass_eq]
  push_cast
  ring

/-- Iterated branch induction agrees with one-step induction on the quadratic moment. -/
theorem tower_moment (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (s : Finset ι) (w q : ι → ℚ) :
    moment (inducedSet e (inducedSet d s)) (inducedWeight (inducedWeight w))
        (inducedPhase e (inducedPhase d q)) = inducedMoment (d * e) s w q := by
  have hleft := tower_defect d e hd he s w q
  have hright := induction_defect (d * e) (Nat.mul_pos hd he) s w q
  unfold defect at hleft hright
  rw [tower_mass] at hleft
  rw [inducedMass_eq] at hright
  push_cast at hleft hright
  linarith

end FiniteProfile

/-- The actual finite spectral multiplicities of eight regular Coxeter cycles
plus the eight primitive Cartan phases. The Lie-algebra identification is a
separate result, not encoded merely by this definition. -/
def adjointWeight (j : ℕ) : ℚ := 8 + if Nat.Coprime j 30 then 1 else 0

def reflectionWeight (j : ℕ) : ℚ := if Nat.Coprime j 30 then 1 else 0

def coxeterPhase (j : ℕ) : ℚ := (j : ℚ) / 30

/-- A general linear combination of the regular and primitive Coxeter spectra. -/
def coxeterWeight (a b : ℚ) (j : ℕ) : ℚ := a + if Nat.Coprime j 30 then b else 0

theorem coxeter_family_defect (a b : ℚ) :
    defect (range 30) (coxeterWeight a b) coxeterPhase = (a - 8 * b) / 90 := by
  norm_num [defect, moment, mass, coxeterWeight, coxeterPhase, sum_range_succ]
  ring

/-- Within this two-spectrum family, cancellation fixes the coefficient ratio. -/
theorem coxeter_family_zero_iff (a b : ℚ) :
    defect (range 30) (coxeterWeight a b) coxeterPhase = 0 ↔ a = 8 * b := by
  rw [coxeter_family_defect]
  constructor <;> intro h <;> linarith

theorem adjoint_mass : mass (range 30) adjointWeight = 248 := by
  norm_num [mass, adjointWeight, sum_range_succ]

theorem adjoint_moment : moment (range 30) adjointWeight coxeterPhase = 124 / 3 := by
  norm_num [moment, adjointWeight, coxeterPhase, sum_range_succ]

theorem adjoint_defect_zero : defect (range 30) adjointWeight coxeterPhase = 0 := by
  rw [defect, adjoint_moment, adjoint_mass]
  norm_num

theorem reflection_mass : mass (range 30) reflectionWeight = 8 := by
  norm_num [mass, reflectionWeight, sum_range_succ]
  decide

theorem reflection_moment : moment (range 30) reflectionWeight coxeterPhase = 56 / 45 := by
  norm_num [moment, reflectionWeight, coxeterPhase, sum_range_succ]

theorem reflection_defect : defect (range 30) reflectionWeight coxeterPhase = -(4 / 45) := by
  rw [defect, reflection_moment, reflection_mass]
  norm_num

/-- Every positive refinement preserves the adjoint weight-two zero. -/
theorem adjoint_all_refinements (d : ℕ) (hd : 0 < d) :
    inducedMoment d (range 30) adjointWeight coxeterPhase -
      inducedMass d (range 30) adjointWeight / 6 = 0 := by
  rw [induction_defect d hd, adjoint_defect_zero, zero_div]

theorem adjoint_264_mass : inducedMass 264 (range 30) adjointWeight = 65472 := by
  rw [inducedMass_eq, adjoint_mass]
  norm_num

theorem adjoint_264_moment :
    inducedMoment 264 (range 30) adjointWeight coxeterPhase = 10912 := by
  rw [inducedMoment_eq 264 (by norm_num), adjoint_moment, adjoint_mass]
  norm_num

/-- The 240-element fixed fiber has a different restricted character profile
from the 240 root directions, despite their equal dimensions. -/
def fixedFiberRestricted (j : ℕ) : ℕ := if j % 30 = 1 then 240 else 0

theorem fixed_fiber_not_root_profile : fixedFiberRestricted ≠ (fun _ : ℕ => 8) := by
  intro h
  have h0 := congrFun h 0
  norm_num [fixedFiberRestricted] at h0

end PerfectPower.RaghavaInduction
