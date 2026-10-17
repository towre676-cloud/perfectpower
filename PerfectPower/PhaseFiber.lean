import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# Exact Fourier descent along a complete phase fiber

If `ζ` is a primitive `d`-th root of unity, the complete fiber
`a, a ζ, ..., a ζ^(d-1)` has a power trace supported exactly on exponents
divisible by `d`.  Thus the finite induction operation and a polynomial
observable commute through a precise coefficient filter.  The proof works
in every integral domain; it does not identify an unrelated set of the same
cardinality with this fiber, and does not assume an analytic continuation.

The finite result is the algebraic input for distribution identities of
absolutely convergent power/Dirichlet series.  Such an infinite-series
passage additionally requires its own convergence argument.
-/

namespace PerfectPower.PhaseFiber

open Finset

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The `k`-th power trace over all branches of one degree-`d` phase fiber. -/
def fiberMoment (d : ℕ) (a ζ : R) (k : ℕ) : R :=
  ∑ j ∈ range d, (a * ζ ^ j) ^ k

/-- The finite Fourier filter: a complete root orbit cancels every
frequency not divisible by its degree. -/
theorem sum_primitive_powers {d : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ d) (k : ℕ) :
    (∑ j ∈ range d, (ζ ^ j) ^ k) = if d ∣ k then (d : R) else 0 := by
  classical
  have hcomm (j : ℕ) : (ζ ^ j) ^ k = (ζ ^ k) ^ j := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp_rw [hcomm]
  by_cases h : d ∣ k
  · rw [if_pos h, (hζ.pow_eq_one_iff_dvd k).mpr h]
    simp
  · rw [if_neg h]
    have hpow : (ζ ^ k) ^ d = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hprod := geom_sum_mul (ζ ^ k) d
    rw [hpow, sub_self] at hprod
    exact (mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr fun h1 => h ((hζ.pow_eq_one_iff_dvd k).mp h1))

/-- A complete fiber preserves precisely its divisible moments, with
the exact multiplicity `d`.  No numerical approximation is involved. -/
theorem fiberMoment_eq_filter {d : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ d) (a : R) (k : ℕ) :
    fiberMoment d a ζ k = if d ∣ k then (d : R) * a ^ k else 0 := by
  classical
  unfold fiberMoment
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, sum_primitive_powers hζ]
  split_ifs <;> ring

/-- Evaluation of every finite polynomial observable descends through the
same Fourier filter, rather than through a separately chosen pairing. -/
theorem weighted_fiber_trace {d : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ d) (a : R) (s : Finset ℕ) (c : ℕ → R) :
    (∑ j ∈ range d, ∑ k ∈ s, c k * (a * ζ ^ j) ^ k) =
      ∑ k ∈ s, if d ∣ k then (d : R) * c k * a ^ k else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mul_sum, ← fiberMoment, fiberMoment_eq_filter hζ]
  split_ifs <;> ring

/-- The coefficient operator after removing the forced zero frequencies.
This is the exact algebraic operation behind a degree-`d` distribution
identity. -/
def descendCoefficients (d : ℕ) (c : ℕ → R) (k : ℕ) : R :=
  (d : R) * c (d * k)

omit [IsDomain R] in
/-- Successive complete descents are the same as descent through the
product-degree tower.  The degrees need not be coprime. -/
theorem descendCoefficients_comp (d e : ℕ) (c : ℕ → R) :
    descendCoefficients d (descendCoefficients e c) =
      descendCoefficients (d * e) c := by
  funext k
  simp only [descendCoefficients, Nat.cast_mul]
  rw [show e * (d * k) = d * e * k by ring]
  ring

/-- The actual 264-branch artifact therefore has an exact moment filter. -/
theorem artifact_fiber_filter {ζ : R} (hζ : IsPrimitiveRoot ζ 264)
    (a : R) (k : ℕ) :
    (∑ j ∈ range 264, (a * ζ ^ j) ^ k) =
      if 264 ∣ k then (264 : R) * a ^ k else 0 :=
  fiberMoment_eq_filter hζ a k

/-- For a fiber above the primitive phase `1/n`, only the new relative
degree can obstruct primitivity: its numerator is already coprime to `n`.
This reduces the full conductor test without enumerating its roots. -/
theorem primitive_fiber_coprime (n d j : ℕ) :
    Nat.Coprime (1 + n * j) (n * d) ↔ Nat.Coprime (1 + n * j) d := by
  rw [Nat.coprime_mul_iff_right]
  simp

/-- Arithmetic branch indices of the artifact fiber above `1/1680`.
Index `j` represents the rational phase `(1 + 1680*j)/443520`. -/
def artifactPrimitiveBranches : Finset ℕ :=
  (range 264).filter fun j => Nat.Coprime (1 + 1680 * j) 443520

/-- Exact primitive-branch count, checked by ordinary kernel reduction. -/
theorem artifact_primitive_count : artifactPrimitiveBranches.card = 240 := by
  decide +kernel

/-- The remaining 24 branches are not primitive at conductor 443520. -/
theorem artifact_nonprimitive_count :
    ((range 264).filter fun j => ¬ Nat.Coprime (1 + 1680 * j) 443520).card = 24 := by
  decide +kernel

/-- Every excluded branch, with no omissions or duplicate parameters.
The new prime 11 removes exactly the residue class `j = 4 mod 11`. -/
theorem artifact_nonprimitive_parameterization :
    ((range 264).filter fun j => ¬ Nat.Coprime (1 + 1680 * j) 443520) =
      (range 24).image (fun t => 4 + 11 * t) := by
  decide +kernel

/-- The primitive 240-branch spectrum has a specific two-filter trace.
This is stronger than its cardinality: its removed frequencies and their
phase shift are completely determined. -/
theorem artifact_primitive_trace {ζ : R} (hζ : IsPrimitiveRoot ζ 264)
    (a : R) (k : ℕ) :
    (∑ j ∈ artifactPrimitiveBranches, (a * ζ ^ j) ^ k) =
      (if 264 ∣ k then (264 : R) * a ^ k else 0) -
      (if 24 ∣ k then (24 : R) * (a * ζ ^ 4) ^ k else 0) := by
  classical
  have h24 : IsPrimitiveRoot (ζ ^ 11) 24 := by
    simpa using hζ.pow_of_dvd (p := 11) (by decide) (by decide)
  have hexcluded :
      (∑ j ∈ (range 264).filter (fun j => ¬ Nat.Coprime (1 + 1680 * j) 443520),
        (a * ζ ^ j) ^ k) = fiberMoment 24 (a * ζ ^ 4) (ζ ^ 11) k := by
    rw [artifact_nonprimitive_parameterization, Finset.sum_image]
    · unfold fiberMoment
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      rw [pow_add, pow_mul]
      ring
    · intro t ht u hu htu
      omega
  have hsplit :
      (∑ j ∈ artifactPrimitiveBranches, (a * ζ ^ j) ^ k) +
        (∑ j ∈ (range 264).filter (fun j => ¬ Nat.Coprime (1 + 1680 * j) 443520),
          (a * ζ ^ j) ^ k) = fiberMoment 264 a ζ k := by
    unfold artifactPrimitiveBranches fiberMoment
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [hexcluded, fiberMoment_eq_filter h24, fiberMoment_eq_filter hζ] at hsplit
  exact eq_sub_iff_add_eq.mpr hsplit

/-- The same distribution holds for an actual convergent complex series.
Summability is an explicit hypothesis for every branch; it is not inferred
from the finite identity or hidden behind a formal infinite expression. -/
theorem summable_fiber_trace {d : ℕ} {a ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (c : ℕ → ℂ)
    (hc : ∀ j ∈ range d, Summable fun k => c k * (a * ζ ^ j) ^ k) :
    (∑ j ∈ range d, ∑' k : ℕ, c k * (a * ζ ^ j) ^ k) =
      ∑' k : ℕ, if d ∣ k then (d : ℂ) * c k * a ^ k else 0 := by
  classical
  rw [← Summable.tsum_finsetSum hc]
  apply tsum_congr
  intro k
  rw [← Finset.mul_sum, ← fiberMoment, fiberMoment_eq_filter hζ]
  split_ifs <;> ring

section FaithfulTrace

variable {N : ℕ} [NeZero N]

/-- All complex character traces of one finite phase spectrum.  Positive
frequencies match the power traces used by the cyclic period family. -/
noncomputable def phaseTrace (c : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j : ZMod N, c j * ZMod.stdAddChar (j * k)

/-- The trace profile is the usual discrete Fourier transform with
the frequency sign reversed. -/
theorem phaseTrace_eq_dft (c : ZMod N → ℂ) (k : ZMod N) :
    phaseTrace c k = ZMod.dft c (-k) := by
  simp only [phaseTrace, ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- An explicit inverse recovers every phase multiplicity from the full
complex trace profile.  Thus the trace is computationally reversible. -/
theorem phaseTrace_reconstruction (c : ZMod N → ℂ) (j : ZMod N) :
    c j = (N : ℂ)⁻¹ *
      ∑ k : ZMod N, phaseTrace c k * ZMod.stdAddChar (-(j * k)) := by
  have hfun : phaseTrace c = fun k => ZMod.dft c (-k) :=
    funext (phaseTrace_eq_dft c)
  have hinv : ZMod.dft (phaseTrace c) j = (N : ℂ) * c j := by
    rw [hfun, ZMod.dft_comp_neg, ZMod.dft_dft]
    simp only [neg_neg, smul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := NeZero.ne _
  calc
    c j = (N : ℂ)⁻¹ * ((N : ℂ) * c j) := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    _ = (N : ℂ)⁻¹ * ZMod.dft (phaseTrace c) j := by rw [hinv]
    _ = _ := by
      rw [ZMod.dft_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [smul_eq_mul, mul_comm, mul_comm j k]

/-- The complete complex trace family is faithful: no distinct finite
phase spectra can have all the same character traces.  This statement
does not assert faithfulness of one weight or of real parts alone. -/
theorem phaseTrace_injective :
    Function.Injective (phaseTrace (N := N)) := by
  intro c e h
  apply ZMod.dft.injective
  funext k
  have hk := congrFun h (-k)
  simpa only [phaseTrace_eq_dft, neg_neg] using hk

/-- Equality of every trace is an exact equality criterion for a finite
spectrum, valid at every positive conductor. -/
theorem phaseTrace_eq_iff (c e : ZMod N → ℂ) :
    (∀ k, phaseTrace c k = phaseTrace e k) ↔ c = e := by
  constructor
  · intro h
    exact phaseTrace_injective (funext h)
  · intro h
    subst e
    intro k
    rfl

end FaithfulTrace

end PerfectPower.PhaseFiber
