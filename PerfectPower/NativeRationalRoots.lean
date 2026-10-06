import PerfectPower.NativePolynomialRoots
import PerfectPower.EllipticDivision

/-! Complete rational roots using the proved signed-divisor integer generator.
The producer supplies a monic scaled coefficient list, never a root list.
Both monicity and the scaling identity remain kernel-checked premises. -/
namespace PerfectPower.NativeRationalRoots
open NativePolynomialSquare

/-- Scale the complete integer root finset back to rational coordinates. -/
def roots (as : List ℤ) (D : ℚ) : Finset ℚ :=
  (NativePolynomialRoots.roots as).image (fun z : ℤ => (z : ℚ) / D)

theorem complete (f : Polynomial ℚ) (as : List ℤ) (D : ℚ)
    (hD : D ≠ 0) (hv : valid as) (hm : (polynomial as).Monic)
    (hscale : (polynomial as).map (Int.castRingHom ℚ) = f.scaleRoots D)
    (r : ℚ) : f.eval r = 0 ↔ r ∈ roots as D := by
  classical
  have hL : ∀ z : ℤ, (polynomial as).eval z = 0 ↔
      z ∈ (NativePolynomialRoots.roots as).toList := by
    intro z
    rw [polynomial_eval, Finset.mem_toList]
    exact NativePolynomialRoots.complete as hv z
  rw [EllipticDivision.rational_root_list_complete f (polynomial as) D hD hm hscale
    (NativePolynomialRoots.roots as).toList hL r]
  simp only [List.mem_map, Finset.mem_toList, roots, Finset.mem_image]

/-- Normalize the leading coefficient without changing any roots. -/
noncomputable def normalize (f : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.C f.leadingCoeff⁻¹ * f

theorem normalize_root_iff (f : Polynomial ℚ) (hf : f ≠ 0) (r : ℚ) :
    (normalize f).eval r = 0 ↔ f.eval r = 0 := by
  have hc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  simp [normalize, hc]

/-- Arbitrary nonzero rational polynomials are admitted after a checked leading
coefficient normalization. Neither monic input nor integral input is required. -/
theorem complete_nonmonic (f : Polynomial ℚ) (hf : f ≠ 0) (as : List ℤ) (D : ℚ)
    (hD : D ≠ 0) (hv : valid as) (hm : (polynomial as).Monic)
    (hscale : (polynomial as).map (Int.castRingHom ℚ) = (normalize f).scaleRoots D)
    (r : ℚ) : f.eval r = 0 ↔ r ∈ roots as D := by
  rw [← normalize_root_iff f hf r]
  exact complete (normalize f) as D hD hv hm hscale r

end PerfectPower.NativeRationalRoots
