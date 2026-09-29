import PerfectPower.Continuation.ProfileReduction

namespace PerfectPower.RationalYun
open Polynomial
open scoped BigOperators
noncomputable section

/-- Clear the rational linear root and strip the rational full-power factor.
The exceptional zero values remain hits even if the residual integer is not a power. -/
theorem radical_integer_reduction {X c u v n : ℤ} {h : ℚ} {r d : ℕ}
    (hd : d ≠ 0) (hv : v ≠ 0) (hr : r ≤ d)
    (hX : (X : ℚ) = (c : ℚ) * ((n : ℚ) - (u : ℚ) / (v : ℚ)) ^ r * h ^ d) :
    PerfectPower.IsHit d X ↔ X = 0 ∨
      PerfectPower.IsHit d (c * v ^ (d - r) * (v * n - u) ^ r) := by
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  have hlinear : (n : ℚ) - (u : ℚ) / (v : ℚ) =
      ((v : ℚ) * (n : ℚ) - (u : ℚ)) / (v : ℚ) := by
    field_simp
    ring
  have hpow : (v : ℚ) ^ d = (v : ℚ) ^ r * (v : ℚ) ^ (d - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hfac : (X : ℚ) =
      ((c * v ^ (d - r) * (v * n - u) ^ r : ℤ) : ℚ) * (h / (v : ℚ)) ^ d := by
    rw [hX]
    push_cast
    rw [hlinear, div_pow, div_pow, hpow]
    field_simp
    ring
  rw [integer_factor_reduction hd hfac]
  exact or_congr Iff.rfl (PerfectPower.isHit_iff_rat hd _).symm

/-- General radical-type reduction for integer polynomials with one bad root.
The result is pointwise and includes all exceptional zeros; counting is separate. -/
theorem Decomposition.integer_radical_reduction {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {d : ℕ}
    (hd : 2 ≤ d) (hbad : Y.badDegree d = 1) :
    ∃ u v : ℤ, 0 < v ∧ ∃ r : ℕ, 0 < r ∧ r < d ∧
      ∀ n : ℤ, PerfectPower.IsHit d (F.eval n) ↔ F.eval n = 0 ∨
        PerfectPower.IsHit d (F.leadingCoeff * v ^ (d - r) * (v * n - u) ^ r) := by
  obtain ⟨α, r, G, hr, hrd, hshape⟩ := Y.radical_shape_of_badDegree_one hd hbad
  refine ⟨α.num, α.den, ?_, r, hr, hrd, ?_⟩
  · exact_mod_cast α.den_pos
  · intro n
    apply radical_integer_reduction (h := G.eval (n : ℚ)) (by omega)
      (by exact_mod_cast α.den_ne_zero) (by omega)
    have heval := congrArg (Polynomial.eval (n : ℚ)) hshape
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_map] at heval
    have hmap : F.eval₂ (Int.castRingHom ℚ) (n : ℚ) = ((F.eval n : ℤ) : ℚ) := by
      change F.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) n) =
        (Int.castRingHom ℚ) (F.eval n)
      exact Polynomial.eval₂_at_apply (Int.castRingHom ℚ) n
    rw [hmap, Y.lead_eq_leadingCoeff,
      Polynomial.leadingCoeff_map' (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)] at heval
    simpa only [Int.cast_natCast, Rat.num_div_den] using heval

/-- General Pell-type reduction to rational square branches of a monic quadratic.
This proves the pointwise reduction, not orbit exhaustion or its asymptotic. -/
theorem Decomposition.integer_pell_reduction {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {e : ℕ} (he : e ≠ 0)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    (Y.pellPart e).Monic ∧ (Y.pellPart e).natDegree = 2 ∧
      ∀ n : ℤ, PerfectPower.IsHit (2 * e) (F.eval n) ↔ F.eval n = 0 ∨
        ∃ γ : ℚ, γ ^ e = (F.leadingCoeff : ℚ) ∧
          RatPower (γ * (Y.pellPart e).eval (n : ℚ)) 2 := by
  obtain ⟨hmon, hdeg, hshape⟩ := Y.pell_shape e hres hdegree
  refine ⟨hmon, hdeg, ?_⟩
  intro n
  apply pell_factor_reduction (h := (Y.quotientPart (2 * e)).eval (n : ℚ)) he
  have heval := congrArg (Polynomial.eval (n : ℚ)) hshape
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_map] at heval
  have hmap : F.eval₂ (Int.castRingHom ℚ) (n : ℚ) = ((F.eval n : ℤ) : ℚ) := by
    change F.eval₂ (Int.castRingHom ℚ) ((Int.castRingHom ℚ) n) =
      (Int.castRingHom ℚ) (F.eval n)
    exact Polynomial.eval₂_at_apply (Int.castRingHom ℚ) n
  rw [hmap, Y.lead_eq_leadingCoeff,
    Polynomial.leadingCoeff_map' (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)] at heval
  exact heval

end
end PerfectPower.RationalYun
