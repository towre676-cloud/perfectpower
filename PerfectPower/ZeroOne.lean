import PerfectPower.Dichotomy

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Density one, and the formal 0–1 law on the rigid branch -/

/-- If every positive index is a hit, the count is `A(N) = N`. -/
lemma A_eq_self_of_forall {S : ℕ → ℤ} {d : ℕ} {k : ℤ}
    (h : ∀ n, 1 ≤ n → IsHit d (S n + k)) (N : ℕ) : A S d k N = N := by
  induction N with
  | zero => exact A_zero S d k
  | succ N ih => rw [A_succ, if_pos (h _ (by omega)), ih]

/-- If every positive index is a hit, the density exists and equals one. -/
theorem hasDensity_one_of_forall {S : ℕ → ℤ} {d : ℕ} {k : ℤ}
    (h : ∀ n, 1 ≤ n → IsHit d (S n + k)) : HasDensity S d k 1 := by
  unfold HasDensity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold ratio
  rw [A_eq_self_of_forall h N, div_self hN']

/-- An integer-polynomial `d`-th power hits at every index, so its hit density is one. -/
theorem hasDensity_one_of_pow {d : ℕ} {F G : ℤ[X]} (h : F = G ^ d) :
    HasDensity (fun n => F.eval (n : ℤ)) d 0 1 :=
  hasDensity_one_of_forall fun n _ => by simpa using hit_of_pow_eq h n

/-- **Formal 0–1 law on the rigid branch.**  If `d ≥ 2`, `d ∣ deg F` and the leading coefficient
of `F ≠ 0` is an integer `d`-th power, then the hit density of `F(n)` exists and is `1` (exactly
when `F = G^d` with `G ∈ ℤ[X]`) or `0` (when the hit set is finite). -/
theorem rigid_zero_one {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} (hF : IsRigid d F) (hF0 : F ≠ 0) :
    ((∃ G : ℤ[X], F = G ^ d) ∧ HasDensity (fun n => F.eval (n : ℤ)) d 0 1) ∨
    ((hitSet (fun n => F.eval (n : ℤ)) d 0).Finite ∧
      HasDensity (fun n => F.eval (n : ℤ)) d 0 0) := by
  rcases rigid_dichotomy hd hF hF0 with ⟨G, hG⟩ | hfin
  · exact Or.inl ⟨⟨G, hG⟩, hasDensity_one_of_pow hG⟩
  · exact Or.inr ⟨hfin, hasDensity_zero_of_finite hfin⟩

/-- Corollary in the language of upper density: on the rigid branch `H ∈ {0, 1}`. -/
theorem rigid_H_mem {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} (hF : IsRigid d F) (hF0 : F ≠ 0) :
    H (fun n => F.eval (n : ℤ)) d 0 = 0 ∨ H (fun n => F.eval (n : ℤ)) d 0 = 1 := by
  rcases rigid_zero_one hd hF hF0 with ⟨_, h1⟩ | ⟨_, h0⟩
  · exact Or.inr (H_eq_of_hasDensity h1)
  · exact Or.inl (H_eq_of_hasDensity h0)

/-! ### Twisted powers: `c · G^d` with `c` not a `d`-th power -/

/-- If `c · g^d = m^d` in `ℤ` with `g ≠ 0` and `d ≠ 0`, then `c` is a `d`-th power. -/
lemma pow_of_mul_pow_eq {d : ℕ} (hd : d ≠ 0) {c g m : ℤ} (hg : g ≠ 0)
    (h : c * g ^ d = m ^ d) : ∃ b : ℤ, c = b ^ d := by
  have hdvd : g ^ d ∣ m ^ d := ⟨c, by rw [← h]; ring⟩
  obtain ⟨b, rfl⟩ := (Int.pow_dvd_pow_iff hd).mp hdvd
  refine ⟨b, ?_⟩
  have hgd : g ^ d ≠ 0 := pow_ne_zero d hg
  apply mul_right_cancel₀ hgd
  rw [h, mul_pow]; ring

/-- **Twisted powers.**  Suppose `D^d · F = c · H^d` in `ℤ[X]` with `c` not an integer
`d`-th power (any `D`, e.g. a common denominator).  Then every hit of `F` is a zero of `H`; in particular, if `H ≠ 0` the hit set is
finite.  (Over `ℚ`: `F = c · G^d` with `G = H / D`, e.g. `F = 2 n^2`, `d = 2`.) -/
theorem twisted_hits_subset {d : ℕ} (hd : 2 ≤ d) {F H : ℤ[X]} {c D : ℤ}
    (hc : ¬ ∃ b : ℤ, c = b ^ d) (hFH : C (D ^ d) * F = C c * H ^ d) :
    hitSet (fun n => F.eval (n : ℤ)) d 0 ⊆ {n | H.eval (n : ℤ) = 0} := by
  intro n hn
  obtain ⟨_, m, hm⟩ := hn
  simp only [add_zero] at hm
  by_contra hH
  have hev := congrArg (Polynomial.eval (n : ℤ)) hFH
  simp only [eval_mul, eval_C, eval_pow] at hev
  rw [hm, ← mul_pow] at hev
  exact hc (pow_of_mul_pow_eq (by omega) hH hev.symm)

/-- Twisted powers with `H ≠ 0` have finitely many hits. -/
theorem twisted_finite {d : ℕ} (hd : 2 ≤ d) {F H : ℤ[X]} {c D : ℤ}
    (hc : ¬ ∃ b : ℤ, c = b ^ d) (hFH : C (D ^ d) * F = C c * H ^ d) (hH : H ≠ 0) :
    (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite := by
  refine Set.Finite.subset ?_ (twisted_hits_subset hd hc hFH)
  have hfin : {z : ℤ | H.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hH
  refine (hfin.preimage (Nat.cast_injective.injOn)).subset ?_
  intro n hn
  simpa [Polynomial.IsRoot] using hn

/-- Twisted powers with `H ≠ 0` have hit density zero. -/
theorem twisted_density_zero {d : ℕ} (hd : 2 ≤ d) {F H : ℤ[X]} {c D : ℤ}
    (hc : ¬ ∃ b : ℤ, c = b ^ d) (hFH : C (D ^ d) * F = C c * H ^ d) (hH : H ≠ 0) :
    HasDensity (fun n => F.eval (n : ℤ)) d 0 0 :=
  hasDensity_zero_of_finite (twisted_finite hd hc hFH hH)

end PerfectPower
