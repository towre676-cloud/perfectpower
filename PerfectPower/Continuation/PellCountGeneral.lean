import PerfectPower.Continuation.RadicalCountGeneral
import Mathlib.NumberTheory.Pell

/-!
# Theorem C as a count, for a general integer polynomial

`Decomposition.integer_pell_reduction` says that, for `F ∈ ℤ[X]` of Pell type (every layer's
multiplicity is `≡ 0` or `≡ e (mod 2e)`, and the `e`-layers have total degree 2), `F(n)` is a
`2e`-th power iff `F(n) = 0` or `γ · Q(n)` is a rational square for some rational `γ` with
`γ^e = lc(F)`, where `Q` is the monic quadratic `pellPart`.  This file turns that into a count.

* `pellPart_squarefree`, `disc_ne_zero`: `Q` is squarefree (its layers are squarefree and
  pairwise coprime), so its discriminant `b^2 - 4c` is nonzero.  Without this the count could be
  linear.
* At most two branches: `γ^e = lc` has at most the solutions `± γ₀` (`pow_eq_pow_iff_of_ne_zero`);
  if it has none, only the zeros of `F` remain.
* `clear_denoms`: each branch is exactly `A n^2 + B n + C ∈ □` with integers `A ≠ 0` and
  `B^2 - 4AC ≠ 0`.
* `branch_count`: `A < 0` gives a bounded count; `A` a positive square gives a bounded count
  (a difference of squares equals the nonzero discriminant); `A > 0` not a square gets a Pell unit
  from Mathlib (`Pell.exists_of_not_isSquare`) and the exact count `atlas_pell`.
* The two branches overlap only at roots of `Q` (`opposite_squares_iff_zero`); the zeros of `F`
  add at most `deg F`.

`Decomposition.pell_count`: `|A(N) - κ log N| ≤ K` for all large `N`, with `κ ≥ 0`.  Here `κ` is
the sum of the branch constants, and `0` when every branch is bounded.  Whether a given branch
has `κ > 0` (orbit population) is not decided here.
-/

open Finset Polynomial
open scoped Classical

namespace PerfectPower.RationalYun

/-- A finite product of squarefree, pairwise coprime polynomials is squarefree. -/
lemma squarefree_prod_of_coprime {ι : Type*} (s : Finset ι) (f : ι → ℚ[X])
    (hsq : ∀ i ∈ s, Squarefree (f i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, squarefree_mul_iff]
    refine ⟨?_, hsq a (mem_insert_self a s),
      ih (fun i hi => hsq i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hcop i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)⟩
    apply IsCoprime.isRelPrime
    apply IsCoprime.prod_right
    intro j hj
    exact hcop a (mem_insert_self a s) j (mem_insert_of_mem hj) (fun h => ha (h ▸ hj))

/-- The Pell quadratic is squarefree. -/
theorem pellPart_squarefree {F : ℚ[X]} (Y : Decomposition F) (e : ℕ) :
    Squarefree (Y.pellPart e) := by
  unfold Decomposition.pellPart
  apply squarefree_prod_of_coprime _ (fun j => Y.part (j + 1))
  · intro j _; exact Y.part_sq (j + 1)
  · intro i _ j _ hij; exact Y.part_cop (i + 1) (j + 1) (by omega)

/-- A monic quadratic evaluates as `x^2 + b x + c`. -/
lemma monic_quadratic_eval {Q : ℚ[X]} (hmon : Q.Monic) (hdeg : Q.natDegree = 2) (x : ℚ) :
    Q.eval x = x ^ 2 + Q.coeff 1 * x + Q.coeff 0 := by
  have h2 : Q.coeff 2 = 1 := by
    have := hmon.leadingCoeff; rwa [leadingCoeff, hdeg] at this
  rw [eval_eq_sum_range, hdeg]
  simp only [sum_range_succ, sum_range_zero, h2]
  ring

/-- A squarefree monic quadratic has nonzero discriminant. -/
theorem disc_ne_zero {Q : ℚ[X]} (hsq : Squarefree Q) (hmon : Q.Monic) (hdeg : Q.natDegree = 2) :
    Q.coeff 1 ^ 2 - 4 * Q.coeff 0 ≠ 0 := by
  intro h
  have hQ : Q = (X + C (Q.coeff 1 / 2)) * (X + C (Q.coeff 1 / 2)) := by
    apply Polynomial.funext
    intro x
    rw [monic_quadratic_eval hmon hdeg x]
    simp only [eval_mul, eval_add, eval_X, eval_C]
    linear_combination (-1 / 4 : ℚ) * h
  have hu := hsq _ (by rw [← hQ])
  have h1 := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_X_add_C] at h1
  exact one_ne_zero h1

/-- At most `deg Q` indices are rational zeros of a nonzero `Q`. -/
theorem card_zeros_le_rat (Q : ℚ[X]) (hQ : Q ≠ 0) (N : ℕ) :
    #((Icc 1 N).filter fun n : ℕ => Q.eval (n : ℚ) = 0) ≤ Q.natDegree := by
  calc #((Icc 1 N).filter fun n : ℕ => Q.eval (n : ℚ) = 0)
      ≤ #Q.roots.toFinset := by
        apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℚ))
        · intro n hn
          rw [mem_filter] at hn
          rw [Multiset.mem_toFinset, mem_roots hQ, IsRoot.def]
          exact hn.2
        · intro a _ b _ h
          simp only at h
          exact_mod_cast h
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q

/-- **Clearing denominators in one branch.** -/
theorem clear_denoms (γ b c : ℚ) (hγ : γ ≠ 0) (hdisc : b ^ 2 - 4 * c ≠ 0) :
    ∃ A B C : ℤ, A ≠ 0 ∧ B ^ 2 - 4 * A * C ≠ 0 ∧
      (∃ s : ℚ, s ≠ 0 ∧ (A : ℚ) = γ * s ^ 2 ∧ (B : ℚ) = γ * s ^ 2 * b) ∧ ∀ n : ℤ,
      (RatPower (γ * ((n : ℚ) ^ 2 + b * n + c)) 2 ↔ IsHit 2 (A * n ^ 2 + B * n + C)) := by
  set D : ℤ := b.den * c.den with hDdef
  have hD : (D : ℚ) ≠ 0 := by rw [hDdef]; push_cast; positivity
  have hβ : ((b.num * c.den : ℤ) : ℚ) = D * b := by
    rw [hDdef]; push_cast; rw [← Rat.mul_den_eq_num b]; ring
  have hχ : ((c.num * b.den : ℤ) : ℚ) = D * c := by
    rw [hDdef]; push_cast; rw [← Rat.mul_den_eq_num c]; ring
  have hg : ((γ.num * γ.den : ℤ) : ℚ) = γ * ((γ.den : ℚ) ^ 2) := by
    push_cast; rw [← Rat.mul_den_eq_num γ]; ring
  have hgne : ((γ.num * γ.den : ℤ) : ℚ) ≠ 0 := by
    rw [hg]; exact mul_ne_zero hγ (by positivity)
  set g : ℤ := γ.num * γ.den
  refine ⟨g * D ^ 2, g * D * (b.num * c.den), g * D * (c.num * b.den), ?_, ?_,
    ⟨(γ.den : ℚ) * D, mul_ne_zero (by positivity) hD, by push_cast; rw [hg]; ring,
      by push_cast; rw [hg, show ((b.num : ℚ) * c.den) = D * b by exact_mod_cast hβ]; ring⟩,
    fun n => ?_⟩
  · have : ((g * D ^ 2 : ℤ) : ℚ) ≠ 0 := by push_cast; exact mul_ne_zero hgne (pow_ne_zero _ hD)
    exact_mod_cast this
  · have : (((g * D * (b.num * c.den)) ^ 2 - 4 * (g * D ^ 2) * (g * D * (c.num * b.den)) : ℤ) : ℚ)
        = (g : ℚ) ^ 2 * D ^ 4 * (b ^ 2 - 4 * c) := by
      push_cast
      rw [show ((b.num : ℚ) * c.den) = D * b by exact_mod_cast hβ,
        show ((c.num : ℚ) * b.den) = D * c by exact_mod_cast hχ]
      ring
    have hne : ((g : ℚ) ^ 2 * D ^ 4 * (b ^ 2 - 4 * c)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hgne) (pow_ne_zero _ hD)) hdisc
    rw [← this] at hne
    exact_mod_cast hne
  · have hs : ((γ.den : ℚ) * D) ≠ 0 := mul_ne_zero (by positivity) hD
    have hval : ((g * D ^ 2 * n ^ 2 + g * D * (b.num * c.den) * n + g * D * (c.num * b.den) : ℤ) : ℚ)
        = γ * ((n : ℚ) ^ 2 + b * n + c) * ((γ.den : ℚ) * D) ^ 2 := by
      push_cast
      rw [show ((b.num : ℚ) * c.den) = D * b by exact_mod_cast hβ,
        show ((c.num : ℚ) * b.den) = D * c by exact_mod_cast hχ, hg]
      ring
    rw [isHit_iff_rat (by norm_num), ← ratPower_mul_pow_iff _ _ 2 hs]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [hval, hy]⟩
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hval, hy]⟩

lemma isSquare_of_isSquare_four_mul {A : ℤ} (h : IsSquare (4 * A)) : IsSquare A := by
  obtain ⟨s, hs⟩ := h
  have heven : Even s := by
    rcases Int.even_or_odd s with he | ⟨k, rfl⟩
    · exact he
    · exfalso
      rw [show (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + 2 * k) + 1 by ring] at hs
      generalize 2 * k * k + 2 * k = t at hs
      omega
  obtain ⟨k, rfl⟩ := heven
  exact ⟨k, by nlinarith⟩

/-- `A < 0`: only `n ≤ |B| + |C|` can hit. -/
lemma hit_le_of_neg {A B C : ℤ} (hneg : A < 0) :
    ∀ n : ℕ, 1 ≤ n → IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) → n ≤ B.natAbs + C.natAbs := by
  intro n hn ⟨m, hm⟩
  by_contra hlt
  push_neg at hlt
  have hB : (B : ℤ) ≤ B.natAbs := Int.le_natAbs
  have hC : (C : ℤ) ≤ C.natAbs := Int.le_natAbs
  have hn' : (B.natAbs : ℤ) + C.natAbs + 1 ≤ n := by exact_mod_cast hlt
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hBn : B * n ≤ B.natAbs * n := mul_le_mul_of_nonneg_right hB hn0
  have hAn : A * (n : ℤ) ^ 2 ≤ -(n : ℤ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg m]

/-- `A = a^2` with nonzero discriminant: only `n ≤ |Δ| + |B|` can hit (a difference of two
squares equals `Δ`). -/
lemma hit_le_of_square {A B C : ℤ} (hpos : 0 < A) (hsqA : IsSquare A)
    (hdisc : B ^ 2 - 4 * A * C ≠ 0) :
    ∀ n : ℕ, 1 ≤ n → IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) →
      n ≤ (B ^ 2 - 4 * A * C).natAbs + B.natAbs := by
  obtain ⟨a, ha⟩ := hsqA
  intro n hn ⟨m, hm⟩
  set Δ := B ^ 2 - 4 * A * C
  set Xv := 2 * A * n + B
  set Yv := 2 * a * m
  have hXY : (Xv - Yv) * (Xv + Yv) = Δ := by
    simp only [Xv, Yv, Δ]
    rw [ha] at hm ⊢
    linear_combination (4 * (a * a)) * hm
  have hp : 1 ≤ |Xv - Yv| := by
    rcases eq_or_ne (Xv - Yv) 0 with h0 | h0
    · rw [h0, zero_mul] at hXY; exact absurd hXY.symm hdisc
    · exact Int.one_le_abs h0
  have hq : 1 ≤ |Xv + Yv| := by
    rcases eq_or_ne (Xv + Yv) 0 with h0 | h0
    · rw [h0, mul_zero] at hXY; exact absurd hXY.symm hdisc
    · exact Int.one_le_abs h0
  have hpq : |Xv - Yv| * |Xv + Yv| = |Δ| := by rw [← abs_mul, hXY]
  have h2X : |2 * Xv| ≤ |Xv - Yv| + |Xv + Yv| := by
    calc |2 * Xv| = |(Xv - Yv) + (Xv + Yv)| := by ring_nf
      _ ≤ _ := abs_add _ _
  have hsum : |Xv - Yv| + |Xv + Yv| ≤ |Δ| + 1 := by nlinarith
  have hX : Xv ≤ |Δ| := by
    have : 2 * Xv ≤ |2 * Xv| := le_abs_self _
    linarith
  have hΔ : |Δ| = (Δ.natAbs : ℤ) := Int.abs_eq_natAbs Δ
  have hB : -(B.natAbs : ℤ) ≤ B := by rw [← Int.abs_eq_natAbs]; exact neg_abs_le B
  have : (n : ℤ) ≤ 2 * A * n := by nlinarith
  have : (n : ℤ) ≤ Δ.natAbs + B.natAbs := by simp only [Xv] at hX; linarith
  exact_mod_cast this

/-- **One branch.**  `A n^2 + B n + C` with `A ≠ 0` and nonzero discriminant is a square for
`κ log N + O(1)` indices `n ≤ N`, with `κ = 0` unless `A > 0` is not a square. -/
theorem branch_count (A B C : ℤ) (hA : A ≠ 0) (hdisc : B ^ 2 - 4 * A * C ≠ 0) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℝ) -
        κ * Real.log N| ≤ K := by
  -- a bounded count, from a bound `M` on the indices that can hit
  have bounded : ∀ M : ℕ, (∀ n : ℕ, 1 ≤ n → IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) → n ≤ M) →
      ∃ κ K : ℝ, 0 ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |(#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℝ) -
          κ * Real.log N| ≤ K := by
    intro M hM
    refine ⟨0, M, le_refl _, 0, fun N _ => ?_⟩
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) ⊆
        Icc 1 M := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      exact ⟨hn.1.1, hM n hn.1.1 hn.2⟩
    have hcard := card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
    simp only [zero_mul, sub_zero, Nat.abs_cast]
    exact_mod_cast hcard
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · exact bounded _ (hit_le_of_neg hneg)
  · by_cases hsqA : IsSquare A
    · exact bounded _ (hit_le_of_square hpos hsqA hdisc)
    · -- `A > 0` not a square: a Pell unit exists, and `atlas_pell` applies
      have h4 : ¬ IsSquare (4 * A) := fun h => hsqA (isSquare_of_isSquare_four_mul h)
      obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (by omega : 0 < 4 * A) h4
      have hv : 0 < |y| := abs_pos.mpr hy
      have hu : |x| ^ 2 - 4 * A * |y| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hxy
      have hu1 : 1 < |x| := by
        have hy2 : 1 ≤ |y| ^ 2 := by nlinarith
        nlinarith [abs_nonneg x]
      exact atlas_pell hpos hu1 hv hu

/-- **Theorem C as a count.**  For `F ∈ ℤ[X]` of Pell type with half-exponent `e`,
`|A(N) - κ log N| ≤ K` for all large `N`, with `κ ≥ 0`; the zeros of `F`, both roots `± γ₀` of
`γ^e = lc(F)` and every sign and square case of the branch quadratics are included. -/
theorem Decomposition.pell_count {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {e : ℕ} (he : e ≠ 0)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(#((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) : ℝ) -
        κ * Real.log N| ≤ K := by
  obtain ⟨hmon, hdeg, hiff⟩ := Y.integer_pell_reduction he hres hdegree
  have hFq : F.map (Int.castRingHom ℚ) ≠ 0 := Y.ne_zero
  have hF : F ≠ 0 := by rintro rfl; exact hFq (Polynomial.map_zero _)
  set Q := Y.pellPart e
  have hdisc := disc_ne_zero (pellPart_squarefree Y e) hmon hdeg
  have hlc : (F.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hF
  set P : ℚ → ℕ → Prop := fun γ n => RatPower (γ * Q.eval (n : ℚ)) 2 with hPdef
  -- each nonzero `γ` gives a branch with a logarithmic count
  have hbranch : ∀ γ : ℚ, γ ≠ 0 → ∃ κ K : ℝ, 0 ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(#((Icc 1 N).filter (P γ)) : ℝ) - κ * Real.log N| ≤ K := by
    intro γ hγ
    obtain ⟨A, B, C, hA, hD, -, hPA⟩ := clear_denoms γ (Q.coeff 1) (Q.coeff 0) hγ hdisc
    obtain ⟨κ, K, hκ, N₀, hK⟩ := branch_count A B C hA hD
    refine ⟨κ, K, hκ, N₀, fun N hN => ?_⟩
    have e1 : (Icc 1 N).filter (P γ) =
        (Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) := by
      apply filter_congr
      intro n _
      simp only [hPdef]
      rw [monic_quadratic_eval hmon hdeg, ← hPA n]
      push_cast
      rfl
    rw [e1]; exact hK N hN
  have hzeros := card_zeros_le F hF
  by_cases hγ : ∃ γ : ℚ, γ ^ e = F.leadingCoeff
  swap
  · refine ⟨0, F.natDegree, le_refl _, 0, fun N _ => ?_⟩
    have hsub : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) ⊆
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 := by
      intro n hn
      simp only [mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      rcases (hiff n).mp hn.2 with h | ⟨γ, hγ', -⟩
      · exact h
      · exact absurd ⟨γ, hγ'⟩ hγ
    have := (card_le_card hsub).trans (hzeros N)
    simp only [zero_mul, sub_zero, Nat.abs_cast]
    exact_mod_cast this
  obtain ⟨γ₀, hγ₀⟩ := hγ
  have hγ₀ne : γ₀ ≠ 0 := by
    rintro rfl; rw [zero_pow he] at hγ₀; exact hlc hγ₀.symm
  have hroots : ∀ γ : ℚ, γ ^ e = F.leadingCoeff → γ = γ₀ ∨ γ = -γ₀ := by
    intro γ hγ
    rw [← hγ₀] at hγ
    rcases (pow_eq_pow_iff_of_ne_zero he).mp hγ with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨κ1, K1, hκ1, N1, hK1⟩ := hbranch γ₀ hγ₀ne
  by_cases h2 : (-γ₀) ^ e = F.leadingCoeff
  · -- two branches, overlapping only at roots of `Q`
    obtain ⟨κ2, K2, hκ2, N2, hK2⟩ := hbranch (-γ₀) (neg_ne_zero.mpr hγ₀ne)
    refine ⟨κ1 + κ2, K1 + K2 + F.natDegree + 2, by linarith, max N1 N2, fun N hN => ?_⟩
    have e1 : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) =
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n) := by
      apply filter_congr
      intro n _
      rw [hiff n]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨γ, hγ, hP⟩
        rcases hroots γ hγ with rfl | rfl
        · exact Or.inl hP
        · exact Or.inr hP
      · rintro (hP | hP)
        · exact ⟨γ₀, hγ₀, hP⟩
        · exact ⟨-γ₀, h2, hP⟩
    rw [e1]
    obtain ⟨c1, c2⟩ := count_or (fun n : ℕ => F.eval (n : ℤ) = 0) (fun n => P γ₀ n ∨ P (-γ₀) n)
      N F.natDegree (hzeros N)
    have hunion : #((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) +
        #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) =
        #((Icc 1 N).filter (P γ₀)) + #((Icc 1 N).filter (P (-γ₀))) := by
      rw [filter_or, filter_and]
      exact card_union_add_card_inter _ _
    have hover : #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) ≤ 2 := by
      calc #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n)
          ≤ #((Icc 1 N).filter fun n : ℕ => Q.eval (n : ℚ) = 0) := by
            apply card_le_card
            intro n hn
            simp only [mem_filter] at hn ⊢
            refine ⟨hn.1, ?_⟩
            have h0 := (opposite_squares_iff_zero (γ₀ * Q.eval (n : ℚ))).mp
              ⟨hn.2.1, by simpa [hPdef, neg_mul] using hn.2.2⟩
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h hγ₀ne
            · exact h
        _ ≤ Q.natDegree := card_zeros_le_rat Q hmon.ne_zero N
        _ = 2 := hdeg
    have b1 := hK1 N (le_of_max_le_left hN)
    have b2 := hK2 N (le_of_max_le_right hN)
    have c1' : ((#((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n)) := by
      exact_mod_cast c1
    have c2' : ((#((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ (P γ₀ n ∨ P (-γ₀) n)) :
        ℕ) : ℝ) ≤ #((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) + F.natDegree := by
      exact_mod_cast c2
    have hunion' : ((#((Icc 1 N).filter fun n => P γ₀ n ∨ P (-γ₀) n) : ℕ) : ℝ) +
        #((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) =
        #((Icc 1 N).filter (P γ₀)) + #((Icc 1 N).filter (P (-γ₀))) := by exact_mod_cast hunion
    have hover' : ((#((Icc 1 N).filter fun n => P γ₀ n ∧ P (-γ₀) n) : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast hover
    rw [abs_le] at b1 b2 ⊢
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
  · -- one branch
    refine ⟨κ1, K1 + F.natDegree, hκ1, N1, fun N hN => ?_⟩
    have e1 : ((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) =
        (Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n := by
      apply filter_congr
      intro n _
      rw [hiff n]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨γ, hγ, hP⟩
        rcases hroots γ hγ with rfl | rfl
        · exact hP
        · exact absurd hγ h2
      · intro hP; exact ⟨γ₀, hγ₀, hP⟩
    rw [e1]
    obtain ⟨c1, c2⟩ := count_or (fun n : ℕ => F.eval (n : ℤ) = 0) (P γ₀) N F.natDegree (hzeros N)
    have b1 := hK1 N hN
    have c1' : ((#((Icc 1 N).filter (P γ₀)) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n) := by exact_mod_cast c1
    have c2' : ((#((Icc 1 N).filter fun n : ℕ => F.eval (n : ℤ) = 0 ∨ P γ₀ n) : ℕ) : ℝ) ≤
        #((Icc 1 N).filter (P γ₀)) + F.natDegree := by exact_mod_cast c2
    rw [abs_le] at b1 ⊢
    constructor <;> linarith [b1.1, b1.2]

end PerfectPower.RationalYun
