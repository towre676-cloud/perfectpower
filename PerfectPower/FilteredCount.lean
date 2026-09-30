import PerfectPower.FilteredPell

/-!
# The filtered Pell count: `A(N) = κ_filtered log N + O(1)`

`FilteredPell.lean` decides whether a stable filter leaves infinitely many solutions.  This file
counts them.  Take one root `ρ` per orbit of quadrant solutions of `X^2 - 4A Y^2 = Δ` (roots are
canonical: `PellExact.root_unique`), a period `P ρ` of its residue cycle modulo `M`, and
`g ρ = #{j < P ρ : the state j is admissible}`.  Then

  `A(N) = (∑_ρ g ρ / P ρ) / log ε · log N + O(1)`,

where `A(N)` counts `n ∈ [1, N]` in the filtered family.  An index is an orbit point `(X, Y ≥ 0)`
and `X` determines `n`, so no `n` is counted twice.

* `orbit_count_pred`: one orbit, any predicate periodic along it.
* `count_of_orbit_estimates`: the assembly, for **any** filter `good` implying `2A ∣ X - B`:
  per-root estimates `|#{j < L : good ∧ X_j ≤ M} - c_ρ log M| ≤ K_ρ` give
  `|A(N) - (∑ c_ρ) log N| ≤ K` for all large `N`.  (The argument of `PellExact.pell_exact_count`
  with the divisibility replaced by `good`.)
* `filtered_count`: for a stable filter, `good` and its residue form differ at finitely many
  indices of each orbit (those with `Y < T`), so `c_ρ = g ρ / (P ρ log ε)`.
* `quadRoot_count`: the same count for the original constraint `a y^2 + b y + c = F(n)`.
-/

namespace PerfectPower.FilteredPell

open PerfectPower PellExact RationalYun Finset
open scoped Classical

variable {D u v Δ : ℤ}

/-- **One orbit, any periodic predicate.** -/
theorem orbit_count_pred (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) {P : ℕ} (hP : 0 < P) (q : ℕ → Prop)
    (hq : ∀ j, q (j + P) ↔ q j) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | q j ∧ ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) -
        (#((range P).filter q) : ℕ) * (Real.log M / (P * Real.log (eps D u v)))| ≤ K := by
  have hK : ∀ r, ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L) →
      |((((range L).filter
          (fun h => ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M)).card : ℕ) : ℝ) -
        Real.log M / (P * Real.log (eps D u v))| ≤ K :=
    fun r => class_count hD hu hu1 hv hρ hP r
  choose Kf hKf using hK
  set G := (range P).filter q
  refine ⟨∑ r ∈ G, Kf r, fun M L hM hL => ?_⟩
  rw [card_split_residue P L hP q hq (fun j => ((unitOrbit D u v ρ j).1 : ℝ) ≤ M) hL]
  push_cast
  have hG : ((#G : ℕ) : ℝ) * (Real.log M / (P * Real.log (eps D u v))) =
      ∑ r ∈ G, Real.log M / (P * Real.log (eps D u v)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hG, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hLr : ∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L := by
    intro h hh
    have := hL _ hh
    have : h ≤ r + P * h := by nlinarith
    omega
  simpa using hKf r M L hM hLr

variable {A B C : ℤ}

/-- The filtered family as a finite count. -/
noncomputable def countHits (A B C : ℤ) (good : ℤ × ℤ → Prop) (N : ℕ) : ℕ :=
  #((Icc 1 N).filter fun n : ℕ => ∃ Y : ℤ,
    Sol (4 * A) (B ^ 2 - 4 * A * C) (2 * A * n + B, Y) ∧ good (2 * A * n + B, Y))

set_option maxHeartbeats 2000000 in
/-- **The assembly.**  Per-root orbit estimates for a filter `good` (which forces
`2A ∣ X - B`) give the count of the filtered family. -/
theorem count_of_orbit_estimates (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (good : ℤ × ℤ → Prop)
    (hdiv : ∀ p, good p → 2 * A ∣ p.1 - B) (R : Finset (ℤ × ℤ))
    (hR : ∀ ρ, ρ ∈ R ↔ IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ) (c K : ℤ × ℤ → ℝ)
    (hc : ∀ ρ ∈ R, 0 ≤ c ρ)
    (hK : ∀ ρ ∈ R, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit (4 * A) u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | good (unitOrbit (4 * A) u v ρ j) ∧
          ((unitOrbit (4 * A) u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) - c ρ * Real.log M| ≤ K ρ) :
    ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |((countHits A B C good N : ℕ) : ℝ) - (∑ ρ ∈ R, c ρ) * Real.log N| ≤
        |B| + 1 + ∑ ρ ∈ R, K ρ + (∑ ρ ∈ R, c ρ) * Real.log (2 * A + |B|) := by
  set D := 4 * A
  set Δ := B ^ 2 - 4 * A * C
  have hD : 0 < D := by positivity
  have hu' : u ^ 2 - D * v ^ 2 = 1 := hu
  have hroot : ∀ ρ ∈ R, Sol D Δ ρ := fun ρ hρ => ((hR ρ).mp hρ).1
  set κ := ∑ ρ ∈ R, c ρ
  have hκ : 0 ≤ κ := sum_nonneg hc
  intro N hN
  set M : ℝ := 2 * A * N + B
  set L : ℕ := (2 * A * N + |B|).toNat + 1
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hBN : (|B| : ℝ) + 1 ≤ N := by
    have : ((B.natAbs : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hN
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hBr' : (B : ℝ) ≤ |B| := by exact_mod_cast le_abs_self B
  have hBr : -(|B| : ℝ) ≤ B := by exact_mod_cast neg_abs_le B
  have hMN : (N : ℝ) ≤ M := by simp only [M]; nlinarith
  have hM1 : (1 : ℝ) ≤ M := hNpos.trans hMN
  have hMup : M ≤ (2 * A + |B|) * N := by
    have : ((|B| : ℤ) : ℝ) ≤ ((|B| : ℤ) : ℝ) * N :=
      le_mul_of_one_le_right (by exact_mod_cast abs_nonneg B) hNpos
    simp only [M]; push_cast at this ⊢; nlinarith [le_abs_self (B : ℝ)]
  have hjL : ∀ ρ, Sol D Δ ρ → ∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L := by
    intro ρ hρ j hj
    have h1 := index_lt_fst hD.le hu1 hv.le hρ j
    have h2 : (unitOrbit D u v ρ j).1 ≤ 2 * A * N + |B| := by
      have : ((unitOrbit D u v ρ j).1 : ℝ) ≤ 2 * A * N + |B| := by simp only [M] at hj; linarith
      exact_mod_cast this
    have : (j : ℤ) < ((2 * A * N + |B|).toNat : ℤ) + 1 := by
      rw [Int.toNat_of_nonneg (by positivity)]; linarith
    omega
  set T := (R ×ˢ range L).filter fun x => good (unitOrbit D u v x.1 x.2) ∧
      ((unitOrbit D u v x.1 x.2).1 : ℝ) ≤ M
  have hTcard : #T = ∑ ρ ∈ R, #{j ∈ range L | good (unitOrbit D u v ρ j) ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} :=
    card_filter_prod R L (fun ρ j => good (unitOrbit D u v ρ j) ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M)
  set hits := (Icc 1 N).filter fun n : ℕ => ∃ Y : ℤ,
    Sol D Δ (2 * A * n + B, Y) ∧ good (2 * A * n + B, Y)
  have hhits : countHits A B C good N = #hits := rfl
  set ψ : (ℤ × ℤ) × ℕ → ℕ := fun x => (((unitOrbit D u v x.1 x.2).1 - B) / (2 * A)).toNat
  have hTsol : ∀ x ∈ T, Sol D Δ (unitOrbit D u v x.1 x.2) := by
    intro x hx
    have := (mem_product.mp (mem_filter.mp hx).1).1
    exact orbit_sol hD.le hu' hu1.le hv.le (hroot _ this) x.2
  -- (A1) hits ≤ #T + |B|
  have hA1 : (#hits : ℤ) ≤ #T + B.natAbs := by
    have hsmall : (hits.filter fun n : ℕ => 2 * A * n + B ≤ 0) ⊆ Icc 1 B.natAbs := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1.1.1, ?_⟩
      have : (n : ℤ) ≤ |B| := by
        nlinarith [neg_abs_le B, (by exact_mod_cast hn.1.1.1 : (1 : ℤ) ≤ n)]
      have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
      omega
    have hbig : (hits.filter fun n : ℕ => ¬ 2 * A * n + B ≤ 0) ⊆ T.image ψ := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc, not_le] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, Y, hs, hg⟩, -⟩ := hn
      obtain ⟨ρ, j, hρ, hj⟩ := exists_root hD hu1 hv hu' _ _ rfl hs
      have hρR : ρ ∈ R := (hR ρ).mpr hρ
      have hXM : ((unitOrbit D u v ρ j).1 : ℝ) ≤ M := by
        rw [hj]; simp only [M]; push_cast
        have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        nlinarith
      refine mem_image.mpr ⟨(ρ, j), mem_filter.mpr ⟨mem_product.mpr ⟨hρR,
        mem_range.mpr (hjL ρ hρ.1 j hXM)⟩, by rw [hj]; exact hg, hXM⟩, ?_⟩
      simp only [ψ, hj]
      rw [show 2 * A * (n : ℤ) + B - B = 2 * A * n by ring,
        Int.mul_ediv_cancel_left _ (by positivity)]
      simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := hits)
      (fun n : ℕ => 2 * A * n + B ≤ 0)
    have c1 := card_le_card hsmall
    have c2 := (card_le_card hbig).trans card_image_le
    simp only [Nat.card_Icc, add_tsub_cancel_right] at c1
    omega
  -- (A2) #T ≤ hits + |B|
  have hA2 : (#T : ℤ) ≤ #hits + B.natAbs := by
    have hinj : ∀ x ∈ T, ∀ y ∈ T,
        (unitOrbit D u v x.1 x.2).1 = (unitOrbit D u v y.1 y.2).1 → x = y := by
      intro x hx y hy hxy
      have e := sol_eq_of_fst hD (hTsol x hx) (hTsol y hy) hxy
      have hx' := (hR _).mp (mem_product.mp (mem_filter.mp hx).1).1
      have hy' := (hR _).mp (mem_product.mp (mem_filter.mp hy).1).1
      obtain ⟨e1, e2⟩ := root_unique hD.le hu1 hv.le hu' x.2 y.2 hx' hy' e
      exact Prod.ext e1 e2
    have h1 : (T.filter fun x => B < (unitOrbit D u v x.1 x.2).1).card ≤ #hits := by
      refine card_le_card_of_injOn ψ ?_ ?_
      · intro x hx
        rw [mem_filter] at hx
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨-, hg, hxM⟩ := mem_filter.mp hxT
        obtain ⟨k, hk⟩ := hdiv _ hg
        have hk1 : 1 ≤ k := by nlinarith
        simp only [hits, mem_filter, mem_Icc, ψ]
        rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
        have hkN : k ≤ N := by
          have : ((2 * A * k + B : ℤ) : ℝ) ≤ M := by
            rw [show 2 * A * k + B = (unitOrbit D u v x.1 x.2).1 by linarith]; exact hxM
          simp only [M] at this; push_cast at this
          have : (k : ℝ) ≤ N := by nlinarith
          exact_mod_cast this
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Int.toNat_of_nonneg (by omega)]
        have e : 2 * A * k + B = (unitOrbit D u v x.1 x.2).1 := by linarith
        refine ⟨(unitOrbit D u v x.1 x.2).2, ?_, ?_⟩
        · rw [e]; exact hTsol x hxT
        · rw [e]; exact hg
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨hyT, hyB⟩ := hy
        obtain ⟨k, hk⟩ := hdiv _ (mem_filter.mp hxT).2.1
        obtain ⟨l, hl⟩ := hdiv _ (mem_filter.mp hyT).2.1
        simp only [ψ] at hxy
        rw [hk, hl, Int.mul_ediv_cancel_left _ (by positivity),
          Int.mul_ediv_cancel_left _ (by positivity)] at hxy
        have hk0 : 0 ≤ k := by nlinarith
        have hl0 : 0 ≤ l := by nlinarith
        have : k = l := by omega
        exact hinj x hxT y hyT (by rw [this] at hk; linarith)
    have h2 : (T.filter fun x => ¬ B < (unitOrbit D u v x.1 x.2).1).card ≤ B.natAbs := by
      calc _ ≤ (Icc 1 B.natAbs).card := by
            refine card_le_card_of_injOn (fun x => ((unitOrbit D u v x.1 x.2).1).toNat) ?_ ?_
            · intro x hx
              rw [mem_filter, not_lt] at hx
              obtain ⟨hxT, hxB⟩ := hx
              have hpos := (hTsol x hxT).1
              dsimp only
              rw [mem_Icc]
              have h1 := le_abs_self B
              have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
              constructor <;> omega
            · intro x hx y hy hxy
              rw [mem_coe, mem_filter] at hx hy
              have := (hTsol x hx.1).1
              have := (hTsol y hy.1).1
              exact hinj x hx.1 y hy.1 (by simp only at hxy; omega)
        _ = B.natAbs := by simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := T)
      (fun x => B < (unitOrbit D u v x.1 x.2).1)
    omega
  -- (B) the per-root estimates
  have hB' : |(#T : ℝ) - κ * Real.log M| ≤ ∑ ρ ∈ R, K ρ := by
    rw [hTcard]; push_cast
    rw [show κ * Real.log M = ∑ ρ ∈ R, c ρ * Real.log M by rw [Finset.sum_mul], ← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ρ hρ =>
      hK ρ hρ M L hM1 (hjL ρ (hroot ρ hρ)))
  -- (C) log M versus log N
  have hlog1 : Real.log N ≤ Real.log M := Real.log_le_log (by linarith) hMN
  have hlog2 : Real.log M ≤ Real.log (2 * A + |B|) + Real.log N := by
    rw [← Real.log_mul (by positivity) (by linarith)]
    exact Real.log_le_log (by linarith) hMup
  have hB : ((B.natAbs : ℕ) : ℝ) = |(B : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hAB1 : ((#hits : ℕ) : ℝ) ≤ (#T : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA1
  have hAB2 : ((#T : ℕ) : ℝ) ≤ (#hits : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA2
  rw [hB] at hAB1 hAB2
  rw [hhits]
  have hcast : ((|B| : ℤ) : ℝ) = |(B : ℝ)| := Int.cast_abs
  rw [hcast] at hlog2 ⊢
  rw [abs_le] at hB' ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlog1 hκ, mul_le_mul_of_nonneg_left hlog2 hκ]

/-- Two index sets that agree beyond `J` differ in size by at most `J`. -/
lemma card_filter_diff_le (L J : ℕ) (p q s : ℕ → Prop) (h : ∀ j, J ≤ j → (p j ↔ q j)) :
    #{j ∈ range L | p j ∧ s j} ≤ #{j ∈ range L | q j ∧ s j} + J := by
  calc #{j ∈ range L | p j ∧ s j}
      ≤ #({j ∈ range L | q j ∧ s j} ∪ range J) := by
        apply card_le_card
        intro j hj
        simp only [mem_filter, mem_range, mem_union] at hj ⊢
        by_cases hjJ : J ≤ j
        · exact Or.inl ⟨hj.1, (h j hjJ).mp hj.2.1, hj.2.2⟩
        · exact Or.inr (by omega)
    _ ≤ #{j ∈ range L | q j ∧ s j} + #(range J) := card_union_le _ _
    _ = _ := by rw [card_range]

set_option maxHeartbeats 1000000 in
/-- **The filtered Pell count.**  With `R` the roots, `P ρ` a period of the residue cycle of
`ρ` modulo `M`, and `g ρ` the number of admissible states in one period:
`|A(N) - (∑_ρ g ρ / P ρ) / log ε · log N| ≤ K` for all large `N`. -/
theorem filtered_count {M : ℕ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M)
    (hdiv : ∀ p, F.good p → 2 * A ∣ p.1 - B) (R : Finset (ℤ × ℤ))
    (hR : ∀ ρ, ρ ∈ R ↔ IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ) (P : ℤ × ℤ → ℕ)
    (hP : ∀ ρ ∈ R, 0 < P ρ ∧ ∀ j, castPair M (unitOrbit (4 * A) u v ρ (j + P ρ)) =
      castPair M (unitOrbit (4 * A) u v ρ j)) :
    ∃ K : ℝ, ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |((countHits A B C F.good N : ℕ) : ℝ) -
        (∑ ρ ∈ R, (#((range (P ρ)).filter fun j =>
          F.goodMod (castPair M (unitOrbit (4 * A) u v ρ j))) : ℝ) / P ρ) /
            Real.log (eps (4 * A) u v) * Real.log N| ≤ K := by
  set D := 4 * A
  set Δ := B ^ 2 - 4 * A * C
  have hD : 0 < D := by positivity
  have hu' : u ^ 2 - D * v ^ 2 = 1 := hu
  have hε := one_lt_eps (D := D) hu1 hv.le
  have hlogε : 0 < Real.log (eps D u v) := Real.log_pos hε
  -- per-root estimates, with the finitely many small `Y` absorbed
  have hest : ∀ ρ, ∃ Kρ : ℝ, ρ ∈ R → ∀ (Mr : ℝ) (L : ℕ), 1 ≤ Mr →
      (∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr → j < L) →
      |((#{j ∈ range L | F.good (unitOrbit D u v ρ j) ∧
          ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr} : ℕ) : ℝ) -
        (#((range (P ρ)).filter fun j => F.goodMod (castPair M (unitOrbit D u v ρ j))) : ℝ) /
          P ρ / Real.log (eps D u v) * Real.log Mr| ≤ Kρ := by
    intro ρ
    by_cases hρ : ρ ∈ R
    swap
    · exact ⟨0, fun h => absurd h hρ⟩
    have hsol := ((hR ρ).mp hρ).1
    obtain ⟨hP0, hper⟩ := hP ρ hρ
    set q : ℕ → Prop := fun j => F.goodMod (castPair M (unitOrbit D u v ρ j))
    obtain ⟨K0, hK0⟩ := orbit_count_pred hD.le hu' hu1 hv.le hsol hP0 q
      (fun j => by simp only [q, hper j])
    -- beyond `J` the filter is its residue form
    set J : ℕ := (|Δ| + D * F.T ^ 2 + 1).toNat
    have hJ : ∀ j, J ≤ j → (F.good (unitOrbit D u v ρ j) ↔ q j) := by
      intro j hj
      have hmono := orbit_mono hD.le hu' hu1 hv.le hsol j
      have hJc : ((J : ℕ) : ℤ) = |Δ| + D * F.T ^ 2 + 1 := Int.toNat_of_nonneg (by positivity)
      have hX : |Δ| + D * F.T ^ 2 + 1 ≤ (unitOrbit D u v ρ j).1 := by
        have := hsol.1; linarith
      exact F.stable _ (snd_ge_of_fst hD.le (orbit_sol hD.le hu' hu1.le hv.le hsol j) hX)
    refine ⟨K0 + J, fun _ Mr L hMr hL => ?_⟩
    have h1 := card_filter_diff_le L J (fun j => F.good (unitOrbit D u v ρ j)) q
      (fun j => ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr) hJ
    have h2 := card_filter_diff_le L J q (fun j => F.good (unitOrbit D u v ρ j))
      (fun j => ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr) (fun j hj => (hJ j hj).symm)
    have h3 := hK0 Mr L hMr hL
    have e : (#((range (P ρ)).filter q) : ℝ) / P ρ / Real.log (eps D u v) * Real.log Mr =
        (#((range (P ρ)).filter q) : ℝ) * (Real.log Mr / (P ρ * Real.log (eps D u v))) := by
      field_simp
    rw [e]
    have h1' : ((#{j ∈ range L | F.good (unitOrbit D u v ρ j) ∧
        ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr} : ℕ) : ℝ) ≤
        (#{j ∈ range L | q j ∧ ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr} : ℕ) + J := by
      exact_mod_cast h1
    have h2' : ((#{j ∈ range L | q j ∧ ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr} : ℕ) : ℝ) ≤
        (#{j ∈ range L | F.good (unitOrbit D u v ρ j) ∧
          ((unitOrbit D u v ρ j).1 : ℝ) ≤ Mr} : ℕ) + J := by
      exact_mod_cast h2
    rw [abs_le] at h3 ⊢
    constructor <;> linarith [h3.1, h3.2]
  choose Kf hKf using hest
  set c : ℤ × ℤ → ℝ := fun ρ =>
    (#((range (P ρ)).filter fun j => F.goodMod (castPair M (unitOrbit D u v ρ j))) : ℝ) /
      P ρ / Real.log (eps D u v)
  have hc : ∀ ρ ∈ R, 0 ≤ c ρ := fun ρ _ => by positivity
  have main := count_of_orbit_estimates hA hu1 hv hu F.good hdiv R hR c Kf hc
    (fun ρ hρ Mr L hMr hL => hKf ρ hρ Mr L hMr hL)
  refine ⟨|B| + 1 + ∑ ρ ∈ R, Kf ρ + (∑ ρ ∈ R, c ρ) * Real.log (2 * A + |B|), fun N hN => ?_⟩
  have e : (∑ ρ ∈ R, (#((range (P ρ)).filter fun j =>
      F.goodMod (castPair M (unitOrbit (4 * A) u v ρ j))) : ℝ) / P ρ) /
        Real.log (eps (4 * A) u v) = ∑ ρ ∈ R, c ρ := by
    simp only [c]; rw [Finset.sum_div]
  rw [e]
  exact main N hN

/-! ### A certificate for the constant -/

/-- Lookup in a certificate list. -/
def lk : List ((ℤ × ℤ) × (ℕ × ℕ)) → ℤ × ℤ → ℕ × ℕ
  | [], _ => (0, 0)
  | e :: t, ρ => if e.1 = ρ then e.2 else lk t ρ

lemma lk_of_mem : ∀ {l : List ((ℤ × ℤ) × (ℕ × ℕ))}, (l.map Prod.fst).Nodup →
    ∀ e ∈ l, lk l e.1 = e.2
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: t, hn, e, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [lk]
    · have hne : a.1 ≠ e.1 := fun heq => hn.1 (heq ▸ List.mem_map_of_mem h)
      simp only [lk, if_neg hne]
      exact lk_of_mem hn.2 e h

/-- The number of `j < n` with `good (f^[j] s)`, counted in one pass along the orbit (the
kernel evaluates this in `n` steps; the `List.range` form below takes `n^2`). -/
def orbitCount {α : Type*} (f : α → α) (good : α → Bool) : ℕ → α → ℕ → ℕ
  | 0, _, acc => acc
  | n + 1, s, acc => orbitCount f good n (f s) (if good s then acc + 1 else acc)

lemma orbitCount_eq {α : Type*} (f : α → α) (good : α → Bool) (n : ℕ) (s : α) (acc : ℕ) :
    orbitCount f good n s acc = acc + ((List.range n).filter fun j => good (f^[j] s)).length := by
  induction n generalizing s acc with
  | zero => simp [orbitCount]
  | succ n ih =>
    rw [orbitCount, ih, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    simp only [Function.iterate_zero, id, Function.comp_def, Function.iterate_succ_apply]
    split_ifs with h <;> simp [h, List.length_cons] <;> omega

/-- `f^[n] s`, with every state compared to itself before the next step.  The comparison
forces the kernel to evaluate each state, so it never builds a chain of `n` unevaluated
applications (the plain `f^[n] s` overflows the stack for `n` in the thousands). -/
def iterForce (f : ℤ × ℤ → ℤ × ℤ) : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, s => s
  | n + 1, s => if f s = f s then iterForce f n (f s) else iterForce f n (f s)

lemma iterForce_eq (f : ℤ × ℤ → ℤ × ℤ) (n : ℕ) (s : ℤ × ℤ) : iterForce f n s = f^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [iterForce, ih, Function.iterate_succ_apply]

/-- A quadrant solution, as a Boolean. -/
def solB (D Δ : ℤ) (p : ℤ × ℤ) : Bool := decide (0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = Δ)

lemma solB_iff {D Δ : ℤ} (p : ℤ × ℤ) : solB D Δ p = true ↔ Sol D Δ p := by
  simp [solB, Sol]

/-! ### Kernel-friendly integer square root (not trusted: the checker verifies it) -/

/-- Newton iteration for `⌊√x⌋`, with fuel. -/
def nsqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, r => r
  | fuel + 1, x, r =>
    let r' := (r + x / r) / 2
    if r' < r then nsqrtAux fuel x r' else r

/-- `⌊√x⌋` for `x < 2^256` (checked by the caller, never assumed). -/
def nsqrt (x : ℕ) : ℕ := if x = 0 then 0 else nsqrtAux 300 x x

/-- `⌊√t⌋` for `t > 0`, and `0` otherwise. -/
def isqrtZ (t : ℤ) : ℤ := if t ≤ 0 then 0 else (nsqrt t.toNat : ℤ)

/-- A certificate for the constant: the roots exactly, each with a period `P` of its residue
cycle and the number `g` of admissible states in it. -/
structure CountCert where
  /-- Every root has `Y ≤ Ymax`. -/
  Ymax : ℕ
  /-- `(root, (P, g))`. -/
  roots : List ((ℤ × ℤ) × (ℕ × ℕ))

/-- The integer check: the listed points are roots (solutions whose predecessor is not), every
root in the box `4A Y^2 ≤ |Δ| u^2` is listed, and each `(P, g)` is a period of the residue
cycle and its number of states accepted by `goodB`. -/
def CountCert.check (M : ℕ) (goodB : ℤ × ℤ → Bool) (A B C u v : ℤ) (c : CountCert) : Bool :=
  decide ((c.roots.map Prod.fst).Nodup) &&
  decide (|B ^ 2 - 4 * A * C| * u ^ 2 < 4 * A * ((c.Ymax : ℤ) + 1) ^ 2) &&
  (List.range (c.Ymax + 1)).all (fun Y =>
    let t := B ^ 2 - 4 * A * C + 4 * A * (Y : ℤ) ^ 2
    let q := isqrtZ t
    decide (t ≤ 0) ||
      (decide (0 ≤ q ∧ q * q ≤ t ∧ t < (q + 1) * (q + 1)) &&
        (!decide (q * q = t) || !decide (0 < q) ||
          solB (4 * A) (B ^ 2 - 4 * A * C) (pred (4 * A) u v (q, (Y : ℤ))) ||
          decide ((q, (Y : ℤ)) ∈ c.roots.map Prod.fst)))) &&
  c.roots.all (fun r =>
    solB (4 * A) (B ^ 2 - 4 * A * C) r.1 &&
    !solB (4 * A) (B ^ 2 - 4 * A * C) (pred (4 * A) u v r.1) &&
    decide (0 < r.2.1) &&
    decide (iterForce (stepInt M (4 * A) u v) r.2.1 (r.1.1 % M, r.1.2 % M) =
      (r.1.1 % M, r.1.2 % M)) &&
    decide (orbitCount (stepInt M (4 * A) u v) goodB r.2.1 (r.1.1 % M, r.1.2 % M) 0 = r.2.2))

/-- **The count with a certified constant.**  If the certificate checks, the filtered family
satisfies `|A(N) - (∑ g / P) / log ε · log N| ≤ K` for all `N > |B|`. -/
theorem count_of_cert {M : ℕ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M)
    (hdiv : ∀ p, F.good p → 2 * A ∣ p.1 - B) (goodB : ℤ × ℤ → Bool)
    (hgood : ∀ p, F.goodMod (castPair M p) ↔ goodB p = true)
    (c : CountCert) (hc : c.check M goodB A B C u v = true) :
    ∃ K : ℝ, ∀ N : ℕ, B.natAbs + 1 ≤ N →
      |((countHits A B C F.good N : ℕ) : ℝ) -
        (c.roots.map fun e => (e.2.2 : ℝ) / e.2.1).sum / Real.log (eps (4 * A) u v) *
          Real.log N| ≤ K := by
  simp only [CountCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨hnodup, hbox⟩, hlist⟩, hroots⟩ := hc
  set D := 4 * A
  set Δ := B ^ 2 - 4 * A * C
  have hD : 0 < D := by positivity
  have hu' : u ^ 2 - D * v ^ 2 = 1 := hu
  set R := (c.roots.map Prod.fst).toFinset
  set P : ℤ × ℤ → ℕ := fun ρ => (lk c.roots ρ).1
  have hentry : ∀ ρ ∈ R, ∃ e ∈ c.roots, e.1 = ρ := by
    intro ρ hρ
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hρ)
    exact ⟨e, he, rfl⟩
  have hR : ∀ ρ, ρ ∈ R ↔ IsRoot D u v Δ ρ := by
    intro ρ
    constructor
    · intro hρ
      obtain ⟨e, he, rfl⟩ := hentry ρ hρ
      obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩ := hroots e he
      exact ⟨(solB_iff _).mp h1, fun h => by rw [(solB_iff _).mpr h] at h2; exact absurd h2 (by decide)⟩
    · intro hρ
      have hρbox := root_in_box hD hu1 hv hu' hρ
      obtain ⟨hρX, hρY, hρN⟩ := hρ.1
      have hρY' : ρ.2 < (c.Ymax : ℤ) + 1 := by
        by_contra h'
        push_neg at h'
        have : D * ((c.Ymax : ℤ) + 1) ^ 2 ≤ D * ρ.2 ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hD.le
          exact pow_le_pow_left₀ (by positivity) h' 2
        linarith [le_abs_self Δ]
      have hYn : ρ.2.toNat < c.Ymax + 1 := by omega
      have hYc : ((ρ.2.toNat : ℕ) : ℤ) = ρ.2 := Int.toNat_of_nonneg hρY
      have ht : Δ + D * ((ρ.2.toNat : ℕ) : ℤ) ^ 2 = ρ.1 * ρ.1 := by rw [hYc]; linarith
      rcases hlist _ hYn with hneg | ⟨⟨hq0, hq1, hq2⟩, hsq⟩
      · rw [ht] at hneg; nlinarith
      rw [ht] at hq0 hq1 hq2 hsq
      generalize isqrtZ (ρ.1 * ρ.1) = q at hq0 hq1 hq2 hsq
      have hqX : q = ρ.1 := by
        have h1 : q ≤ ρ.1 := by nlinarith
        have h2 : ρ.1 < q + 1 := by nlinarith
        omega
      rw [hqX, hYc] at hsq
      rcases hsq with ((hnot | hnot) | hpred) | hmem
      · exact absurd rfl hnot
      · exact absurd hρX hnot
      · exact absurd ((solB_iff _).mp hpred) hρ.2
      · exact List.mem_toFinset.mpr hmem
  have hP : ∀ ρ ∈ R, 0 < P ρ ∧ ∀ j, castPair M (unitOrbit D u v ρ (j + P ρ)) =
      castPair M (unitOrbit D u v ρ j) := by
    intro ρ hρ
    obtain ⟨e, he, rfl⟩ := hentry ρ hρ
    obtain ⟨⟨⟨-, hP0⟩, hper⟩, -⟩ := hroots e he
    rw [iterForce_eq] at hper
    have hlk : P e.1 = e.2.1 := by simp only [P, lk_of_mem hnodup e he]
    refine ⟨hlk ▸ hP0, fun j => ?_⟩
    rw [hlk, castPair_orbit, castPair_orbit, ← castPair_mod M e.1, ← castPair_stepInt_iter,
      ← castPair_stepInt_iter, Function.iterate_add_apply, hper]
  have hmain := filtered_count hA hu1 hv hu F hdiv R hR P hP
  have hsum : (∑ ρ ∈ R, (#((range (P ρ)).filter fun j =>
      F.goodMod (castPair M (unitOrbit D u v ρ j))) : ℝ) / P ρ) =
      (c.roots.map fun e => (e.2.2 : ℝ) / e.2.1).sum := by
    rw [List.sum_toFinset _ hnodup, List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    obtain ⟨⟨-, -⟩, hg⟩ := hroots e he
    rw [orbitCount_eq, zero_add] at hg
    simp only [Function.comp, P, lk_of_mem hnodup e he]
    congr 2
    rw [← hg]
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 1
    apply List.filter_congr
    intro j _
    rw [castPair_orbit, ← castPair_mod M e.1, ← castPair_stepInt_iter]
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff, hgood])
  rw [hsum] at hmain
  exact hmain

/-! ### The quadratic-root constraint, counted -/

/-- The number of `n ∈ [1, N]` solving `a y^2 + b y + c = A₀ n^2 + B₀ n + C₀`, `y` in its
domain. -/
noncomputable def countQuad (a b c A₀ B₀ C₀ : ℤ) (L : Option ℤ) (N : ℕ) : ℕ :=
  #((Icc 1 N).filter fun n => n ∈ QuadHits a b c A₀ B₀ C₀ L)

/-- The original count and the filtered count differ only below the vertex. -/
lemma countQuad_near {a b c A₀ B₀ C₀ : ℤ} (L : Option ℤ) (ha : a ≠ 0) (hA : 0 < 4 * a * A₀)
    (N : ℕ) :
    ((countHits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
        (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).good N : ℕ) : ℤ) ≤
        countQuad a b c A₀ B₀ C₀ L N ∧
      (countQuad a b c A₀ B₀ C₀ L N : ℤ) ≤
        countHits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
          (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).good N + (4 * a * B₀).natAbs := by
  set A := 4 * a * A₀
  set B := 4 * a * B₀
  constructor
  · unfold countHits countQuad
    have : ((Icc 1 N).filter fun n : ℕ => ∃ Y : ℤ, Sol (4 * A) (B ^ 2 - 4 * A *
        (4 * a * C₀ + b ^ 2 - 4 * a * c)) (2 * A * n + B, Y) ∧
        (quadFilter a b A B L ha).good (2 * A * n + B, Y)) ⊆
        (Icc 1 N).filter fun n => n ∈ QuadHits a b c A₀ B₀ C₀ L := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      obtain ⟨⟨hn1, hnN⟩, Y, hs, hg⟩ := hn
      exact ⟨⟨hn1, hnN⟩, (quadHits_iff L ha hA n hs.1).mpr ⟨hn1, Y, hs, hg⟩⟩
    exact_mod_cast card_le_card this
  · have hsplit := filter_card_add_filter_neg_card_eq_card
      (s := (Icc 1 N).filter fun n => n ∈ QuadHits a b c A₀ B₀ C₀ L)
      (fun n : ℕ => 0 < 2 * A * n + B)
    have h1 : (((Icc 1 N).filter fun n => n ∈ QuadHits a b c A₀ B₀ C₀ L).filter
        fun n : ℕ => 0 < 2 * A * n + B).card ≤ countHits A B (4 * a * C₀ + b ^ 2 - 4 * a * c)
          (quadFilter a b A B L ha).good N := by
      unfold countHits
      apply card_le_card
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      obtain ⟨⟨⟨hn1, hnN⟩, hq⟩, hX⟩ := hn
      obtain ⟨-, Y, hs, hg⟩ := (quadHits_iff L ha hA n hX).mp hq
      exact ⟨⟨hn1, hnN⟩, Y, hs, hg⟩
    have h2 : (((Icc 1 N).filter fun n => n ∈ QuadHits a b c A₀ B₀ C₀ L).filter
        fun n : ℕ => ¬ 0 < 2 * A * n + B).card ≤ B.natAbs := by
      calc _ ≤ (Icc 1 B.natAbs).card := by
            apply card_le_card
            intro n hn
            simp only [mem_filter, mem_Icc, not_lt] at hn ⊢
            obtain ⟨⟨⟨hn1, -⟩, -⟩, hX⟩ := hn
            refine ⟨hn1, ?_⟩
            have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
            have : (n : ℤ) ≤ |B| := by
              nlinarith [neg_abs_le B, (by exact_mod_cast hn1 : (1 : ℤ) ≤ n)]
            omega
        _ = B.natAbs := by simp
    unfold countQuad
    omega

/-- **The quadratic-root constraint with a certified constant.**  If the certificate checks,
`|#{n ≤ N : a y^2 + b y + c = F(n) for some y in the domain} - κ log N| ≤ K` for all large `N`,
with `κ = (∑ g / P) / log ε` read off the certificate. -/
theorem quadRoot_count_of_cert {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) (cert : CountCert)
    (hc : cert.check (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v = true) :
    ∃ K : ℝ, ∀ N : ℕ, (4 * a * B₀).natAbs + 1 ≤ N →
      |((countQuad a b c A₀ B₀ C₀ L N : ℕ) : ℝ) -
        (cert.roots.map fun e => (e.2.2 : ℝ) / e.2.1).sum /
          Real.log (eps (4 * (4 * a * A₀)) u v) * Real.log N| ≤ K := by
  obtain ⟨K, hK⟩ := count_of_cert hA hu1 hv hu (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha)
    (fun p hp => hp.1) _ (fun p => quadGoodB_iff L ha p) cert hc
  refine ⟨K + (4 * a * B₀).natAbs, fun N hN => ?_⟩
  have h := hK N hN
  obtain ⟨h1, h2⟩ := countQuad_near L ha hA N (b := b) (c := c) (C₀ := C₀)
  have h1' : ((countHits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
      (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).good N : ℕ) : ℝ) ≤
      countQuad a b c A₀ B₀ C₀ L N := by exact_mod_cast h1
  have h2' : ((countQuad a b c A₀ B₀ C₀ L N : ℕ) : ℝ) ≤
      (countHits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
        (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).good N : ℕ) +
        ((4 * a * B₀).natAbs : ℕ) := by exact_mod_cast h2
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

end PerfectPower.FilteredPell
