import PerfectPower.PellExact

/-!
# Observations of orbits: counting the values a coordinate takes

A Pell orbit is one arithmetic object; a sequence in a table is one **coordinate** of it (the
`X`, the `Y`, `Y^2`, `(X - 1)/2`, …).  The count of a coordinate's values up to `N` depends on
how fast the coordinate grows: if it grows like `E^j` with `E = ε^r`, the count is
`log N / (r log ε)`, so the same orbit gives different constants for different observations.

* `count_between`: a sequence with `c₁ E^h ≤ f h ≤ c₂ E^h` has `log M / log E + O(1)` indices
  with `f h ≤ M`.
* `filtered_obs_count`: the same, restricted to indices in a periodic set with `g` of `P`
  residues accepted: `g log M / (P log E) + O(1)`.
* `value_count`: **from indices to values.**  For finitely many observations `obs ρ`, each
  strictly increasing, whose accepted values do not coincide across different `ρ` above a
  threshold `V₀`, the number of values in `[1, N]` differs from the sum of the index counts by
  at most `(#R + 1)(V₀ + 1)`.
* `observed_count`: **the counting law for observations of filtered orbits**
  `#{v ≤ N} = (∑_ρ g_ρ / (P_ρ log E_ρ)) log N + O(1)`.

Nothing here mentions Pell equations: the orbit enters only through the growth bounds, the
period of the filter, and the disjointness of the observed images, which each instance proves.
-/

namespace PerfectPower.Observation

open PerfectPower PellExact Finset

/-- **Counting between two geometric bounds.** -/
theorem count_between {f : ℕ → ℝ} {E c₁ c₂ : ℝ} (hE : 1 < E) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ h, c₁ * E ^ h ≤ f h) (hup : ∀ h, f h ≤ c₂ * E ^ h) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M → (∀ h, f h ≤ M → h < L) →
      |(((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ) - Real.log M / Real.log E| ≤ K := by
  have hlogE : 0 < Real.log E := Real.log_pos hE
  refine ⟨|Real.log c₁| / Real.log E + 1 + |Real.log c₂| / Real.log E, fun M L hM hL => ?_⟩
  have hM0 : 0 < M := by linarith
  set cnt := (((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hupper : cnt ≤ Real.log M / Real.log E + |Real.log c₁| / Real.log E + 1 := by
    rcases le_or_lt c₁ M with h1 | h1
    · have := geometric_count_le hE hc₁ h1 hlow L
      rw [Real.log_div hM0.ne' hc₁.ne', sub_div] at this
      have : -(Real.log c₁ / Real.log E) ≤ |Real.log c₁| / Real.log E := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_le_abs _) hlogE.le
      linarith
    · have hzero : (Finset.range L).filter (fun h => f h ≤ M) = ∅ := by
        apply Finset.filter_false_of_mem
        intro h _ hh
        have := hlow h
        have : c₁ ≤ c₁ * E ^ h := le_mul_of_one_le_right hc₁.le (one_le_pow₀ hE.le)
        linarith
      have : cnt = 0 := by simp only [cnt, hzero, Finset.card_empty, Nat.cast_zero]
      have := div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le
      have := div_nonneg hlogM hlogE.le
      linarith
  have hlower : Real.log M / Real.log E - |Real.log c₂| / Real.log E ≤ cnt := by
    have hLb : Real.log (M / c₂) / Real.log E < L := by
      set q := Real.log (M / c₂) / Real.log E
      rcases lt_or_le q 0 with hq | hq
      · exact hq.trans_le (Nat.cast_nonneg _)
      · have hfl := Nat.floor_le hq
        have hmem := le_of_index_le_geometric hE hc₂ hM0 hup hfl
        have := hL _ hmem
        have : (⌊q⌋₊ : ℝ) + 1 ≤ L := by exact_mod_cast this
        linarith [Nat.lt_floor_add_one q]
    have := le_geometric_count hE hc₂ hM0 hup L hLb
    rw [Real.log_div hM0.ne' hc₂.ne', sub_div] at this
    have : Real.log c₂ / Real.log E ≤ |Real.log c₂| / Real.log E :=
      div_le_div_of_nonneg_right (le_abs_self _) hlogE.le
    linarith
  rw [abs_le]
  constructor <;> linarith [div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le,
    div_nonneg (abs_nonneg (Real.log c₂)) hlogE.le]

/-- **A filtered observation.**  With `g` accepted residues among `P`, the number of accepted
indices with `f j ≤ M` is `g log M / (P log E) + O(1)`. -/
theorem filtered_obs_count {f : ℕ → ℝ} {E c₁ c₂ : ℝ} (hE : 1 < E) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ h, c₁ * E ^ h ≤ f h) (hup : ∀ h, f h ≤ c₂ * E ^ h) {P : ℕ} (hP : 0 < P)
    (q : ℕ → Prop) [DecidablePred q] (hq : ∀ j, q (j + P) ↔ q j) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M → (∀ j, f j ≤ M → j < L) →
      |((#{j ∈ range L | q j ∧ f j ≤ M} : ℕ) : ℝ) -
        (#((range P).filter q) : ℕ) * (Real.log M / (P * Real.log E))| ≤ K := by
  have hE0 : 0 < E := by linarith
  have hEP : 1 < E ^ P := one_lt_pow₀ hE hP.ne'
  have hK : ∀ r, ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M → (∀ h, f (r + P * h) ≤ M → h < L) →
      |((((range L).filter (fun h => f (r + P * h) ≤ M)).card : ℕ) : ℝ) -
        Real.log M / (P * Real.log E)| ≤ K := by
    intro r
    obtain ⟨K, hK⟩ := count_between (f := fun h => f (r + P * h)) hEP
      (mul_pos hc₁ (pow_pos hE0 r)) (mul_pos hc₂ (pow_pos hE0 r))
      (fun h => by have := hlow (r + P * h); rw [pow_add, pow_mul] at this; linarith)
      (fun h => by have := hup (r + P * h); rw [pow_add, pow_mul] at this; linarith)
    refine ⟨K, fun M L hM hL => ?_⟩
    have := hK M L hM hL
    rwa [Real.log_pow] at this
  choose Kf hKf using hK
  set G := (range P).filter q
  refine ⟨∑ r ∈ G, Kf r, fun M L hM hL => ?_⟩
  rw [card_split_residue P L hP q hq (fun j => f j ≤ M) hL]
  push_cast
  have hG : ((#G : ℕ) : ℝ) * (Real.log M / (P * Real.log E)) =
      ∑ r ∈ G, Real.log M / (P * Real.log E) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hG, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hLr : ∀ h, f (r + P * h) ≤ M → h < L := by
    intro h hh
    have := hL _ hh
    have : h ≤ r + P * h := by nlinarith
    omega
  exact hKf r M L hM hLr

/-- **From indices to values.**  Finitely many strictly increasing observations, whose accepted
values coincide across different `ρ` only at or below `V₀`: the number of values in `[1, N]`
is the sum of the index counts up to `(#R + 1)(V₀ + 1)`. -/
theorem value_count {ι : Type*} (R : Finset ι) (obs : ι → ℕ → ℕ)
    (q : ι → ℕ → Prop) [∀ ρ, DecidablePred (q ρ)] (hmono : ∀ ρ ∈ R, StrictMono (obs ρ))
    (V₀ : ℕ) (hdisj : ∀ ρ ∈ R, ∀ σ ∈ R, ∀ i j, q ρ i → q σ j → obs ρ i = obs σ j →
      V₀ < obs ρ i → ρ = σ)
    (S : Set ℕ) [DecidablePred (· ∈ S)] (hS : ∀ v, v ∈ S ↔ ∃ ρ ∈ R, ∃ j, q ρ j ∧ obs ρ j = v)
    (N : ℕ) :
    |((#{v ∈ Icc 1 N | v ∈ S} : ℕ) : ℝ) -
        ∑ ρ ∈ R, ((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ)| ≤
      (R.card + 1) * (V₀ + 1) := by
  -- the accepted indices whose value is above `V₀`
  set I : ι → Finset ℕ := fun ρ => {j ∈ range (N + 1) | q ρ j ∧ V₀ < obs ρ j ∧ obs ρ j ≤ N}
  set A := {v ∈ Icc 1 N | v ∈ S}
  have hsplit : A = {v ∈ A | v ≤ V₀} ∪ R.biUnion (fun ρ => (I ρ).image (obs ρ)) := by
    ext v
    simp only [A, I, mem_union, mem_filter, mem_Icc, mem_biUnion, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, hN⟩, hv⟩
      rcases le_or_lt v V₀ with hs | hb
      · exact Or.inl ⟨⟨⟨h1, hN⟩, hv⟩, hs⟩
      · obtain ⟨ρ, hρ, j, hq, rfl⟩ := (hS v).mp hv
        have hj : j ≤ obs ρ j := (hmono ρ hρ).id_le j
        exact Or.inr ⟨ρ, hρ, j, ⟨by omega, hq, hb, hN⟩, rfl⟩
    · rintro (⟨h, -⟩ | ⟨ρ, hρ, j, ⟨-, hq, hb, hN⟩, rfl⟩)
      · exact h
      · exact ⟨⟨by omega, hN⟩, (hS _).mpr ⟨ρ, hρ, j, hq, rfl⟩⟩
  have hdisjU : Disjoint ({v ∈ A | v ≤ V₀}) (R.biUnion (fun ρ => (I ρ).image (obs ρ))) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [mem_filter] at hv
    simp only [I, mem_biUnion, mem_image, mem_filter] at hv'
    obtain ⟨ρ, -, j, ⟨-, -, hb, -⟩, rfl⟩ := hv'
    omega
  have hpair : (R : Set ι).PairwiseDisjoint (fun ρ => (I ρ).image (obs ρ)) := by
    intro ρ hρ σ hσ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [I, mem_image, mem_filter] at hv hv'
    obtain ⟨i, ⟨-, hqi, hbi, -⟩, rfl⟩ := hv
    obtain ⟨j, ⟨-, hqj, -, -⟩, hij⟩ := hv'
    exact hne (hdisj ρ hρ σ hσ i j hqi hqj hij.symm hbi)
  have hcardA : #A = #{v ∈ A | v ≤ V₀} + ∑ ρ ∈ R, #(I ρ) := by
    have h1 := card_union_of_disjoint hdisjU
    rw [← hsplit, card_biUnion hpair] at h1
    rw [h1]
    congr 1
    refine sum_congr rfl fun ρ hρ => ?_
    rw [card_image_of_injOn]
    intro i _ j _ h
    exact (hmono ρ hρ).injective h
  have hsmall : (#{v ∈ A | v ≤ V₀} : ℝ) ≤ V₀ + 1 := by
    have : {v ∈ A | v ≤ V₀} ⊆ range (V₀ + 1) := by
      intro v hv; simp only [mem_filter] at hv; simp only [mem_range]; omega
    have := card_le_card this
    rw [card_range] at this
    exact_mod_cast this
  have hidx : ∀ ρ ∈ R, (#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℝ) - #(I ρ) ∈
      Set.Icc (0 : ℝ) (V₀ + 1) := by
    intro ρ hρ
    have hsub : I ρ ⊆ {j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} := by
      intro j hj; simp only [I, mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.1, hj.2.2.2⟩
    have hdiff : {j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} \ I ρ ⊆ range (V₀ + 1) := by
      intro j hj
      simp only [I, mem_sdiff, mem_filter, mem_range] at hj ⊢
      obtain ⟨⟨hjN, hq, hle⟩, hn⟩ := hj
      have hsm : obs ρ j ≤ V₀ := by
        by_contra hc
        push_neg at hc
        exact hn ⟨hjN, hq, hc, hle⟩
      have hid : j ≤ obs ρ j := (hmono ρ hρ).id_le j
      omega
    have h1 := card_sdiff hsub
    have h2 := card_le_card hdiff
    have h3 := card_le_card hsub
    rw [card_range] at h2
    constructor
    · have : (#(I ρ) : ℝ) ≤ #{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} := by exact_mod_cast h3
      linarith
    · have : (#({j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} \ I ρ) : ℝ) ≤ V₀ + 1 := by
        exact_mod_cast h2
      rw [h1, Nat.cast_sub h3] at this
      linarith
  have hcardA' : (#A : ℝ) = #{v ∈ A | v ≤ V₀} + ∑ ρ ∈ R, (#(I ρ) : ℝ) := by
    rw [hcardA]; push_cast; ring
  rw [hcardA']
  have hsum : ∑ ρ ∈ R, ((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ) -
      ∑ ρ ∈ R, (#(I ρ) : ℝ) ∈ Set.Icc (0 : ℝ) (R.card * (V₀ + 1)) := by
    rw [← sum_sub_distrib]
    constructor
    · exact sum_nonneg fun ρ hρ => (hidx ρ hρ).1
    · have := sum_le_sum fun ρ hρ => (hidx ρ hρ).2
      rw [sum_const, nsmul_eq_mul] at this
      exact this
  rw [abs_le]
  constructor <;> nlinarith [hsum.1, hsum.2, (Nat.cast_nonneg _ : (0 : ℝ) ≤ #{v ∈ A | v ≤ V₀})]

/-- **The counting law for observations of filtered orbits.**  Finitely many observations
`obs ρ`, strictly increasing, with `c₁ E_ρ^j ≤ obs ρ j ≤ c₂ E_ρ^j`, accepted on a set of indices
of period `P_ρ`, and with images that coincide across orbits only at or below `V₀`: the set `S`
of all accepted values satisfies
`#{v ∈ S : v ≤ N} = (∑_ρ g_ρ / (P_ρ log E_ρ)) log N + O(1)`. -/
theorem observed_count {ι : Type*} [DecidableEq ι] (R : Finset ι) (obs : ι → ℕ → ℕ)
    (E c₁ c₂ : ι → ℝ) (hE : ∀ ρ ∈ R, 1 < E ρ) (hc₁ : ∀ ρ ∈ R, 0 < c₁ ρ) (hc₂ : ∀ ρ ∈ R, 0 < c₂ ρ)
    (hlow : ∀ ρ ∈ R, ∀ j, c₁ ρ * E ρ ^ j ≤ obs ρ j)
    (hup : ∀ ρ ∈ R, ∀ j, (obs ρ j : ℝ) ≤ c₂ ρ * E ρ ^ j)
    (P : ι → ℕ) (hP : ∀ ρ ∈ R, 0 < P ρ)
    (q : ι → ℕ → Prop) [∀ ρ, DecidablePred (q ρ)] (hq : ∀ ρ ∈ R, ∀ j, q ρ (j + P ρ) ↔ q ρ j)
    (hmono : ∀ ρ ∈ R, StrictMono (obs ρ))
    (V₀ : ℕ) (hdisj : ∀ ρ ∈ R, ∀ σ ∈ R, ∀ i j, q ρ i → q σ j → obs ρ i = obs σ j →
      V₀ < obs ρ i → ρ = σ)
    (S : Set ℕ) [DecidablePred (· ∈ S)] (hS : ∀ v, v ∈ S ↔ ∃ ρ ∈ R, ∃ j, q ρ j ∧ obs ρ j = v) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |((#{v ∈ Icc 1 N | v ∈ S} : ℕ) : ℝ) -
        (∑ ρ ∈ R, (#((range (P ρ)).filter (q ρ)) : ℝ) / (P ρ * Real.log (E ρ))) * Real.log N| ≤ K := by
  have hK : ∀ ρ, ∃ K : ℝ, ρ ∈ R → ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, (obs ρ j : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | q ρ j ∧ (obs ρ j : ℝ) ≤ M} : ℕ) : ℝ) -
        (#((range (P ρ)).filter (q ρ)) : ℕ) * (Real.log M / (P ρ * Real.log (E ρ)))| ≤ K := by
    intro ρ
    by_cases hρ : ρ ∈ R
    · obtain ⟨K, hK⟩ := filtered_obs_count (f := fun j => (obs ρ j : ℝ)) (hE ρ hρ) (hc₁ ρ hρ)
        (hc₂ ρ hρ) (hlow ρ hρ) (hup ρ hρ) (hP ρ hρ) (q ρ) (hq ρ hρ)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hρ⟩
  choose Kf hKf using hK
  refine ⟨∑ ρ ∈ R, Kf ρ + (R.card + 1) * (V₀ + 1), fun N hN => ?_⟩
  have hv := value_count R obs q hmono V₀ hdisj S hS N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hidx : ∀ ρ ∈ R, |((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ) -
      (#((range (P ρ)).filter (q ρ)) : ℕ) * (Real.log N / (P ρ * Real.log (E ρ)))| ≤ Kf ρ := by
    intro ρ hρ
    have hL : ∀ j, (obs ρ j : ℝ) ≤ N → j < N + 1 := by
      intro j hj
      have hjN : obs ρ j ≤ N := by exact_mod_cast hj
      have hid : j ≤ obs ρ j := (hmono ρ hρ).id_le j
      omega
    have := hKf ρ hρ N (N + 1) hN1 hL
    have e : ({j ∈ range (N + 1) | q ρ j ∧ (obs ρ j : ℝ) ≤ N} : Finset ℕ) =
        {j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} := by
      apply filter_congr; intro j _; rw [Nat.cast_le]
    rwa [e] at this
  have hsum : |∑ ρ ∈ R, ((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ) -
      (∑ ρ ∈ R, (#((range (P ρ)).filter (q ρ)) : ℝ) / (P ρ * Real.log (E ρ))) * Real.log N| ≤
      ∑ ρ ∈ R, Kf ρ := by
    rw [sum_mul, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ρ hρ => ?_)
    have := hidx ρ hρ
    have e : (#((range (P ρ)).filter (q ρ)) : ℝ) / (P ρ * Real.log (E ρ)) * Real.log N =
        (#((range (P ρ)).filter (q ρ)) : ℕ) * (Real.log N / (P ρ * Real.log (E ρ))) := by ring
    rwa [e]
  calc _ ≤ |((#{v ∈ Icc 1 N | v ∈ S} : ℕ) : ℝ) -
          ∑ ρ ∈ R, ((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ)| +
        |∑ ρ ∈ R, ((#{j ∈ range (N + 1) | q ρ j ∧ obs ρ j ≤ N} : ℕ) : ℝ) -
          (∑ ρ ∈ R, (#((range (P ρ)).filter (q ρ)) : ℝ) / (P ρ * Real.log (E ρ))) * Real.log N| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

end PerfectPower.Observation
