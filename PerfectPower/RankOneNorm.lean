import PerfectPower.RankOneZeros

/-!
# Rank-one norm orbits: elements of norm `±N`

`RankOne.units_eq` reduces every unit to `±ηⁿ`.  This module does the same for elements of norm
`±N`: every `w` with `N(w) = ±N` is `γ ηⁿ` for some `γ` in an explicit list `L` (`normN_eq`).
* The reduced element `v = w η^{−n}` has `1 ≤ |σ(v)| < σ(η)`, so `re² + κ² j² = N/|σ| ≤ N`.
  The certificate replaces `|re| ≤ 1` by `|re| ≤ R₀` (`R₀² ≥ N`) and `κ² J² ≥ 1` by `κ² J² ≥ N`
  (`condNB`).  The slab check (`slabNB`) finds only elements of `L` among those of norm `±N`.
* **Orbit congruence** (`orbit_ne`): if `η^M ≡ 1 (mod q)` and `q ∤ (γ η^r)₂` for all `r < M`
  (and likewise for `ε = η⁻¹`), then `(γ ηⁿ)₂ ≠ 0` for every integer `n`.
Together: `N(w) = ±N` and `w₂ = 0` is impossible (`no_corner_zero`).  For a nonmonic Thue
equation `F(u, v) = 1`, the monic reduction (`LatticeTransport.monic_identity`) gives exactly
such a `w`, so the equation has no solution.
-/

namespace PerfectPower.RankOneNorm

open PerfectPower UnitBox UnitPremises UnitGenProof NormRepProof RankOne Matrix

/-- **The side conditions for norm `N`** (`condB` with `|re| ≤ R₀`, `κ² J² ≥ N`). -/
def condNB (P Q : ℤ) (η : Z3) (c : Cert) (N : ℕ) (R0 : ℚ) : Bool :=
  decide (c.lo ≤ c.hi) && decide (cub P Q c.lo * cub P Q c.hi < 0) && decide (0 < c.K P) &&
  decide (0 ≤ c.J) && decide ((N : ℚ) ≤ c.K P * c.J ^ 2) && decide (0 < c.Dn P) &&
  decide (1 < sigQ c.lo η - rad η c.lo c.hi) &&
  decide (c.E η + R0 + 3 / 2 * c.T * c.J < (c.C + 1) * c.Dn P) &&
  decide (0 ≤ R0) && decide ((N : ℚ) ≤ R0 ^ 2)

/-- The candidates for `a` given `b, c`, with `|re| ≤ R₀`. -/
def aRangeN (P : ℤ) (c : Cert) (R0 : ℚ) (b cc : ℤ) : List ℤ :=
  ints (-R0 + lmin b c.lo c.hi / 2 - cc * P + lmin cc c.t2lo (c.T ^ 2) / 2)
    (R0 + lmax b c.lo c.hi / 2 - cc * P + lmax cc c.t2lo (c.T ^ 2) / 2)

/-- One slab: every element of norm `±N` is in `L` or has `|σ| < 1`. -/
def slabSliceNB (P Q : ℤ) (c : Cert) (N : ℕ) (R0 : ℚ) (L : List Z3) (l : ℕ) : Bool :=
  (bRange c ((l : ℤ) - c.C)).all fun b => (aRangeN P c R0 b ((l : ℤ) - c.C)).all fun a =>
    let g : Z3 := (a, b, (l : ℤ) - c.C)
    decide (nrm P Q g ≠ N ∧ nrm P Q g ≠ -N) || decide (g ∈ L) || decide (pHi g c.lo c.hi < 1)

/-- The reduction check for norm `N`. -/
def slabNB (P Q : ℤ) (c : Cert) (N : ℕ) (R0 : ℚ) (L : List Z3) : Bool :=
  (List.range (2 * c.C + 1)).all (slabSliceNB P Q c N R0 L)

set_option maxHeartbeats 1000000 in
/-- **A reduced element of norm `±N` is in the list `L`.** -/
@[nolint unusedHavesSuffices]
theorem reduced_memN {P Q : ℤ} {η : Z3} {c : Cert} {N : ℕ} {R0 : ℚ} {L : List Z3}
    (hc : condNB P Q η c N R0 = true) (hbox : slabNB P Q c N R0 L = true)
    {t : ℝ} (h1 : (c.lo : ℝ) ≤ t) (h2 : t ≤ c.hi) (ht : t ^ 3 = (P : ℝ) * t + Q) (v : Z3)
    (hv : nrm P Q v = N ∨ nrm P Q v = -N) (hs1 : 1 ≤ |sig t v|) (hs2 : |sig t v| ≤ ((c.E η : ℚ) : ℝ)) :
    v ∈ L := by
  simp only [condNB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hK⟩, hJ0⟩, hKJ⟩, hDn⟩, _⟩, hcC⟩, hR0⟩, hNR⟩ := hc
  obtain ⟨R, hRdef⟩ : ∃ x, x = ((R0 : ℚ) : ℝ) := ⟨_, rfl⟩
  have hR0' : (0 : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hR0
  have hNR' : (N : ℝ) ≤ R ^ 2 := by rw [hRdef]; exact_mod_cast hNR
  obtain ⟨a, b, cc⟩ := v
  have hsplit := norm_split ht (a, b, cc)
  simp only at hsplit
  obtain ⟨s, hsdef⟩ : ∃ s, s = sig t (a, b, cc) := ⟨_, rfl⟩
  obtain ⟨re, hredef⟩ : ∃ re, re = (a : ℝ) - b * t / 2 + cc * (P - t ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = (b : ℝ) - cc * t := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 3 * t ^ 2 / 4 - (P : ℝ) := ⟨_, rfl⟩
  rw [← hsdef, ← hredef, ← hjdef, ← hκdef] at hsplit
  rw [← hsdef] at hs1 hs2
  -- rational bounds as reals
  obtain ⟨T, hTdef⟩ : ∃ T, T = ((c.T : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨t2l, ht2ldef⟩ : ∃ x, x = ((c.t2lo : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ x, x = ((c.J : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ x, x = ((c.E η : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hEdef] at hs2
  have hta : |t| ≤ T := by rw [hTdef]; exact abs_le_max_of h1 h2
  have ht2l : t2l ≤ t ^ 2 := by rw [ht2ldef]; exact t2lo_le h1 h2
  have ht2h : t ^ 2 ≤ T ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) hta 2
  have hK' : (0 : ℝ) < 3 * t2l / 4 - P := by
    rw [ht2ldef]; have : (0 : ℚ) < c.K P := hK; simp only [Cert.K] at this; exact_mod_cast this
  have hKJ' : (N : ℝ) ≤ (3 * t2l / 4 - P) * J ^ 2 := by
    rw [ht2ldef, hJdef]; have : (N : ℚ) ≤ c.K P * c.J ^ 2 := hKJ; simp only [Cert.K] at this
    exact_mod_cast this
  have hJ0' : (0 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hJ0
  have hDn' : (0 : ℝ) < 3 * t2l - P := by
    rw [ht2ldef]; have : (0 : ℚ) < c.Dn P := hDn; simp only [Cert.Dn] at this; exact_mod_cast this
  have hκK : 3 * t2l / 4 - P ≤ κ := by rw [hκdef]; linarith
  have hκ0 : 0 < κ := by linarith
  -- |s| G = N, so G ≤ N
  have hG0 : 0 ≤ re ^ 2 + κ * j ^ 2 := by positivity
  have hsG : |s| * (re ^ 2 + κ * j ^ 2) = N := by
    have : |s * (re ^ 2 + κ * j ^ 2)| = N := by
      rw [← hsplit]; rcases hv with h | h <;> rw [h] <;> simp
    rwa [abs_mul, abs_of_nonneg hG0] at this
  have hGle : re ^ 2 + κ * j ^ 2 ≤ N := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hs1 hG0
    linarith
  have hκj : 0 ≤ κ * j ^ 2 := by positivity
  have hre2 : re ^ 2 ≤ R ^ 2 := by linarith
  have hre' : |re| ≤ R := abs_le_of_sq_le_sq' hre2 hR0' |> fun h => abs_le.mpr h
  have hj' : |j| ≤ J := by
    have hkj : (3 * t2l / 4 - P) * j ^ 2 ≤ N := by
      have := mul_le_mul_of_nonneg_right hκK (sq_nonneg j)
      have := sq_nonneg re
      linarith
    have hsq : j ^ 2 ≤ J ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hK'
      linarith
    exact abs_le_of_sq_le_sq' hsq hJ0' |> fun h => abs_le.mpr h
  -- invert: c (3t² − P) = s − re − (3t/2) j
  have ec : (cc : ℝ) * (3 * t ^ 2 - P) = s - re - 3 * t / 2 * j := by
    rw [hsdef, hredef, hjdef]; simp only [sig]; ring
  have htj : |t| * |j| ≤ T * J := mul_le_mul hta hj' (abs_nonneg j) (le_trans (abs_nonneg t) hta)
  have hden : 3 * t2l - P ≤ 3 * t ^ 2 - P := by linarith
  have hpos : (0 : ℝ) < 3 * t ^ 2 - P := by linarith
  have hcR : |(cc : ℝ)| < c.C + 1 := by
    have h3 : |3 * t / 2 * j| = 3 / 2 * (|t| * |j|) := by
      rw [abs_mul, abs_div, abs_mul]; norm_num; ring
    have hnum : |s - re - 3 * t / 2 * j| ≤ E + R + 3 / 2 * (T * J) := by
      have e1 := abs_sub (s - re) (3 * t / 2 * j)
      have e2 := abs_sub s re
      linarith only [e1, e2, h3, htj, hs2, hre']
    have hcabs : |(cc : ℝ) * (3 * t ^ 2 - P)| = |(cc : ℝ)| * (3 * t ^ 2 - P) := by
      rw [abs_mul, abs_of_pos hpos]
    rw [ec] at hcabs
    have hm := mul_le_mul_of_nonneg_left hden (abs_nonneg (cc : ℝ))
    have hq : E + R + 3 / 2 * (T * J) < (c.C + 1) * (3 * t2l - P) := by
      rw [hEdef, hTdef, hJdef, ht2ldef, hRdef]
      have : c.E η + R0 + 3 / 2 * c.T * c.J < (c.C + 1) * c.Dn P := hcC
      simp only [Cert.Dn] at this
      have := (Rat.cast_lt (K := ℝ)).mpr this
      push_cast at this
      linarith
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_right hcon hDn'.le
    linarith only [this, hq, hm, hcabs, hnum]
  have ic : |cc| ≤ c.C := by
    have : |(cc : ℝ)| < ((c.C : ℤ) : ℝ) + 1 := by exact_mod_cast hcR
    have : |cc| < (c.C : ℤ) + 1 := by exact_mod_cast this
    omega
  -- the slab: b from |j| ≤ J, a from |re| ≤ R
  have hj2 := abs_le.mp hj'
  have hre3 := abs_le.mp hre'
  have hb : b ∈ bRange c cc := by
    have l1 := lmin_le (cc : ℚ) h1 h2
    have l2 := le_lmax (cc : ℚ) h1 h2
    push_cast at l1 l2
    apply mem_ints
    · have : ((lmin cc c.lo c.hi - c.J : ℚ) : ℝ) ≤ (b : ℝ) := by
        push_cast; rw [← hJdef]; linarith only [l1, hj2.1, hjdef]
      exact_mod_cast this
    · have : (b : ℝ) ≤ ((lmax cc c.lo c.hi + c.J : ℚ) : ℝ) := by
        push_cast; rw [← hJdef]; linarith only [l2, hj2.2, hjdef]
      exact_mod_cast this
  have ht2h' : t ^ 2 ≤ (((c.T ^ 2 : ℚ)) : ℝ) := by push_cast; rw [← hTdef]; exact ht2h
  have ht2l' : (((c.t2lo : ℚ)) : ℝ) ≤ t ^ 2 := by rw [← ht2ldef]; exact ht2l
  have ha : a ∈ aRangeN P c R0 b cc := by
    have l1 := lmin_le (b : ℚ) h1 h2
    have l2 := le_lmax (b : ℚ) h1 h2
    have l3 := lmin_le (cc : ℚ) ht2l' ht2h'
    have l4 := le_lmax (cc : ℚ) ht2l' ht2h'
    push_cast at l1 l2 l3 l4
    apply mem_ints
    · have : ((-R0 + lmin b c.lo c.hi / 2 - cc * P + lmin cc c.t2lo (c.T ^ 2) / 2 : ℚ) : ℝ) ≤ (a : ℝ) := by
        push_cast; rw [← hRdef]; linarith only [l1, l3, hre3.1, hredef]
      exact_mod_cast this
    · have : (a : ℝ) ≤ ((R0 + lmax b c.lo c.hi / 2 - cc * P + lmax cc c.t2lo (c.T ^ 2) / 2 : ℚ) : ℝ) := by
        push_cast; rw [← hRdef]; linarith only [l2, l4, hre3.2, hredef]
      exact_mod_cast this
  simp only [slabNB, List.all_eq_true, List.mem_range] at hbox
  have ic' := abs_le.mp ic
  have hh := hbox (cc + c.C).toNat (by omega)
  have e3 : ((cc + c.C).toNat : ℤ) - c.C = cc := by omega
  simp only [slabSliceNB, e3, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hh
  rcases hh b hb a ha with (hn | hm) | hp
  · exfalso; rcases hv with h | h <;> simp [h] at hn
  · exact hm
  · exfalso
    have := (encl_sound (a, b, cc) h1 h2).2
    have hp' : ((pHi (a, b, cc) c.lo c.hi : ℚ) : ℝ) < 1 := by exact_mod_cast hp
    rw [← hsdef] at this
    linarith only [this, hp', hs1]

/-- **Norm-`N` generation**: every `w` with `N(w) = ±N` is `γ ηⁿ` with `γ ∈ L`. -/
@[nolint unusedHavesSuffices]
theorem normN_eq {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} {N : ℕ} {R0 : ℚ} {L : List Z3}
    (hc : condNB P Q η c N R0 = true) (hbox : slabNB P Q c N R0 L = true) (hN : 0 < N) (w : Z3)
    (hw : nrm P Q w = N ∨ nrm P Q w = -N) :
    ∃ n : ℤ, ∃ γ ∈ L, w = mul P Q γ (zp P Q η ε n) := by
  have hc' := hc
  simp only [condNB, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hle, hsgn⟩, _⟩, _⟩, _⟩, _⟩, hηlo⟩, _⟩, _⟩, _⟩ := hc'
  obtain ⟨t, ht1, ht2, ht⟩ := root_in P Q c.lo c.hi hle hsgn
  set E := sig t η with hE
  have hnear := sig_near η ht1 ht2
  have hE1 : 1 < E := by
    have : ((1 : ℚ) : ℝ) < ((sigQ c.lo η - rad η c.lo c.hi : ℚ) : ℝ) := by exact_mod_cast hηlo
    push_cast at this
    have := (abs_le.mp hnear).1
    linarith
  have hE2 : E ≤ ((c.E η : ℚ) : ℝ) := by
    have := (abs_le.mp hnear).2
    simp only [Cert.E]; push_cast; linarith
  have hs0 : sig t w ≠ 0 := by
    intro h0
    have := norm_split ht w
    rw [h0, zero_mul] at this
    rcases hw with h | h <;> rw [h] at this <;> simp at this <;> omega
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hs0) hE1
  set v := mul P Q w (zp P Q η ε (-n))
  have hsv : sig t v = sig t w * E ^ (-n) := by
    simp only [v]; rw [sig_mul ht, sig_zp ht h1]
  have hEpos : 0 < E := by linarith
  have hv1 : 1 ≤ |sig t v| := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    rw [le_mul_inv_iff₀ (zpow_pos hEpos _), one_mul]; exact hn1
  have hv2 : |sig t v| ≤ ((c.E η : ℚ) : ℝ) := by
    rw [hsv, abs_mul, abs_of_pos (zpow_pos hEpos _), zpow_neg]
    have : |sig t w| * (E ^ n)⁻¹ < E := by
      rw [mul_inv_lt_iff₀ (zpow_pos hEpos _), ← zpow_one_add₀ hEpos.ne', add_comm]; exact hn2
    linarith
  have hnv : nrm P Q v = N ∨ nrm P Q v = -N := by
    simp only [v]; rw [nrm_mul, nrm_zp P Q hnη hnε, mul_one]; exact hw
  have hmem := reduced_memN hc hbox ht1 ht2 ht v hnv hv1 hv2
  have hMw : Mx P Q w = Mx P Q v * ((uη P Q η ε h1 h2 ^ n : (Matrix (Fin 3) (Fin 3) ℤ)ˣ) : Matrix (Fin 3) (Fin 3) ℤ) := by
    simp only [v]
    rw [Mx_mul, Mx_zp P Q η ε h1 h2, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, mul_one]
  have e : Mx P Q w = Mx P Q (mul P Q v (zp P Q η ε n)) := by rw [Mx_mul, Mx_zp P Q η ε h1 h2]; exact hMw
  refine ⟨n, v, hmem, ?_⟩
  have c1 := Mx_col P Q w
  have c2 := Mx_col P Q (mul P Q v (zp P Q η ε n))
  rw [e] at c1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← c1.1, c2.1]
  · rw [← c1.2.1, c2.2.1]
  · rw [← c1.2.2, c2.2.2]

/-! ### Orbit congruences -/

/-- `g^M ≡ 1 (mod q)` and `q ∤ (γ g^r)₂` for every `r < M`. -/
def orbitB (P Q : ℤ) (γ g : Z3) (q M : ℕ) : Bool :=
  decide (0 < M) && RankOneZeros.oneModB P Q (pow P Q g M) q &&
    (List.range M).all fun r => decide (¬ (q : ℤ) ∣ (mul P Q γ (pow P Q g r)).2.2)

/-- **No zero of the `z²` coordinate on the forward orbit** `γ g^N`, `N ≥ 0`. -/
theorem orbit_ne {P Q : ℤ} {γ g : Z3} {q M : ℕ} (h : orbitB P Q γ g q M = true) (N : ℕ) :
    (mul P Q γ (pow P Q g N)).2.2 ≠ 0 := by
  simp only [orbitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hM, hone⟩, hr⟩ := h
  obtain ⟨Dq, hA⟩ := RankOneZeros.oneMod_of hone
  intro h0
  have hc : ∀ n, (mul P Q γ (pow P Q g n)).2.2 = (Mx P Q γ * Mx P Q g ^ n) 2 0 := fun n => by
    rw [← Mx_pow, ← Mx_mul, (Mx_col P Q _).2.2]
  obtain ⟨W, hW⟩ := SkolemP.one_add_pow q Dq (N / M)
  have e : Mx P Q g ^ N = (1 + q • W) * Mx P Q g ^ (N % M) := by
    rw [← hW, ← hA, ← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hc, e, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_apply,
    Matrix.mul_smul, smul_mul_assoc, Matrix.smul_apply, nsmul_eq_mul, ← hc] at h0
  exact hr (N % M) (Nat.mod_lt _ hM) ⟨-((Mx P Q γ * W * Mx P Q g ^ (N % M)) 2 0), by linarith⟩

/-- **No element of norm `±N` has `z²` coordinate `0`**, when every representative's orbit is
excluded by a congruence in both directions. -/
theorem no_corner_zero {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} {N : ℕ} {R0 : ℚ} {L : List Z3}
    (hc : condNB P Q η c N R0 = true) (hbox : slabNB P Q c N R0 L = true) (hN : 0 < N)
    {q M M' : ℕ} (hL : L.all (fun γ => orbitB P Q γ η q M && orbitB P Q γ ε q M') = true)
    (w : Z3) (hw : nrm P Q w = N ∨ nrm P Q w = -N) : w.2.2 ≠ 0 := by
  obtain ⟨n, γ, hγ, rfl⟩ := normN_eq h1 h2 hnη hnε hc hbox hN w hw
  simp only [List.all_eq_true, Bool.and_eq_true] at hL
  obtain ⟨hη, hε⟩ := hL γ hγ
  unfold zp
  split_ifs
  · exact orbit_ne hη _
  · exact orbit_ne hε _

end PerfectPower.RankOneNorm
