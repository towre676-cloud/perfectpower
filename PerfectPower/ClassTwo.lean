import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Combinatorics.Pigeonhole
import PerfectPower.Basic

/-!
# The class-group template for `y^2 = x^3 - D`, without ideals

For `D > 0` and `α = y + √-D` with `x^3 = y^2 + D`, the classical argument says: the ideal `I`
with `I^3 = (α)` is principal whenever the class number of `ℤ[√-D]` is prime to 3.  This file
makes that argument explicit for every `D`, as integer arithmetic, leaving only a finite,
kernel-decidable table to each instance.

1. *The ideal `I`* is the lattice `{(a, b) : x ∣ a - y b}` of index `x`.
2. *Minkowski's bound* (`short_relation`): Thue's pigeonhole lemma on the box
   `[0, A] × [0, B]` with `A = ⌊√(r x / t)⌋`, `B = ⌊√(t x / r)⌋` gives `v = (a, b) ≠ 0` in the
   lattice with `a^2 + D b^2 = k x`, where `1 ≤ k ≤ K` whenever `r^2 + D t^2 < (K + 1) r t`.
3. *`I^3 = (α)`*: `x^3` divides both coordinates of `α · conj(v)^3`, so
   `α · conj(v)^3 = x^3 β` with `N(β) = k^3` and `k^3 α = β v^3` (identities `Q2_eq`, `norm_id`,
   `idR`, `idI`, valid for all `D`).
4. *The class group* enters only through the table `TableOK D K P Q`: every solution of
   `p^2 + D q^2 = k^3` with `k ≤ K` has `q = 0` and `(k, p) = (1, ± 1)` or `(4, ± 8)`.  With
   `HalvesOK D` (a congruence mod 8 that halves `v` when `k = 4`), `cube_of_table` concludes
   that `α = (p + q √-D)^3`.

Instances: `MordellMinus5`, `MordellMinus6`, `MordellMinus13`.
-/

namespace PerfectPower.ClassTwo

/-- Coordinates of `(a - b√-D)^3 = W1 + W2 √-D`. -/
def W1 (D a b : ℤ) : ℤ := a ^ 3 - 3 * D * a * b ^ 2
/-- The `√-D` coordinate of `(a - b√-D)^3`. -/
def W2 (D a b : ℤ) : ℤ := D * b ^ 3 - 3 * a ^ 2 * b

/-- Coordinates of `(y + √-D) · (a - b√-D)^3 = Q1 + Q2 √-D`. -/
def Q1 (D y a b : ℤ) : ℤ := y * W1 D a b - D * W2 D a b
/-- The `√-D` coordinate of `(y + √-D) · (a - b√-D)^3`. -/
def Q2 (D y a b : ℤ) : ℤ := y * W2 D a b + W1 D a b

lemma Q2_eq (D y a b : ℤ) :
    Q2 D y a b = (a - y * b) ^ 3 - (y ^ 2 + D) * (3 * a * b ^ 2 - y * b ^ 3) := by
  simp only [Q2, W1, W2]; ring

lemma Q1_eq (D y a b : ℤ) : Q1 D y a b = y * Q2 D y a b - (y ^ 2 + D) * W2 D a b := by
  simp only [Q1, Q2]; ring

lemma norm_id (D y a b : ℤ) :
    Q1 D y a b ^ 2 + D * Q2 D y a b ^ 2 = (y ^ 2 + D) * (a ^ 2 + D * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

lemma idR (D y a b : ℤ) :
    Q1 D y a b * W1 D a b + D * Q2 D y a b * W2 D a b = y * (a ^ 2 + D * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

lemma idI (D y a b : ℤ) :
    Q2 D y a b * W1 D a b - Q1 D y a b * W2 D a b = (a ^ 2 + D * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_inj (⟨1, rfl⟩ : Odd 3)).mp h

/-- **Thue's lemma**: a short nonzero vector with `x ∣ a - t b`. -/
lemma exists_short (x t : ℤ) (hx : 0 < x) (A B : ℕ) (hAB : x < ((A + 1) * (B + 1) : ℕ)) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ A ∧ |b| ≤ B ∧ x ∣ a - t * b := by
  classical
  let S := Finset.range (A + 1) ×ˢ Finset.range (B + 1)
  let f : ℕ × ℕ → ℕ := fun p => (((p.1 : ℤ) - t * p.2) % x).toNat
  have hmaps : ∀ p ∈ S, f p ∈ Finset.range x.toNat := by
    intro p _
    simp only [Finset.mem_range, f]
    have h2 := Int.emod_lt_of_pos ((p.1 : ℤ) - t * p.2) hx
    generalize ((p.1 : ℤ) - t * p.2) % x = r at h2
    omega
  have hcard : (Finset.range x.toNat).card < S.card := by
    simp only [Finset.card_range, S, Finset.card_product]
    omega
  obtain ⟨p, hp, q, hq, hpq, hfpq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [S, Finset.mem_product, Finset.mem_range] at hp hq
  refine ⟨(p.1 : ℤ) - q.1, (p.2 : ℤ) - q.2, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact hpq (Prod.ext (by omega) (by omega))
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega
  · have e : ((p.1 : ℤ) - t * p.2) % x = ((q.1 : ℤ) - t * q.2) % x := by
      simp only [f] at hfpq
      have h1 := Int.emod_nonneg ((p.1 : ℤ) - t * p.2) hx.ne'
      have h2 := Int.emod_nonneg ((q.1 : ℤ) - t * q.2) hx.ne'
      generalize ((p.1 : ℤ) - t * p.2) % x = u at hfpq h1
      generalize ((q.1 : ℤ) - t * q.2) % x = w at hfpq h2
      omega
    have := Int.ModEq.dvd (Int.ModEq.symm e)
    convert this using 1
    ring

/-- The pigeonhole box `A = ⌊√(r n / t)⌋`, `B = ⌊√(t n / r)⌋` has more than `n` points and
satisfies `t A^2 ≤ r n`, `r B^2 ≤ t n`. -/
lemma box (r t n : ℕ) (hr : 0 < r) (ht : 0 < t) :
    t * (Nat.sqrt (r * n / t) * Nat.sqrt (r * n / t)) ≤ r * n ∧
    r * (Nat.sqrt (t * n / r) * Nat.sqrt (t * n / r)) ≤ t * n ∧
    n < (Nat.sqrt (r * n / t) + 1) * (Nat.sqrt (t * n / r) + 1) := by
  set A := Nat.sqrt (r * n / t)
  set B := Nat.sqrt (t * n / r)
  refine ⟨?_, ?_, ?_⟩
  · calc t * (A * A) ≤ t * (r * n / t) := Nat.mul_le_mul_left t (Nat.sqrt_le _)
      _ ≤ r * n := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  · calc r * (B * B) ≤ r * (t * n / r) := Nat.mul_le_mul_left r (Nat.sqrt_le _)
      _ ≤ t * n := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  · have h1 : r * n < (A + 1) * (A + 1) * t := (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_succ_sqrt _)
    have h2 : t * n < (B + 1) * (B + 1) * r := (Nat.div_lt_iff_lt_mul hr).mp (Nat.lt_succ_sqrt _)
    have h3 : (r * n) * (t * n) < ((A + 1) * (A + 1) * t) * ((B + 1) * (B + 1) * r) :=
      Nat.mul_lt_mul'' h1 h2
    have h4 : (r * t) * (n * n) < (r * t) * (((A + 1) * (B + 1)) * ((A + 1) * (B + 1))) := by
      calc (r * t) * (n * n) = (r * n) * (t * n) := by ring
        _ < _ := h3
        _ = _ := by ring
    exact Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_mul_lt_mul_left h4)

/-- **The Minkowski step, for every `D`.** -/
theorem short_relation (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K : ℤ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < (K + 1) * r * t) (x y : ℤ) (h : y ^ 2 + D = x ^ 3)
    (hx : 0 < x) :
    ∃ a b k e1 e2 : ℤ, 1 ≤ k ∧ k ≤ K ∧ e1 ^ 2 + D * e2 ^ 2 = k ^ 3 ∧
      k ^ 3 * y = e1 * W1 D a b + D * e2 * W2 D a b ∧ k ^ 3 = e2 * W1 D a b - e1 * W2 D a b := by
  set n := x.toNat
  have hn : (n : ℤ) = x := Int.toNat_of_nonneg hx.le
  obtain ⟨hA, hB, hAB⟩ := box r t n hr ht
  generalize Nat.sqrt (r * n / t) = A at hA hAB
  generalize Nat.sqrt (t * n / r) = B at hB hAB
  clear_value n
  obtain ⟨a, b, hne, ha, hb, hdiv⟩ := exists_short x y hx A B (by rw [← hn]; exact_mod_cast hAB)
  obtain ⟨m, hm⟩ := hdiv
  obtain ⟨k, hk⟩ : ∃ k, a ^ 2 + D * b ^ 2 = x * k :=
    ⟨m * (a + y * b) + b ^ 2 * x ^ 2, by linear_combination (a + y * b) * hm + b ^ 2 * h⟩
  have hpos : 0 < a ^ 2 + D * b ^ 2 := by
    rcases hne with h0 | h0
    · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; nlinarith [sq_nonneg b]
    · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; nlinarith [sq_nonneg a]
  have hk1 : 1 ≤ k := by
    by_contra hc; push_neg at hc; nlinarith
  have hkK : k ≤ K := by
    have hA' : (t : ℤ) * ((A : ℤ) * A) ≤ r * x := by rw [← hn]; exact_mod_cast hA
    have hB' : (r : ℤ) * ((B : ℤ) * B) ≤ t * x := by rw [← hn]; exact_mod_cast hB
    have ha2 : a ^ 2 ≤ (A : ℤ) * A := by
      rw [← sq_abs, ← sq]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hb2 : b ^ 2 ≤ (B : ℤ) * B := by
      rw [← sq_abs, ← sq]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
    have i1 : (r : ℤ) * (t * a ^ 2) ≤ r * (r * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    have i2 : D * t * (r * b ^ 2) ≤ D * t * (t * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    have i3 : ((r : ℤ) ^ 2 + D * (t : ℤ) ^ 2) * x < (K + 1) * r * t * x :=
      mul_lt_mul_of_pos_right hK hx
    have i4 : ((r : ℤ) * t * x) * k < ((r : ℤ) * t * x) * (K + 1) := by
      have : (r : ℤ) * t * (a ^ 2 + D * b ^ 2) < (K + 1) * r * t * x := by linarith
      rw [hk] at this; linarith
    have hrtx : 0 < (r : ℤ) * t * x := by positivity
    have := lt_of_mul_lt_mul_left i4 hrtx.le
    linarith
  -- `x^3` divides both coordinates of `α · conj(v)^3`
  have hQ2 : x ^ 3 ∣ Q2 D y a b := by
    rw [Q2_eq]
    refine dvd_sub (pow_dvd_pow_of_dvd ⟨m, hm⟩ 3) ?_
    rw [h]; exact dvd_mul_right _ _
  have hQ1 : x ^ 3 ∣ Q1 D y a b := by
    rw [Q1_eq]
    refine dvd_sub (dvd_mul_of_dvd_right hQ2 _) ?_
    rw [h]; exact dvd_mul_right _ _
  obtain ⟨e1, he1⟩ := hQ1
  obtain ⟨e2, he2⟩ := hQ2
  have hx3 : x ^ 3 ≠ 0 := by positivity
  refine ⟨a, b, k, e1, e2, hk1, hkK, ?_, ?_, ?_⟩
  · have hx6 : x ^ 6 ≠ 0 := by positivity
    apply mul_left_cancel₀ hx6
    linear_combination (-(Q1 D y a b + x ^ 3 * e1)) * he1 + (-D * (Q2 D y a b + x ^ 3 * e2)) * he2
      + norm_id D y a b + (a ^ 2 + D * b ^ 2) ^ 3 * h
      + x ^ 3 * ((a ^ 2 + D * b ^ 2) ^ 2 + (a ^ 2 + D * b ^ 2) * (x * k) + (x * k) ^ 2) * hk
  · apply mul_left_cancel₀ hx3
    linear_combination W1 D a b * he1 + D * W2 D a b * he2 - idR D y a b
      + (-y) * ((a ^ 2 + D * b ^ 2) ^ 2 + (a ^ 2 + D * b ^ 2) * (x * k) + (x * k) ^ 2) * hk
  · apply mul_left_cancel₀ hx3
    linear_combination W1 D a b * he2 - W2 D a b * he1 - idI D y a b
      + (-1) * ((a ^ 2 + D * b ^ 2) ^ 2 + (a ^ 2 + D * b ^ 2) * (x * k) + (x * k) ^ 2) * hk

/-- The finite class-group input: norms `k^3`, `k ≤ K`, are represented only trivially. -/
def TableOK (D K P Q : ℤ) : Prop :=
  ∀ k ∈ Finset.Icc (1 : ℤ) K, ∀ q ∈ Finset.Icc (-Q) Q, ∀ p ∈ Finset.Icc (-P) P,
    p ^ 2 + D * q ^ 2 = k ^ 3 → q = 0 ∧ ((k = 1 ∧ (p = 1 ∨ p = -1)) ∨ (k = 4 ∧ (p = 8 ∨ p = -8)))

/-- The halving input for `k = 4`. -/
def HalvesOK (D : ℤ) : Prop := ∀ a b : ℤ, 8 ∣ W1 D a b → 8 ∣ W2 D a b → 2 ∣ a ∧ 2 ∣ b

/-- `HalvesOK` from a check over residues mod 8. -/
lemma halvesOK_of_mod8 (D : ℤ)
    (key : ∀ A B : ZMod 8, A ^ 3 - 3 * (D : ZMod 8) * A * B ^ 2 = 0 →
      (D : ZMod 8) * B ^ 3 - 3 * A ^ 2 * B = 0 → 4 * A = 0 ∧ 4 * B = 0) : HalvesOK D := by
  intro a b h1 h2
  have c1 : ((W1 D a b : ℤ) : ZMod 8) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h1
  have c2 : ((W2 D a b : ℤ) : ZMod 8) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h2
  simp only [W1, W2] at c1 c2
  push_cast at c1 c2
  obtain ⟨k1, k2⟩ := key _ _ c1 c2
  have d1 : (8 : ℤ) ∣ 4 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact k1)
  have d2 : (8 : ℤ) ∣ 4 * b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact k2)
  omega

/-- **The template**: under the table and halving inputs, `y + √-D` is a cube. -/
theorem cube_of_table (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K P Q : ℤ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < (K + 1) * r * t)
    (hP : K ^ 3 < (P + 1) ^ 2) (hQ : K ^ 3 < D * (Q + 1) ^ 2) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (htable : TableOK D K P Q) (hhalf : HalvesOK D) (x y : ℤ) (h : y ^ 2 + D = x ^ 3) :
    ∃ p q : ℤ, y = p ^ 3 - 3 * D * p * q ^ 2 ∧ 1 = 3 * p ^ 2 * q - D * q ^ 3 := by
  have hx : 0 < x := by
    by_contra hc
    push_neg at hc
    have : x ^ 3 ≤ 0 := Odd.pow_nonpos (⟨1, rfl⟩ : Odd 3) hc
    nlinarith [sq_nonneg y]
  obtain ⟨a, b, k, e1, e2, hk1, hkK, hnorm, hre, him⟩ :=
    short_relation D hD r t hr ht K hK x y h hx
  have hk3 : k ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (by linarith) hkK 3
  have he2b : e2 ∈ Finset.Icc (-Q) Q := by
    have hq : D * e2 ^ 2 < D * (Q + 1) ^ 2 := by nlinarith [sq_nonneg e1]
    have := abs_lt_of_sq_lt_sq' (lt_of_mul_lt_mul_left hq hD.le) (by linarith)
    rw [Finset.mem_Icc]; constructor <;> linarith [this.1, this.2]
  have he1b : e1 ∈ Finset.Icc (-P) P := by
    have hp : e1 ^ 2 < (P + 1) ^ 2 := by nlinarith [sq_nonneg e2]
    have := abs_lt_of_sq_lt_sq' hp (by linarith)
    rw [Finset.mem_Icc]; constructor <;> linarith [this.1, this.2]
  obtain ⟨rfl, hcase⟩ := htable k (Finset.mem_Icc.mpr ⟨hk1, hkK⟩) e2 he2b e1 he1b hnorm
  have finish : ∀ a' b' ε : ℤ, (ε = 1 ∨ ε = -1) → y = ε * W1 D a' b' → 1 = -ε * W2 D a' b' →
      ∃ p q : ℤ, y = p ^ 3 - 3 * D * p * q ^ 2 ∧ 1 = 3 * p ^ 2 * q - D * q ^ 3 := by
    intro a' b' ε hε h1 h2
    rcases hε with rfl | rfl
    · exact ⟨a', b', by rw [h1, W1]; ring, by rw [h2, W2]; ring⟩
    · exact ⟨-a', -b', by rw [h1, W1]; ring, by rw [h2, W2]; ring⟩
  rcases hcase with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · rcases hp with rfl | rfl
    · norm_num at hre him
      exact finish a b 1 (Or.inl rfl) (by linarith) (by linarith)
    · norm_num at hre him
      exact finish a b (-1) (Or.inr rfl) (by linarith) (by linarith)
  · have h8 : 8 ∣ W1 D a b ∧ 8 ∣ W2 D a b := by
      rcases hp with rfl | rfl
      · norm_num at hre him
        exact ⟨⟨y, by linarith⟩, ⟨-1, by linarith⟩⟩
      · norm_num at hre him
        exact ⟨⟨-y, by linarith⟩, ⟨1, by linarith⟩⟩
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hhalf a b h8.1 h8.2
    have w1 : W1 D (2 * a') (2 * b') = 8 * W1 D a' b' := by simp only [W1]; ring
    have w2 : W2 D (2 * a') (2 * b') = 8 * W2 D a' b' := by simp only [W2]; ring
    rw [w1, w2] at hre him
    rcases hp with rfl | rfl
    · norm_num at hre him
      exact finish a' b' 1 (Or.inl rfl) (by linarith) (by linarith)
    · norm_num at hre him
      exact finish a' b' (-1) (Or.inr rfl) (by linarith) (by linarith)

end PerfectPower.ClassTwo
