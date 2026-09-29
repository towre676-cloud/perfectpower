import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Combinatorics.Pigeonhole
import PerfectPower.Basic

/-!
# Class number two: the integral points of `y^2 = x^3 - 13`

`y^2 = x^3 - 13` has rank one and its integral points are `(17, ± 70)`.  The ring `ℤ[√-13]` has
class number 2, so the elementary descent of `MordellMinus2` (unique factorisation) does not apply:
the classical proof (Baanen–Best–Coppola–Dahmen formalised it in Lean 3) shows that the ideal `I`
with `I^3 = (y + √-13)` is principal because the class group has order 2, prime to 3.

Here that argument is made **explicit and ideal-free**; everything is integer arithmetic.
Write `α = y + √-13`, `x^3 = y^2 + 13`.

1. *The ideal `I` above `x`* is the lattice `{(a, b) : x ∣ a - y b}` of index `x`.
2. *Minkowski's bound* is a pigeonhole (Thue) argument (`exists_short`): the lattice has a
   vector `v = (a, b) ≠ 0` with `a^2 + 13 b^2 = k x` and `1 ≤ k ≤ 8`.
3. *`I^3 = (α)`* becomes: `x^3` divides both coordinates of `α · conj(v)^3`, by the identity
   `ψ(z^3) ≡ ψ(z)^3 (mod y^2 + 13)` for `ψ(z) = z.re + y z.im` and `x ∣ ψ(conj v)`.
   So `α · conj(v)^3 = x^3 β` with `N(β) = k^3`, and `k^3 α = β v^3`.
4. *The class group has order 2* becomes a finite table (`norm_table`): `p^2 + 13 q^2 = k^3`
   with `1 ≤ k ≤ 8` forces `q = 0` and `(k, p) = (1, ± 1)` or `(4, ± 8)`; the norms
   `8, 27, 125, 216, 343, 512` (the non-principal class) are not represented.
   For `k = 4` a congruence mod 8 halves `v`.  Either way `α` is a cube `(p + q√-13)^3`.
5. The `√-13`-coefficient gives `q (3p^2 - 13 q^2) = 1`, so `y = ∓ 70`, `x = 17`.

Small `x` (`x ≤ 35`, where the pigeonhole bound is too weak) are checked by kernel evaluation.
-/

namespace PerfectPower.MordellMinus13

/-- Coordinates of `(a - b√-13)^3 = W1 + W2 √-13`. -/
def W1 (a b : ℤ) : ℤ := a ^ 3 - 39 * a * b ^ 2
def W2 (a b : ℤ) : ℤ := 13 * b ^ 3 - 3 * a ^ 2 * b

/-- Coordinates of `α · (a - b√-13)^3 = Q1 + Q2 √-13`, `α = y + √-13`. -/
def Q1 (y a b : ℤ) : ℤ := y * W1 a b - 13 * W2 a b
def Q2 (y a b : ℤ) : ℤ := y * W2 a b + W1 a b

lemma Q2_eq (y a b : ℤ) :
    Q2 y a b = (a - y * b) ^ 3 - (y ^ 2 + 13) * (3 * a * b ^ 2 - y * b ^ 3) := by
  simp only [Q2, W1, W2]; ring

lemma Q1_eq (y a b : ℤ) : Q1 y a b = y * Q2 y a b - (y ^ 2 + 13) * W2 a b := by
  simp only [Q1, Q2]; ring

/-- Norm multiplicativity for `α · conj(v)^3`. -/
lemma norm_id (y a b : ℤ) :
    Q1 y a b ^ 2 + 13 * Q2 y a b ^ 2 = (y ^ 2 + 13) * (a ^ 2 + 13 * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

/-- `α · conj(v)^3 · v^3 = α · N(v)^3`, real part. -/
lemma idR (y a b : ℤ) :
    Q1 y a b * W1 a b + 13 * Q2 y a b * W2 a b = y * (a ^ 2 + 13 * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

/-- `α · conj(v)^3 · v^3 = α · N(v)^3`, `√-13` part. -/
lemma idI (y a b : ℤ) :
    Q2 y a b * W1 a b - Q1 y a b * W2 a b = (a ^ 2 + 13 * b ^ 2) ^ 3 := by
  simp only [Q1, Q2, W1, W2]; ring

/-- **Thue's lemma** (the Minkowski step): a short nonzero vector with `x ∣ a - t b`. -/
lemma exists_short (x t : ℤ) (hx : 0 < x) (A B : ℕ) (hAB : x < ((A + 1) * (B + 1) : ℕ)) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ A ∧ |b| ≤ B ∧ x ∣ a - t * b := by
  classical
  let S := Finset.range (A + 1) ×ˢ Finset.range (B + 1)
  let f : ℕ × ℕ → ℕ := fun p => (((p.1 : ℤ) - t * p.2) % x).toNat
  have hmaps : ∀ p ∈ S, f p ∈ Finset.range x.toNat := by
    intro p _
    simp only [Finset.mem_range, f]
    have h1 := Int.emod_nonneg ((p.1 : ℤ) - t * p.2) hx.ne'
    have h2 := Int.emod_lt_of_pos ((p.1 : ℤ) - t * p.2) hx
    generalize ((p.1 : ℤ) - t * p.2) % x = r at h1 h2
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

/-- **The class-number-two table.** -/
lemma norm_table : ∀ k ∈ Finset.Icc (1 : ℤ) 8, ∀ q ∈ Finset.Icc (-6 : ℤ) 6,
    ∀ p ∈ Finset.Icc (-23 : ℤ) 23, p ^ 2 + 13 * q ^ 2 = k ^ 3 →
      q = 0 ∧ ((k = 1 ∧ (p = 1 ∨ p = -1)) ∨ (k = 4 ∧ (p = 8 ∨ p = -8))) := by
  decide +kernel

/-- For `k = 4`: if `8` divides both coordinates of `(a - b√-13)^3`, then `2 ∣ a` and `2 ∣ b`. -/
lemma two_dvd_of_eight_dvd (a b : ℤ) (h1 : 8 ∣ W1 a b) (h2 : 8 ∣ W2 a b) : 2 ∣ a ∧ 2 ∣ b := by
  have key : ∀ A B : ZMod 8, A ^ 3 - 39 * A * B ^ 2 = 0 → 13 * B ^ 3 - 3 * A ^ 2 * B = 0 →
      4 * A = 0 ∧ 4 * B = 0 := by decide
  have c1 : ((W1 a b : ℤ) : ZMod 8) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h1
  have c2 : ((W2 a b : ℤ) : ZMod 8) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h2
  simp only [W1, W2] at c1 c2
  push_cast at c1 c2
  obtain ⟨k1, k2⟩ := key _ _ c1 c2
  have d1 : (8 : ℤ) ∣ 4 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact k1)
  have d2 : (8 : ℤ) ∣ 4 * b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact k2)
  omega

/-- **The cube root**, for `x ≥ 36`: `y + √-13 = (p + q√-13)^3` for some integers `p, q`. -/
theorem cube_root (x y : ℤ) (h : y ^ 2 + 13 = x ^ 3) (hx : 36 ≤ x) :
    ∃ p q : ℤ, y = p ^ 3 - 39 * p * q ^ 2 ∧ 1 = 3 * p ^ 2 * q - 13 * q ^ 3 := by
  -- 1–2. a short vector in the lattice of `I`
  set n := x.toNat
  set s := Nat.sqrt n
  have hn : (n : ℤ) = x := Int.toNat_of_nonneg (by linarith)
  have hn36 : 36 ≤ n := by omega
  have hs1 : s * s ≤ n := Nat.sqrt_le n
  have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs6 : 6 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hcount : n < (2 * s + 1 + 1) * (s / 2 + 1) := by
    have : s + 1 ≤ 2 * (s / 2 + 1) := by omega
    nlinarith
  obtain ⟨a, b, hne, ha, hb, hdiv⟩ :=
    exists_short x y (by linarith) (2 * s + 1) (s / 2) (by rw [← hn]; exact_mod_cast hcount)
  obtain ⟨m, hm⟩ := hdiv
  set k := m * (a + y * b) + b ^ 2 * x ^ 2 with hkdef
  have hk : a ^ 2 + 13 * b ^ 2 = x * k := by
    rw [hkdef]; linear_combination (a + y * b) * hm + b ^ 2 * h
  clear_value k
  have hx0 : 0 < x := by linarith
  have hpos : 0 < a ^ 2 + 13 * b ^ 2 := by
    rcases hne with h0 | h0
    · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; nlinarith [sq_nonneg b]
    · have := pow_pos (abs_pos.mpr h0) 2; rw [sq_abs] at this; nlinarith [sq_nonneg a]
  have hk1 : 1 ≤ k := by
    by_contra hc; push_neg at hc; nlinarith
  have hk8 : k ≤ 8 := by
    have hS : ((s : ℕ) : ℤ) * s ≤ x := by rw [← hn]; exact_mod_cast hs1
    have hS6 : (6 : ℤ) ≤ s := by exact_mod_cast hs6
    have hB : 2 * ((s / 2 : ℕ) : ℤ) ≤ s := by exact_mod_cast (show 2 * (s / 2) ≤ s by omega)
    have hB0 : (0 : ℤ) ≤ ((s / 2 : ℕ) : ℤ) := by positivity
    have ha' : |a| ≤ 2 * (s : ℤ) + 1 := by push_cast at ha; exact ha
    have ha2 : a ^ 2 ≤ (2 * (s : ℤ) + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha' 2
    have hb2 : b ^ 2 ≤ ((s / 2 : ℕ) : ℤ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
    have h4b : 4 * b ^ 2 ≤ (s : ℤ) ^ 2 := by
      have h1 : (2 * ((s / 2 : ℕ) : ℤ)) ^ 2 ≤ (s : ℤ) ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
      have h2 : (2 * ((s / 2 : ℕ) : ℤ)) ^ 2 = 4 * ((s / 2 : ℕ) : ℤ) ^ 2 := by ring
      rw [h2] at h1
      linarith only [h1, hb2]
    have ha2' : a ^ 2 ≤ 4 * (s : ℤ) ^ 2 + 4 * s + 1 := by linear_combination ha2
    have hS' : (s : ℤ) ^ 2 ≤ x := by linear_combination hS
    have e16 : 16 * (s : ℤ) + 4 ≤ 3 * (s : ℤ) ^ 2 := by
      have hm6 := mul_nonneg (by linarith : (0 : ℤ) ≤ (s : ℤ) - 6) (by linarith : (0 : ℤ) ≤ 3 * (s : ℤ) + 2)
      have hexp : ((s : ℤ) - 6) * (3 * (s : ℤ) + 2) = 3 * (s : ℤ) ^ 2 - 16 * s - 12 := by ring
      rw [hexp] at hm6
      linarith only [hm6]
    have hsum : x * k ≤ x * 8 := by rw [← hk]; linarith only [ha2', h4b, e16, hS']
    exact le_of_mul_le_mul_left hsum hx0
  -- 3. `x^3` divides both coordinates of `α · conj(v)^3`
  have hQ2 : x ^ 3 ∣ Q2 y a b := by
    rw [Q2_eq]
    refine dvd_sub (pow_dvd_pow_of_dvd ⟨m, hm⟩ 3) ?_
    rw [h]; exact dvd_mul_right _ _
  have hQ1 : x ^ 3 ∣ Q1 y a b := by
    rw [Q1_eq]
    refine dvd_sub (dvd_mul_of_dvd_right hQ2 _) ?_
    rw [h]; exact dvd_mul_right _ _
  obtain ⟨e1, he1⟩ := hQ1
  obtain ⟨e2, he2⟩ := hQ2
  have hx3 : x ^ 3 ≠ 0 := by positivity
  -- `N(β) = k^3`
  have hnorm : e1 ^ 2 + 13 * e2 ^ 2 = k ^ 3 := by
    have hx6 : x ^ 6 ≠ 0 := by positivity
    apply mul_left_cancel₀ hx6
    linear_combination (-(Q1 y a b + x ^ 3 * e1)) * he1 + (-13 * (Q2 y a b + x ^ 3 * e2)) * he2
      + norm_id y a b + (a ^ 2 + 13 * b ^ 2) ^ 3 * h
      + x ^ 3 * ((a ^ 2 + 13 * b ^ 2) ^ 2 + (a ^ 2 + 13 * b ^ 2) * (x * k) + (x * k) ^ 2) * hk
  -- `k^3 α = β v^3`, coordinatewise
  have hre : k ^ 3 * y = e1 * W1 a b + 13 * e2 * W2 a b := by
    apply mul_left_cancel₀ hx3
    linear_combination W1 a b * he1 + 13 * W2 a b * he2 - idR y a b
      + (-y) * ((a ^ 2 + 13 * b ^ 2) ^ 2 + (a ^ 2 + 13 * b ^ 2) * (x * k) + (x * k) ^ 2) * hk
  have him : k ^ 3 = e2 * W1 a b - e1 * W2 a b := by
    apply mul_left_cancel₀ hx3
    linear_combination W1 a b * he2 - W2 a b * he1 - idI y a b
      + (-1) * ((a ^ 2 + 13 * b ^ 2) ^ 2 + (a ^ 2 + 13 * b ^ 2) * (x * k) + (x * k) ^ 2) * hk
  -- 4. the table
  have hk3 : k ^ 3 ≤ 8 ^ 3 := pow_le_pow_left₀ (by linarith) hk8 3
  have he2b : e2 ∈ Finset.Icc (-6 : ℤ) 6 := by
    have h7 : e2 ^ 2 < 7 ^ 2 := by linarith only [hnorm, sq_nonneg e1, hk3]
    have := abs_lt_of_sq_lt_sq' h7 (by norm_num)
    rw [Finset.mem_Icc]; constructor <;> linarith only [this.1, this.2]
  have he1b : e1 ∈ Finset.Icc (-23 : ℤ) 23 := by
    have h24 : e1 ^ 2 < 24 ^ 2 := by linarith only [hnorm, sq_nonneg e2, hk3]
    have := abs_lt_of_sq_lt_sq' h24 (by norm_num)
    rw [Finset.mem_Icc]; constructor <;> linarith only [this.1, this.2]
  have hkb : k ∈ Finset.Icc (1 : ℤ) 8 := Finset.mem_Icc.mpr ⟨hk1, hk8⟩
  obtain ⟨rfl, hcase⟩ := norm_table k hkb e2 he2b e1 he1b hnorm
  -- from `y = ε W1(a', b')`, `1 = -ε W2(a', b')` to a cube root
  have finish : ∀ a' b' ε : ℤ, (ε = 1 ∨ ε = -1) → y = ε * W1 a' b' → 1 = -ε * W2 a' b' →
      ∃ p q : ℤ, y = p ^ 3 - 39 * p * q ^ 2 ∧ 1 = 3 * p ^ 2 * q - 13 * q ^ 3 := by
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
  · -- `k = 4`: halve `v`
    have h8 : 8 ∣ W1 a b ∧ 8 ∣ W2 a b := by
      rcases hp with rfl | rfl
      · norm_num at hre him
        exact ⟨⟨y, by linarith⟩, ⟨-1, by linarith⟩⟩
      · norm_num at hre him
        exact ⟨⟨-y, by linarith⟩, ⟨1, by linarith⟩⟩
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := two_dvd_of_eight_dvd a b h8.1 h8.2
    have w1 : W1 (2 * a') (2 * b') = 8 * W1 a' b' := by simp only [W1]; ring
    have w2 : W2 (2 * a') (2 * b') = 8 * W2 a' b' := by simp only [W2]; ring
    rw [w1, w2] at hre him
    rcases hp with rfl | rfl
    · norm_num at hre him
      exact finish a' b' 1 (Or.inl rfl) (by linarith) (by linarith)
    · norm_num at hre him
      exact finish a' b' (-1) (Or.inr rfl) (by linarith) (by linarith)

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_inj (⟨1, rfl⟩ : Odd 3)).mp h

/-- 5. The Thue step. -/
lemma thue (y p q : ℤ) (hy : y = p ^ 3 - 39 * p * q ^ 2) (h1 : 1 = 3 * p ^ 2 * q - 13 * q ^ 3) :
    y = 70 ∨ y = -70 := by
  have hq : q * (3 * p ^ 2 - 13 * q ^ 2) = 1 := by linear_combination -h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hq with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · exfalso
    have h3 : 3 * p ^ 2 = 14 := by linarith
    generalize p ^ 2 = t at h3
    omega
  · have hp2 : p ^ 2 = 4 := by nlinarith
    have : (p - 2) * (p + 2) = 0 := by linear_combination hp2
    rcases mul_eq_zero.mp this with hp | hp
    · have : p = 2 := by linarith
      subst this; right; linarith
    · have : p = -2 := by linarith
      subst this; left; linarith

/-- Small `x`, by kernel evaluation. -/
lemma small_table : ∀ x ∈ Finset.Icc (1 : ℤ) 35, ∀ y ∈ Finset.Icc (-216 : ℤ) 216,
    y ^ 2 + 13 = x ^ 3 → x = 17 ∧ (y = 70 ∨ y = -70) := by
  decide +kernel

/-- **The integral points of `y^2 = x^3 - 13` are `(17, ± 70)`.** -/
theorem points (x y : ℤ) : y ^ 2 = x ^ 3 - 13 ↔ x = 17 ∧ (y = 70 ∨ y = -70) := by
  constructor
  swap
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num
  intro h
  have h' : y ^ 2 + 13 = x ^ 3 := by linarith
  have hxpos : 1 ≤ x := by
    by_contra hc
    push_neg at hc
    have : x ^ 3 ≤ 0 := Odd.pow_nonpos (⟨1, rfl⟩ : Odd 3) (by linarith)
    nlinarith [sq_nonneg y]
  by_cases hx : x ≤ 35
  · have hy : y ∈ Finset.Icc (-216 : ℤ) 216 := by
      have : x ^ 3 ≤ 35 ^ 3 := pow_le_pow_left₀ (by linarith) hx 3
      rw [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg (y + 216), sq_nonneg (y - 216)]
    exact small_table x (Finset.mem_Icc.mpr ⟨hxpos, hx⟩) y hy h'
  · push_neg at hx
    obtain ⟨p, q, hp, hq⟩ := cube_root x y h' (by linarith)
    have hy := thue y p q hp hq
    refine ⟨cube_inj ?_, hy⟩
    rcases hy with rfl | rfl <;> linarith

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 13` is a perfect square iff `n = 17`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 13) ↔ n = 17 := by
  constructor
  · rintro ⟨m, hm⟩
    have := ((points n m).mp hm.symm).1
    exact_mod_cast this
  · rintro rfl
    exact ⟨70, by norm_num⟩

end PerfectPower.MordellMinus13
