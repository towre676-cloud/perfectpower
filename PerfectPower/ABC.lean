import Mathlib.RingTheory.Radical
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open UniqueFactorizationMonoid

namespace PerfectPower

/-! ### The abc-conditional layer

abc is **not** assumed as an axiom.  `ABC ε C` is an ordinary proposition, and every theorem
below takes it as an explicit hypothesis, so `#print axioms` stays at the standard three.  A
future proof or disproof of abc lands on these machine-checked implications.

We prove, for coprime bases:
* `hall_of_abc`: `x^(1 - 5ε) ≤ 2^(1+ε) C^2 K^(2+2ε)` whenever `0 < K = |x^3 - y^2| ≤ x^3`
  (Hall's conjecture `K ≫ x^(1/2 - ε')`, conditionally);
* `pillai_bound_of_abc` / `pillai_finite_of_abc`: for fixed `K`, the equation
  `x^a - y^b = ±K` with `1/a + 1/b < 1` has only finitely many solutions in all four unknowns
  (the abc-conditional form of Pillai's conjecture). -/

/-- The abc conjecture with explicit `ε` and constant `C`, for coprime positive `a + b = c`. -/
def ABC (ε C : ℝ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- `rad(x^m y^n K) ≤ x y K` for positive `m, n`. -/
lemma radical_pow_pow_le {x y K m n : ℕ} (hx : 0 < x) (hy : 0 < y) (hK : 0 < K)
    (hm : m ≠ 0) (hn : n ≠ 0) : radical (x ^ m * y ^ n * K) ≤ x * y * K := by
  have hdvd : radical (x ^ m * y ^ n * K) ∣ x * y * K := by
    calc radical (x ^ m * y ^ n * K) ∣ radical (x ^ m * y ^ n) * radical K := radical_mul_dvd
      _ ∣ radical (x ^ m) * radical (y ^ n) * radical K := mul_dvd_mul_right radical_mul_dvd _
      _ = radical x * radical y * radical K := by rw [radical_pow x hm, radical_pow y hn]
      _ ∣ x * y * K := mul_dvd_mul (mul_dvd_mul radical_dvd_self radical_dvd_self) radical_dvd_self
  exact Nat.le_of_dvd (by positivity) hdvd

/-- Core abc step: if `u + K = v` or `v + K = u` with `u = x^m`, `v = y^n` coprime, then
`max u v ≤ C (x y K)^(1+ε)`. -/
lemma abc_step {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 < C) (habc : ABC ε C) {x y m n K : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime x y) (hK : 0 < K)
    (h : x ^ m = y ^ n + K ∨ y ^ n = x ^ m + K) :
    ((max (x ^ m) (y ^ n) : ℕ) : ℝ) ≤ C * ((x : ℝ) * y * K) ^ (1 + ε) := by
  have hcop' : Nat.Coprime (x ^ m) (y ^ n) := Nat.Coprime.pow m n hcop
  have hmono : ∀ r : ℕ, r ≤ x * y * K → C * ((r : ℕ) : ℝ) ^ (1 + ε) ≤ C * ((x : ℝ) * y * K) ^ (1 + ε) :=
    fun r hr => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hr) (by linarith)) hC.le
  rcases h with h | h
  · -- y^n + K = x^m
    have hc : Nat.Coprime (y ^ n) K := by
      have := (Nat.coprime_sub_self_right (show y ^ n ≤ x ^ m by omega)).mpr hcop'.symm
      rwa [show x ^ m - y ^ n = K by omega] at this
    have hmax : max (x ^ m) (y ^ n) = x ^ m := max_eq_left (by omega)
    have hA := habc (y ^ n) K (x ^ m) (by positivity) hK h.symm hc
    have hr : radical (y ^ n * K * x ^ m) ≤ x * y * K := by
      rw [show y ^ n * K * x ^ m = x ^ m * y ^ n * K by ring]
      exact radical_pow_pow_le hx hy hK hm hn
    rw [hmax]; exact hA.trans (hmono _ hr)
  · -- x^m + K = y^n
    have hc : Nat.Coprime (x ^ m) K := by
      have := (Nat.coprime_sub_self_right (show x ^ m ≤ y ^ n by omega)).mpr hcop'
      rwa [show y ^ n - x ^ m = K by omega] at this
    have hmax : max (x ^ m) (y ^ n) = y ^ n := max_eq_right (by omega)
    have hA := habc (x ^ m) K (y ^ n) (by positivity) hK h.symm hc
    have hr : radical (x ^ m * K * y ^ n) ≤ x * y * K := by
      rw [show x ^ m * K * y ^ n = x ^ m * y ^ n * K by ring]
      exact radical_pow_pow_le hx hy hK hm hn
    rw [hmax]; exact hA.trans (hmono _ hr)

/-- **Hall's inequality from abc** (coprime case).  If `x, y` are coprime, `K = |x^3 - y^2| > 0`
and `K ≤ x^3`, then `x^(1 - 5ε) ≤ 2^(1+ε) · C^2 · K^(2 + 2ε)`; that is,
`K ≥ c(ε, C) · x^((1 - 5ε)/(2 + 2ε))`, which is `x^(1/2 - O(ε))`. -/
theorem hall_of_abc {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 < C) (habc : ABC ε C) {x y K : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hcop : Nat.Coprime x y) (hK : 0 < K)
    (h : x ^ 3 = y ^ 2 + K ∨ y ^ 2 = x ^ 3 + K) (hKx : K ≤ x ^ 3) :
    (x : ℝ) ^ (1 - 5 * ε) ≤ 2 ^ (1 + ε) * C ^ 2 * (K : ℝ) ^ (2 + 2 * ε) := by
  have core := abc_step hε hC habc hx hy (by norm_num) (by norm_num) hcop hK h
  have hx3 : ((x ^ 3 : ℕ) : ℝ) ≤ ((max (x ^ 3) (y ^ 2) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hy2 : (y : ℝ) ^ 2 ≤ 2 * (x : ℝ) ^ 3 := by
    have : y ^ 2 ≤ 2 * x ^ 3 := by omega
    exact_mod_cast this
  have xr : (0 : ℝ) < x := by exact_mod_cast hx
  have Kr : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 : 0 < 1 + ε := by linarith
  -- x^3 ≤ C (x y K)^(1+ε), squared:  x^6 ≤ C^2 (x^2 y^2 K^2)^(1+ε) ≤ C^2 (2 x^5 K^2)^(1+ε)
  have h3 : (x : ℝ) ^ 3 ≤ C * ((x : ℝ) * y * K) ^ (1 + ε) := by
    have := hx3.trans core; push_cast at this; exact this
  have hsq : ((x : ℝ) ^ 3) ^ 2 ≤ C ^ 2 * ((2 * (x : ℝ) ^ 5 * (K : ℝ) ^ 2)) ^ (1 + ε) := by
    have hA : ((x : ℝ) ^ 3) ^ 2 ≤ (C * ((x : ℝ) * y * K) ^ (1 + ε)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    have hB : (C * ((x : ℝ) * y * K) ^ (1 + ε)) ^ 2
        = C ^ 2 * (((x : ℝ) * y * K) ^ 2) ^ (1 + ε) := by
      rw [mul_pow, ← Real.rpow_natCast (((x : ℝ) * y * K) ^ (1 + ε)) 2,
        ← Real.rpow_mul (by positivity), mul_comm (1 + ε), Real.rpow_mul (by positivity),
        Real.rpow_natCast]
    have hC2 : ((x : ℝ) * y * K) ^ 2 ≤ 2 * (x : ℝ) ^ 5 * (K : ℝ) ^ 2 := by
      have : ((x : ℝ) * y * K) ^ 2 = (x : ℝ) ^ 2 * (y : ℝ) ^ 2 * (K : ℝ) ^ 2 := by ring
      rw [this]
      have hx2 : (0 : ℝ) ≤ (x : ℝ) ^ 2 * (K : ℝ) ^ 2 := by positivity
      nlinarith
    calc ((x : ℝ) ^ 3) ^ 2 ≤ C ^ 2 * (((x : ℝ) * y * K) ^ 2) ^ (1 + ε) := hA.trans hB.le
      _ ≤ C ^ 2 * ((2 * (x : ℝ) ^ 5 * (K : ℝ) ^ 2)) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hC2 e1.le) (by positivity)
  -- rewrite everything as real powers of x and K
  have lhs : ((x : ℝ) ^ 3) ^ 2 = (x : ℝ) ^ (1 - 5 * ε) * (x : ℝ) ^ (5 * (1 + ε)) := by
    rw [← Real.rpow_add xr, ← pow_mul, ← Real.rpow_natCast]; congr 1; push_cast; ring
  have rhs : (2 * (x : ℝ) ^ 5 * (K : ℝ) ^ 2) ^ (1 + ε)
      = 2 ^ (1 + ε) * (x : ℝ) ^ (5 * (1 + ε)) * (K : ℝ) ^ (2 + 2 * ε) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (x : ℝ) 5, ← Real.rpow_natCast (K : ℝ) 2, ← Real.rpow_mul xr.le,
      ← Real.rpow_mul Kr.le]
    congr 2
    push_cast; ring
  rw [lhs, rhs] at hsq
  have hpos : 0 < (x : ℝ) ^ (5 * (1 + ε)) := Real.rpow_pos_of_pos xr _
  have : (x : ℝ) ^ (1 - 5 * ε) * (x : ℝ) ^ (5 * (1 + ε))
      ≤ (2 ^ (1 + ε) * C ^ 2 * (K : ℝ) ^ (2 + 2 * ε)) * (x : ℝ) ^ (5 * (1 + ε)) := by
    calc _ ≤ C ^ 2 * (2 ^ (1 + ε) * (x : ℝ) ^ (5 * (1 + ε)) * (K : ℝ) ^ (2 + 2 * ε)) := hsq
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

/-- `1/a + 1/b ≤ 5/6` for exponents `a, b ≥ 2` other than `(2, 2)`. -/
lemma inv_add_inv_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : ¬ (a = 2 ∧ b = 2)) :
    (1 : ℝ) / a + 1 / b ≤ 5 / 6 := by
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have i1 : (1 : ℝ) / a ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have i2 : (1 : ℝ) / b ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  by_cases h3 : 3 ≤ a
  · have : (1 : ℝ) / a ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; exact_mod_cast (by omega : 1 * 3 ≤ 1 * a)
    linarith
  · have hb3 : 3 ≤ b := by omega
    have : (1 : ℝ) / b ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; exact_mod_cast (by omega : 1 * 3 ≤ 1 * b)
    linarith

/-- **Pillai from abc, quantitative.**  For coprime `x, y ≥ 2`, exponents `a, b ≥ 2` with
`(a, b) ≠ (2, 2)` and `x^a - y^b = ±K ≠ 0`, the height `Z = max(x^a, y^b)` satisfies
`Z^(1 - 5(1+ε)/6) ≤ C K^(1+ε)`. -/
theorem pillai_bound_of_abc {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 < C) (habc : ABC ε C)
    {x y a b K : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ¬ (a = 2 ∧ b = 2)) (hcop : Nat.Coprime x y) (hK : 0 < K)
    (h : x ^ a = y ^ b + K ∨ y ^ b = x ^ a + K) :
    ((max (x ^ a) (y ^ b) : ℕ) : ℝ) ^ (1 - 5 / 6 * (1 + ε)) ≤ C * (K : ℝ) ^ (1 + ε) := by
  set Z : ℝ := ((max (x ^ a) (y ^ b) : ℕ) : ℝ) with hZ
  have core := abc_step hε hC habc (by omega) (by omega) (by omega) (by omega) hcop hK h
  rw [← hZ] at core
  have Z1 : (1 : ℝ) ≤ Z := by
    have : 1 ≤ max (x ^ a) (y ^ b) := le_max_of_le_left (Nat.one_le_pow _ _ (by omega))
    rw [hZ]; exact_mod_cast this
  have Z0 : (0 : ℝ) < Z := by linarith
  have ax : (a : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ a := by exact_mod_cast ha
                              linarith
  have bx : (b : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ b := by exact_mod_cast hb
                              linarith
  -- x ≤ Z^(1/a), y ≤ Z^(1/b)
  have hxZ : (x : ℝ) ≤ Z ^ ((1 : ℝ) / a) := by
    have e : (x : ℝ) = ((x : ℝ) ^ a) ^ ((1 : ℝ) / a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel ax,
        Real.rpow_one]
    rw [e]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : x ^ a ≤ max (x ^ a) (y ^ b) := le_max_left _ _
    rw [hZ]; exact_mod_cast this
  have hyZ : (y : ℝ) ≤ Z ^ ((1 : ℝ) / b) := by
    have e : (y : ℝ) = ((y : ℝ) ^ b) ^ ((1 : ℝ) / b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel bx,
        Real.rpow_one]
    rw [e]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : y ^ b ≤ max (x ^ a) (y ^ b) := le_max_right _ _
    rw [hZ]; exact_mod_cast this
  have hxy : (x : ℝ) * y ≤ Z ^ ((5 : ℝ) / 6) := by
    calc (x : ℝ) * y ≤ Z ^ ((1 : ℝ) / a) * Z ^ ((1 : ℝ) / b) :=
          mul_le_mul hxZ hyZ (Nat.cast_nonneg _) (by positivity)
      _ = Z ^ ((1 : ℝ) / a + 1 / b) := (Real.rpow_add Z0 _ _).symm
      _ ≤ Z ^ ((5 : ℝ) / 6) := Real.rpow_le_rpow_of_exponent_le Z1 (inv_add_inv_le ha hb hab)
  have e1 : 0 < 1 + ε := by linarith
  have Kr : (0 : ℝ) < K := by exact_mod_cast hK
  have step : Z ≤ C * (Z ^ ((5 : ℝ) / 6 * (1 + ε)) * (K : ℝ) ^ (1 + ε)) := by
    calc Z ≤ C * ((x : ℝ) * y * K) ^ (1 + ε) := core
      _ ≤ C * (Z ^ ((5 : ℝ) / 6) * K) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_right hxy Kr.le) e1.le) hC.le
      _ = C * (Z ^ ((5 : ℝ) / 6 * (1 + ε)) * (K : ℝ) ^ (1 + ε)) := by
          rw [Real.mul_rpow (by positivity) Kr.le, ← Real.rpow_mul Z0.le]
  have hpos : 0 < Z ^ ((5 : ℝ) / 6 * (1 + ε)) := Real.rpow_pos_of_pos Z0 _
  have split : Z = Z ^ (1 - 5 / 6 * (1 + ε)) * Z ^ ((5 : ℝ) / 6 * (1 + ε)) := by
    rw [← Real.rpow_add Z0]; norm_num
  have : Z ^ (1 - 5 / 6 * (1 + ε)) * Z ^ ((5 : ℝ) / 6 * (1 + ε))
      ≤ (C * (K : ℝ) ^ (1 + ε)) * Z ^ ((5 : ℝ) / 6 * (1 + ε)) := by
    rw [← split]; linarith [step]
  exact le_of_mul_le_mul_right this hpos

/-- **Pillai's conjecture from abc** (coprime bases).  If `ABC ε C` holds for some `ε < 1/5`, then for
each fixed `K > 0` there are only finitely many `(x, y, a, b)` with `x, y ≥ 2` coprime, `a, b ≥ 2`,
`(a, b) ≠ (2, 2)` and `x^a - y^b = ±K` — uniformly over all exponents. -/
theorem pillai_finite_of_abc {ε C : ℝ} (hε : 0 ≤ ε) (hε5 : ε < 1 / 5) (hC : 0 < C)
    (habc : ABC ε C) {K : ℕ} (hK : 0 < K) :
    {s : ℕ × ℕ × ℕ × ℕ | 2 ≤ s.1 ∧ 2 ≤ s.2.1 ∧ 2 ≤ s.2.2.1 ∧ 2 ≤ s.2.2.2 ∧
      ¬ (s.2.2.1 = 2 ∧ s.2.2.2 = 2) ∧ Nat.Coprime s.1 s.2.1 ∧
      (s.1 ^ s.2.2.1 = s.2.1 ^ s.2.2.2 + K ∨ s.2.1 ^ s.2.2.2 = s.1 ^ s.2.2.1 + K)}.Finite := by
  set e : ℝ := 1 - 5 / 6 * (1 + ε) with he
  have he0 : 0 < e := by rw [he]; linarith
  set M : ℝ := (C * (K : ℝ) ^ (1 + ε)) ^ (1 / e)
  set N : ℕ := ⌈M⌉₊
  -- every coordinate is at most N
  have hbound : ∀ x y a b : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ a → 2 ≤ b → ¬ (a = 2 ∧ b = 2) →
      Nat.Coprime x y → (x ^ a = y ^ b + K ∨ y ^ b = x ^ a + K) → max (x ^ a) (y ^ b) ≤ N := by
    intro x y a b hx hy ha hb hab hcop h
    have hZ := pillai_bound_of_abc hε hC habc hx hy ha hb hab hcop hK h
    set Z : ℝ := ((max (x ^ a) (y ^ b) : ℕ) : ℝ)
    have Z0 : 0 ≤ Z := Nat.cast_nonneg _
    have hZM : Z ≤ M := by
      have : Z = (Z ^ e) ^ (1 / e) := by
        rw [← Real.rpow_mul Z0, mul_one_div_cancel he0.ne', Real.rpow_one]
      rw [this]
      exact Real.rpow_le_rpow (Real.rpow_nonneg Z0 _) hZ (by positivity)
    have : ((max (x ^ a) (y ^ b) : ℕ) : ℝ) ≤ (N : ℝ) := hZM.trans (Nat.le_ceil M)
    exact_mod_cast this
  refine ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod
    ((Set.finite_Iic N).prod (Set.finite_Iic N)))).subset ?_
  rintro ⟨x, y, a, b⟩ hs
  simp only [Set.mem_setOf_eq] at hs
  obtain ⟨hx, hy, ha, hb, hab, hcop, h⟩ := hs
  have hm := hbound x y a b hx hy ha hb hab hcop h
  have hxa : x ^ a ≤ N := le_trans (le_max_left _ _) hm
  have hyb : y ^ b ≤ N := le_trans (le_max_right _ _) hm
  have h1 : x ≤ x ^ a := Nat.le_self_pow (by omega) x
  have h2 : y ≤ y ^ b := Nat.le_self_pow (by omega) y
  have h3 : a ≤ x ^ a := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hx a)
  have h4 : b ≤ y ^ b := le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hy b)
  simp only [Set.mem_prod, Set.mem_Iic]
  omega

end PerfectPower
