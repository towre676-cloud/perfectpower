import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace PerfectPower.CoefficientPowerCharts

/-- The exact prime-exponent balance behind every nonzero coefficient chart. -/
theorem valuation_balance (c d x y p q l : ℕ)
    (hc : c ≠ 0) (hd : d ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : c * x ^ p = d * y ^ q) :
    c.factorization l + p * x.factorization l =
      d.factorization l + q * y.factorization l := by
  have he := congrArg (fun n : ℕ => n.factorization l) h
  simpa only [Nat.factorization_mul hc (pow_ne_zero _ hx),
    Nat.factorization_mul hd (pow_ne_zero _ hy),Nat.factorization_pow,
    Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] using he

/-- The gcd divisibility obstruction is necessary; zero points are excluded
explicitly from the valuation premise. -/
theorem valuation_gcd (c d x y p q l : ℕ)
    (hc : c ≠ 0) (hd : d ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : c * x ^ p = d * y ^ q) :
    (p.gcd q : ℤ) ∣ (d.factorization l : ℤ) - c.factorization l := by
  have he : (c.factorization l : ℤ) + p * x.factorization l =
      (d.factorization l : ℤ) + q * y.factorization l := by
    exact_mod_cast valuation_balance c d x y p q l hc hd hx hy h
  have hp : (p.gcd q : ℤ) ∣ (p : ℤ) := by exact_mod_cast Nat.gcd_dvd_left p q
  have hq : (p.gcd q : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_right p q
  have hg := dvd_sub (dvd_mul_of_dvd_left hp (x.factorization l : ℤ))
    (dvd_mul_of_dvd_left hq (y.factorization l : ℤ))
  convert hg using 1
  linarith

/-- Bézout gives the entire integer line of exponent solutions. -/
theorem exponent_line (p q : ℕ) (hcop : Nat.Coprime p q)
    (u v u₀ v₀ : ℤ) (h : (p : ℤ) * (u-u₀) = (q : ℤ) * (v-v₀)) :
    ∃ k : ℤ, u = u₀ + q*k ∧ v = v₀ + p*k := by
  have hb := Nat.gcd_eq_gcd_ab p q
  rw [hcop.gcd_eq_one] at hb
  let k := Nat.gcdA p q * (v-v₀) + Nat.gcdB p q * (u-u₀)
  refine ⟨k,?_,?_⟩
  · dsimp [k]
    linear_combination (u-u₀)*hb + Nat.gcdA p q*h
  · dsimp [k]
    linear_combination (v-v₀)*hb - Nat.gcdB p q*h

/-- The primitive row condition forces the free prime exponent nonnegative. -/
theorem primitive_row (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (u v u₀ v₀ : ℤ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hprimitive : u₀ < q ∨ v₀ < p)
    (h : (p : ℤ) * (u-u₀) = (q : ℤ) * (v-v₀)) :
    ∃ k : ℕ, u = u₀ + q*k ∧ v = v₀ + p*k := by
  obtain ⟨k,hku,hkv⟩ := exponent_line p q hcop u v u₀ v₀ h
  have hk : 0 ≤ k := by
    by_contra hh
    have hk' : k ≤ -1 := by omega
    rcases hprimitive with h | h
    · have hq' : (0 : ℤ) < q := by exact_mod_cast hq
      nlinarith
    · have hp' : (0 : ℤ) < p := by exact_mod_cast hp
      nlinarith
  exact ⟨k.toNat,by simpa [Int.toNat_of_nonneg hk] using hku,
    by simpa [Int.toNat_of_nonneg hk] using hkv⟩

/-- Coefficient/scaling identity produces only points of the original equation. -/
theorem chart_sound (c d α β t : ℤ) (p q : ℕ)
    (h : c * α ^ p = d * β ^ q) :
    c * (α * t ^ q) ^ p = d * (β * t ^ p) ^ q := by
  rw [mul_pow,mul_pow,← mul_assoc,← mul_assoc,h,← pow_mul,← pow_mul]
  simp only [Nat.mul_comm]

/-- A reusable completeness theorem for coprime coefficient-bearing powers.
The primitive certificate rules out fractional parameters via denominator powers. -/
theorem coprime_complete (c d α β : ℤ) (p q : ℕ)
    (hc : c ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (_hp : p ≠ 0) (_hq : q ≠ 0)
    (hcop : Nat.Coprime p q) (scale : c * α ^ p = d * β ^ q)
    (primitive : ∀ n : ℕ, (n : ℤ) ^ q ∣ α → (n : ℤ) ^ p ∣ β → n = 1)
    (x y : ℤ) :
    c * x ^ p = d * y ^ q ↔ ∃ t : ℤ, x = α * t ^ q ∧ y = β * t ^ p := by
  constructor
  · intro h
    have cross : x ^ p * β ^ q = y ^ q * α ^ p := by
      apply mul_left_cancel₀ hc
      calc
        c * (x ^ p * β ^ q) = (c * x ^ p) * β ^ q := by ring
        _ = (d * y ^ q) * β ^ q := by rw [h]
        _ = (d * β ^ q) * y ^ q := by ring
        _ = (c * α ^ p) * y ^ q := by rw [← scale]
        _ = c * (y ^ q * α ^ p) := by ring
    have hαq : (α : ℚ) ≠ 0 := by exact_mod_cast hα
    have hβq : (β : ℚ) ≠ 0 := by exact_mod_cast hβ
    have hr : ((x : ℚ) / α) ^ p = ((y : ℚ) / β) ^ q := by
      rw [div_pow,div_pow,div_eq_div_iff (pow_ne_zero _ hαq) (pow_ne_zero _ hβq)]
      exact_mod_cast cross
    obtain ⟨t,htx,hty⟩ := (pow_eq_pow_iff_of_coprime hcop).mp hr
    have hdenx : (t.den : ℤ) ^ q ∣ α := by
      have hd := Rat.den_dvd x α
      rw [Rat.divInt_eq_div,htx,Rat.den_pow] at hd
      simpa only [Nat.cast_pow] using hd
    have hdeny : (t.den : ℤ) ^ p ∣ β := by
      have hd := Rat.den_dvd y β
      rw [Rat.divInt_eq_div,hty,Rat.den_pow] at hd
      simpa only [Nat.cast_pow] using hd
    have ht : t.den = 1 := primitive t.den hdenx hdeny
    have hti : t = (t.num : ℚ) := (Rat.coe_int_num_of_den_eq_one ht).symm
    rw [hti] at htx hty
    refine ⟨t.num,?_,?_⟩
    · have he := (div_eq_iff hαq).mp htx
      exact_mod_cast (by simpa [mul_comm] using he : (x : ℚ) = α * (t.num : ℚ) ^ q)
    · have he := (div_eq_iff hβq).mp hty
      exact_mod_cast (by simpa [mul_comm] using he : (y : ℚ) = β * (t.num : ℚ) ^ p)
  · rintro ⟨t,rfl,rfl⟩
    exact chart_sound c d α β t p q scale

/-- Complete coefficient-bearing square/cube family, including all signs and zero. -/
theorem two_square_three_cube (x y : ℤ) :
    2 * x ^ 2 = 3 * y ^ 3 ↔ ∃ t : ℤ, x = 18 * t ^ 3 ∧ y = 6 * t ^ 2 := by
  apply coprime_complete 2 3 18 6 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ x y
  intro n _ hn
  have h : n ^ 2 ∣ 6 := by exact_mod_cast hn
  have hle : n ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) h
  have hnle : n ≤ 2 := by nlinarith
  interval_cases n <;> norm_num at h ⊢

end PerfectPower.CoefficientPowerCharts
