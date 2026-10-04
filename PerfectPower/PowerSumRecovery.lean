import Mathlib
namespace PerfectPower.PowerSumRecovery

/-- Recovered primitive quartic identity; the old common-divisor claim is false. -/
theorem quartic_identity : (95800:ℕ)^4+217519^4+414560^4=422481^4 := by norm_num

theorem quartic_primitive : Nat.gcd (Nat.gcd (Nat.gcd 95800 217519) 414560) 422481=1 := by decide +kernel

theorem quintic_identity : (27:ℕ)^5+84^5+110^5+133^5=144^5 := by norm_num

theorem quintic_primitive : Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd 27 84) 110) 133) 144=1 := by decide +kernel

/-- Meet-in-the-middle decomposition is exact, with repeats retained. -/
theorem four_pair_iff (a b c e t : ℕ) (k : ℕ) :
    a^k+b^k+c^k+e^k=t^k ↔
      c^k+e^k ≤ t^k ∧ a^k+b^k=t^k-(c^k+e^k) := by omega

theorem three_pair_iff (a b c t : ℕ) (k : ℕ) :
    a^k+b^k+c^k=t^k ↔ c^k ≤ t^k ∧ a^k+b^k=t^k-c^k := by omega

/-- Positive terms force each summand strictly below the target. -/
theorem summand_lt (a b c t k : ℕ) (hb : 0 < b)
    (h : a^k+b^k+c^k=t^k) : a<t := by
  have hp : 0 < b^k := pow_pos hb k
  by_contra hn
  have hpow := pow_le_pow_left₀ (Nat.zero_le t) (show t ≤ a by omega) k
  omega

end PerfectPower.PowerSumRecovery
