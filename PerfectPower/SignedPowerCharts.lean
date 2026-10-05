import PerfectPower.ArithmeticSimplifier

namespace PerfectPower.SignedPowerCharts

/-- A sign chart for every integer; zero has the positive chart. -/
theorem sign_choice (x : ℤ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ x = s * (x.natAbs : ℤ) := by
  rcases Int.natAbs_eq x with h | h
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

/-- Magnitude extraction after dividing both exponents by their gcd. -/
theorem magnitude_parameter (a b g : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : g ≠ 0) (hab : Nat.Coprime a b) (x y : ℤ)
    (h : x ^ (a * g) = y ^ (b * g)) :
    ∃ t : ℕ, x.natAbs = t ^ b ∧ y.natAbs = t ^ a := by
  have hn := congrArg Int.natAbs h
  simp only [Int.natAbs_pow, pow_mul] at hn
  have hr : x.natAbs ^ a = y.natAbs ^ b := Nat.pow_left_injective hg hn
  have hi : (x.natAbs : ℤ) ^ a = (y.natAbs : ℤ) ^ b := by exact_mod_cast hr
  obtain ⟨t,hx,hy⟩ :=
    (PerfectPower.ArithmeticSimplifier.coprime_power_parameter a b ha hb hab _ _).mp hi
  refine ⟨t.natAbs, ?_, ?_⟩
  · have hh := congrArg Int.natAbs hx
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using hh
  · have hh := congrArg Int.natAbs hy
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using hh

/-- Complete signed charts, with exactly one chart permitted at zero. -/
theorem signed_charts (a b g : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : g ≠ 0) (hab : Nat.Coprime a b) (x y : ℤ) :
    x ^ (a * g) = y ^ (b * g) ↔
    ∃ (t : ℕ) (sx sy : ℤ),
      (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
      sx ^ (a * g) = sy ^ (b * g) ∧
      x = sx * (t : ℤ) ^ b ∧ y = sy * (t : ℤ) ^ a ∧
      (t = 0 → sx = 1 ∧ sy = 1) := by
  have hp : a * g ≠ 0 := Nat.mul_ne_zero ha hg
  have hq : b * g ≠ 0 := Nat.mul_ne_zero hb hg
  constructor
  · intro h
    by_cases hx0 : x = 0
    · have hy0 : y = 0 := by
        have hh : y ^ (b * g) = 0 := by simpa [hx0, zero_pow hp] using h.symm
        exact (pow_eq_zero hh)
      refine ⟨0,1,1,Or.inl rfl,Or.inl rfl,by simp,?_,?_,by simp⟩
      · simp [hx0,zero_pow hb]
      · simp [hy0,zero_pow ha]
    obtain ⟨t,htx,hty⟩ := magnitude_parameter a b g ha hb hg hab x y h
    obtain ⟨sx,hsx,hx⟩ := sign_choice x
    obtain ⟨sy,hsy,hy⟩ := sign_choice y
    have hx' : x = sx * (t : ℤ) ^ b := by simpa [htx] using hx
    have hy' : y = sy * (t : ℤ) ^ a := by simpa [hty] using hy
    have ht : t ≠ 0 := by
      intro ht
      apply hx0
      simpa [ht,zero_pow hb] using hx'
    have hti : (t : ℤ) ≠ 0 := by exact_mod_cast ht
    have he : b * (a * g) = a * (b * g) := by ring
    have hs : sx ^ (a * g) = sy ^ (b * g) := by
      rw [hx',hy',mul_pow,mul_pow,← pow_mul,← pow_mul,he] at h
      exact mul_right_cancel₀ (pow_ne_zero _ hti) h
    exact ⟨t,sx,sy,hsx,hsy,hs,hx',hy',fun h => (ht h).elim⟩
  · rintro ⟨t,sx,sy,_,_,hs,rfl,rfl,_⟩
    rw [mul_pow,mul_pow,← pow_mul,← pow_mul,hs]
    congr 2
    ring

/-- Arbitrary positive original exponents use their actual gcd. -/
theorem gcd_signed_charts (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (x y : ℤ) :
    x ^ p = y ^ q ↔
    ∃ (t : ℕ) (sx sy : ℤ),
      (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧ sx ^ p = sy ^ q ∧
      x = sx * (t : ℤ) ^ (q / p.gcd q) ∧
      y = sy * (t : ℤ) ^ (p / p.gcd q) ∧
      (t = 0 → sx = 1 ∧ sy = 1) := by
  have hg : 0 < p.gcd q := Nat.gcd_pos_of_pos_left q hp
  have ha : p / p.gcd q ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left q hp) hg).ne'
  have hb : q / p.gcd q ≠ 0 :=
    (Nat.div_pos (by simpa [Nat.gcd_comm] using Nat.gcd_le_left p hq) hg).ne'
  simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left p q),
    Nat.div_mul_cancel (Nat.gcd_dvd_right p q)] using
    signed_charts (p / p.gcd q) (q / p.gcd q) (p.gcd q) ha hb hg.ne'
      (Nat.coprime_div_gcd_div_gcd hg) x y

/-- Shared offsets cancel additively, while all signed power charts remain. -/
theorem shared_offset_charts (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (A B : ℤ → ℤ) (k x y : ℤ) :
    (A x) ^ p + k = (B y) ^ q + k ↔
    ∃ (t : ℕ) (sx sy : ℤ),
      (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧ sx ^ p = sy ^ q ∧
      A x = sx * (t : ℤ) ^ (q / p.gcd q) ∧
      B y = sy * (t : ℤ) ^ (p / p.gcd q) ∧
      (t = 0 → sx = 1 ∧ sy = 1) := by
  rw [add_left_inj]
  exact gcd_signed_charts p q hp hq (A x) (B y)

end PerfectPower.SignedPowerCharts
