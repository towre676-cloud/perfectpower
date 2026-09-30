import PerfectPower.MordellDescent

/-!
# A genus-one family solved for every member: `k = (4t - 1)^3 - 4m^2`

`MordellDescent.lean` proves the descent for one curve at a time: each instance needs a
congruence table checked for its own `c`.  For Mordell's classical family the congruence is
uniform in `t`, so the whole family is one theorem.

**Theorem** (`no_points`).  Let `c = 4t - 1` and let `m` have no prime factor `≡ 3 (mod 4)`
(this excludes `m = 0`).  Then `y^2 = x^3 + c^3 - 4m^2` has no integral point.

*Proof.*  Modulo 4, `y^2 ≡ x^3 - 1`, which forces `x ≡ 1`.  Then `q = x^2 - c x + c^2 ≡ 3`
(mod 4) and `q > 0`, so `q` has a prime factor `p ≡ 3 (mod 4)` (`exists_bad_prime`).  From
`y^2 + (2m)^2 = (x + c) q`, `p ∣ y^2 + (2m)^2`; since `-1` is not a square mod `p`, `p ∣ 2m`,
hence `p ∣ m`, which the hypothesis forbids.

* `no_points_cert`: the hypothesis on `m` from a checkable certificate `m = 2^j m₁`,
  `m₁ ∣ u^2 + 1`.
* `family_not_isHit`: **every member, through every affine substitution**: for all `t`, all such
  `m`, all `r, s` and all `n`, `(r n + s)^3 + (4t - 1)^3 - 4m^2` is not a square.  So the
  compiler's answer for this family (no solutions) is exactly the solution set, for every input.
-/

namespace PerfectPower.MordellFamily

open PerfectPower MordellDescent

lemma mod4_x (x y : ℤ) (h : (y : ZMod 4) ^ 2 = (x : ZMod 4) ^ 3 - 1) : (x : ZMod 4) = 1 := by
  generalize (x : ZMod 4) = a at h ⊢
  generalize (y : ZMod 4) = b at h
  revert a b; decide

/-- **Mordell's family.**  No integral points on `y^2 = x^3 + (4t - 1)^3 - 4m^2` when `m` has no
prime factor `≡ 3 (mod 4)`. -/
theorem no_points (t m : ℤ) (hm : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p % 4 ≠ 3) (x y : ℤ) :
    y ^ 2 ≠ x ^ 3 + ((4 * t - 1) ^ 3 - 4 * m ^ 2) := by
  intro heq
  set c := 4 * t - 1 with hc
  -- modulo 4, x ≡ 1
  have h4 : (y : ZMod 4) ^ 2 = (x : ZMod 4) ^ 3 - 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 4) heq
    push_cast at this
    rw [this, hc]
    push_cast
    have e4 : (4 : ZMod 4) = 0 := by decide
    rw [e4]; ring
  have hx1 : (x : ZMod 4) = 1 := mod4_x x y h4
  set q := x ^ 2 - c * x + c ^ 2 with hqdef
  have hq3 : q % 4 = 3 := by
    have hq : (q : ZMod 4) = 3 := by
      rw [hqdef, hc]; push_cast; rw [hx1]
      have e4 : (4 : ZMod 4) = 0 := by decide
      rw [e4]; simp only [zero_mul, zero_sub]; decide
    have := (ZMod.intCast_eq_intCast_iff' q 3 4).mp (by rw [hq]; rfl)
    omega
  have hqpos : 0 < q := by
    have : 0 ≤ q := by nlinarith [sq_nonneg (2 * x - c), sq_nonneg c]
    omega
  set N := q.toNat
  have hN : (N : ℤ) = q := Int.toNat_of_nonneg hqpos.le
  have hN2 : N % 2 = 1 := by omega
  have hN8 : ¬ good 1 (N % 8) := by
    unfold good; omega
  obtain ⟨p, hp, hpN, hpbad⟩ := exists_bad_prime (Or.inl rfl) N hN2 hN8
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hp3 : p % 4 = 3 := by
    have hp_odd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
    unfold good at hpbad; omega
  have hpq : (p : ℤ) ∣ q := by rw [← hN]; exact_mod_cast hpN
  have hpy : (p : ℤ) ∣ y ^ 2 + 1 * (2 * m) ^ 2 :=
    hpq.trans ⟨x + c, by rw [hqdef]; linear_combination heq⟩
  by_cases hpb : (p : ℤ) ∣ 2 * m
  · have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd hpb with h2 | hpm
    · have : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    · exact hm p hp hpm hp3
  · have := good_of_dvd (Or.inl rfl) hp hp2 hpy hpb
    unfold good at this; omega

/-- The hypothesis on `m` from a certificate: `m = 2^j m₁` with `m₁ ∣ u^2 + 1`. -/
theorem good_of_cert {m m₁ u : ℤ} (j : ℕ) (hm : m = 2 ^ j * m₁) (hu : m₁ ∣ u ^ 2 + 1) :
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p % 4 ≠ 3 := by
  intro p hp hpm
  by_cases hp2 : p = 2
  · omega
  have := goodDivisors_of_cert (D := 1) (Or.inl rfl) j hm (by simpa using hu) p hp hp2 hpm
  unfold good at this; omega

/-- `no_points` from the certificate. -/
theorem no_points_cert (t m m₁ u : ℤ) (j : ℕ) (hm : m = 2 ^ j * m₁) (hu : m₁ ∣ u ^ 2 + 1)
    (x y : ℤ) : y ^ 2 ≠ x ^ 3 + ((4 * t - 1) ^ 3 - 4 * m ^ 2) :=
  no_points t m (good_of_cert j hm hu) x y

/-- **The family, end to end.**  For every member and every affine substitution, no value is a
square: the empty answer is exactly the solution set. -/
theorem family_not_isHit (t m : ℤ) (hm : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p % 4 ≠ 3)
    (r s : ℤ) (n : ℤ) : ¬ IsHit 2 ((r * n + s) ^ 3 + ((4 * t - 1) ^ 3 - 4 * m ^ 2)) := by
  rintro ⟨y, hy⟩
  exact no_points t m hm (r * n + s) y hy.symm

end PerfectPower.MordellFamily
