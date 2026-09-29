import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import PerfectPower.Basic

/-!
# Mordell curves without integral points: an unconditional, kernel-checked descent

For `k = c^3 - D b^2` with `D ∈ {1, 2, -2}`, the classical argument (Mordell, *Diophantine
Equations*, ch. 26, for `D = 1`) runs:

  `y^2 = x^3 + k`  ⇒  `y^2 + D b^2 = (x + c) q`,  `q = x^2 - c x + c^2 > 0`.

A congruence modulo `M` (checked here by kernel evaluation over all residues) forces `q` odd with
`q mod 8` outside the multiplicatively closed set of residues of the primes `p` for which `-D`
is a square mod `p`.  So some prime `p ∣ q` has `-D` a non-square mod `p`; then `p ∣ y^2 + D b^2`
forces `p ∣ b`, which a certificate `b = 2^j b₁`, `b₁ ∣ u^2 + D` excludes.

Nothing here is assumed: no point list, no rank, no external computation.  Each instance is a
complete (empty) list of integral points on `y^2 = x^3 + k`, hence a complete (empty) hit list for
`n^3 + k = m^2`.
-/

namespace PerfectPower.MordellDescent

/-- Residues mod 8 of odd primes `p` for which `-D` is a square mod `p`. -/
def good (D : ℤ) (r : ℕ) : Prop :=
  (D = 1 ∧ (r = 1 ∨ r = 5)) ∨ (D = 2 ∧ (r = 1 ∨ r = 3)) ∨ (D = -2 ∧ (r = 1 ∨ r = 7))

instance (D : ℤ) (r : ℕ) : Decidable (good D r) := by unfold good; infer_instance

/-- If an odd prime divides `y^2 + D b^2` but not `b`, then `-D` is a square mod `p`. -/
theorem good_of_dvd {D : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y b : ℤ} (hdvd : (p : ℤ) ∣ y ^ 2 + D * b ^ 2) (hb : ¬ (p : ℤ) ∣ b) : good D (p % 8) := by
  haveI := Fact.mk hp
  have h0 : ((y ^ 2 + D * b ^ 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  push_cast at h0
  have hsq : IsSquare (-(D : ZMod p)) := ⟨(y : ZMod p) / b, by
    field_simp; linear_combination (-1 : ZMod p) * h0⟩
  have hodd : p % 2 = 1 := hp.eq_one_or_self_of_dvd 2 |> fun _ => (Nat.Prime.mod_two_eq_one_iff_ne_two).mpr hp2
  rcases hD with rfl | rfl | rfl
  · have := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp (by simpa using hsq)
    left; refine ⟨rfl, ?_⟩; omega
  · have := (ZMod.exists_sq_eq_neg_two_iff hp2).mp (by simpa using hsq)
    right; left; exact ⟨rfl, this⟩
  · have := (ZMod.exists_sq_eq_two_iff hp2).mp (by simpa using hsq)
    right; right; exact ⟨rfl, this⟩

lemma good_mul {D : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2) {a b : ℕ} (ha : good D (a % 8))
    (hb : good D (b % 8)) : good D (a * b % 8) := by
  have key : ∀ r, r < 8 → ∀ s, s < 8 → good D r → good D s → good D (r * s % 8) := by
    rcases hD with rfl | rfl | rfl <;> decide
  rw [Nat.mul_mod]; exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) ha hb

/-- An odd `N` whose residue mod 8 is not good has a prime factor whose residue is not good. -/
theorem exists_bad_prime {D : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2) :
    ∀ N : ℕ, N % 2 = 1 → ¬ good D (N % 8) → ∃ p, p.Prime ∧ p ∣ N ∧ ¬ good D (p % 8) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hodd hbad
  have hN1 : N ≠ 1 := by
    rintro rfl; apply hbad; rcases hD with rfl | rfl | rfl <;> decide
  have hp := Nat.minFac_prime hN1
  by_cases hg : good D (N.minFac % 8)
  · obtain ⟨m, hm⟩ := Nat.minFac_dvd N
    have hpos : 0 < N := by omega
    have hm_lt : m < N := by
      rw [hm]; have := hp.two_le
      have : 0 < m := by rcases Nat.eq_zero_or_pos m with h | h <;> [simp [h] at hm; omega; exact h]
      nlinarith
    have hmodd : m % 2 = 1 := by
      rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
      · exfalso; rw [hm, ht] at hodd; rw [show N.minFac * (t + t) = 2 * (N.minFac * t) by ring] at hodd; omega
      · omega
    have hmbad : ¬ good D (m % 8) := fun h => hbad (hm ▸ good_mul hD hg h)
    obtain ⟨p, hpp, hpm, hpb⟩ := ih m hm_lt hmodd hmbad
    exact ⟨p, hpp, hpm.trans ⟨N.minFac, by rw [hm, mul_comm]⟩, hpb⟩
  · exact ⟨_, hp, Nat.minFac_dvd N, hg⟩

/-- Certificate for the prime factors of `b`: `b = 2^j b₁` with `b₁ ∣ u^2 + D`. -/
theorem goodDivisors_of_cert {D : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2) {b b₁ u : ℤ} (j : ℕ)
    (hb : b = 2 ^ j * b₁) (hu : b₁ ∣ u ^ 2 + D) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ b → good D (p % 8) := by
  intro p hp hp2 hpb
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpb₁ : (p : ℤ) ∣ b₁ := by
    rw [hb] at hpb
    rcases hpZ.dvd_or_dvd hpb with h | h
    · have h2 := hpZ.dvd_of_dvd_pow h
      have : p ∣ 2 := by exact_mod_cast h2
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
    · exact h
  have hdvd : (p : ℤ) ∣ u ^ 2 + D * 1 ^ 2 := by simpa using hpb₁.trans hu
  refine good_of_dvd hD hp hp2 hdvd ?_
  intro h1
  have : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- The congruence hypothesis: for every residue pair solving the equation mod `M`, the value of
`q = X^2 - c X + c^2` is odd with a residue mod 8 that is not good.  Checked by kernel evaluation. -/
def CongOK (D c b : ℤ) (M : ℕ) : Prop :=
  ∀ X, X < M → ∀ Y, Y < M → ((Y : ℤ) ^ 2 - X ^ 3 - c ^ 3 + D * b ^ 2) % M = 0 →
    ((X : ℤ) ^ 2 - c * X + c ^ 2) % 2 = 1 ∧ ¬ good D (((X : ℤ) ^ 2 - c * X + c ^ 2) % 8).toNat

instance (D c b : ℤ) (M : ℕ) : Decidable (CongOK D c b M) := by unfold CongOK; infer_instance

lemma cast_emod (M : ℕ) (x : ℤ) : (((x % M).toNat : ℕ) : ℤ) = x % M :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

/-- **The descent.** -/
theorem no_points {D c b : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2)
    (hb : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ b → good D (p % 8))
    {M : ℕ} (hM : 8 ∣ M) (hcong : CongOK D c b M) (x y : ℤ) :
    y ^ 2 ≠ x ^ 3 + (c ^ 3 - D * b ^ 2) := by
  intro heq
  have hM0 : (0 : ℤ) < M := by
    have : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
    exact_mod_cast this
  set X := (x % M).toNat
  set Y := (y % M).toNat
  have hX : (X : ℤ) = x % M := cast_emod M x
  have hY : (Y : ℤ) = y % M := cast_emod M y
  have hXlt : X < M := by have := Int.emod_lt_of_pos x hM0; omega
  have hYlt : Y < M := by have := Int.emod_lt_of_pos y hM0; omega
  -- `x ≡ X`, `y ≡ Y` mod `M`
  obtain ⟨s, hs⟩ : (M : ℤ) ∣ x - X := by rw [hX]; exact Int.dvd_sub_of_emod_eq rfl
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ y - Y := by rw [hY]; exact Int.dvd_sub_of_emod_eq rfl
  have hc : ((Y : ℤ) ^ 2 - X ^ 3 - c ^ 3 + D * b ^ 2) % M = 0 := by
    apply Int.emod_eq_zero_of_dvd
    have hx' : x = X + M * s := by linarith
    have hy' : y = Y + M * t := by linarith
    refine ⟨-(2 * Y * t + M * t ^ 2) + (3 * X ^ 2 * s + 3 * X * M * s ^ 2 + M ^ 2 * s ^ 3), ?_⟩
    rw [hx', hy'] at heq; linear_combination -heq
  obtain ⟨hq2, hq8⟩ := hcong X hXlt Y hYlt hc
  set q := x ^ 2 - c * x + c ^ 2 with hqdef
  obtain ⟨r, hr⟩ : (8 : ℤ) ∣ q - ((X : ℤ) ^ 2 - c * X + c ^ 2) := by
    have h8 : (8 : ℤ) ∣ M := by exact_mod_cast hM
    exact h8.trans ⟨s * (x + X - c), by rw [hqdef]; linear_combination (x + X - c) * hs⟩
  have hq2' : q % 2 = 1 := by omega
  have hq8' : (q % 8) = ((X : ℤ) ^ 2 - c * X + c ^ 2) % 8 := by omega
  have hqnn : 0 ≤ q := by nlinarith [sq_nonneg (2 * x - c), sq_nonneg c]
  set N := q.toNat
  have hN : (N : ℤ) = q := Int.toNat_of_nonneg hqnn
  have hN2 : N % 2 = 1 := by omega
  have hN8 : N % 8 = (((X : ℤ) ^ 2 - c * X + c ^ 2) % 8).toNat := by omega
  obtain ⟨p, hp, hpN, hpbad⟩ := exists_bad_prime hD N hN2 (by rw [hN8]; exact hq8)
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hpq : (p : ℤ) ∣ q := by rw [← hN]; exact_mod_cast hpN
  have hpy : (p : ℤ) ∣ y ^ 2 + D * b ^ 2 :=
    hpq.trans ⟨x + c, by rw [hqdef]; linear_combination heq⟩
  by_cases hpb : (p : ℤ) ∣ b
  · exact hpbad (hb p hp hp2 hpb)
  · exact hpbad (good_of_dvd hD hp hp2 hpy hpb)

/-- The hit-list form: `n^3 + k` is never a square, for any integer `n`. -/
theorem not_isHit {D c b k : ℤ} (hD : D = 1 ∨ D = 2 ∨ D = -2)
    (hb : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ b → good D (p % 8))
    {M : ℕ} (hM : 8 ∣ M) (hcong : CongOK D c b M) (hk : k = c ^ 3 - D * b ^ 2) (n : ℤ) :
    ¬ IsHit 2 (n ^ 3 + k) := by
  rintro ⟨m, hm⟩
  exact no_points hD hb hM hcong n m (by rw [← hk]; exact hm.symm)

/-- `y^2 = x^3 + 7` has no integral points (`c = 2`, `b = 1`, `D = 1`). -/
theorem mordell_7 (x y : ℤ) : y ^ 2 ≠ x ^ 3 + 7 := by
  have := no_points (D := 1) (c := 2) (b := 1) (by norm_num)
    (goodDivisors_of_cert (by norm_num) 0 (b₁ := 1) (u := 0) (by norm_num) (by norm_num))
    (M := 8) (by norm_num) (by decide +kernel) x y
  norm_num at this; exact this

end PerfectPower.MordellDescent
