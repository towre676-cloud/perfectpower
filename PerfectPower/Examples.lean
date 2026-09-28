import PerfectPower.Monomial

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-! ### Complete hit lists proved by the Runge squeeze

Each proof traps `2m` (or `m`) strictly between consecutive integers except at the listed
hits — the argument of Theorem R with `t` ranging over a tiny explicit set. -/

/-- An integer strictly between `a` and `a + 1` does not exist; squared form. -/
lemma not_sq_between {a m : ℤ} (ha : 0 ≤ a) (h1 : a ^ 2 < m ^ 2) (h2 : m ^ 2 < (a + 1) ^ 2) :
    False := by
  rcases le_or_lt 0 m with hm | hm
  · have : a < m := by nlinarith
    have : m < a + 1 := by nlinarith
    omega
  · have : a < -m := by nlinarith
    have : -m < a + 1 := by nlinarith
    omega

/-- **Four consecutive integers.** `n(n+1)(n+2)(n+3)` is never a square for `n ≥ 1`:
it equals `(n^2+3n+1)^2 - 1`. -/
theorem consecutive_four_not_square (n : ℕ) (hn : 1 ≤ n) :
    ¬ IsHit 2 ((n : ℤ) * (n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, hm⟩
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  apply not_sq_between (a := (n : ℤ) ^ 2 + 3 * n) (m := m) (by positivity)
  · nlinarith
  · nlinarith

theorem consecutive_four_hitSet :
    hitSet (fun n => (n : ℤ) * (n + 1) * (n + 2) * (n + 3)) 2 0 = ∅ := by
  ext n
  simp only [hitSet, Set.mem_setOf_eq, add_zero, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hn, h⟩
  exact consecutive_four_not_square n hn h

/-- **Ljunggren's quartic.** For `n ≥ 1`, `1 + n + n^2 + n^3 + n^4` is a square iff `n = 3`
(value `121`).  Proof: `4F = (2n^2+n)^2 + 3n^2+4n+4`, which lies strictly between
`(2n^2+n)^2` and `(2n^2+n+2)^2` once `n ≥ 1`, so `4F = (2n^2+n+1)^2`, i.e. `n^2 = 2n + 3`. -/
theorem ljunggren_quartic (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (1 + (n : ℤ) + n ^ 2 + n ^ 3 + n ^ 4) ↔ n = 3 := by
  constructor
  · rintro ⟨m, hm⟩
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    set a : ℤ := 2 * n ^ 2 + n with ha
    have ha0 : 0 ≤ a := by positivity
    -- (2m)^2 = 4F lies in ((a)^2, (a+2)^2)
    have hlo : a ^ 2 < (2 * m) ^ 2 := by nlinarith
    have hhi : (2 * m) ^ 2 < (a + 2) ^ 2 := by nlinarith
    -- so (2m)^2 = (a+1)^2
    have hmid : (2 * m) ^ 2 = (a + 1) ^ 2 := by
      rcases lt_trichotomy ((2 * m) ^ 2) ((a + 1) ^ 2) with h | h | h
      · exact (not_sq_between ha0 hlo h).elim
      · exact h
      · exact (not_sq_between (by positivity) h (by linarith [hhi])).elim
    have hq : ((n : ℤ) - 3) * ((n : ℤ) + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hq with h | h
    · omega
    · omega
  · rintro rfl
    exact ⟨11, by norm_num⟩

theorem ljunggren_hitSet :
    hitSet (fun n => 1 + (n : ℤ) + n ^ 2 + n ^ 3 + n ^ 4) 2 0 = {3} := by
  ext n
  simp only [hitSet, Set.mem_setOf_eq, add_zero, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, h⟩; exact (ljunggren_quartic n hn).mp h
  · rintro rfl; exact ⟨by norm_num, (ljunggren_quartic 3 (by norm_num)).mpr rfl⟩

end PerfectPower
