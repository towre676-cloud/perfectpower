import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Square-root trial division, with exact equality to Mathlib's divisor sets.
The generator and kernel checker use the same proved algorithm; no factorization oracle. -/
namespace PerfectPower.FastDivisors

-- Structural fuel avoids reducing Mathlib's well-founded recursion in the kernel.
def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, guess => guess
  | fuel + 1, n, guess =>
    let next := (guess + n / guess) / 2
    if next < guess then sqrtIter fuel n next else guess

theorem sqrtIter_eq (fuel n guess : ℕ) (h : guess ≤ fuel) :
    sqrtIter fuel n guess = Nat.sqrt.iter n guess := by
  induction fuel generalizing guess with
  | zero =>
    have hg : guess = 0 := by omega
    subst guess
    simp [sqrtIter, Nat.sqrt.iter]
  | succ fuel ih =>
    rw [sqrtIter, Nat.sqrt.iter]
    split_ifs with hn
    · exact ih _ (by omega)
    · rfl

def sqrt (n : ℕ) : ℕ := if n ≤ 1 then n else sqrtIter n n (n / 2)

theorem sqrt_eq (n : ℕ) : sqrt n = Nat.sqrt n := by
  unfold sqrt Nat.sqrt
  split_ifs
  · rfl
  · exact sqrtIter_eq n n (n / 2) (Nat.div_le_self n 2)

def small (n : ℕ) : Finset ℕ := (Finset.Icc 1 (sqrt n)).filter (· ∣ n)

def divisors (n : ℕ) : Finset ℕ := small n ∪ (small n).image (n / ·)

theorem small_mem {n d : ℕ} : d ∈ small n ↔ 1 ≤ d ∧ d ≤ Nat.sqrt n ∧ d ∣ n := by
  simp [small, sqrt_eq, and_assoc]

theorem mem_divisors {n d : ℕ} : d ∈ divisors n ↔ d ∣ n ∧ n ≠ 0 := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨hd, hs, hv⟩ := small_mem.mp h
      refine ⟨hv, ?_⟩
      intro hz
      simp [hz] at hs
      omega
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨ha, hs, hv⟩ := small_mem.mp ha
      refine ⟨Nat.div_dvd_of_dvd hv, ?_⟩
      intro hz
      simp [hz] at hs
      omega
  · rintro ⟨hd, hn⟩
    have hp : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)
    by_cases hs : d ≤ Nat.sqrt n
    · exact Finset.mem_union_left _ (small_mem.mpr ⟨hp, hs, hd⟩)
    · have he : d * (n / d) = n := Nat.mul_div_cancel' hd
      have hq : 1 ≤ n / d := by
        exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (by omega)
      have hqs : n / d ≤ Nat.sqrt n := by
        by_contra h
        have hb := Nat.lt_succ_sqrt n
        have hd' : Nat.sqrt n + 1 ≤ d := Nat.succ_le_of_lt (Nat.lt_of_not_ge hs)
        have hq' : Nat.sqrt n + 1 ≤ n / d := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
        have hprod : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ d * (n / d) :=
          Nat.mul_le_mul hd' hq'
        simp only [Nat.succ_eq_add_one] at hb
        rw [he] at hprod
        exact (not_lt_of_ge hprod) hb
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨n / d, small_mem.mpr ⟨hq, hqs, Nat.div_dvd_of_dvd hd⟩, ?_⟩
      exact Nat.div_div_self hd hn

theorem divisors_eq (n : ℕ) : divisors n = n.divisors := by
  ext d
  rw [mem_divisors, Nat.mem_divisors]

def natPairs (n : ℕ) : Finset (ℕ × ℕ) := (divisors n).image fun d => (d, n / d)

theorem natPairs_eq (n : ℕ) : natPairs n = n.divisorsAntidiagonal := by
  rw [natPairs, divisors_eq]
  simpa only [Finset.map_eq_image] using (Nat.map_div_right_divisors (n := n))

def pairs (k : ℤ) : Finset (ℤ × ℤ) :=
  if 0 ≤ k then
    ((natPairs k.natAbs).image fun z => ((z.1 : ℤ), (z.2 : ℤ))) ∪
      ((natPairs k.natAbs).image fun z => (-(z.1 : ℤ), -(z.2 : ℤ)))
  else
    ((natPairs k.natAbs).image fun z => ((z.1 : ℤ), -(z.2 : ℤ))) ∪
      ((natPairs k.natAbs).image fun z => (-(z.1 : ℤ), (z.2 : ℤ)))

theorem pairs_eq (k : ℤ) : pairs k = k.divisorsAntidiag := by
  cases k with
  | ofNat n => simp [pairs, natPairs_eq, Int.divisorsAntidiag, Finset.map_eq_image,
      Finset.disjUnion_eq_union]; rfl
  | negSucc n => simp [pairs, natPairs_eq, Int.divisorsAntidiag, Finset.map_eq_image,
      Finset.disjUnion_eq_union]; rfl

theorem mem_pairs {k u v : ℤ} : (u,v) ∈ pairs k ↔ u*v = k ∧ k ≠ 0 := by
  rw [pairs_eq, Int.mem_divisorsAntidiag]

def signed (k : ℤ) : Finset ℤ := (pairs k).image Prod.fst

theorem mem_signed {k d : ℤ} : d ∈ signed k ↔ d ∣ k ∧ k ≠ 0 := by
  simp only [signed, Finset.mem_image]
  constructor
  · rintro ⟨⟨u,v⟩, h, rfl⟩
    obtain ⟨hm, hk⟩ := mem_pairs.mp h
    exact ⟨⟨v, hm.symm⟩, hk⟩
  · rintro ⟨⟨v, hm⟩, hk⟩
    exact ⟨(d,v), mem_pairs.mpr ⟨hm.symm, hk⟩, rfl⟩

end PerfectPower.FastDivisors
