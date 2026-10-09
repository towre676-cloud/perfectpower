import PerfectPower.QueryNative
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace PerfectPower.PellPopulation

def pellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (3 * (pellSeq k).1 + 4 * (pellSeq k).2, 2 * (pellSeq k).1 + 3 * (pellSeq k).2)

/-- Invariants of the Pell orbit: norm one, `m_k ≥ 2k+1`, `n_k ≥ k^2`, `n_k ≥ 0`. -/
lemma pellSeq_spec (k : ℕ) :
    (pellSeq k).1 ^ 2 - 2 * (pellSeq k).2 ^ 2 = 1 ∧ 2 * k + 1 ≤ (pellSeq k).1 ∧
      (k : ℤ) ^ 2 ≤ (pellSeq k).2 ∧ 0 ≤ (pellSeq k).2 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [pellSeq]
    push_cast
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Descent: every nonnegative solution of `m^2 - 2 n^2 = 1` is on the orbit. -/
theorem pell_descent : ∀ (n : ℕ) (m : ℤ), 0 ≤ m → m ^ 2 - 2 * (n : ℤ) ^ 2 = 1 →
    ∃ k, pellSeq k = (m, (n : ℤ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, ?_⟩
      have h' : (m - 1) * (m + 1) = 0 := by push_cast at h; ring_nf; linarith
      have : m = 1 := by
        rcases mul_eq_zero.mp h' with h1 | h1 <;> omega
      simp [pellSeq, this]
    · have hn2 : 2 ≤ n := by
        by_contra hlt
        have : n = 1 := by omega
        subst this
        have hm3 : m ^ 2 = 3 := by push_cast at h; linarith
        rcases le_or_lt m 1 with h1 | h1
        · nlinarith
        · nlinarith
      -- predecessor (3m - 4n, 3n - 2m)
      have hmn : (n : ℤ) < m := by nlinarith
      have hA : 0 ≤ 3 * m - 4 * n := by nlinarith
      have hB : 0 ≤ 3 * (n : ℤ) - 2 * m := by nlinarith
      have hlt : (3 * (n : ℤ) - 2 * m).toNat < n := by omega
      obtain ⟨k, hk⟩ := ih _ hlt (3 * m - 4 * n) hA (by
        rw [Int.toNat_of_nonneg hB]; nlinarith)
      refine ⟨k + 1, ?_⟩
      simp only [pellSeq, hk, Int.toNat_of_nonneg hB]
      ext <;> simp <;> ring


/-- Source input is n; source output is its unique nonnegative square root. -/
def point (k : ℕ) : ℤ × ℤ := ((pellSeq k).2,(pellSeq k).1)

theorem point_spec (k : ℕ) :
    0 ≤ (point k).1 ∧ 0 ≤ (point k).2 ∧ (point k).2^2 = 2*(point k).1^2+1 := by
  obtain ⟨h1,h2,h3,h4⟩ := pellSeq_spec k
  simp only [point, Prod.fst, Prod.snd]
  exact ⟨h4, by linarith, by linarith⟩

theorem global_complete (p : ℤ × ℤ) :
    (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2^2 = 2*p.1^2+1) ↔ ∃ k, point k = p := by
  constructor
  · rintro ⟨hn,hm,he⟩
    obtain ⟨k,hk⟩ := pell_descent p.1.toNat p.2 hm (by rw [Int.toNat_of_nonneg hn]; linarith)
    refine ⟨k, ?_⟩
    simp [point, hk, Int.toNat_of_nonneg hn]
  · rintro ⟨k,rfl⟩
    exact point_spec k

theorem input_strictMono : StrictMono (fun k => (point k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨h1,h2,h3,h4⟩ := pellSeq_spec k
  simp only [point, pellSeq]
  nlinarith

theorem point_injective : Function.Injective point := by
  intro k l h
  exact input_strictMono.injective (congrArg Prod.fst h)

def populationPrefix (length : ℕ) : List (ℤ × ℤ) := (List.range length).map point

theorem prefix_complete (length : ℕ) (cutoff : ℤ)
    (hinside : ((populationPrefix length).all fun p => decide (p.1 ≤ cutoff)) = true)
    (hnext : cutoff < (point length).1) (p : ℤ × ℤ) :
    p ∈ populationPrefix length ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ cutoff ∧ p.2^2 = 2*p.1^2+1 := by
  constructor
  · intro hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hn,hm,he⟩ := point_spec k
    exact ⟨hn,hm,of_decide_eq_true (List.all_eq_true.mp hinside _ hp),he⟩
  · rintro ⟨hn,hm,hcut,he⟩
    obtain ⟨k,hk⟩ := global_complete p |>.mp ⟨hn,hm,he⟩
    have hb : k < length := by
      by_contra hh
      have hl : length ≤ k := by omega
      have hm := input_strictMono.monotone hl
      rw [hk] at hm
      omega
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr hb,hk⟩

theorem prefix_nodup (length : ℕ) : (populationPrefix length).Nodup :=
  List.Nodup.map point_injective (List.nodup_range)

end PerfectPower.PellPopulation
