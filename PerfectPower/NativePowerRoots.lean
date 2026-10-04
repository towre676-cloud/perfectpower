import Mathlib.Tactic

/-! Binary integer root extraction with a proved floor-root specification. -/
namespace PerfectPower.NativePowerRoots

/-- Binary search with an explicit decreasing fuel; wide intervals are halved. -/
def search (d N : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if hi ≤ lo+1 then lo else
      let mid := lo+(hi-lo)/2
      if mid^d ≤ N then search d N fuel mid hi else search d N fuel lo mid

/-- Search correctness needs only endpoint powers and a width bound. -/
theorem search_bounds (d N fuel lo hi : ℕ)
    (hl : lo^d ≤ N) (hh : N < hi^d) (hw : hi-lo ≤ fuel+1) :
    (search d N fuel lo hi)^d ≤ N ∧ N < (search d N fuel lo hi+1)^d := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [search]
    refine ⟨hl,lt_of_lt_of_le hh ?_⟩
    exact pow_le_pow_left₀ (Nat.zero_le _) (by omega) d
  | succ fuel ih =>
    simp only [search]
    split_ifs with he hm
    · refine ⟨hl,lt_of_lt_of_le hh ?_⟩
      exact pow_le_pow_left₀ (Nat.zero_le _) he d
    · apply ih _ _ hm hh
      omega
    · apply ih _ _ hl (by omega)
      omega

/-- The floor of the nonnegative d-th root, for nonzero d. -/
def root (d N : ℕ) : ℕ := search d N (N+1) 0 (N+1)

theorem root_bounds (d N : ℕ) (hd : d ≠ 0) :
    (root d N)^d ≤ N ∧ N < (root d N+1)^d := by
  apply search_bounds d N (N+1) 0 (N+1)
  · simp [zero_pow hd]
  · have h := le_self_pow₀ (a := N+1) (by omega) hd
    omega
  · omega

theorem root_exact (d N u : ℕ) (hd : d ≠ 0) (hu : u^d=N) : root d N=u := by
  obtain ⟨hl,hh⟩ := root_bounds d N hd
  apply le_antisymm
  · by_contra hn
    have hpow := pow_lt_pow_left₀ (show u < root d N by omega) (Nat.zero_le u) hd
    omega
  · by_contra hn
    have hpow := pow_le_pow_left₀ (Nat.zero_le (root d N+1))
      (show root d N+1 ≤ u by omega) d
    omega

/-- Both signs are proposed and filtered on the original equation. -/
def roots (d : ℕ) (n : ℤ) : Finset ℤ :=
  ({(root d n.natAbs : ℤ), -(root d n.natAbs : ℤ)} : Finset ℤ).filter fun y => y^d=n

theorem roots_complete (d : ℕ) (n y : ℤ) (hd : d ≠ 0) : y^d=n ↔ y ∈ roots d n := by
  constructor
  · intro h
    have ha : y.natAbs^d=n.natAbs := by rw [← Int.natAbs_pow, h]
    have hr := root_exact d n.natAbs y.natAbs hd ha
    apply Finset.mem_filter.mpr
    refine ⟨?_,h⟩
    have he : |y|=|(root d n.natAbs : ℤ)| := by
      rw [hr,abs_of_nonneg (Int.natCast_nonneg _),← Int.natCast_natAbs]
    rcases abs_eq_abs.mp he with he | he <;> simp [he]
  · intro h; exact (Finset.mem_filter.mp h).2

end PerfectPower.NativePowerRoots
