import Init.Data.BitVec.Lemmas

/-! Unconditional unsigned machine arithmetic. No mathematical-integer
replacement of a wrapping operation is performed without its guard. -/
namespace PerfectPower.BVWorkflow

theorem sub_le_self {w : Nat} (n b : BitVec w) (h : b ≤ n) : n-b ≤ n := by
  rw [BitVec.le_def, BitVec.toNat_sub_of_le h]
  exact Nat.sub_le _ _

theorem sub_le_bound {w : Nat} (n b x : BitVec w) (hb : b ≤ n) (hx : n ≤ x) : n-b ≤ x := by
  have h := sub_le_self n b hb
  rw [BitVec.le_def] at h hx ⊢
  exact Nat.le_trans h hx

theorem ule_sub_bound {w : Nat} (n b x : BitVec w)
    (hb : b.ule n = true) (hx : n.ule x = true) : (n-b).ule x = true := by
  simp only [BitVec.ule_iff_le] at hb hx ⊢
  exact sub_le_bound n b x hb hx

/-- The subtraction assignment obligation, with its active program premises. -/
theorem subtraction_assignment {w : Nat} (n b x after : BitVec w)
    (hassign : after = n-b) (hb : b ≤ n) (hx : n ≤ x) : after ≤ x := by
  rw [hassign]
  exact sub_le_bound n b x hb hx

/-- The terminal Von Neumann obligation needs no axiom about `sqr`.
Its two uses have the same argument after the machine shift by zero. -/
theorem terminal_square_bound {w : Nat} (x num res resg m : BitVec w)
    (sqr : BitVec w → BitVec w) (hm : m = 0)
    (hr : res = resg * ((1 : BitVec w) <<< m.toNat))
    (he : x-num = sqr resg) (hn : num ≤ x) : sqr res ≤ x := by
  have hr' : res = resg := by simpa [hm] using hr
  rw [hr', ← he]
  exact sub_le_self x num hn

end PerfectPower.BVWorkflow
