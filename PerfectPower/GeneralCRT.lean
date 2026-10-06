import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-! Noncoprime residue intersections: compatibility, a canonical anchor and
the exact lcm period. No pairwise-coprimality premise is hidden in a chart. -/
namespace PerfectPower.GeneralCRT

theorem compatible_iff (m n a b : ℕ) :
    (∃ x, Nat.ModEq m x a ∧ Nat.ModEq n x b) ↔ Nat.ModEq (Nat.gcd m n) a b := by
  constructor
  · rintro ⟨x, ha, hb⟩
    exact (ha.of_dvd (Nat.gcd_dvd_left m n)).symm.trans
      (hb.of_dvd (Nat.gcd_dvd_right m n))
  · intro h
    exact ⟨(Nat.chineseRemainder' h).val, (Nat.chineseRemainder' h).property⟩

/-- Canonical representative of a compatible residue intersection. -/
def anchor (m n a b : ℕ) (h : Nat.ModEq (Nat.gcd m n) a b) : ℕ :=
  (Nat.chineseRemainder' h).val

theorem intersection_iff (m n a b x : ℕ) (h : Nat.ModEq (Nat.gcd m n) a b) :
    (Nat.ModEq m x a ∧ Nat.ModEq n x b) ↔ Nat.ModEq (Nat.lcm m n) x (anchor m n a b h) := by
  have ha := (Nat.chineseRemainder' h).property.1
  have hb := (Nat.chineseRemainder' h).property.2
  constructor
  · rintro ⟨hx, hy⟩
    exact Nat.mod_lcm (hx.trans ha.symm) (hy.trans hb.symm)
  · intro hx
    exact ⟨(hx.of_dvd (Nat.dvd_lcm_left m n)).trans ha,
      (hx.of_dvd (Nat.dvd_lcm_right m n)).trans hb⟩

theorem anchor_lt (m n a b : ℕ) (h : Nat.ModEq (Nat.gcd m n) a b)
    (hm : m ≠ 0) (hn : n ≠ 0) : anchor m n a b h < Nat.lcm m n :=
  Nat.chineseRemainder'_lt_lcm h hm hn

/-- The lcm chart remains exact for negative integer parameters and residues. -/
theorem integer_intersection_iff (m n : ℕ) (a b anchor x : ℤ)
    (ha : Int.ModEq (m:ℤ) anchor a) (hb : Int.ModEq (n:ℤ) anchor b) :
    (Int.ModEq (m:ℤ) x a ∧ Int.ModEq (n:ℤ) x b) ↔
      Int.ModEq (Nat.lcm m n : ℤ) x anchor := by
  constructor
  · rintro ⟨hx,hy⟩
    exact Int.modEq_iff_dvd.mpr (Int.coe_lcm_dvd
      (Int.modEq_iff_dvd.mp (hx.trans ha.symm))
      (Int.modEq_iff_dvd.mp (hy.trans hb.symm)))
  · intro hx
    exact ⟨(hx.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left m n))).trans ha,
      (hx.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right m n))).trans hb⟩

end PerfectPower.GeneralCRT
