import PerfectPower.SemilinearCapacity
import PerfectPower.SignedPowerCharts

namespace PerfectPower.SemilinearExamples

/-- A huge residue interval is counted by a proof, without scanning. -/
theorem huge_count :
    ((Finset.Icc (-1000000000000000000000000000000 : ℤ) 1000000000000000000000000000000).filter (fun n => n % 13 = 7)).card = 153846153846153846153846153846 := by
  native_residue_count

/-- The same proof assembles multiple disjoint residues. -/
theorem huge_three_residues :
    ((Finset.Icc (-1000000000000000000000000000000 : ℤ) 1000000000000000000000000000000).filter
      (fun n => n % 13 ∈ ({0,1,12} : Finset ℤ))).card = 461538461538461538461538461541 := by
  rw [PerfectPower.SemilinearCapacity.residue_set_count _ _ _ _ (by norm_num)
    (by intro r hr; simp only [Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl <;> norm_num)]
  norm_num [Int.toNat]

/-- Both signs survive when the original exponents are even. -/
theorem six_four_charts (x y : ℤ) :
    x ^ 6 = y ^ 4 ↔ ∃ (t : ℕ) (sx sy : ℤ),
      (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧ sx ^ 6 = sy ^ 4 ∧
      x = sx * (t : ℤ) ^ 2 ∧ y = sy * (t : ℤ) ^ 3 ∧
      (t = 0 → sx = 1 ∧ sy = 1) := by
  simpa using PerfectPower.SignedPowerCharts.gcd_signed_charts 6 4
    (by norm_num) (by norm_num) x y

/-- An enormous translated objective on a disconnected residue domain
has exactly two minimizers. -/
theorem huge_lattice_ties (x : ℤ) (hx : x % 7 = 2 ∨ x % 7 = 5) :
    (∀ y : ℤ, y % 7 = 2 ∨ y % 7 = 5 →
      (x - 7000000000000000000000000000000) ^ 2 ≤ (y - 7000000000000000000000000000000) ^ 2) ↔
      x = 6999999999999999999999999999998 ∨ x = 7000000000000000000000000000002 := by
  have lower : ∀ y : ℤ, y % 7 = 2 ∨ y % 7 = 5 →
      4 ≤ (y - 7000000000000000000000000000000) ^ 2 := by
    intro y hy
    have gap : y - 7000000000000000000000000000000 ≤ -2 ∨ 2 ≤ y - 7000000000000000000000000000000 := by omega
    rcases gap with h | h <;> nlinarith
  constructor
  · intro h
    have hlo := lower x hx
    have hhi := h 7000000000000000000000000000002 (by norm_num)
    have he : (x - 7000000000000000000000000000000) ^ 2 = 4 := by nlinarith
    have bounds : -2 ≤ x - 7000000000000000000000000000000 ∧ x - 7000000000000000000000000000000 ≤ 2 := by
      constructor <;> nlinarith
    have gap : x - 7000000000000000000000000000000 ≤ -2 ∨ 2 ≤ x - 7000000000000000000000000000000 := by omega
    omega
  · rintro (rfl | rfl) <;> intro y hy <;> simpa using lower y hy

end PerfectPower.SemilinearExamples

#print axioms PerfectPower.SemilinearExamples.huge_count
#print axioms PerfectPower.SemilinearExamples.huge_three_residues
#print axioms PerfectPower.SemilinearExamples.six_four_charts
#print axioms PerfectPower.SemilinearExamples.huge_lattice_ties
