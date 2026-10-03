import PerfectPower.WeightedNorm107

namespace PerfectPower.Norm107Consumer
/-- The arithmetic atom can be replaced everywhere by this finite point formula. -/
theorem atom_iff (u v : ℤ) : u^3+4*v^3=107 ↔ u= -1 ∧ v=3 :=
  WeightedNorm107.cubic107 u v

def original : Prop := ∃ u v : ℤ, u^3+4*v^3=107 ∧ 0 ≤ u
/-- Exact whole-query unsatisfiability, including the extra nonnegative constraint. -/
theorem original_iff_false : original ↔ False := by
  constructor
  · rintro ⟨u,v,h,hpos⟩
    have hu := ((atom_iff u v).mp h).1
    omega
  · exact False.elim
end PerfectPower.Norm107Consumer
#print axioms PerfectPower.Norm107Consumer.original_iff_false
