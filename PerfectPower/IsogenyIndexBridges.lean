import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Ker

namespace PerfectPower.IsogenyIndexBridges

/-- The composed image index includes the second map's kernel correction. -/
theorem composition_index {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (g : H →+ G) :
    (g.comp f).range.index = (f.range ⊔ g.ker).index*g.range.index := by
  rw [AddMonoidHom.range_comp,AddSubgroup.index_map]

/-- The kernel correction is measured by an actual subgroup relative index. -/
theorem kernel_correction {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (g : H →+ G) :
    f.range.relindex (f.range ⊔ g.ker)*(f.range ⊔ g.ker).index=f.range.index := by
  exact AddSubgroup.relindex_mul_index le_sup_left

/-- A doubling factorization yields the corrected descent index equation. -/
theorem doubling_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (g : H →+ G) (double : G →+ G)
    (hdouble : g.comp f=double) :
    f.range.relindex (f.range ⊔ g.ker)*double.range.index=
      f.range.index*g.range.index := by
  rw [← hdouble,composition_index,← mul_assoc,kernel_correction]

/-- Kernel containment is an additional hypothesis, never silently discarded. -/
theorem composition_index_of_kernel_le {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (g : H →+ G) (hker : g.ker ≤ f.range) :
    (g.comp f).range.index=f.range.index*g.range.index := by
  rw [composition_index,sup_of_le_left hker]

end PerfectPower.IsogenyIndexBridges
