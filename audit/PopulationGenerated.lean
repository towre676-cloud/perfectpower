import PerfectPower.FiniteDomainCertificate
namespace PerfectPower.GeneratedPopulation
open PerfectPower.FiniteDomainCertificate
private def accepts (x : ℤ) : Prop := ((((((0) + x * (((1) + x * (0))))) % (4)) < (2)) ∨ (((-9) + x * (((0) + x * (((1) + x * (0)))))) = (0)))
private instance : DecidablePred accepts := fun x => by unfold accepts; infer_instance
private def imageMap (x : ℤ) : ℤ := ((0) + x * (((0) + x * (((1) + x * (0))))))
private def transcript : Domain := boundedImage (-12) (12) accepts imageMap

theorem source_complete (z : ℤ) :
    z ∈ evaluate transcript ↔ ∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = z :=
  bounded_image_complete (-12) (12) accepts imageMap z

theorem count_checked : (evaluate transcript).card = 10 := by decide +kernel

theorem selection_0 :
    (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = (0)) ∧
    ∀ z, (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 0 → z = (0) := by
  exact bounded_image_select (-12) (12) accepts imageMap 0 (0)
    (by decide +kernel) (by decide +kernel)

theorem selection_1 :
    (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = (16)) ∧
    ∀ z, (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 3 → z = (16) := by
  exact bounded_image_select (-12) (12) accepts imageMap 3 (16)
    (by decide +kernel) (by decide +kernel)

theorem selection_2 :
    (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = (144)) ∧
    ∀ z, (∃ x : ℤ, (-12) ≤ x ∧ x ≤ (12) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 9 → z = (144) := by
  exact bounded_image_select (-12) (12) accepts imageMap 9 (144)
    (by decide +kernel) (by decide +kernel)

end PerfectPower.GeneratedPopulation

#print axioms PerfectPower.GeneratedPopulation.source_complete
#print axioms PerfectPower.GeneratedPopulation.count_checked
#print axioms PerfectPower.GeneratedPopulation.selection_0
#print axioms PerfectPower.GeneratedPopulation.selection_1
#print axioms PerfectPower.GeneratedPopulation.selection_2
