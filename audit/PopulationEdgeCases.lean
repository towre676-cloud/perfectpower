import PerfectPower.FiniteDomainCertificate
namespace PerfectPower.GeneratedPopulationFixture0
open PerfectPower.FiniteDomainCertificate
private def accepts (x : ℤ) : Prop := True
private instance : DecidablePred accepts := fun x => by unfold accepts; infer_instance
private def imageMap (x : ℤ) : ℤ := ((0) + x * (((1) + x * (0))))
private def transcript : Domain := boundedImage (4) (1) accepts imageMap

theorem source_complete (z : ℤ) :
    z ∈ evaluate transcript ↔ ∃ x : ℤ, (4) ≤ x ∧ x ≤ (1) ∧ accepts x ∧ imageMap x = z :=
  bounded_image_complete (4) (1) accepts imageMap z

theorem count_checked : (evaluate transcript).card = 0 := by decide +kernel

end PerfectPower.GeneratedPopulationFixture0

#print axioms PerfectPower.GeneratedPopulationFixture0.source_complete

#print axioms PerfectPower.GeneratedPopulationFixture0.count_checked
namespace PerfectPower.GeneratedPopulationFixture1
open PerfectPower.FiniteDomainCertificate
private def accepts (x : ℤ) : Prop := True
private instance : DecidablePred accepts := fun x => by unfold accepts; infer_instance
private def imageMap (x : ℤ) : ℤ := ((5) + x * (0))
private def transcript : Domain := boundedImage (-4) (4) accepts imageMap

theorem source_complete (z : ℤ) :
    z ∈ evaluate transcript ↔ ∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = z :=
  bounded_image_complete (-4) (4) accepts imageMap z

theorem count_checked : (evaluate transcript).card = 1 := by decide +kernel

theorem selection_0 :
    (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = (5)) ∧
    ∀ z, (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 0 → z = (5) := by
  exact bounded_image_select (-4) (4) accepts imageMap 0 (5)
    (by decide +kernel) (by decide +kernel)

end PerfectPower.GeneratedPopulationFixture1

#print axioms PerfectPower.GeneratedPopulationFixture1.source_complete

#print axioms PerfectPower.GeneratedPopulationFixture1.count_checked

#print axioms PerfectPower.GeneratedPopulationFixture1.selection_0
namespace PerfectPower.GeneratedPopulationFixture2
open PerfectPower.FiniteDomainCertificate
private def accepts (x : ℤ) : Prop := (¬ ((((((0) + x * (((1) + x * (0))))) % (3)) ≥ (1)) ∨ (((0) + x * (((1) + x * (0)))) = (0))))
private instance : DecidablePred accepts := fun x => by unfold accepts; infer_instance
private def imageMap (x : ℤ) : ℤ := ((3) + x * (((-2) + x * (((1) + x * (0))))))
private def transcript : Domain := boundedImage (-4) (4) accepts imageMap

theorem source_complete (z : ℤ) :
    z ∈ evaluate transcript ↔ ∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = z :=
  bounded_image_complete (-4) (4) accepts imageMap z

theorem count_checked : (evaluate transcript).card = 2 := by decide +kernel

theorem selection_0 :
    (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = (6)) ∧
    ∀ z, (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 0 → z = (6) := by
  exact bounded_image_select (-4) (4) accepts imageMap 0 (6)
    (by decide +kernel) (by decide +kernel)

theorem selection_1 :
    (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = (18)) ∧
    ∀ z, (∃ x : ℤ, (-4) ≤ x ∧ x ≤ (4) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = 1 → z = (18) := by
  exact bounded_image_select (-4) (4) accepts imageMap 1 (18)
    (by decide +kernel) (by decide +kernel)

end PerfectPower.GeneratedPopulationFixture2

#print axioms PerfectPower.GeneratedPopulationFixture2.source_complete

#print axioms PerfectPower.GeneratedPopulationFixture2.count_checked

#print axioms PerfectPower.GeneratedPopulationFixture2.selection_0

#print axioms PerfectPower.GeneratedPopulationFixture2.selection_1
