import PerfectPower.DresdenCalendar
namespace PerfectPower.DresdenAudit

theorem huge_calendar_count :
    (PerfectPower.ResiduePopulation.values ⟨0,10^30,18980,0⟩).card =
      52687038988408851422550053 := by
  rw [PerfectPower.ResiduePopulation.card_values _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num [PerfectPower.ResiduePopulation.count] <;> rfl

theorem lunar_405_crossing :
    8052-405 = (4026-405) + (8052-4026-405) + 405 := by
  exact PerfectPower.DresdenCalendar.lunar_split_count 8052 4026 405 (by norm_num) (by norm_num)

theorem duplicate_tail_example (x : ℤ) :
    ((10 ≤ x ∧ Int.ModEq 5 x 10) ∨ (25 ≤ x ∧ Int.ModEq 5 x 25)) ↔
      10 ≤ x ∧ Int.ModEq 5 x 10 := by
  have h : Int.ModEq 5 (10:ℤ) 25 := by decide
  simpa using PerfectPower.DresdenCalendar.restart_activation 10 25 x 5 h

end PerfectPower.DresdenAudit
#print axioms PerfectPower.DresdenCalendar.polynomial_pullback
#print axioms PerfectPower.DresdenCalendar.condition_pullback
#print axioms PerfectPower.DresdenCalendar.chart_injective
#print axioms PerfectPower.DresdenCalendar.integer_pullback
#print axioms PerfectPower.DresdenCalendar.accepted_membership
#print axioms PerfectPower.DresdenCalendar.accepted_image
#print axioms PerfectPower.DresdenCalendar.accepted_count
#print axioms PerfectPower.DresdenCalendar.affine_rank
#print axioms PerfectPower.DresdenCalendar.accepted_rank
#print axioms PerfectPower.DresdenCalendar.selected_day
#print axioms PerfectPower.DresdenCalendar.calendar_compatibility
#print axioms PerfectPower.DresdenCalendar.calendar_period
#print axioms PerfectPower.DresdenCalendar.joint_venus_period
#print axioms PerfectPower.DresdenCalendar.long_count_uinal_carry
#print axioms PerfectPower.DresdenCalendar.long_count_unique
#print axioms PerfectPower.DresdenCalendar.restart_activation
#print axioms PerfectPower.DresdenCalendar.affine_envelope
#print axioms PerfectPower.DresdenCalendar.lunar_window_count
#print axioms PerfectPower.DresdenCalendar.lunar_split_count
#print axioms PerfectPower.DresdenAudit.huge_calendar_count
#print axioms PerfectPower.DresdenAudit.lunar_405_crossing
#print axioms PerfectPower.DresdenAudit.duplicate_tail_example
