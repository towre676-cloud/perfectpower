import PerfectPower.ArithmeticSimplifier
namespace PerfectPower.ArithmeticSimplifierExamples

theorem coupled_system :
    (∃ x y z : ℤ, x ^ 2 = y ^ 3 ∧ z = x + 1 ∧ z > 3) ↔
    ∃ t : ℤ, t ^ 3 + 1 > 3 := by
  constructor
  · rintro ⟨x,y,z,h,rfl,hz⟩
    obtain ⟨t,rfl,rfl⟩ := (PerfectPower.FormulaTransport.square_eq_cube x y).mp h
    exact ⟨t,hz⟩
  · rintro ⟨t,ht⟩
    exact ⟨t^3,t^2,t^3+1,by ring,rfl,ht⟩

theorem signed_fifth_cube :
    ((-32 : ℤ) ^ 3 = (-8 : ℤ) ^ 5) ∧
    ∃ t : ℤ, (-32 : ℤ) = t ^ 5 ∧ (-8 : ℤ) = t ^ 3 := by
  constructor
  · norm_num
  · exact (PerfectPower.ArithmeticSimplifier.coprime_power_parameter 3 5
      (by decide) (by decide) (by decide) (-32) (-8)).mp (by norm_num)

theorem cannot_cancel_shared_square :
    ∃ x y : ℤ, x ^ 2 = y ^ 2 ∧ x ≠ y := by
  exact ⟨1,-1,by norm_num,by norm_num⟩

theorem polynomial_pullback_identity (x : ℤ) :
    (x ^ 2 + x) ^ 4 + 1 =
    x ^ 8 + 4*x ^ 7 + 6*x ^ 6 + 4*x ^ 5 + x ^ 4 + 1 := by
  ring

end PerfectPower.ArithmeticSimplifierExamples
#print axioms PerfectPower.ArithmeticSimplifierExamples.coupled_system
#print axioms PerfectPower.ArithmeticSimplifierExamples.signed_fifth_cube
#print axioms PerfectPower.ArithmeticSimplifierExamples.cannot_cancel_shared_square
#print axioms PerfectPower.ArithmeticSimplifierExamples.polynomial_pullback_identity
