import PerfectPower.CertifiedTelescoping

namespace PerfectPower.Generated.BinomialPower2
open PerfectPower.CertifiedTelescoping
-- Source packet SHA-256: aa6c5044f0dc307c908bf151e6992c38f9c57639ef6cdabcad99b1dc92ec1c50
theorem compiled_recurrence (n : ℕ) :
  (((-2)*(n:ℚ)^0 + (-4)*(n:ℚ)^1)/((1)*(n:ℚ)^0 + (1)*(n:ℚ)^1))*S 2 (n+0) + (((1)*(n:ℚ)^0)/((1)*(n:ℚ)^0))*S 2 (n+1) = 0 := by
  have h := recurrence2 n
  have hd0 : ((1)*(n:ℚ)^0 + (1)*(n:ℚ)^1) ≠ 0 := by positivity
  have hd1 : ((1)*(n:ℚ)^0) ≠ 0 := by positivity
  field_simp
  nlinarith [h]

#print axioms compiled_recurrence
end PerfectPower.Generated.BinomialPower2
