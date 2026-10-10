import PerfectPower.CertifiedTelescoping

namespace PerfectPower.Generated.BinomialPower4
open PerfectPower.CertifiedTelescoping
-- Source packet SHA-256: 9ccc7c37902bf322b12a72cb49e0b1317d385f606551a869f1d3fbd4695592b2
theorem compiled_recurrence (n : ℕ) :
  (((-60)*(n:ℚ)^0 + (-188)*(n:ℚ)^1 + (-192)*(n:ℚ)^2 + (-64)*(n:ℚ)^3)/((8)*(n:ℚ)^0 + (12)*(n:ℚ)^1 + (6)*(n:ℚ)^2 + (1)*(n:ℚ)^3))*S 4 (n+0) + (((-42)*(n:ℚ)^0 + (-82)*(n:ℚ)^1 + (-54)*(n:ℚ)^2 + (-12)*(n:ℚ)^3)/((8)*(n:ℚ)^0 + (12)*(n:ℚ)^1 + (6)*(n:ℚ)^2 + (1)*(n:ℚ)^3))*S 4 (n+1) + (((1)*(n:ℚ)^0)/((1)*(n:ℚ)^0))*S 4 (n+2) = 0 := by
  have h := recurrence4 n
  have hd0 : ((8)*(n:ℚ)^0 + (12)*(n:ℚ)^1 + (6)*(n:ℚ)^2 + (1)*(n:ℚ)^3) ≠ 0 := by positivity
  have hd1 : ((8)*(n:ℚ)^0 + (12)*(n:ℚ)^1 + (6)*(n:ℚ)^2 + (1)*(n:ℚ)^3) ≠ 0 := by positivity
  have hd2 : ((1)*(n:ℚ)^0) ≠ 0 := by positivity
  field_simp
  nlinarith [h]

#print axioms compiled_recurrence
end PerfectPower.Generated.BinomialPower4
