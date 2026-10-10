import PerfectPower.CertifiedTelescoping

namespace PerfectPower.Generated.BinomialPower3
open PerfectPower.CertifiedTelescoping
-- Source packet SHA-256: bc5cb5ef5b99df60dada7c9009fdc424d80dd269bc25ac7eb0638337ad8899bd
theorem compiled_recurrence (n : ℕ) :
  (((-8)*(n:ℚ)^0 + (-16)*(n:ℚ)^1 + (-8)*(n:ℚ)^2)/((4)*(n:ℚ)^0 + (4)*(n:ℚ)^1 + (1)*(n:ℚ)^2))*S 3 (n+0) + (((-16)*(n:ℚ)^0 + (-21)*(n:ℚ)^1 + (-7)*(n:ℚ)^2)/((4)*(n:ℚ)^0 + (4)*(n:ℚ)^1 + (1)*(n:ℚ)^2))*S 3 (n+1) + (((1)*(n:ℚ)^0)/((1)*(n:ℚ)^0))*S 3 (n+2) = 0 := by
  have h := recurrence3 n
  have hd0 : ((4)*(n:ℚ)^0 + (4)*(n:ℚ)^1 + (1)*(n:ℚ)^2) ≠ 0 := by positivity
  have hd1 : ((4)*(n:ℚ)^0 + (4)*(n:ℚ)^1 + (1)*(n:ℚ)^2) ≠ 0 := by positivity
  have hd2 : ((1)*(n:ℚ)^0) ≠ 0 := by positivity
  field_simp
  nlinarith [h]

#print axioms compiled_recurrence
end PerfectPower.Generated.BinomialPower3
