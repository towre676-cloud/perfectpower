import PerfectPower.CertifiedTelescoping

namespace PerfectPower.Generated.BinomialPower1
open PerfectPower.CertifiedTelescoping
-- Source packet SHA-256: aed04c76d60acefda7e4bf12f8ba929affbb65c7b0df0a6530938639c1b17df2
theorem compiled_recurrence (n : ℕ) :
  (((-2)*(n:ℚ)^0)/((1)*(n:ℚ)^0))*S 1 (n+0) + (((1)*(n:ℚ)^0)/((1)*(n:ℚ)^0))*S 1 (n+1) = 0 := by
  rw [first_power,first_power]
  norm_num
  ring

#print axioms compiled_recurrence
end PerfectPower.Generated.BinomialPower1
