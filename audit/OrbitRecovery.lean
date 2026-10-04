import PerfectPower.Generated.OrbitRecovery
#print axioms PerfectPower.OrbitRecovery.transport
#print axioms PerfectPower.OrbitRecovery.zero_output
#print axioms PerfectPower.OrbitRecovery.invariant_zero
#print axioms PerfectPower.OrbitRecovery.matrix_zero
#print axioms PerfectPower.OrbitRecovery.lift_obstruction
#print axioms PerfectPower.Generated.OrbitRecovery.A048739_all
#print axioms PerfectPower.Generated.OrbitRecovery.A052995_all
#print axioms PerfectPower.Generated.OrbitRecovery.A078057_all
#print axioms PerfectPower.Generated.OrbitRecovery.A128588_all
#print axioms PerfectPower.Generated.OrbitRecovery.A176981_all
#print axioms PerfectPower.Generated.OrbitRecovery.A212804_all
#print axioms PerfectPower.Generated.OrbitRecovery.A373566_all

-- A corrupted entry in the first actual receiver cannot become a certificate.
example : True := by
  fail_if_success
    have bad : PerfectPower.Generated.OrbitRecovery.A048739_C 0 0 = 0 := by decide +kernel
  trivial
