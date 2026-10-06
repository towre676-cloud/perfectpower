import PerfectPower.EllipticPointLaw
import PerfectPower.TriplingCoordinates
import PerfectPower.TypedDivisionPackets
import PerfectPower.PolynomialSourceSemantics
import PerfectPower.SubgroupDivisionClosure

#print axioms PerfectPower.EllipticPointLaw.add_refinement
#print axioms PerfectPower.EllipticPointLaw.binary_refinement
#print axioms PerfectPower.TriplingCoordinates.psi_displacement
#print axioms PerfectPower.TriplingCoordinates.expanded_phi
#print axioms PerfectPower.TriplingCoordinates.tripling_numerator
#print axioms PerfectPower.TriplingCoordinates.tripling_x_iff
#print axioms PerfectPower.TypedDivisionPackets.RationalPacket.complete
#print axioms PerfectPower.TypedDivisionPackets.compose_complete
#print axioms PerfectPower.PolynomialSourceSemantics.compile_correct
#print axioms PerfectPower.PolynomialSourceSemantics.equality_correct
#print axioms PerfectPower.SubgroupDivisionClosure.closed_two_three

example : PerfectPower.PolynomialSourceSemantics.evaluate 7
    (.add (.power .variable 2) (.constant (-49)))=0 := by decide +kernel

/-- Composition retains the entire intermediate fibre, not just one anchor. -/
example {G : Type*} [AddCommGroup G] (P Q : G)
    (a : PerfectPower.TypedDivisionPackets.FibrePacket 3 P)
    (b : ∀ H, H ∈ a.points → PerfectPower.TypedDivisionPackets.FibrePacket 2 H) :
    (6 : ℤ) • Q=P ↔ Q ∈ PerfectPower.TypedDivisionPackets.compose 2 3 P a b :=
  PerfectPower.TypedDivisionPackets.compose_complete 2 3 P a b Q
