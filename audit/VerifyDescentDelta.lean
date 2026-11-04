import PerfectPower.DescentDelta
import PerfectPower.DescentDeltaLabel

/-!
Axiom audit for the descent-map modules. Every line must print
exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`.
-/

#print axioms PerfectPower.DescentDelta.delta_zero
#print axioms PerfectPower.DescentDelta.delta_add
#print axioms PerfectPower.DescentDelta.deltaHom_apply
#print axioms PerfectPower.DescentDelta.deltaPhi_comp_phi
#print axioms PerfectPower.DescentDelta.deltaDual_comp_dual
#print axioms PerfectPower.DescentDelta.deltaPhi_comp_phiHom
#print axioms PerfectPower.DescentDelta.deltaDual_comp_dualHom
#print axioms PerfectPower.DescentDelta.phiHom_range_le_deltaPhi_ker
#print axioms PerfectPower.DescentDelta.dualHom_range_le_deltaDual_ker
#print axioms PerfectPower.DescentDelta.deltaDual_image_bound
#print axioms PerfectPower.DescentDelta.deltaPhi_image_bound
#print axioms PerfectPower.DescentDelta.squarefree_divisors_finite
#print axioms PerfectPower.DescentDelta.deltaDual_range_finite
#print axioms PerfectPower.DescentDelta.deltaPhi_range_finite
#print axioms PerfectPower.DescentDelta.squarefree_label_injective
#print axioms PerfectPower.DescentDelta.deltaDual_label_unique
#print axioms PerfectPower.DescentDelta.deltaPhi_label_unique
#print axioms PerfectPower.DescentDelta.delta_label_unique_of_rep
