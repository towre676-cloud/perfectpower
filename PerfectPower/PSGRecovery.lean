import PerfectPower.PowerComposition

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace PerfectPower.PSGRecovery

def source (U L Z : ℚ) : ℚ := L^14*U*Z^4 - 4*L^14*U*Z^3 + 4*L^14*U*Z^2 - L^14*Z^3 + L^14*Z^2 - 2*L^13*U*Z^4 + 2*L^13*U*Z^3 + 4*L^13*U*Z^2 + 2*L^13*Z^3 - 8*L^13*Z^2 + 6*L^13*Z + 4*L^12*U^2*Z^4 - 16*L^12*U^2*Z^3 + 16*L^12*U^2*Z^2 + L^12*U*Z^4 - 22*L^12*U*Z^3 + 73*L^12*U*Z^2 - 48*L^12*U*Z - L^12*Z^3 + 7*L^12*Z^2 - 15*L^12*Z + 9*L^12 - 12*L^11*U^2*Z^3 + 24*L^11*U^2*Z^2 - 6*L^11*U*Z^3 + 72*L^11*U*Z^2 - 66*L^11*U*Z + 6*L^10*U^3*Z^4 - 24*L^10*U^3*Z^3 + 24*L^10*U^3*Z^2 - 20*L^10*U^2*Z^4 + 46*L^10*U^2*Z^3 - 2*L^10*U^2*Z^2 - 16*L^10*U^2*Z + 30*L^10*U*Z^3 - 18*L^10*U*Z^2 - 30*L^10*U*Z + 18*L^10*U + 12*L^9*U^3*Z^4 - 48*L^9*U^3*Z^3 + 48*L^9*U^3*Z^2 + 16*L^9*U^2*Z^4 - 72*L^9*U^2*Z^3 + 100*L^9*U^2*Z^2 - 44*L^9*U^2*Z + 4*L^8*U^4*Z^4 - 16*L^8*U^4*Z^3 + 16*L^8*U^4*Z^2 - 34*L^8*U^3*Z^4 + 136*L^8*U^3*Z^3 - 210*L^8*U^3*Z^2 + 112*L^8*U^3*Z - 51*L^8*U^2*Z^3 + 81*L^8*U^2*Z^2 - 45*L^8*U^2*Z + 15*L^8*U^2 + 16*L^7*U^4*Z^4 - 52*L^7*U^4*Z^3 + 40*L^7*U^4*Z^2 - 32*L^7*U^3*Z^4 + 136*L^7*U^3*Z^3 - 236*L^7*U^3*Z^2 + 132*L^7*U^3*Z + L^6*U^5*Z^4 - 4*L^6*U^5*Z^3 + 4*L^6*U^5*Z^2 - 4*L^6*U^4*Z^4 + 51*L^6*U^4*Z^3 - 127*L^6*U^4*Z^2 + 80*L^6*U^4*Z + 64*L^6*U^3*Z^4 - 180*L^6*U^3*Z^3 + 196*L^6*U^3*Z^2 - 108*L^6*U^3*Z + 28*L^6*U^3 + 6*L^5*U^5*Z^4 - 18*L^5*U^5*Z^3 + 12*L^5*U^5*Z^2 - 48*L^5*U^4*Z^4 + 198*L^5*U^4*Z^3 - 252*L^5*U^4*Z^2 + 102*L^5*U^4*Z + 9*L^4*U^5*Z^4 - 18*L^4*U^5*Z^3 + 9*L^4*U^5*Z^2 - 51*L^4*U^4*Z^3 + 141*L^4*U^4*Z^2 - 129*L^4*U^4*Z + 39*L^4*U^4 - 2*L^3*U^5*Z^3 + 4*L^3*U^5*Z^2 - 2*L^3*U^5*Z - 18*L^2*U^5*Z^3 + 54*L^2*U^5*Z^2 - 54*L^2*U^5*Z + 18*L^2*U^5 - U^6*Z^3 + 3*U^6*Z^2 - 3*U^6*Z + U^6

def quotient (W L Z : ℚ) : ℚ := L^4*W^5*Z^4 - 4*L^4*W^5*Z^3 + 4*L^4*W^5*Z^2 + 4*L^4*W^4*Z^4 - 16*L^4*W^4*Z^3 + 16*L^4*W^4*Z^2 + 6*L^4*W^3*Z^4 - 24*L^4*W^3*Z^3 + 24*L^4*W^3*Z^2 + 4*L^4*W^2*Z^4 - 16*L^4*W^2*Z^3 + 16*L^4*W^2*Z^2 + L^4*W*Z^4 - 4*L^4*W*Z^3 + 4*L^4*W*Z^2 + 6*L^3*W^5*Z^4 - 18*L^3*W^5*Z^3 + 12*L^3*W^5*Z^2 + 16*L^3*W^4*Z^4 - 52*L^3*W^4*Z^3 + 40*L^3*W^4*Z^2 + 12*L^3*W^3*Z^4 - 48*L^3*W^3*Z^3 + 48*L^3*W^3*Z^2 - 12*L^3*W^2*Z^3 + 24*L^3*W^2*Z^2 - 2*L^3*W*Z^4 + 2*L^3*W*Z^3 + 4*L^3*W*Z^2 + 9*L^2*W^5*Z^4 - 18*L^2*W^5*Z^3 + 9*L^2*W^5*Z^2 - 4*L^2*W^4*Z^4 + 51*L^2*W^4*Z^3 - 127*L^2*W^4*Z^2 + 80*L^2*W^4*Z - 34*L^2*W^3*Z^4 + 136*L^2*W^3*Z^3 - 210*L^2*W^3*Z^2 + 112*L^2*W^3*Z - 20*L^2*W^2*Z^4 + 46*L^2*W^2*Z^3 - 2*L^2*W^2*Z^2 - 16*L^2*W^2*Z + L^2*W*Z^4 - 22*L^2*W*Z^3 + 73*L^2*W*Z^2 - 48*L^2*W*Z - L^2*Z^3 + L^2*Z^2 - 2*L*W^5*Z^3 + 4*L*W^5*Z^2 - 2*L*W^5*Z - 48*L*W^4*Z^4 + 198*L*W^4*Z^3 - 252*L*W^4*Z^2 + 102*L*W^4*Z - 32*L*W^3*Z^4 + 136*L*W^3*Z^3 - 236*L*W^3*Z^2 + 132*L*W^3*Z + 16*L*W^2*Z^4 - 72*L*W^2*Z^3 + 100*L*W^2*Z^2 - 44*L*W^2*Z - 6*L*W*Z^3 + 72*L*W*Z^2 - 66*L*W*Z + 2*L*Z^3 - 8*L*Z^2 + 6*L*Z - W^6*Z^3 + 3*W^6*Z^2 - 3*W^6*Z + W^6 - 18*W^5*Z^3 + 54*W^5*Z^2 - 54*W^5*Z + 18*W^5 - 51*W^4*Z^3 + 141*W^4*Z^2 - 129*W^4*Z + 39*W^4 + 64*W^3*Z^4 - 180*W^3*Z^3 + 196*W^3*Z^2 - 108*W^3*Z + 28*W^3 - 51*W^2*Z^3 + 81*W^2*Z^2 - 45*W^2*Z + 15*W^2 + 30*W*Z^3 - 18*W*Z^2 - 30*W*Z + 18*W - Z^3 + 7*Z^2 - 15*Z + 9

/-- All 100 recovered source terms agree with the independently saved deweighting. -/
theorem deweighting (W L Z : ℚ) : source (L^2*W) L Z=L^12*quotient W L Z := by
  dsimp [source,quotient]
  ring

theorem zero_scale (W Z : ℚ) : source 0 0 Z=0 :=
  PowerComposition.deweighting_zero source quotient deweighting W Z

theorem nonzero_chart (W L Z : ℚ) (hL : L ≠ 0) :
    source (L^2*W) L Z=0 ↔ quotient W L Z=0 :=
  PowerComposition.deweighting_nonzero source quotient deweighting W L Z hL

theorem specialized_coefficients (W : ℚ) : quotient W 1 2=
    -9+270*W-159*W^2+4*W^3-55*W^4+14*W^5-W^6 := by
  dsimp [quotient]
  ring

/-- A matching outer coefficient ratio does not imply reversal symmetry. -/
theorem reversal_obstruction : (270:ℚ) ≠ 9*14 := by norm_num

end PerfectPower.PSGRecovery
