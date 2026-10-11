import PerfectPower.RealVisibility
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open PerfectPower.PlanarCertificates
namespace Crossing
def polygons : List (List (ℚ × ℚ)) := [[(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))),(((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))),(((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))]]
def start : ℚ × ℚ := (((-1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
def finish : ℚ × ℚ := (((3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
theorem real_hit : PerfectPower.RealVisibility.blockedFormula polygons start finish ((1 : ℚ)/(2 : ℚ)) = true := by decide +kernel
theorem real_blocked : ¬PerfectPower.RealVisibility.FreeSegment polygons start finish :=
  PerfectPower.RealVisibility.blocked_segment _ _ _ ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num) real_hit
#print axioms real_blocked
end Crossing
