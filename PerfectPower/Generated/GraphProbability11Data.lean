import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability11
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 4) (Fin 4) ℚ := !![(1/2),0,0,(1/2);0,(1/2),(1/2),0;0,(1/2),(1/2),0;(1/2),0,0,(1/2)]
def O : Fin 4 → Finset (Fin 4) := ![{0,1},{0,2},{1,3},{2,3}]
def w : Fin 4 → ℚ := ![(1/4),(1/4),(1/4),(1/4)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability11
