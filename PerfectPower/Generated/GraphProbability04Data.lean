import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 7) (Fin 7) ℚ := !![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;(1/4),0,(1/4),0,(1/4),0,(1/4)]
def O : Fin 12 → Finset (Fin 7) := ![{0,1},{0,3},{0,5},{1,2},{1,4},{1,6},{2,3},{2,5},{3,4},{3,6},{4,5},{5,6}]
def w : Fin 12 → ℚ := ![(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12),(1/12)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability04
