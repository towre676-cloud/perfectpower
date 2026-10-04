import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability05
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 6) (Fin 6) ℚ := !![(1/4),0,(1/4),0,(1/4),(1/4);0,(1/2),0,(1/2),0,0;(1/4),0,(1/4),0,(1/4),(1/4);0,(1/2),0,(1/2),0,0;(1/4),0,(1/4),0,(1/4),(1/4);(1/4),0,(1/4),0,(1/4),(1/4)]
def O : Fin 8 → Finset (Fin 6) := ![{0,1},{0,3},{1,2},{1,4},{1,5},{2,3},{3,4},{3,5}]
def w : Fin 8 → ℚ := ![(1/8),(1/8),(1/8),(1/8),(1/8),(1/8),(1/8),(1/8)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability05
