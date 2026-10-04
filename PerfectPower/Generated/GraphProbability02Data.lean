import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability02
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 5) (Fin 5) ℚ := !![(1/3),0,(1/3),0,(1/3);0,(1/2),0,(1/2),0;(1/3),0,(1/3),0,(1/3);0,(1/2),0,(1/2),0;(1/3),0,(1/3),0,(1/3)]
def O : Fin 6 → Finset (Fin 5) := ![{0,1},{0,3},{1,2},{1,4},{2,3},{3,4}]
def w : Fin 6 → ℚ := ![(1/6),(1/6),(1/6),(1/6),(1/6),(1/6)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability02
