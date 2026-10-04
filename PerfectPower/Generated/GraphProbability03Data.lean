import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability03
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 6) (Fin 6) ℚ := !![(1/3),0,(1/3),0,(1/3),0;0,(1/3),0,(1/3),0,(1/3);(1/3),0,(1/3),0,(1/3),0;0,(1/3),0,(1/3),0,(1/3);(1/3),0,(1/3),0,(1/3),0;0,(1/3),0,(1/3),0,(1/3)]
def O : Fin 9 → Finset (Fin 6) := ![{0,1},{0,3},{0,5},{1,2},{1,4},{2,3},{2,5},{3,4},{4,5}]
def w : Fin 9 → ℚ := ![(1/9),(1/9),(1/9),(1/9),(1/9),(1/9),(1/9),(1/9),(1/9)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability03
