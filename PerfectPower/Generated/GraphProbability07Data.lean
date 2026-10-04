import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability07
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 4) (Fin 4) ℚ := !![(1/3),0,(1/3),(1/3);0,1,0,0;(1/3),0,(1/3),(1/3);(1/3),0,(1/3),(1/3)]
def O : Fin 3 → Finset (Fin 4) := ![{0,1},{1,2},{1,3}]
def w : Fin 3 → ℚ := ![(1/3),(1/3),(1/3)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability07
