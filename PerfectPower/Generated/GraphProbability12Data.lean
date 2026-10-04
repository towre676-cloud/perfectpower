import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability12
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 3) (Fin 3) ℚ := !![(1/2),(1/2),0;(1/2),(1/2),0;0,0,1]
def O : Fin 2 → Finset (Fin 3) := ![{0,2},{1,2}]
def w : Fin 2 → ℚ := ![(1/2),(1/2)]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability12
