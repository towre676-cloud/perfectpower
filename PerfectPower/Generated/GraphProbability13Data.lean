import PerfectPower.FiniteGraphProbability
namespace PerfectPower.GraphProbability13
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def K : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,1]
def O : Fin 1 → Finset (Fin 2) := ![{0,1}]
def w : Fin 1 → ℚ := ![1]
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
end PerfectPower.GraphProbability13
