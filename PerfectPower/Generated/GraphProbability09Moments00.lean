import PerfectPower.Generated.GraphProbability09Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability09
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_000 : det (DeterminantalEvents.padded K (∅ : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O (∅ : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K (∅ : Finset (Fin 3)))=(1 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,0,1]) (!![1,0,0;0,1,0;0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O (∅ : Finset (Fin 3))=(1 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_001 : det (DeterminantalEvents.padded K ({0} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({0} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({0} : Finset (Fin 3)))=(1 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,0,1]) (!![1,0,0;0,1,0;0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0} : Finset (Fin 3))=(1 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_002 : det (DeterminantalEvents.padded K ({1} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({1} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({1} : Finset (Fin 3)))=((1/2) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,0,1]) (!![1,0,0;0,(1/2),(1/2);0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1} : Finset (Fin 3))=((1/2) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_003 : det (DeterminantalEvents.padded K ({0,1} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({0,1} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1} : Finset (Fin 3)))=((1/2) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,0,1]) (!![1,0,0;0,(1/2),(1/2);0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1} : Finset (Fin 3))=((1/2) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_004 : det (DeterminantalEvents.padded K ({2} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({2} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({2} : Finset (Fin 3)))=((1/2) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,(-1/2),1]) (!![1,0,0;0,1,0;0,0,(1/2)]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2} : Finset (Fin 3))=((1/2) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_005 : det (DeterminantalEvents.padded K ({0,2} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({0,2} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2} : Finset (Fin 3)))=((1/2) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,(-1/2),1]) (!![1,0,0;0,1,0;0,0,(1/2)]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2} : Finset (Fin 3))=((1/2) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_006 : det (DeterminantalEvents.padded K ({1,2} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({1,2} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2} : Finset (Fin 3)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,-1,1]) (!![1,0,0;0,(1/2),(1/2);0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2} : Finset (Fin 3))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_007 : det (DeterminantalEvents.padded K ({0,1,2} : Finset (Fin 3)))=FiniteGraphProbability.inclusion w O ({0,1,2} : Finset (Fin 3)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2} : Finset (Fin 3)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0;0,1,0;0,-1,1]) (!![1,0,0;0,(1/2),(1/2);0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2} : Finset (Fin 3))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability09
