import PerfectPower.Generated.GraphProbability04Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_088 : det (DeterminantalEvents.padded K ({3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;(-1/4),0,(-1/4),0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,-1,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,(1/4),0,(1/4);0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_089 : det (DeterminantalEvents.padded K ({0,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;-1,0,0,0,1,0,0;0,0,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_090 : det (DeterminantalEvents.padded K ({1,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,-1,0,1,0,0,0;(-1/4),0,(-1/4),0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,-1,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,(1/4),0,(1/4);0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_091 : det (DeterminantalEvents.padded K ({0,1,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,-1,0,1,0,0,0;-1,0,0,0,1,0,0;0,0,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_092 : det (DeterminantalEvents.padded K ({2,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({2,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({2,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;0,0,-1,0,1,0,0;0,0,0,0,0,1,0;0,0,-1,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_093 : det (DeterminantalEvents.padded K ({0,2,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,2,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;-1,0,0,0,1,0,0;0,0,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_094 : det (DeterminantalEvents.padded K ({1,2,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,2,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,-1,0,1,0,0,0;0,0,-1,0,1,0,0;0,0,0,0,0,1,0;0,0,-1,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_095 : det (DeterminantalEvents.padded K ({0,1,2,3,4,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,2,3,4,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2,3,4,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,-1,0,1,0,0,0;-1,0,0,0,1,0,0;0,0,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2,3,4,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability04
