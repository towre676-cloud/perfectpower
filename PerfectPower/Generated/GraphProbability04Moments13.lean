import PerfectPower.Generated.GraphProbability04Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_104 : det (DeterminantalEvents.padded K ({3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,-1,0,1,0;(-1/4),0,(-1/4),0,(-1/4),0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,(1/4)]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_105 : det (DeterminantalEvents.padded K ({0,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,-1,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_106 : det (DeterminantalEvents.padded K ({1,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,-1,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;(-1/4),0,(-1/4),0,(-1/4),0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,(1/4)]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_107 : det (DeterminantalEvents.padded K ({0,1,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,-1,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_108 : det (DeterminantalEvents.padded K ({2,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({2,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({2,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,-1,0,1,0;0,0,-1,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,(1/3),0,(1/3),0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_109 : det (DeterminantalEvents.padded K ({0,2,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,2,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,(-1/3),0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,-1,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,(1/3),0,(1/3),0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_110 : det (DeterminantalEvents.padded K ({1,2,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,2,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,-1,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;0,0,-1,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,0,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_111 : det (DeterminantalEvents.padded K ({0,1,2,3,5,6} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,2,3,5,6} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2,3,5,6} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,-1,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;-1,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,0]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2,3,5,6} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability04
