import PerfectPower.Generated.GraphProbability04Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_032 : det (DeterminantalEvents.padded K ({5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({5} : Finset (Fin 7)))=((1/3) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,(-1/3),0,(-1/3),0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,(1/3),0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({5} : Finset (Fin 7))=((1/3) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_033 : det (DeterminantalEvents.padded K ({0,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,5} : Finset (Fin 7)))=((1/12) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,(-1/3),0,(-1/3),0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,(1/3),0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,5} : Finset (Fin 7))=((1/12) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_034 : det (DeterminantalEvents.padded K ({1,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,5} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,5} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_035 : det (DeterminantalEvents.padded K ({0,1,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,5} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,5} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_036 : det (DeterminantalEvents.padded K ({2,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({2,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({2,5} : Finset (Fin 7)))=((1/12) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,(-1/3),0,(-1/3),0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,(1/3),0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2,5} : Finset (Fin 7))=((1/12) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_037 : det (DeterminantalEvents.padded K ({0,2,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,2,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2,5} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,(-1/3),0,(-1/3),0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,(1/3),0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2,5} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_038 : det (DeterminantalEvents.padded K ({1,2,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,2,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2,5} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2,5} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_039 : det (DeterminantalEvents.padded K ({0,1,2,5} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,2,5} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2,5} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,-1,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,0,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2,5} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability04
