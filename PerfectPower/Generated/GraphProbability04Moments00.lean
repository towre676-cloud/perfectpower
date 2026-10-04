import PerfectPower.Generated.GraphProbability04Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability04
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_000 : det (DeterminantalEvents.padded K (∅ : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O (∅ : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K (∅ : Finset (Fin 7)))=(1 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O (∅ : Finset (Fin 7))=(1 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_001 : det (DeterminantalEvents.padded K ({0} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0} : Finset (Fin 7)))=((1/4) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0} : Finset (Fin 7))=((1/4) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_002 : det (DeterminantalEvents.padded K ({1} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1} : Finset (Fin 7)))=((1/3) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1} : Finset (Fin 7))=((1/3) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_003 : det (DeterminantalEvents.padded K ({0,1} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1} : Finset (Fin 7)))=((1/12) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1} : Finset (Fin 7))=((1/12) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_004 : det (DeterminantalEvents.padded K ({2} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({2} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({2} : Finset (Fin 7)))=((1/4) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2} : Finset (Fin 7))=((1/4) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_005 : det (DeterminantalEvents.padded K ({0,2} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,2} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,1,0,0,0,0,0;0,0,0,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_006 : det (DeterminantalEvents.padded K ({1,2} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({1,2} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2} : Finset (Fin 7)))=((1/12) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;(-1/4),0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![1,0,0,0,0,0,0;0,(1/3),0,(1/3),0,(1/3),0;0,0,(1/4),0,(1/4),0,(1/4);0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2} : Finset (Fin 7))=((1/12) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_007 : det (DeterminantalEvents.padded K ({0,1,2} : Finset (Fin 7)))=FiniteGraphProbability.inclusion w O ({0,1,2} : Finset (Fin 7)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2} : Finset (Fin 7)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0,0;0,1,0,0,0,0,0;-1,0,1,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),0,(1/4);0,(1/3),0,(1/3),0,(1/3),0;0,0,0,0,0,0,0;0,0,0,1,0,0,0;0,0,0,0,1,0,0;0,0,0,0,0,1,0;0,0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2} : Finset (Fin 7))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability04
