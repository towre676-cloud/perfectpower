import PerfectPower.Generated.GraphProbability08Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability08
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_008 : det (DeterminantalEvents.padded K ({3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({3} : Finset (Fin 5)))=((1/4) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;(-1/4),0,(-1/4),1,0;0,0,0,0,1]) (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,(1/4),(1/4);0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({3} : Finset (Fin 5))=((1/4) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_009 : det (DeterminantalEvents.padded K ({0,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({0,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({0,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;-1,0,0,1,0;0,0,0,0,1]) (!![(1/4),0,(1/4),(1/4),(1/4);0,1,0,0,0;0,0,1,0,0;0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_010 : det (DeterminantalEvents.padded K ({1,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({1,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({1,3} : Finset (Fin 5)))=((1/4) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;(-1/4),0,(-1/4),1,0;0,0,0,0,1]) (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,(1/4),(1/4);0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,3} : Finset (Fin 5))=((1/4) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_011 : det (DeterminantalEvents.padded K ({0,1,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({0,1,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;-1,0,0,1,0;0,0,0,0,1]) (!![(1/4),0,(1/4),(1/4),(1/4);0,1,0,0,0;0,0,1,0,0;0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_012 : det (DeterminantalEvents.padded K ({2,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({2,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({2,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;(-1/4),0,1,0,0;0,0,-1,1,0;0,0,0,0,1]) (!![1,0,0,0,0;0,1,0,0,0;0,0,(1/4),(1/4),(1/4);0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_013 : det (DeterminantalEvents.padded K ({0,2,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({0,2,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;-1,0,1,0,0;-1,0,0,1,0;0,0,0,0,1]) (!![(1/4),0,(1/4),(1/4),(1/4);0,1,0,0,0;0,0,0,0,0;0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_014 : det (DeterminantalEvents.padded K ({1,2,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({1,2,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;(-1/4),0,1,0,0;0,0,-1,1,0;0,0,0,0,1]) (!![1,0,0,0,0;0,1,0,0,0;0,0,(1/4),(1/4),(1/4);0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_015 : det (DeterminantalEvents.padded K ({0,1,2,3} : Finset (Fin 5)))=FiniteGraphProbability.inclusion w O ({0,1,2,3} : Finset (Fin 5)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2,3} : Finset (Fin 5)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0;0,1,0,0,0;-1,0,1,0,0;-1,0,0,1,0;0,0,0,0,1]) (!![(1/4),0,(1/4),(1/4),(1/4);0,1,0,0,0;0,0,0,0,0;0,0,0,0,0;0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2,3} : Finset (Fin 5))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability08
