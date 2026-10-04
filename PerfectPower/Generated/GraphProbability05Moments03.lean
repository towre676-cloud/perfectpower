import PerfectPower.Generated.GraphProbability05Data
import PerfectPower.TriangularDeterminant
namespace PerfectPower.GraphProbability05
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inclusion_024 : det (DeterminantalEvents.padded K ({3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({3,4} : Finset (Fin 6)))=((1/8) : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,(-1/2),0,1,0,0;(-1/4),0,(-1/4),0,1,0;0,0,0,0,0,1]) (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,(1/2),0,0;0,0,0,0,(1/4),(1/4);0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({3,4} : Finset (Fin 6))=((1/8) : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_025 : det (DeterminantalEvents.padded K ({0,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({0,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({0,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,(-1/2),0,1,0,0;-1,0,0,0,1,0;0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),(1/4);0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,(1/2),0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_026 : det (DeterminantalEvents.padded K ({1,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({1,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({1,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,-1,0,1,0,0;(-1/4),0,(-1/4),0,1,0;0,0,0,0,0,1]) (!![1,0,0,0,0,0;0,(1/2),0,(1/2),0,0;0,0,1,0,0,0;0,0,0,0,0,0;0,0,0,0,(1/4),(1/4);0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_027 : det (DeterminantalEvents.padded K ({0,1,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({0,1,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,-1,0,1,0,0;-1,0,0,0,1,0;0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),(1/4);0,(1/2),0,(1/2),0,0;0,0,1,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_028 : det (DeterminantalEvents.padded K ({2,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({2,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({2,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;(-1/4),0,1,0,0,0;0,(-1/2),0,1,0,0;0,0,-1,0,1,0;0,0,0,0,0,1]) (!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,(1/4),0,(1/4),(1/4);0,0,0,(1/2),0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({2,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_029 : det (DeterminantalEvents.padded K ({0,2,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({0,2,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({0,2,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;-1,0,1,0,0,0;0,(-1/2),0,1,0,0;-1,0,0,0,1,0;0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),(1/4);0,1,0,0,0,0;0,0,0,0,0,0;0,0,0,(1/2),0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,2,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_030 : det (DeterminantalEvents.padded K ({1,2,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({1,2,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({1,2,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;(-1/4),0,1,0,0,0;0,-1,0,1,0,0;0,0,-1,0,1,0;0,0,0,0,0,1]) (!![1,0,0,0,0,0;0,(1/2),0,(1/2),0,0;0,0,(1/4),0,(1/4),(1/4);0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({1,2,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
theorem inclusion_031 : det (DeterminantalEvents.padded K ({0,1,2,3,4} : Finset (Fin 6)))=FiniteGraphProbability.inclusion w O ({0,1,2,3,4} : Finset (Fin 6)) := by
  have hd : det (DeterminantalEvents.padded K ({0,1,2,3,4} : Finset (Fin 6)))=(0 : ℚ) :=
    TriangularDeterminant.checked _ (!![1,0,0,0,0,0;0,1,0,0,0,0;-1,0,1,0,0,0;0,-1,0,1,0,0;-1,0,0,0,1,0;0,0,0,0,0,1]) (!![(1/4),0,(1/4),0,(1/4),(1/4);0,(1/2),0,(1/2),0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,1]) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)
  have hm : FiniteGraphProbability.inclusion w O ({0,1,2,3,4} : Finset (Fin 6))=(0 : ℚ) := by decide +kernel
  exact hd.trans hm.symm
end PerfectPower.GraphProbability05
