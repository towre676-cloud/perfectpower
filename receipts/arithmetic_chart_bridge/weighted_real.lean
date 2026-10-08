import PerfectPower.UnorderedWeightedGram
namespace ArithmeticWeightedReal
open PerfectPower.UnorderedWeightedGram
open scoped BigOperators
noncomputable def B : Matrix (Fin 3) (Fin 2) ℚ := !![1,0;0,1;1,1]
def w : Fin 3 → ℚ := ![2,3,5]
theorem gram_checked : (PerfectPower.CauchyBinet.gram B w).det=31 := by
  norm_num [PerfectPower.CauchyBinet.gram,B,w,Matrix.det_fin_two,Fin.sum_univ_succ]
theorem unordered_sum_checked :
    (∑ s : Basis (Fin 3) 2, (∏ i, w (canonical s i))*
      star (Matrix.det (fun i j => B (canonical s i) j))*Matrix.det (fun i j => B (canonical s i) j))=31 := by
  rw [← weighted_gram]; exact gram_checked
#print axioms gram_checked
#print axioms unordered_sum_checked
end ArithmeticWeightedReal
