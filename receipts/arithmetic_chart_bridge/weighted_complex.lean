import PerfectPower.UnorderedWeightedGram
namespace ArithmeticWeightedComplex
open PerfectPower.UnorderedWeightedGram
open scoped BigOperators
noncomputable def B : Matrix (Fin 3) (Fin 2) ℂ := !![1,Complex.I;Complex.I,1;1,1]
noncomputable def w : Fin 3 → ℂ := ![1+Complex.I,2-Complex.I,0]
theorem gram_checked : (PerfectPower.CauchyBinet.gram B w).det=12+4*Complex.I := by
  norm_num [PerfectPower.CauchyBinet.gram,B,w,Matrix.det_fin_two,Fin.sum_univ_succ,Complex.star_def]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq, Complex.I_pow_three]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring
theorem unordered_sum_checked :
    (∑ s : Basis (Fin 3) 2, (∏ i, w (canonical s i))*
      star (Matrix.det (fun i j => B (canonical s i) j))*Matrix.det (fun i j => B (canonical s i) j))=12+4*Complex.I := by
  rw [← weighted_gram]; exact gram_checked
#print axioms gram_checked
#print axioms unordered_sum_checked
end ArithmeticWeightedComplex
