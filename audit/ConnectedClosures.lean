import PerfectPower.CauchyBinet
import PerfectPower.IntegralRecognition
import PerfectPower.FiniteDomainCertificate

open scoped BigOperators

-- A genuinely rectangular, two-column matrix with three source rows.
example (M : Matrix (Fin 2) (Fin 3) ℚ) (N : Matrix (Fin 3) (Fin 2) ℚ) :
    2 * (M * N).det = ∑ p : Fin 2 → Fin 3,
      Matrix.det (fun i j => M i (p j)) * Matrix.det (fun i j => N (p i) j) := by
  simpa using PerfectPower.CauchyBinet.ordered_cauchy_binet M N

-- Strict half-unit recognition does not require an analytic execution oracle.
example (y : ℤ) (hy : |(101/100 : ℚ) - (y : ℚ)| ≤ 1/40) : y = 1 := by
  exact PerfectPower.IntegralRecognition.integer_unique (101/100) (1/40) y 1
    (by norm_num) hy (by norm_num [abs_of_nonneg])

#print axioms PerfectPower.CauchyBinet.ordered_cauchy_binet
#print axioms PerfectPower.CauchyBinet.weighted_gram
#print axioms PerfectPower.CauchyBinet.gram_det_zero_of_minors_zero
#print axioms PerfectPower.IntegralRecognition.integer_unique
#print axioms PerfectPower.IntegralRecognition.matrix_unique
#print axioms PerfectPower.FiniteDomainCertificate.bounded_image_complete
#print axioms PerfectPower.FiniteDomainCertificate.bounded_image_select

#lint in PerfectPower.CauchyBinet
#lint in PerfectPower.IntegralRecognition
#lint in PerfectPower.FiniteDomainCertificate
