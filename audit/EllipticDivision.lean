import PerfectPower.EllipticDivision
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linter.Lint

open PerfectPower.EllipticDivision

-- The group result is instantiated on Mathlib's actual generalized curve
-- point group, including infinity; no extra arithmetic premise is needed.
example {F : Type*} [Field F] (E : WeierstrassCurve.Affine F)
    (P H Q : E.Point) (hH : (2 : ℤ) • H = P) :
    (2 : ℤ) • Q = P ↔ ∃ T ∈ divisionKernel (G := E.Point) 2, Q = H + T :=
  fibre_eq_coset 2 P H Q hH

-- A nontrivial finite fibre, with both halves and no duplicates.
example (Q : ZMod 8) : (2 : ℤ) • Q = 4 ↔ Q ∈ ([2, 6] : List (ZMod 8)) := by
  have hL : ∀ T : ZMod 8, (2 : ℤ) • T = 0 ↔ T ∈ ([0, 4] : List (ZMod 8)) := by
    decide +kernel
  simpa using fibre_list_complete 2 (4 : ZMod 8) 2 (by decide +kernel) [0, 4] hL Q

-- The target is twice (3,5) on Y² = x³-2; the exact x-coordinate is 129/100.
example : halvingPolynomial (0 : ℚ) 0 (-2) (129 / 100) 3 = 0 := by
  norm_num [halvingPolynomial]

example : ((3 * (3 : ℚ) ^ 2) / (2 * 5)) ^ 2 - 2 * 3 = 129 / 100 := by
  norm_num

-- Generalized model from the retained elliptic witness corpus.
example : (2 * (3 : ℚ) + 1 * 3 + 1) ^ 2 =
    4 * 3 ^ 3 + (1 ^ 2 + 4 * (-1 / 4)) * 3 ^ 2 +
      2 * (2 * (-1 / 2) + 1 * 1) * 3 + 1 ^ 2 + 4 * (-9 / 4) := by norm_num

-- Real rational-root transport, not only an abstract existence statement.
example (r : ℚ) : (r - 1 / 2) * (r + 1 / 2) = 0 ↔
    r ∈ ([-1 / 2, 1 / 2] : List ℚ) := by
  simp [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, neg_div, or_comm]

#print axioms divisionKernel
#print axioms mem_divisionKernel
#print axioms fibre_iff
#print axioms fibre_eq_coset
#print axioms fibreEquiv
#print axioms fibre_list_complete
#print axioms translate_injective
#print axioms transport_fibre
#print axioms cubic
#print axioms halvingPolynomial
#print axioms halving_identity
#print axioms doubling_x_iff
#print axioms complete_square_identity
#print axioms complete_square_iff
#print axioms short_translation_identity
#print axioms scaled_root_integral
#print axioms rational_root_list_complete

-- The dedicated lint avoids importing the repository's large generated census.
#lint in PerfectPower.EllipticDivision
