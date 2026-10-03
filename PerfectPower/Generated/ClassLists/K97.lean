import PerfectPower.Generated.ClassLists.K97S0
import PerfectPower.Generated.ClassLists.K97S1
import PerfectPower.Generated.ClassLists.K97S2
import PerfectPower.Generated.ClassLists.K97S3

/-! The box, the class list and the curve theorem for `k = 97` (data in `K97Data`). -/

set_option Elab.async false

namespace PerfectPower.Generated.ClassLists.K97

open PerfectPower MordellCubicForm ClassListProof PositiveKCurve ReducibleThue

theorem box : boxCertB 97 6 20 (cs_97.map Prod.fst) certs = true :=
  boxCertB_of_slices fun i hi => by
    simp only [show (2 * (6 : ℤ) + 1).toNat = 13 by rfl] at hi
    interval_cases i
    exacts [slice_0, slice_1, slice_2, slice_3, slice_4, slice_5, slice_6, slice_7, slice_8, slice_9, slice_10, slice_11, slice_12]

/-- **`ClassList 97`, proved.** -/
theorem classList : ClassList 97 (cs_97.map Prod.fst) :=
  classList_of (by norm_num) P_ok (by simp only [P]; norm_num) (by simp only [P]; norm_num)
    (by simp only [P]; norm_num) (by norm_num) (by norm_num) box

/-- **`y² = x³ + 97`: the integral points are exactly [(18, (-77)), (18, 77)]**, with no premise. -/
theorem plus97 (x y : ℤ) : y ^ 2 = x ^ 3 + 97 ↔ (x, y) ∈ ([(18, (-77)), (18, 77)] : List (ℤ × ℤ)) :=
  complete_of_sols classList sols_97 (by decide +kernel) x y

end PerfectPower.Generated.ClassLists.K97
