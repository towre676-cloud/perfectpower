import PerfectPower.Generated.ClassLists.K97Data

/-! Box slices for `k = 97` (part 2). -/

set_option Elab.async false

namespace PerfectPower.Generated.ClassLists.K97

open PerfectPower MordellCubicForm ClassListProof PositiveKCurve ReducibleThue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_8 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_9 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_10 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_11 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 11 = true := by decide +kernel

end PerfectPower.Generated.ClassLists.K97
