import PerfectPower.Generated.ClassLists.K97Data

/-! Box slices for `k = 97` (part 1). -/

set_option Elab.async false

namespace PerfectPower.Generated.ClassLists.K97

open PerfectPower MordellCubicForm ClassListProof PositiveKCurve ReducibleThue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_4 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_5 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_6 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem slice_7 : boxSliceB 97 6 20 (cs_97.map Prod.fst) certs 7 = true := by decide +kernel

end PerfectPower.Generated.ClassLists.K97
