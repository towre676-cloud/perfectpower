import PerfectPower.Generated.RankOneSources.K22Parts.IntegerDefs
set_option Elab.async false
namespace PerfectPower.Generated.RankOneSources.K22
open PerfectPower.UnitBox PerfectPower.UnitPremises PerfectPower.RankOne
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk0_13 : (List.range' (13 * 2000) 2000).all (slabSliceB 9 (-14) η0 c0) = true := by
  rw [show slabSliceB 9 (-14) η0 c0 = PerfectPower.RankOneIntegerSlab.slice 9 (-14) η0 c0 scaled from
    funext (fun l => PerfectPower.RankOneIntegerSlab.slice_eq scaled_matches 9 (-14) η0 l)]
  decide +kernel


end PerfectPower.Generated.RankOneSources.K22
