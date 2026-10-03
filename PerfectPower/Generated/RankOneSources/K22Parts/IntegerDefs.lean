import PerfectPower.Generated.RankOneSources.K22Parts.Defs
import PerfectPower.RankOneIntegerSlab
namespace PerfectPower.Generated.RankOneSources.K22
open PerfectPower.UnitBox PerfectPower.UnitPremises PerfectPower.RankOne
open PerfectPower.RankOneIntegerSlab
def scaled : Scaled := ⟨1000000000000000000,-3591405721000000000,-3591405720000000000,1218385000000000000,12898195045648718400,12898195052831529841⟩
theorem scaled_matches : Matches c0 scaled := by unfold Matches; decide +kernel
end PerfectPower.Generated.RankOneSources.K22
