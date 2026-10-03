import PerfectPower.RankOne
set_option Elab.async false
namespace PerfectPower.Generated.RankOneSources.K22
open PerfectPower.UnitBox PerfectPower.UnitPremises PerfectPower.RankOne
/-! ### Source 0: `F = (-1, -6, -3, -4)`, `z³ = (9) z + (-14)`, shift `h = 2` -/

/-- The fundamental unit `η` (`σ(η) > 1`) of source 0. -/
def η0 : Z3 := (388537, (-357959), 99671)

/-- `ε = η⁻¹` for source 0. -/
def ε0 : Z3 := ((-199), 609, 185)

/-- The rank-one certificate for source 0. -/
def c0 : Cert := ⟨(-3591405721 / 1000000000 : ℚ), (-89785143 / 25000000 : ℚ), (243677 / 200000 : ℚ), 99671⟩

theorem h1_0 : mul 9 (-14) η0 ε0 = (1, 0, 0) := by decide

theorem h2_0 : mul 9 (-14) ε0 η0 = (1, 0, 0) := by decide

theorem n1_0 : nrm 9 (-14) η0 = 1 := by decide

theorem n2_0 : nrm 9 (-14) ε0 = 1 := by decide

theorem cond_0 : condB 9 (-14) η0 c0 = true := by decide +kernel


end PerfectPower.Generated.RankOneSources.K22
