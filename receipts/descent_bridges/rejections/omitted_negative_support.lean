import PerfectPower.LocalQuarticBridges
import PerfectPower.IsogenyCoordinates

example : ∀ d ∈ Finset.Icc (-12:ℤ) 12,
    (∀ e ∈ ([2,3]:List ℤ), ¬e*e∣d) → d ∣ (-12:ℤ) →
    d ∈ ([1,2,3,6]:List ℤ) := by decide
