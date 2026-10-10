import PerfectPower.LocalQuarticBridges
import PerfectPower.IsogenyCoordinates

example : ∀ r s : ZMod 8, s^2 ≠ (-3:ZMod 8)*r^4+(-5:ZMod 8)*r^2+(-6) := by decide
