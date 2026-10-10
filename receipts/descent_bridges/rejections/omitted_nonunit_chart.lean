import PerfectPower.LocalQuarticBridges
import PerfectPower.IsogenyCoordinates

example : ∀ r s : ZMod 8, (∃ t : ZMod 8, r*t=1) ∨
    s^2 ≠ (-3:ZMod 8)+(-5:ZMod 8)*r^2+(-6:ZMod 8)*r^4 := by decide
