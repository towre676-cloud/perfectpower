import PerfectPower.Exponential  -- every hand-written module; Generated/ is excluded
import PerfectPower.Davenport
import PerfectPower.ABC
import PerfectPower.Binomial
import PerfectPower.RadicalValuation
import PerfectPower.PellGeneral
import PerfectPower.RadicalCount
import PerfectPower.ProfileG
import PerfectPower.Reflect
import PerfectPower.PellExact
import Batteries.Tactic.Lint
/-! Batteries' environment linters over the hand-written library, not the generated certificates (docstrings, unused haves,
simp-normal forms, ...).  Run with `lake env lean audit/Lint.lean`; it must report 0 errors. -/
#lint in PerfectPower
