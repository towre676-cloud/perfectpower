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
import PerfectPower.RadicalAsymp
import PerfectPower.Atlas
import PerfectPower.Genus1
import PerfectPower.MordellDescent
import PerfectPower.MordellFLT3
import PerfectPower.MordellMinus2
import PerfectPower.MordellMinus4
import PerfectPower.ClassTwo
import PerfectPower.MordellMinus13
import PerfectPower.MordellMinus5
import PerfectPower.MordellMinus6
import PerfectPower.Transport
import PerfectPower.Continuation.DenominatorReduction
import PerfectPower.Continuation.RadicalCountGeneral
import PerfectPower.Continuation.PellCountGeneral
import PerfectPower.Continuation.KappaPositive
import PerfectPower.Continuation.PellPositive
import Batteries.Tactic.Lint
/-! Batteries' environment linters over the hand-written library, not the generated certificates (docstrings, unused haves,
simp-normal forms, ...).  Run with `lake env lean audit/Lint.lean`; it must report 0 errors. -/
#lint in PerfectPower
