# Lean-native effective power equations

Import `PerfectPower.Tactic.NativePower`, then write:

```lean
import PerfectPower.Tactic.NativePower

native_near_square quartic_one for 0, 0, 1
#check quartic_one_complete
#eval quartic_one

native_near_square shifted_four for 1, 0, 4
#check shifted_four_complete
```

The command computes the finite point set in Lean and emits its completeness theorem. It supports the family `y^2 = (x^2 + a*x + b)^2 + k` with closed integer coefficients and `k ≠ 0`. It proves the search rectangle from those coefficients, rather than accepting a caller-supplied bound. The result covers negative as well as positive integer coordinates. It uses `decide +kernel` for the point-set equality and rejects `k = 0`.

Import `PerfectPower.FunctionFieldPower` for the generic finite-field polynomial Fermat classification. `FunctionFieldPower.complete` reduces `f^n + g^n = 1` to the finite field's constant points when `n ≥ 3` and `(n : K) ≠ 0`. `FunctionFieldPower.Seven.quartic_complete` is the complete `F_7[t]` instance, with its eight constant pairs. `frobenius_family` records the excluded characteristic-exponent family explicitly.

Run `bash scripts/check_native_power.sh` after installing the repository's pinned Lean toolchain and Mathlib cache. The focused audit computes six native point lists, checks their completeness and standard axioms, checks the finite-field result, and exercises rejection of a wrong list and of the infinite `k = 0` case. This is a modular check of the new sources, not a full build of every historical theorem. The mathematical scope and remaining research program are developed in [the monograph](NATIVE_POWER_MONOGRAPH.md).
