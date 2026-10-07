# Local power-free arithmetic continuation

Read docs/POWER_FREE_LOCAL_MONOGRAPH.md and receipts/power_free_local/summary.json. The exact local route is implemented in python/perfectpower/power_free_local.py; the reusable eleven-theorem module is PerfectPower/PowerFreeLocal.lean. The query service exposes power_free_local, power_free_wheel and native_power_free_certificate. Run make power-free-check with the repository's pinned Lean toolchain.

The all-prime certificate uses an integer Bezout identity and native root-set equalities. It handles signed, nonmonic and squarefree reducible inputs. Repeated-factor all-prime queries are unsupported; finite root lifting and avoidance wheels still handle them. Do not interpret local admissibility as a global density result or wheel survivors as globally power-free values.

The next bounded mathematical extension is a general fixed-divisor theorem via integer finite differences, which could remove the derivative-coprimality restriction. The next formal implementation extension is proving the lifting producer and finite wheel assembly, then connecting their typed data to the generic JSON interpreter. Preserve all incoming flavor and elliptic commits on the existing working branch.
