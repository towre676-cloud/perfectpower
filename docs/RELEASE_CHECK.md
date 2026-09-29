# Release check

`make verify` was run on commit `a5081a6` (branch `claude/laughing-lamport-qqzdo9`) with a clean working tree and exited with status 0. This file archives the key lines of its output. The Lean build used Lean `leanprover/lean4:v4.20.0` with Mathlib `v4.20.0` compiled from source, and Python 3.11.15 (standard library only). The optional Sage steps (`make crosscheck`, passagemath 10.8.12) are not part of `verify`; their receipts are re-checked in plain Python by it.

```
Build completed successfully.
axiom audit passed: 163 declarations
-- Found 0 errors in 310 declarations (plus 1226 automatically generated ones) in PerfectPower with 15 linters
-- All linting checks passed!
Ran 66 tests in 14.347s
OK
19/19 certificates passed (independent audit)
/home/user/perfectpower/PerfectPower/Generated/Runge.lean 17 certificates
/home/user/perfectpower/PerfectPower/Generated/Sandwich.lean 2 certificates
binomial gate OK: {'C(n,2)=m^3': [1, 2], 'C(n,3)=m^2': [1, 2, 3, 4, 50]}
genus-1 gate OK: 400 families, labels {'CONDITIONAL_ON_UNPROVEN_RANK': 1, 'INDEPENDENT_COMPUTATION': 399}, 3 certified hits beyond the scan
Theorem G gate OK: 462 cases, genus computed in 462, places at infinity in 453, 0 disagreements
399 genus-one reduction theorems
1163 Mordell curves without integral points
- Lean declarations audited: **163**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **163**.
git diff --exit-code -- receipts/ certs/ data/ docs/figures/ PerfectPower/Generated/ README.md audit/axioms_report.txt
verify: OK
```

GitHub Actions CI was not used for this check: its jobs are never assigned a runner (an account-level block; see the README).
