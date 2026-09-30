# Release check

`make verify` was run on commit `e54ef11` (branch `claude/laughing-lamport-qqzdo9`) with a clean working tree and exited with status 0. This file archives the key lines of its output. The Lean build used Lean `leanprover/lean4:v4.20.0` with Mathlib `v4.20.0` compiled from source, and Python 3.11.15 (standard library only). The optional Sage steps (`make crosscheck`, passagemath 10.8.12) are not part of `verify`; their receipts are re-checked in plain Python by it.

```
Build completed successfully.
axiom audit passed: 404 declarations
-- Found 0 errors in 801 declarations (plus 2280 automatically generated ones) in PerfectPower with 15 linters
-- All linting checks passed!
Ran 123 tests in 24.308s
OK
Ran 14 tests in 11.505s (continuation_tests)
OK
19/19 certificates passed (independent audit)
/home/user/perfectpower/PerfectPower/Generated/Runge.lean 17 certificates
/home/user/perfectpower/PerfectPower/Generated/Sandwich.lean 2 certificates
binomial gate OK: {'C(n,2)=m^3': [1, 2], 'C(n,3)=m^2': [1, 2, 3, 4, 50]}
genus-1 gate OK: 400 families, labels {'CONDITIONAL_ON_UNPROVEN_RANK': 1, 'INDEPENDENT_COMPUTATION': 399}, 3 certified hits beyond the scan
Theorem G gate OK: 462 cases, genus computed in 462, places at infinity in 453, 0 disagreements
399 genus-one reduction theorems
1163 Mordell curves without integral points
- Lean declarations audited: **404**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **404**.
descent gate, seed 20260930
nonempty: m^2 = 64*n**3 + (-3120)*n**2 + (50700)*n + (-274699)  (D = 74, t = 4n + (-65))  hits [41]  Lean: OK
empty: m^2 = 8*n**3 + (-132)*n**2 + (726)*n + (-1616)  (D = 285, t = 2n + (-11))  hits []  Lean: OK
descent gate OK
39 entries {'DEFINITION_PROVED_EQUIVALENT': 13, 'TERMS_AGREE_UNPROVED': 23, 'REJECTED': 3}; Mordell: 41 certified lists checked, 0 disagreements, 155 leads -> receipts/oeis_sqrt2_atlas.json
git diff --exit-code -- receipts/ certs/ data/ docs/figures/ PerfectPower/Generated/ README.md audit/axioms_report.txt
verify: OK
```

GitHub Actions CI was not used for this check: its jobs are never assigned a runner (an account-level block; see the README).
