# Release check

`make verify` was run on commit `47eb944` (branch `claude/laughing-lamport-qqzdo9`) with a clean working tree and exited with status 0. This file archives the key lines of its output. The Lean build used Lean `leanprover/lean4:v4.20.0` with Mathlib `v4.20.0` compiled from source, and Python 3.11.15 (standard library only). The optional Sage/PARI steps (`make crosscheck`, passagemath 10.8.12) are not part of `verify`; their receipts are re-checked in plain Python by it. `crosscheck/branch_thue_pari.py` was run for this release (`receipts/mordell_branch_thue.json`); `expert_push/src/sage_mordell.py` was not.

```
Build completed successfully.
axiom audit passed: 640 declarations
-- Found 0 errors in 974 declarations (plus 2709 automatically generated ones) in PerfectPower with 15 linters
-- All linting checks passed!
Ran 146 tests in 22.895s
OK
Ran 14 tests in 10.449s (continuation_tests)
OK
Ran 10 tests in 0.025s (expert_push)
OK
19/19 certificates passed
binomial gate OK: {'C(n,2)=m^3': [1, 2], 'C(n,3)=m^2': [1, 2, 3, 4, 50]}
genus-1 gate OK: 400 families, labels {'CONDITIONAL_ON_UNPROVEN_RANK': 1, 'INDEPENDENT_COMPUTATION': 399}, 3 certified hits beyond the scan
Theorem G gate OK: 462 cases, genus computed in 462, places at infinity in 453, 0 disagreements
399 genus-one reduction theorems
1163 Mordell curves without integral points
59 curves y^2 = x^3 - D: 26 complete lists emitted, 33 with open branches; complete lists agree with Sage 26/26, with published counts 26/26; ranks {'0': 10, '1': 12, '2': 4}
140 candidate entries {'PROVED': 69, 'NOT_TRANSLATED': 71} -> PerfectPower/Generated/OEISAuto.lean
phi: 57 entries {'DEFINITION_PROVED_EQUIVALENT': 15, 'TERMS_AGREE_UNPROVED': 18, 'TRANSPORTED_FROM_DUPLICATE': 1, 'REJECTED': 20, 'EXCEPTIONAL_SET_PROVED': 3}
sqrt3: 19 entries {'DEFINITION_PROVED_EQUIVALENT': 8, 'TERMS_AGREE_UNPROVED': 10, 'REJECTED': 1}
sqrt2: 39 entries {'DEFINITION_PROVED_EQUIVALENT': 29, 'TERMS_AGREE_UNPROVED': 5, 'TRANSPORTED_WITH_SHIFT': 1, 'EXCEPTIONAL_SET_PROVED': 3, 'TRANSPORTED_FROM_DUPLICATE': 1}; Mordell: 67 certified lists checked, 0 disagreements, 129 leads -> receipts/oeis_sqrt2_atlas.json
155 unresolved curves (59 with k < 0): {'CLASS_3': 12, 'ELEMENT_CUBE': 1, 'NONMAXIMAL': 34, 'NONMAXIMAL_CUBE': 6, 'NOT_COPRIME': 36, 'REAL_QUADRATIC': 96, 'UNIT_BEYOND_PM1': 1}
  expert scan joined: 155 curves, 98 nonempty, 155/155 match the published count
descent gate OK
verify: OK
```

GitHub Actions CI was not used for this check: its jobs are never assigned a runner (an account-level block; see the README).
