# Release check

`make verify` was run on commit `af196bd` (branch `claude/laughing-lamport-qqzdo9`) with a clean working tree. It exited with status 0.

This file archives the key lines of its output. The environment was:
- Lean `leanprover/lean4:v4.20.0`, with Mathlib `v4.20.0` compiled from source;
- Python 3.11.15, standard library only.

The optional Sage/PARI steps (`make crosscheck`, passagemath 10.8.12) are not part of `verify`, but `verify` re-checks their receipts in plain Python. For this release three crosscheck scripts were run:
- `crosscheck/branch_thue_pari.py`, which writes `receipts/mordell_branch_thue.json`;
- `crosscheck/thue_fields_pari.py`, which writes `receipts/thue_fields.json`;
- `crosscheck/field756_pilot.py`, which writes `receipts/field756_pilot.json`.

```
Build completed successfully.
axiom audit passed: 697 declarations
-- Found 0 errors in 1032 declarations (plus 2986 automatically generated ones) in PerfectPower with 15 linters
-- All linting checks passed!
Ran 169 tests (5 z3 adapter tests skipped: z3-solver is optional)
OK
Ran 14 tests in 9.743s (continuation_tests)
OK
Ran 10 tests in 0.023s (expert_push)
OK
Ran 8 tests in 0.008s (galois_merge)
OK
19/19 certificates passed
binomial gate OK: {'C(n,2)=m^3': [1, 2], 'C(n,3)=m^2': [1, 2, 3, 4, 50]}
genus-1 gate OK: 400 families, labels {'CONDITIONAL_ON_UNPROVEN_RANK': 1, 'INDEPENDENT_COMPUTATION': 399}, 3 certified hits beyond the scan
Theorem G gate OK: 462 cases, genus computed in 462, places at infinity in 453, 0 disagreements
399 genus-one reduction theorems
1163 Mordell curves without integral points
36 registry entries, all checked against their Lean statements -> receipts/mordell_registry.json
25 plan theorems -> PerfectPower/Generated/Plans.lean
59 curves y^2 = x^3 - D: 26 complete lists emitted, 33 with open branches; complete lists agree with Sage 26/26, with published counts 26/26; ranks {'0': 10, '1': 12, '2': 4}
56 (9, 9, -3) exceptional [2, 3, 5, 7] all witnesses found
57 (9, 21, -2) exceptional [2, 3, 5, 7] all witnesses found
{'classes_open': 66, 'unit_leaves_total': 189, 'distinct_unit_equations': 109, 'unit_equations_shared_by_several_classes': 24, ...}
branch adapter: 474 edges, 0 cross repo classes, 79 components vs 79 classes; restricted edges 0
corpus adapter: 144 .seq files, B-index matches [('A000129', [0]), ('A048624', [2]), ('A069306', [1])]
140 candidate entries {'PROVED': 69, 'NOT_TRANSLATED': 71} -> PerfectPower/Generated/OEISAuto.lean
sqrt2: 39 entries {'DEFINITION_PROVED_EQUIVALENT': 29, 'TERMS_AGREE_UNPROVED': 5, 'TRANSPORTED_WITH_SHIFT': 1, 'EXCEPTIONAL_SET_PROVED': 3, 'TRANSPORTED_FROM_DUPLICATE': 1}; Mordell: 77 certified lists checked, 0 disagreements, 119 leads -> receipts/oeis_sqrt2_atlas.json
155 unresolved curves (59 with k < 0): {'CLASS_3': 12, 'ELEMENT_CUBE': 1, 'NONMAXIMAL': 34, 'NONMAXIMAL_CUBE': 6, 'NOT_COPRIME': 36, 'REAL_QUADRATIC': 96, 'UNIT_BEYOND_PM1': 1}
descent gate OK
verify: OK
```

**Thue generator.** `python/make_lean_thue_branch.py`, run by `make verify`, reported:
- 316 branch equations in 79 computed GL2(Z) classes;
- 15 descent obligations, as DAG certificates with 178 nodes (220 unfolded) and 2,008 leaf lifts;
- 10 closed curves (D = 29, 32, 36, 38, 52, 56, 77, 80, 86, 92), each agreeing with the Sage census.

**Compiler.** It reads the solved-family registry, and every entry of the registry is checked against its Lean statement by a full parse in both directions. The optional host-solver adapter (`make adapter-bench`, which needs `z3-solver`) is not part of `verify`. `Generated/Plans.lean` includes `plan_thue_minus56` and `plan_branch_minus20`, which are theorems about the original disguised cubics.

GitHub Actions CI was not used for this check. Its jobs are never assigned a runner, an account-level block described in the README.
