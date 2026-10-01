# Release check

`make release-verify` was run on commit `960fb18` (branch `claude/laughing-lamport-qqzdo9`) with a clean working tree. It exited with status 0. `release-verify` is `make verify` with `z3-solver` required, so the adapter and certificate tests run instead of being skipped.

This file archives the key lines of its output. The environment was:
- Lean `leanprover/lean4:v4.20.0`, with Mathlib `v4.20.0` compiled from source;
- Python 3.11.15 with `z3-solver` 5.1.0;
- Why3 1.6.0, used by `make why3-bridge` (not part of `verify`; `receipts/why3_bridge.json`).

The optional Sage/PARI steps (`make crosscheck`, passagemath 10.8.12, mpmath 1.3.0) are not part of `verify`, but `verify` re-checks their receipts in plain Python. For this release these crosscheck scripts were run:
- `crosscheck/branch_thue_pari.py`, which writes `receipts/mordell_branch_thue.json`;
- `crosscheck/thue_fields_pari.py`, which writes `receipts/thue_fields.json`;
- `crosscheck/field756_pilot.py`, which writes `receipts/field756_pilot.json`;
- `crosscheck/d72_unit_pilot.py 40`, which writes `receipts/d72_unit_pilot.json` (positive control passed);
- `crosscheck/thue_bound_d72.py`, which writes `receipts/d72_thue_bound.json` (direct reduction: `H ≤ 4`, `V = 1`);
- `crosscheck/thue_bound_field756.py`, which writes `receipts/field756_bound.json` (direct reduction: `H ≤ 5, 7, 5, 6, 6, 6, 5`, `V ≤ 1`).

```
Build completed successfully.
axiom audit passed: 963 declarations
-- Found 0 errors in 1724 declarations (plus 5820 automatically generated ones) in PerfectPower with 15 linters
-- All linting checks passed!
z3-solver: present: adapter/certificate tests run
Ran 215 tests in 49.442s
OK
Ran 14 tests in 9.052s (continuation_tests)
OK
Ran 10 tests in 0.025s (expert_push)
OK
Ran 8 tests in 0.009s (galois_merge)
OK
19/19 certificates passed
binomial gate OK: {'C(n,2)=m^3': [1, 2], 'C(n,3)=m^2': [1, 2, 3, 4, 50]}
genus-1 gate OK: 400 families, labels {'CONDITIONAL_ON_UNPROVEN_RANK': 1, 'INDEPENDENT_COMPUTATION': 399}, 3 certified hits beyond the scan
Theorem G gate OK: 462 cases, genus computed in 462, places at infinity in 453, 0 disagreements
399 genus-one reduction theorems
1163 Mordell curves without integral points
59 curves y^2 = x^3 - D: 26 complete lists emitted, 33 with open branches; complete lists agree with Sage 26/26, with published counts 26/26; ranks {'0': 10, '1': 12, '2': 4}
x^3 - 6x - 2: disc 756, index primes [2, 3], p=2: {'0': 3} max=True tot=True, p=3: {'2': 3} max=True tot=True; targets [8, 64, 256, 512, 576, 8192] all unique
x^3 - 9x - 6: disc 1944, index primes [2, 3], p=2: {'0': 1, '1': 2} max=True tot=False, p=3: {'0': 3} max=True tot=True; targets [9, -9] all unique
x^3 - 6x - 2: unit box {'witness_box': [9, 3, 3], 'witness_triples': 931, 'witness_candidates': 12, 'lean_box': [8, 2, 2], 'lean_triples': 425, 'lean_units': 6}
0: B=5 V=1 box 121 steps 7 hits [(1, 1), (10, -2)]
1: B=7 V=1 box 225 steps 7 hits [(-11, 1), (1, 1)]
2: B=5 V=1 box 121 steps 7 hits [(-2, 0), (1, -3)]
18: B=6 V=1 box 169 steps 7 hits [(2, -1), (6, 1)]
19: B=6 V=1 box 169 steps 7 hits [(-8, 0), (2, 1)]
20: B=6 V=1 box 169 steps 7 hits [(-4, 0), (2, -1)]
50: B=5 V=0 box 121 steps 7 hits [(-4, 0), (2, -6)]
D=7: classes [0, 1, 2], points [(32, -181), (2, -1), (2, 1), (32, 181)]
D=28: classes [18, 19, 20], points [(37, -225), (8, -22), (4, -6), (4, 6), (8, 22), (37, 225)]
D=63: classes [50], points [(568, -13537), (4, -1), (4, 1), (568, 13537)]
x^3 - 9x - 6: unit box {'witness_box': [28, 8, 5], 'witness_triples': 10659, 'witness_candidates': 8, 'lean_box': [27, 7, 4], 'lean_triples': 7425, 'lean_units': 8}
1: B=4 V=1 box 81 steps 6 hits []
-1: B=4 V=1 box 81 steps 6 hits []
36 registry entries, all checked against their Lean statements -> receipts/mordell_registry.json
pairs_square_1e9: 24 solutions, 32 orbit steps, seeds [(2, 0)]
25 plan theorems -> PerfectPower/Generated/Plans.lean
56 (9, 9, -3) exceptional [2, 3, 5, 7] all witnesses found
57 (9, 21, -2) exceptional [2, 3, 5, 7] all witnesses found
{'classes_open': 64, 'unit_leaves_total': 189, 'distinct_unit_equations': 109, 'unit_equations_shared_by_several_classes': 24, ...}
branch adapter: 474 edges, 0 cross repo classes, 79 components vs 79 classes; restricted edges 0
corpus adapter: 144 .seq files, B-index matches [('A000129', [0]), ('A048624', [2]), ('A069306', [1])]
140 candidate entries {'PROVED': 69, 'NOT_TRANSLATED': 71} -> PerfectPower/Generated/OEISAuto.lean
sqrt2: 39 entries {'DEFINITION_PROVED_EQUIVALENT': 33, 'TRANSPORTED_WITH_SHIFT': 2, 'EXCEPTIONAL_SET_PROVED': 3, 'TRANSPORTED_FROM_DUPLICATE': 1}; Mordell: 77 certified lists checked, 0 disagreements, 119 leads -> receipts/oeis_sqrt2_atlas.json
155 unresolved curves (59 with k < 0): {'CLASS_3': 12, 'ELEMENT_CUBE': 1, 'NONMAXIMAL': 34, 'NONMAXIMAL_CUBE': 6, 'NOT_COPRIME': 36, 'REAL_QUADRATIC': 96, 'UNIT_BEYOND_PM1': 1}
descent gate OK
verify: OK
```

**Unit fields** (`python/make_lean_unit_fields.py`, run by `make verify`; [UNIT_PREMISES.md](UNIT_PREMISES.md)). The field-756 class theorems, `minus7`, `minus28`, `minus63` and `D72Residual.residual_empty` are kernel-checked **under one named premise per class**, `matveev_i` (Matveev's lower bound, three explicit instances). Unit generation (`unitGen_proved`, `UnitGen.lean`), the norm representatives (`normRep_*_proved`, `NormRepProof.lean`) and the analytic inequality (`analytic_i_proved`, `AnalyticBridge.lean`; 24 interval certificates `caseOK_i_k` by `decide +kernel`, from `python/perfectpower/analytic_cert.py`) are proved. The direct-H reduction chains (56 stages), their forged negative controls, norm identities, boxes and small cases are evaluated by the kernel. In every class the box hits equal PARI's solution list, and each curve's points equal the Sage census. These curves are not counted among the 26 closed ones. `python/unit_basis_witness.py` (exact fundamental-domain witness) and `python/norm_rep_localization.py` (Dedekind's criterion, total ramification) run in `make verify` too.

**Bounded Pell.** `Generated/BoundedPlans.lean` (`pairs_square_1e9`) is unconditional; the adapter's default bounded-Pell path runs the kernel per query (`lean_kernel_checked`).

**Thue generator.** `python/make_lean_thue_branch.py`, run by `make verify`, reported:
- 316 branch equations in 79 computed GL2(Z) classes;
- 15 descent obligations, as DAG certificates with 178 nodes (220 unfolded) and 2,008 leaf lifts;
- multi-prime certificates (`ThueLocal.descM`) are tried when single-prime descent fails, and none are needed;
- 10 closed curves (D = 29, 32, 36, 38, 52, 56, 77, 80, 86, 92), each agreeing with the Sage census.

**Compiler.** It reads the solved-family registry, and every entry of the registry is checked against its Lean statement by a full parse in both directions. The optional host-solver adapter (`make adapter-bench`, which needs `z3-solver`) is not part of `verify`. `Generated/Plans.lean` includes `plan_thue_minus56` and `plan_branch_minus20`, which are theorems about the original disguised cubics.

**Independent corpus.** The z3 baselines, the query-level timing and the PerfectPower ledger for `independent_nia/` (`make nia-ledger`, `make nia-timing`; they need z3-solver) are not part of `verify`, because their timings depend on the machine. The ledger finds 0 checked replacements (`independent_nia/reports/PERFECTPOWER_COVERAGE.md`).

GitHub Actions CI was not used for this check. Its jobs are never assigned a runner, an account-level block described in the README.
