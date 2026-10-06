# Elliptic witness validation

The implementation starts from 90e8271d44f80c813394119da2cccb11e8d704af on claude/laughing-lamport-qqzdo9. This checkpoint changes Python arithmetic, public object integration, certificate checking, tests, scientific receipts and documentation. It changes no Lean theorem or arithmetic axiom.

The new focused suites pass all 17 tests. Existing test_curve_structure.py passes all 20 tests, and test_literature_curve_execution.py passes all 39 tests. The latter completed in 93.142 seconds and the former in 35.652 seconds on this execution environment; these are validation timings, not performance claims.

All 14 files in receipts/elliptic_witnesses reproduce byte for byte in a fresh temporary output directory. A fresh SQLite JSONL replay gives seven responses byte-identical to service_responses.jsonl. The corpus builder additionally closes and reopens its database after each request. All four complete halving packets and all four independence packets pass discovery-free checking before they are saved.

The six-page monograph renders successfully using both an explicit source and the elliptic edition's default source. Its body and final page were inspected. git diff --check passes.

The focused mathematical checks cover complete two-torsion, empty and nonempty rational halving fibres, a four-element torsion coset, repeated and very large rational roots, generalized Weierstrass models, rational isomorphism round trips, two-isogeny exceptional fibres, two independent rational witnesses, dependent and torsion witnesses, exact halving replacements including a nonzero torsion offset, independent finite-group character enumeration, separate F2 elimination, malformed packets, checking budgets and cold public-service persistence.

The full make test run passes: 1122 core cases (four skips), 14 continuation cases, 10 expert-push cases and eight integration cases. This is 1154 cases in total, with 1150 passing and four skipped. The final emitted-certificate allocation guard was followed by another successful 17-test focused run and unchanged corpus regeneration. The complete test transcript is audit/elliptic_witnesses_tests.log. Z3 5.1.0.0 and python-flint are installed so their tests run. Full Lean make verify and make release-verify are not claimed for this Python-only checkpoint; this validation does not refresh historical Lean evidence.
