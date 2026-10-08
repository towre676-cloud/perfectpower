# Eleven/thirteen arithmetic handoff

This push extends exact prime division, complete projective-line subgroup preimages and bounded saturation to 11 and 13, while preserving all existing coefficient semantics and budget failures. Composite division supports factors 2,3,5,7,11,13 and scalar at most 30030. Four-generator preimages retain every projective line.

Core components: elliptic_prime_division.py and its independent verifier; elliptic_subgroups.py and subgroup/saturation verifiers; elliptic_presentation.py; sturm_fibres.py; residue_cover.py; elliptic_reduction.py. New mordell_cover_charts.py supplies exact binary-form chart transport, weighted projective poles and denominator-window searches.

Reproduce with PERFECTPOWER_GP=/path/to/gp make check-elliptic-eleven-thirteen. Tests include independent division recurrences, mixed determinant-11/13 relations and actual indices, composite 143 division, six-prime closure, corruptions, high-degree roots, cache budget enforcement, independent SymPy substitutions and live GP box searches. Read deterministic .json.gz worked receipts with gzip.decompress before json.loads.

The rank ledger now reports 457 equal backend intervals separately from 365 matching point witnesses. The 92 missing witnesses remain the constructive target; this push closes no integral-point completeness case. Preserve the legacy field and census provenance. New backend rank corrections total twelve, including -9257.

Next implementation: select a small witness-deficient batch, transform retained covers with exact charts, run disjoint denominator windows with explicit timeout accounting, retain only exactly lifted points, then replay existing independence tests and compare their ranks to retained upper bounds. Stop at the bounded batch and report discovery failures honestly. Do not claim a complete integral list, automatic global saturation, arbitrary-prime support or new Lean coverage.

Concurrent upstream commits through d0fdfb3 were merged before this publication, preserving their unit, Weil, flavor and wall changes. The Makefile merge retains both sessions' targets.

Local-obstruction mode at 11/13 now permits a finite good-reduction proof of trivial rational p-kernel, using prime-to-reduction torsion injectivity. The verifier enumerates the finite group independently; root_nodes is zero for this proof and the finite enumeration charges the replay work budget. Full Sturm certificates remain supported and are used by ordinary single-fibre mode. Modular Horner evaluation and necessary rational-root divisibility filters improve anchor discovery without changing exact acceptance.
