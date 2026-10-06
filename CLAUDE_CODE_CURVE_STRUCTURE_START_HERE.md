# Curve-structure research handoff

This release extends the curve-family compiler with exact geometric explanations. Start with docs/CURVE_STRUCTURE_MONOGRAPH.md and receipts/curve_structure/summary.json. The complete archive includes all preceding arithmetic, geometry and flavor research, with no size cap.

CurveFamily.deformation projects coefficient motion modulo affine coordinate changes and recognizes centered-binomial scaling. root_motion constructs -P_t/P_x in Q(t)[x]/P. collisions handles all simple finite discriminant roots in split squarefree Q-algebras, records their common root and connection residue, and explicitly retains omitted multiple-root loci.

EllipticQuotientFamily discovers translated-even sextics and compiles their two elliptic quotient connections. Four independent residue-free genus-two reductions are compared exactly with those blocks. translated_even_specification constructs a family from a first cubic quotient and center. discover_elliptic_quotients reports symmetry conditions even when the generic family fails them. Point images and complete rational fibres retain original-coordinate integrality.

Run python/develop_curve_structure.py, the focused python/tests/test_curve_structure.py suite, scripts/check_structure_workbench.cjs and the saved service request transcript. Open receipts/curve_structure/structure_workbench.html locally to inspect root motion and shape coordinates. Its 183 root samples are numerical; its structural packets are exact. Period execution remains numerical and supports specified quotient marks.

Public curve_family parameter degree is now at most eight. Internal quotient changes can raise parameter degree within the declared algebra budgets. Do not turn skipped repeated discriminant factors into a smoothness assertion, a coordinate chart pole into a degeneration, a first-order observable into a genus reduction, or a quotient period into an arbitrary original-cycle period.

Next mathematics: projective coordinate directions and binary forms; local multiple-root/infinity degeneration models; integral cycle and quotient maps; Hodge-compatible horizontal projectors with actual algebraic correspondences; broader low-degree rational quotient discovery; multiparameter flat connections. General continuous Hodge identification and Lean proofs are not delivered here.
