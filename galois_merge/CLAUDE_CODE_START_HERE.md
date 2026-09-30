# Galois × Forge integration handoff

The user authorizes implementing this merge in the actual PerfectPower repository. Read its AGENTS.md and current mathematical interfaces first. This package is additive; it does not contain the current repo or the 316-obligation ledger. The full earlier sequence corpus was unavailable in the producing session, so use the corpus already available in your repository/session. Do not ask the user to manually reconstruct accessible data.

Start with docs/MATHEMATICAL_MERGE.md, then src/arithmetic.py and the two input adapters. Run `python3 -m unittest discover -s tests -v`, then `python3 run_experiments.py`. The latter independently rechecks five actual Forge rational programs and signature geometry, and emits clearly labeled derived arithmetic experiments. These are not substitutes for the real 316 branches.

Export actual obligations with form=[c0,c1,c2,c3], rhs integer, and complete restrictions/readout identifiers. Run branch_adapter.py; it searches bounded matrices and verifies returned identities, never claims a full canonical partition. Port exact substitution, inverse, composition and bound transport into Lean, with explicit restriction pullbacks. Intern exact repeated descent suffixes; only share inequivalent-looking nodes after proving their transformation.

Run corpus_adapter.py --source PATH_TO_REAL_SEQ_DIRECTORY_OR_ZIP --out receipts/oeis_actual.json. Keep finite matches separate from definition theorems. Extend source grammar only with precise semantics. The synthetic parser test is a test, not an acquired OEIS entry.

Do real next mathematical work: classify D=72's restricted local problem, choose one shared cubic-field family for a proved solution-bound pilot, and define the real-quadratic unit-mod-cubes interface for positive k. Keep ideal seeds, lattice constraints and fundamental-unit completeness explicit. Do not assume a field match transports integral solutions or that finite unit classes prove effective enumeration.

The vendored Wilson files are selected original bytes. Their provenance manifest records archive hash and member hashes. The source root README is stale at v0.25 even though v0.26 dual execution notes exist; retain the original and explain the mismatch in integration docs. No Wilson algebra/number-field identification is asserted.

Retain existing make verify, axiom audit, OEIS promotion checks and complete-list boundaries. Update the reader with the final implementation, measured certificate costs and actual new closures. End with a full checkpoint ZIP even if some research targets remain unresolved.
