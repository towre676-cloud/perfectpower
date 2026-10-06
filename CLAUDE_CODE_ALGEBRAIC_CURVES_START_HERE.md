# Algebraic curve extension: start here

This checkpoint extends the polynomial-to-de-Rham bridge with algebraic coefficient fields, exact local execution and actual finite-action quotient maps. Preserve the separate flavor and physics investigation in this checkout. Read README.md and docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md before making broader mathematical claims.

## Reproduce and execute

```sh
PYTHONPATH=python python -m unittest discover -s python/tests \
  -p test_algebraic_curve_extensions.py
PYTHONPATH=python python python/develop_algebraic_curve_extensions.py
PYTHONPATH=python python -m perfectpower service \
  --database /tmp/pp-algebraic.sqlite \
  < receipts/algebraic_curve_extensions/service_requests.jsonl
make test
python python/render_polynomial_monograph.py --edition extensions \
  --source docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md \
  --output docs/ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.pdf
python python/render_algebraic_curve_workbench.py
```

Use a new database for deterministic replay. The PDF renderer requires optional ReportLab and Matplotlib; the mathematical engines use the Python standard library. The receipt workbench is a self-contained HTML document displaying precomputed exact packets. No server or external JavaScript dependency is required.

## Code map

`python/perfectpower/differential_extensions.py` contains finite étale algebras, nested arithmetic, unique extended derivations, complete fixed-algebra kernels, cyclic scalar Hilbert–90 and primitive models of full tensors. Preserve the distinction between a finite étale algebra and a field. Nonunit witnesses must not be swallowed.

`python/perfectpower/algebraic_local_curves.py` pulls connections into rational/algebraic/infinite ramified charts, covers discriminant support with component splitting, solves coupled logarithmic recurrences and executes transverse ordinary-node branches. A finite jet is a formal identity, not a certified analytic approximation.

`python/perfectpower/symmetry_quotients.py` independently reduces odd/even hyperelliptic differentials, checks actual Möbius curve actions and group closure, constructs complete fixed fields, derives normalized quotient equations and verifies full differential pullbacks. Its paired-involution method uses actual covers and norm/pullback identities to certify a degree-2^g Jacobian isogeny. Keep this stronger geometric result separate from an arbitrary differential idempotent.

`python/perfectpower/arithmetic_curve_structure.py` gives supported ramified smooth binomial charts and exact cyclotomic character-orbit obstructions. Passing the orbit test is necessary, not sufficient for an algebraic correspondence. Its ramification exponent is minimal for the stated scaling ansatz, not necessarily among every stable model.

The persistent API is wired through catalogue.py and query_service.py. The existing CurveFamily gains six new operations. The catalogue has fifteen kinds. The corpus builder generates the equations, witnesses, summary and twenty-three-request service replay in receipts/algebraic_curve_extensions. validation.json records the release checks separately from scientific receipts and measured timings.

## Concrete next mathematical work

Generalize local normalization from centered binomials to several simultaneous root clusters, retaining algebraic conjugacy and infinity data. Construct actual integral homology maps and 2-torsion kernel generators for the paired double covers, with a marked comparison to their de Rham pullbacks. Extend finite-action quotient reconstruction over algebraic coefficients beyond its bounded rational ansatz. Connect several parameter directions to the local algebraic execution engine, preserving flatness and component splitting. Add descent tests for correspondences beyond scalar Hilbert–90 and cyclotomic necessary conditions.

Do not claim general stable reduction, automatic integral period marking, explicit isogeny-kernel generators, arbitrary Jacobian decomposition, analytic convergence bounds, new Lean kernel proofs or physical predictions from this checkpoint. The previous projective tangent quotient, three-parameter smooth-family connection and simplicial integral maps remain available and distinct.

## Complete-source packaging

After committing the intended tree, package every tracked path without a size cap:

```sh
python python/package_open_content.py --reference HEAD \
  --output /tmp/perfectpower-algebraic-curves-complete.zip
```

This includes prior open content and physics sources, the new mathematical modules, tests, receipts, monograph source/PDF and workbench. The ZIP is generated from a git tree, so uncommitted files are deliberately excluded; commit first and validate the archive.
