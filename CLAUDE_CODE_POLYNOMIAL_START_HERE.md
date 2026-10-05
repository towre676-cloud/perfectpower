# Polynomial capacity handoff

Start with `docs/POLYNOMIAL_CAPACITY_MONOGRAPH.md`. The core additions are `python/perfectpower/polynomial_composition.py`, `polynomial_domains.py` and `polynomial_relations.py`, integrated into `arithmetic_engine.py`, `simplifier.py` and `enhanced_cli.py`. The concurrent Gamma and integral-output-machine work is preserved.

Run `PYTHONPATH=python python -m unittest discover -s python/tests -p test_polynomial_capacity.py` for the focused checks. Run `PYTHONPATH=python python python/develop_polynomial_capacity.py` to regenerate the stored 6,422-equation and 3,080-objective experiment. Run the entire Python suite with `PYTHONPATH=python python -m unittest discover -s python/tests`. Computational interfaces require Python 3.10 or later and only the standard library.

The saved receipts are under `receipts/polynomial_capacity/`. The baseline already closes all nonlinear quartic examples; the 141 new completions arise from transformed unconditional Mordell leaves. Timings do not show a speed advantage. The added polynomial code contains no new Lean proofs and explicitly labels execution as unverified. General real-root variation, the whole compiler and arbitrary multivariate solving remain open.

Preserve the integer image at every transport: denominator-scaled witnesses require divisibility, nonlinear maps require every integer fibre, and polynomial outer functions cannot be cancelled without injectivity. Optimization uses the forward difference and keeps all ties. These invariants are the best starting point for generic Lean certificate interpretation.
