# Divisor-sum atlas

See [the monograph](../../docs/DIVISOR_SUM_RESULTS_MONOGRAPH.md) for definitions, domains, proofs, counts, commands, and limitations. Rebuild with `PYTHONPATH=python python python/build_divisor_sum_atlas.py` from the repository root.

`complete_quartics.json` contains globally complete integer lists for 3,080 equations using generic Lean-proved bounds, with Python execution marked separately. `CompleteQuartics.lean` contains all corresponding native commands. Compilation status is recorded in validation.json, not inferred from file existence.

`bounded_power_hits.json` covers n=1 through 1,000,000 and degrees 2 through 8. `prime_power_grid.json` and `prime_pair_square_hits.json` cover primes at most 1,000 and exponents 1 through 8, with distinct primes in each product. These finite-domain collections make no global claim beyond their stated domains.

This release kernel-checks 2,686 of the 3,080 emitted literal lists and all six divisor-sum bridge theorems. Exact checked indices are recorded in lean_catalogue_validation.json. The offline results.html browser searches and exports the collection. prime_shift_classifications.json contains all 401 shifted prime classifications.
