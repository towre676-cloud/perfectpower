# Differential fuzzers

Contributed by an external reviewer (the `pp_fuzz` harnesses) and made deterministic: each takes a
seed and a trial count instead of a wall-clock budget, so a run is reproducible.  They compare
the atlas against brute force; a disagreement or an exception is a bug.

    PYTHONPATH=python python3 python/fuzz/fuzz_structural_vs_scan.py SEED TRIALS
    PYTHONPATH=python python3 python/fuzz/fuzz_pell_quadratic.py SEED TRIALS
    PYTHONPATH=python python3 python/fuzz/fuzz_finite_bucket_late_hits.py SEED TRIALS SCAN

`make fuzz` runs all three with fixed seeds (the finite-bucket scan goes to 10^8 with the sieve of
`perfectpower/sieve.py`); `python/tests/test_fuzz.py` runs small fixed-seed versions in `make test`.
Late hits found by the finite-bucket fuzzer are *evidence*, not certificates: see
`receipts/genus1_crossval.json` for the Sage-certified genus-one cases.
