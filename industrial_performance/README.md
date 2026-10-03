# Industrial performance checkpoint

The later [bounded replay push](REPLAY_README.md) preserves the original solver strategy and targets command-scanning and transport overhead. Its full-corpus scanner comparison checks 3,602,272 exact command slices, and its paired replay reports are separate from the negative strategy-portfolio result below. See [the replay monograph](REPLAY_MONOGRAPH.md) for the mathematical sequence justification, measurements and scope.

This opt-in experiment acquires all 181 ELSTER incremental QF_NIA files from SMT-LIB/benchmark-submission at commit `bdae77b0a144895098f82b51a531bc2b566df9e6`. The files total 307,442,420 bytes. Acquisition verifies Git blob SHA-1 and records SHA-256, byte counts and paths. The upstream headers describe industrial tax-form test-data generation and carry the upstream licensing information. Preserve those headers when using or redistributing the corpus.

Install `z3-solver`, then run from the repository root:

```sh
python industrial_performance/acquire.py --destination /tmp/elster-industrial
python industrial_performance/run.py --corpus /tmp/elster-industrial --cap 8 --timeout-ms 250 --workers 3 --output industrial_performance/portfolio_8.json
PYTHONPATH=python python -m unittest discover -s python/tests -p test_industrial_performance.py
```

The frozen cohort contains every file, in sorted path order, with the first `min(cap, query_count)` queries. It is a prefix experiment, not a full-corpus query run or a blind holdout. Each mode executes independently in fresh Z3 contexts; execution order alternates by file. The original receives 250 ms per query. An eligible portfolio query receives 125 ms in the original context and, only after unknown, 125 ms in a QF_LIA context. Ineligible queries receive the original 250 ms budget. Solver setup, syntax classification, command parsing, and maintenance of both contexts count in the candidate wall time. Timeouts apply to check commands only, and are reset to zero before subsequent assertions or push/pop operations. Observer requests are omitted in both modes. Any native error or incomplete stream aborts the experiment.

`industrial_router.py` validates the sorts and linear syntax of all live assertions. It permits numeral multiplication and nonzero numeral division/modulus, Boolean connectives, and conditionals. It rejects symbolic multiplication, symbolic division, binders, definitions, options, undeclared terms and unsupported operations. Routing changes the logic header only. It preserves exact assertion source text and maintains declaration scopes. This is solver dispatch, not a downstream verifier certificate. The Python classifier is tested; its implementation is not formally verified.

The portfolio is experimental and has no default integration. The 250 ms allocation is a solver timeout allocation, not a hard wall-clock deadline: setup and solver cancellation overhead may exceed it. Per-file wall sums and batch elapsed time are both reported. Three worker processes share one machine; timings do not establish performance across machines or solver versions. `portfolio_8.json` contains source hashes, selected and full query counts, every answer and latency, and aggregate paired gains, losses and SAT/UNSAT conflicts. Checkpoint files are written during execution and marked incomplete.

Earlier completed 32-query experiments were lost with an uncommitted workspace during maintenance. Their aggregate observations are retained in the monograph with that limitation, not reconstructed as raw measurements. The new eight-query report is a fresh measurement with retained raw rows. No results from an unfinished pre-maintenance portfolio are asserted.
