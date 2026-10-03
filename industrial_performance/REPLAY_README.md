# Bounded incremental replay

On the committed 181-file, 5,612-query prefix experiment, the combined fast scanner and batched transport reduced summed replay wall time from 742.481 to 707.361 seconds (4.73%) and solved 64 more queries within the same 250 ms solver allocation. All streams completed and there were zero SAT/UNSAT conflicts. The result is specific to this host, solver version and prefix sample; it is not a full-corpus query run or a downstream verifier result. Full-corpus scanning separately matched all 3,602,272 source command slices and was approximately 2.7 times faster.

Install the optional dependency with `python -m pip install '.[industrial]'` from the repository root. The original package remains standard-library-only unless this extra is selected. Z3 is pinned to the measured distribution version, 5.1.0.0.

Replay a source without altering its assertions or solver logic:

```sh
python industrial_performance/replay.py source.smt2 --fast-split --output answers.json
python industrial_performance/replay.py source.smt2 --command-control --output control.json
```

The engine groups non-query commands into batches of at most 262,144 characters, except for an oversized individual command, which is sent alone. It flushes before every query, configures that query's timeout, and resets the timeout before proceeding. `--batch-chars` controls transport size; `--timeout-ms` controls the solver query allocation. Invalid input or a native error stops the stream and returns a nonzero CLI exit status. Model/proof/value observers are omitted; this is an answer-ledger interface. Source hashes and Z3 version are written into the output.

Acquire the complete pinned corpus automatically and reproduce the comparisons:

```sh
python industrial_performance/acquire.py --destination /tmp/elster-industrial
python industrial_performance/check_scanner.py --corpus /tmp/elster-industrial --output scanner_full.json
python industrial_performance/run_replay.py --corpus /tmp/elster-industrial --cap 32 --fast-split --output replay_fast_32.json
```

Use `--resume` after an interrupted replay experiment to reuse its matching checkpoint. A changed manifest, engine, protocol or recorded runtime configuration rejects reuse. Full-corpus scanner comparison checks every input byte; replay comparisons select fixed per-file query prefixes. These scopes differ. See `REPLAY_MONOGRAPH.md` and the committed raw reports for measurements and limits. The `snapshots/` files preserve the exact engine and runner used in `replay_8.json`; their SHA-256 values match that report's original code hashes. They are provenance snapshots, not separate installed entry points.

The parallel norm-107 fixture is also replayed with this transport engine. Its unreduced formula times out at the 250 ms budget in `norm107_replay.json`; the other session's complete theorem and reduced fixture establish its finite replacement. This authored example is not included in the industrial cohort or its speed claims.
