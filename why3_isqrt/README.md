# Why3 Von Neumann integer square root: a guarded unsigned-bitvector route

This directory holds an independently authored software workload, and the fixtures, scripts and
receipts for a PerfectPower extension that helps on part of it. The full write-up is
[docs/ARITHMETIC_WORKFLOW.md](../docs/ARITHMETIC_WORKFLOW.md).

## What is here

| path | content |
|---|---|
| `raw_bv_vcs/` | 134 native-bitvector VCs exported by Why3 1.6.0 from the unmodified `examples/isqrt_von_neumann.mlw` (16, 32 and 64 bits) |
| `raw_vcs/` | the 32 ordinary `examples/isqrt.mlw` VCs (a negative performance control: all are easy for Z3) |
| `negative_controls/` | a mutated terminal readout `r = r_g + 1`, in full and as its ground slice |
| `upstream/` | the pinned upstream sources with their licenses (Why3, AdaCore SPARK tests, Mark Dickinson's isqrt proof); see `NOTICE.md` |
| `receipts/` | the measurements of the original handoff (`summary.json` first); `reproduced_*` were re-run in this repository |
| `benchmark_adapter.py` | paired replay: original task against the task with guarded facts added |
| `pp_z3.py` | a Why3-compatible prover wrapper (fails open to the intact task) |
| `lean_instances.py`, `lean_contexts.py` | emit `PerfectPower/Generated/WorkflowInstances.lean` (307 instances) and `WorkflowContexts.lean` (4 complete ground contexts) |
| `export_why3.py`, `why3_host.conf` | re-export from Why3 (paths in the config are workspace-specific) |
| `HANDOFF_MANIFEST.json` | SHA-256 of every file in the original handoff layout |

The Lean modules are in the library: `PerfectPower/BVWorkflow.lean` (core only),
`PerfectPower/ArithmeticWorkflow.lean` (Mathlib), and the two generated files above. The adapter is
`python/perfectpower/unsigned_adapter.py`, with the wrapper `python/perfectpower/unsigned_why3.py`.
The tests are `python/tests/test_unsigned_adapter.py` (z3-solver required; 20 tests including the
re-derivation of all 307 instances) and `python/tests/test_arithmetic_oracles.py`.

## Reproduce

```
python3 why3_isqrt/lean_instances.py      # regenerates WorkflowInstances.lean (307)
python3 why3_isqrt/lean_contexts.py       # regenerates WorkflowContexts.lean (4)
python3 -m unittest python.tests.test_unsigned_adapter python.tests.test_arithmetic_oracles
python3 why3_isqrt/benchmark_adapter.py --z3 "$(which z3)" --budget 3 --seeds 0
python3 why3_isqrt/benchmark_adapter.py --z3 "$(which z3)" --budget 3 --seeds 0,1,2,3,4 --hard-only
```

The benchmark overwrites `receipts/paired_goal_*.json` and writes `certificates/`. Re-exporting from
Why3 changes path comments and so the task hashes; regenerate certificates rather than reusing them.

## What is not claimed

- No Why3 proof session accepted the wrapper (the native scheduler could not open its socket in
  the handoff environment), and GNATprove was not run. The AdaCore files are leads.
- The SMT-to-Lean translation is Python over Z3's parser, not a verified import. The four contexts
  prove the normalized ground implications with every ground premise kept; quantified premises
  are omitted, which makes the implication stronger.
- The existing Mordell/Pell adapter makes zero replacements on all 166 tasks. This is a separate
  route, not evidence for that adapter.
- The timings are measurements on one machine and one pinned workload.
