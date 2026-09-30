# PerfectPower as a host-solver component (`perfectpower/smt_adapter.py`)

A host solver (an SMT solver, or a verifier that emits SMT-LIB tasks) hands over a problem. The
adapter:
- recognizes top-level conjuncts whose complete integer solution set PerfectPower knows;
- replaces each one by that set, written as a finite disjunction or as `false`;
- returns the smaller problem, which the host then solves.

Everything the adapter does not recognize is passed through unchanged.

```
python3 -m perfectpower.smt_adapter TASK.smt2 --out REDUCED.smt2 --report REPORT.json
```

It needs `z3-solver` for parsing and printing, and nothing else in the repository depends on it.

**Fail-closed by default.** A replacement is applied only when its complete theorem's statement
is re-parsed from the Lean source. Every replacement records its evidence level:

| evidence | applied by default | meaning |
|---|---|---|
| `lean_statement_parsed` | yes | the curve's complete list is a Lean theorem over all integers, and its statement was re-parsed |
| `theorem_cited` | only with `--allow-unchecked` | a Lean theorem is named but its statement is not re-parsed (`y² = x³ − 4`, the FLT3 family) |
| `python_enumeration_unchecked` | only with `--allow-unchecked` | a bounded Pell/radical enumeration executed in Python |

**Script level** (`perfectpower/smt_cert.py`). Real tasks are incremental scripts, so the
script-level path works as follows:
- it replays `push`/`pop`, classifies every assertion in its live declaration context, and ledgers
  each `check-sat`;
- it issues **source-bound certificates** (script hash, command index, assertion hash, atom,
  normalized polynomial, parsed theorem, witnesses);
- `check_certificate` re-derives every field from the source;
- `python/tests/test_smt_cert.py` tests the boundary: tampering, binding, sign loss, domains,
  Boolean context, `let`, `define-fun`, extensions, the singular `k = 0` curve, and the
  incremental stack.

## What is replaced, and why it is sound

Each replacement is an **equivalence over ℤ** of one conjunct. For a verification condition
`Γ ⇒ G`, sent to the solver as `Γ ∧ ¬G`, replacing a hypothesis `C ∈ Γ` by an equivalent `L`
preserves validity exactly. Nothing is weakened, dropped or summarized, and every other hypothesis
stays in place.

| conjunct | recognized when | replaced by | justification |
|---|---|---|---|
| `m² = (r n + s)³ + k` | the coefficients match exactly (`match_affine_cube`) and `y² = x³ + k` has a Lean-proved complete list | the finite list over **all** integers `n` (the substitution `x = r n + s`), or `false` | the cited Lean theorem (solved-family registry, `MordellDescent`, hand-proved curves) plus the coefficient identity, checked exactly |
| `a S² + b S + c = F(N)`, `F` quadratic, with numeric bounds `lo ≤ N ≤ hi` among the conjuncts | the compiler has an exact orbit enumeration (`exact_to_any_N`) | the finite list of solutions with `lo ≤ N ≤ hi` (negative `N` by reflection, `N = 0` directly) | the Pell-orbit theorems the plan cites (`PellExact.pell_branch_explicit`, …); the enumeration itself is executed in Python (`execution_verified: false`) |

Without numeric bounds, a Pell equation is not replaced: its solution set is infinite, and the host
keeps it.

## What is not claimed

- **No Lean proof of the reduced task.** The curve's complete list is a Lean theorem. The step
  from the SMT conjunct to that theorem (the substitution and the coefficient match) is checked
  in Python. A verifier that must not trust Python needs that bridge formalized, or a proof
  reconstructed in its own system (for example, a Why3 lemma per replacement).
- **Machine arithmetic.** The equivalences hold over mathematical integers. They apply to a
  program's verification condition only where its terms *are* mathematical integers:
  - SPARK's `Integer` arithmetic under proved absence of overflow qualifies;
  - modular types and wrapping arithmetic do not, and are not handled.
- **Coverage.** Only the two shapes above are recognized. Most arithmetic verification
  conditions (inequalities, arrays, induction, division and modulo reasoning) fall outside them.

## Two verification-condition-shaped examples (`examples/smt/`)

Both are constructed. Times are z3 5.1.0 wall clock on this container.

| task | hypotheses | goal | z3 alone | adapter + z3 |
|---|---|---|---|---|
| `vc_minus56.smt2` | `n ≥ 1`, `m² = n³ − 56`, `len = 2n + m` | `len ≤ 200` | `unknown` at 10 s | proved (`unsat` of the negation) in 0.002 s |
| `vc_pairs_square.smt2` | `2 ≤ N ≤ 10⁹`, `N(N−1) = 2S²` | `N mod 4 ∈ {1, 2}` | `unknown` at 30 s | proved in 0.003 s (24 solutions `(N, S)`), **with `--allow-unchecked`**: the enumeration is Python |

## Benchmark (`python/host_adapter_bench.py`, `receipts/host_adapter_bench.json`)

48 **constructed** instances, 12 per group, z3 5.1.0 with a 10 s timeout per call. Adapter
times include recognition and replacement.

| group | what it is | z3 alone solved | adapter + z3 solved | z3 alone, total s | adapter + z3, total s |
|---|---|---|---|---|---|
| `sat` | a disguised solved curve with points, plus a side constraint a point satisfies | 2 / 12 | 12 / 12 | 102.0 | 0.48 |
| `unsat_side` | the side constraint excludes every point | 1 / 12 | 12 / 12 | 110.3 | 0.32 |
| `no_points` | a curve proved to have no integral points | 0 / 12 | 12 / 12 | 872.2 | 0.05 |
| `unsupported` | a cubic that is not a solved curve (control) | 12 / 12 | 12 / 12 | 2.69 | 3.12 |

- **Wherever both finished, the answers agree.** The script aborts on any mismatch.
- **The `no_points` total is inflated.** One z3 call ignored its 10 s timeout and took 754 s, and
  the total counts it as measured.
- **On the controls the adapter only adds overhead.** Recognition takes about 2 ms per task. The
  rest of the 0.43 s difference comes from z3 solving the same unchanged problem twice. That
  run-to-run variation was not measured separately.
- The 36 recognized tasks go from 3 solved to 36 solved. This is the expected outcome on instances
  **built** to contain a solved conjunct, so it says nothing about how often such conjuncts occur.

## An independent corpus: zero coverage (`independent_nia/reports/PERFECTPOWER_COVERAGE.md`)

The corpus is 69 upstream SMT-LIB QF_NIA files, byte-exact with provenance: 19 industrial ELSTER
files with 12,801 incremental queries, 49 cvc5 regressions, and one crafted STAUB problem.
- The script-level adapter finds **zero checked replacements** and, in the industrial cohort,
  zero candidates.
- ELSTER's hard queries (2 s cap under z3) lie in linear arithmetic with `div`/`mod` by
  constants: 116 of 8,124 such queries hit the cap, against 7 of 3,615 queries with a guarded
  bilinear product.
- The flagged cvc5 cases are correctly rejected: the singular `x² = y³`, `x² = y`, and
  `int.pow2`.
- Routing overhead is 0.7 ms per query, 1.5 % of z3's time.

The constructed benchmark above therefore shows the mechanism, and the independent corpus shows
the fragment does not occur there. The report names the smallest workloads that would test it:
- SMT-LIB `QF_NIA/MathProblems`;
- saved GNATprove/Why3 tasks from SPARK code with nonlinear specifications.
