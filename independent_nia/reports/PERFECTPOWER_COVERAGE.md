# PerfectPower on an independent QF_NIA corpus: coverage and economics

## Summary

**Zero checked replacements, and zero unchecked candidates in the industrial cohort.**
- The fail-closed adapter found nothing in the 12,801 industrial ELSTER queries that PerfectPower
  can replace.
- The expensive queries in that cohort belong to a different fragment: linear arithmetic with
  `div`/`mod` by constants.
- The adapter falls back correctly on every attractive-but-unsupported case the handoff flagged.

This is the honest outcome the work order anticipated. The corpus does not yet contain a
workload where PerfectPower's certificates remove search.

## What was run

| item | value |
|---|---|
| project revision | `claude/laughing-lamport-qqzdo9` (the handoff's reviewed anchor was `631b08d`; this work starts from `0b1b7e6` and later) |
| corpus integrity | `tools/verify_manifest.py`: PASS, 69 byte-exact upstream files; `tools/selfcheck.py`: PASS |
| solver | z3 5.1.0 (the `z3-solver` wheel's binary and Python API). cvc5 1.4.1 was available only as Python bindings, so the CLI runner could not use it. |
| file-level baseline | `tools/run_baseline.py`, 10 s per file, raw files, harness flags **not** applied: `z3_{cvc5,elster,staub}.json` |
| query-level timing | `python/nia_query_timing.py`: z3's own SMT-LIB interpreter, command by command, 2 s per `check-sat`, 120 s budget per file, unrun queries recorded as `not_run`: `z3_query_timing.json` |
| adapter ledger | `python/nia_ledger.py` with `perfectpower/smt_cert.py`: `perfectpower_ledger.json` |

## Coverage (`perfectpower_ledger.json`)

Every assertion is classified once, in its live declaration context. Each positive conjunct of
a top-level `and` is counted.

| cohort | files | queries | linear | `div`/`mod` by a numeral | nonlinear | extension or barrier | unchecked candidates | **checked replacements** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ELSTER (industrial) | 19 | 12,801 | 126,766 | 3,467 | 24 | 0 | 0 | **0** |
| cvc5 regressions | 49 | 58 | 210 | 3 | 126 | 36 | 2 | **0** |
| STAUB (crafted) | 1 | 1 | 0 | 0 | 1 | 0 | 0 | **0** |

**ELSTER: the generator's header is not exact.** Every ELSTER header says that all products have
the form `(* x c ...)` with numeral factors. The classifier finds 24 conjuncts with a product of
two unknowns, all in the four `type2/B` files:
- `B_htc_9`, `B_htc_check_10`, `B_htc_fill_6`, `B_min`.
- Each is a Boolean-guarded bilinear definition, `¬(B₁ ∧ B₂ ∧ B₃ ∧ I₃ ≠ I₁·I₂)`, which amounts to
  `I₃ = I₁·I₂` under three flags.
- These are the four "syntactically symbolic products" the handoff's triage mentioned.
- They are not power equations, and they are not equalities in positive context, so the adapter
  leaves them to the solver.

**cvc5: the three flagged files.**
- `disj-eval`, `x·x = y·y·y`: recognized as `m² = (r n + s)³ + k` with `k = 0`. That is the
  singular curve `m² = t³`, which has infinitely many points (`t = u²`), so it is rejected.
  The finite value sets that make the file easy are left to the solver.
- `proj-issue-425`, `x·x = y`: recognized as a square equal to a linear polynomial, which is not
  an affine cube. It is not replaced, and the file is an intentional option-parsing failure test.
- `pow2-monotone-neg-soundness`: `int.pow2` is an extension and is classified as unsupported.
- The other 123 nonlinear conjuncts are not equalities (112), have shapes outside the fragment
  (9), or use terms the normalizer refuses (3, `*_L` helper symbols).

**STAUB:** `x³ + y³ + z³ = 855` has three unknowns and lies outside the fragment. Its source
status (SAT) is metadata, not a certificate.

## Where the time goes (`z3_query_timing.json`)

ELSTER, z3 5.1.0, 2 s per query:
- Queries run: 11,739, with results sat 9,750, unsat 1,866, unknown (hit 2 s) 123.
- 1,062 queries were not run because of the 120 s budget per file.
- Summed query time: 607 s.

| live atoms in the query | queries run | hit 2 s |
|---|---:|---:|
| a guarded bilinear product | 3,615 | 7 (0.19 %) |
| linear and `div`/`mod` by numerals only | 8,124 | 116 (1.4 %) |

The hard industrial queries sit in the fragment with no multiplication of unknowns at all:
linear integer arithmetic with `div`/`mod` by constants, over large data-entry forms. No certificate
PerfectPower can issue today applies to them.

The file-level baseline (10 s per file) agrees: 10 of 19 ELSTER files time out, and 4,719 of
12,801 queries are answered inside the file budget. This is a statement about whole query
streams; the file time is never divided among its queries.

## Economics

The handoff's planning equation is `ΔT = N p (t_s − t_c − t_r) − N t_f − K t_g`.
- On this corpus `p = 0`, so `ΔT = −N t_f`: pure routing overhead.
- **Measured `t_f`:** the classifier takes 9.1 s over the 12,801 ELSTER queries, about 0.7 ms per
  query, or 1.5 % of z3's 607 s on the same queries. The per-query share assumes each assertion
  is classified once, as the ledger does.
  - An earlier version took 340 s, 56 % of solve time, because it rebuilt the `define-fun` set
    for every assertion.
  - With the fix, the category counts are identical.
- Any positive business case therefore depends on a workload with `p > 0`. This corpus has none.
- Per query, without averaging, the saving is

  `ΔT = Σ_{q∈E} t_s(q) − Σ_{q∈Q} t_f(q) − Σ_{q∈E} [t_c(q) + t_r(q)] − Σ_{κ∈K} t_g(κ)`

  over eligible queries `E`, all queries `Q` and distinct certified statements `K`. With
  homogeneous averages and reuse `R = Np/K`, specialization pays only if
  `t_s − t_c − t_r − t_f/p > 0` **and** `R > t_g / (t_s − t_c − t_r − t_f/p)`.
- With `p = 0` the first condition cannot hold.
- The 9.1 s figure is classification only. The whole ledger run, with bookkeeping and JSON
  output, takes about 25 s. A deployed measurement must also include certificate checking and
  the residual solve.

## What the adapter guarantees (`python/perfectpower/smt_cert.py`, `python/tests/test_smt_cert.py`)

A replacement is applied only with a certificate that `check_certificate` re-derives from the
source. The certificate fixes:
- the script's SHA-256, the command index, the assertion hash, and the exact atom;
- that the unknowns are Int (`to_poly` rejects any non-Int constant);
- the normalized polynomial, with the coefficients of `(r n + s)³ + k` matched exactly and
  `k ≠ 0`;
- a complete theorem whose Lean statement is re-parsed and quantifies over **all** integers, so no
  `n ≥ 1` contract is involved;
- witness and sign transport, with each witness re-evaluated on the atom.

`test_smt_cert.py` covers the following. Each case is either rejected or left unrecognized:
- a malformed certificate, a wrong binding (file, index, atom), and changed coefficients or `k`;
- a dropped sign witness, and negative and zero inputs;
- `div`, `or`, `not`, `let`, `define-fun` and extension contexts, the singular `k = 0` curve, a
  curve with no parsed theorem, three unknowns, and `Real` sort;
- live-stack scoping across `push`/`pop`;
- a box check that the finite replacement is equivalent to the atom on `|n| ≤ 400`.

The trust boundary: a checked replacement is a statement about one mathematical Int conjunct,
backed by a Lean theorem and by a Python-checked substitution. No consumer checker (Why3,
GNATprove, an SMT proof checker) accepts it yet.

## What would test the current fragment

These are the smallest real workloads likely to contain `m² = (rn+s)³ + k`, bounded Pell
equations, or affine disguises of them:
1. **SMT-LIB `QF_NIA/MathProblems`** (the `STC_*` family, where the STAUB sample comes from). It
   is crafted but independently authored arithmetic, with cubes and power sums. The handoff's
   GitHub route (`fetch_remaining_elster.py`'s approach) can pin and fetch a family manifest
   without Zenodo.
2. **Saved GNATprove/Why3 SMT tasks from SPARK code with nonlinear specifications**, such as
   lemma-library clients and code with explicit square or cube identities. This is the workload
   the AdaCore question is actually about, and only a customer or the SPARK team can supply it.
3. **The remaining 162 ELSTER files**, via `tools/fetch_remaining_elster.py`. They would test
   whether the bilinear `type2` pattern is common. Given the timing above, that would inform a
   *different* fragment (guarded products, linear plus `div`/`mod`), not the current one.

The next fragment this corpus actually motivates is not PerfectPower's: certified reasoning for
linear integer arithmetic with `div`/`mod` by constants. PerfectPower's exact residue and
periodicity machinery is related in spirit (finite-state filters), but no such certificate
exists here, and none is claimed.
