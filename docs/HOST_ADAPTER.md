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
| `vc_pairs_square.smt2` | `2 ≤ N ≤ 10⁹`, `N(N−1) = 2S²` | `N mod 4 ∈ {1, 2}` | `unknown` at 30 s | proved in 0.003 s (24 solutions `(N, S)`) |

## Benchmark (`python/host_adapter_bench.py`, `receipts/host_adapter_bench.json`)

BENCH_PLACEHOLDER

## What would make this evidence

These instances are constructed to contain a recognizable conjunct, so they show the mechanism,
not its frequency. The test that matters is independently sourced tasks, such as saved
GNATprove/Why3 SMT-LIB tasks or the SMT-LIB `QF_NIA` library. On those, three things need
measuring:
- how often a supported structure occurs;
- the total time with recognition included, on unsupported tasks as well;
- how often an unproved task becomes proved.
