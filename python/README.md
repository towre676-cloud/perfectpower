# `perfectpower` (Python, standard library only)

The package installs from the repository root with `pip install .` and provides the `perfectpower` command. The CLI and the function API are stable within the 0.6 series.

## Function API

| Function | Returns | Status of the result |
|---|---|---|
| `atlas.classify(F, d)` | Type (`power`, `radical`, `pell`, `finite`, `constant`), $t$-profile, growth, exponent, $\kappa$, effectivity | Paper proofs; the finite type rests on Siegel through Theorem G |
| `atlas.structural_hits(F, d, N)` / `structural_count(F, d, N)` | Exact hits or count up to $N$ from the structure theorems | Paper proofs, cross-checked by scans |
| `runge.runge_enumerate(F, d)` | Complete hit list for rigid $F$ | Theorem R plus exact arithmetic |
| `lean_emit.emit(name, F, d)` / `lean_sandwich.emit_sandwich(name, F, d)` | Lean source of a hit-set theorem | Becomes a theorem only once Lean compiles it |
| `atlas.integerize(F, d)` | Integer polynomial with the same hits as an integer-valued $F\in\mathbb Q[x]$ | Elementary |
| `atlas.shift_spectrum(S, d)` | Critical shifts and the type of $S+k$ | Finite type rests on Siegel through Theorem G |
| `exponential.exponential_progression(c, a, d)` | Hit progression of $c\,a^n$ | Theorem E |

Coefficients are always low-to-high.

Infinitude and growth labels use exact residue or Pell-orbit arithmetic. The JSON
`kappa` field is a floating-point approximation; if a positive constant is too
small to represent, it is `null` and `kappa_exact` carries the expression instead.
Do not interpret `null` as a zero constant.

## CLI

The CLI exposes these commands:

- `scan`
- `classify`
- `count`
- `enumerate`
- `lean` (with `--method runge|sandwich`)
- `shifts`
- `certificate`, `verify` and `surgery`, kept from v0.5

Each command takes `--coeff` and `--d`. For an end-to-end example, see `docs/TUTORIAL.md`.
