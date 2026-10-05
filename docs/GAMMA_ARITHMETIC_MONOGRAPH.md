# Gamma as an exact arithmetic input language

PerfectPower now accepts fixed Gamma shifts, rising factorials, finite affine
products, fixed-width binomial coefficients, factorial ratios, linear-index
binomial coefficients and multinomial coefficients. The compiler exposes exact
polynomial reductions, integrality certificates, prime and unit obstructions,
complete bounded decisions, and polynomial-coefficient recurrences. Its domain
is explicitly nonnegative integer indices. It does not approximate Gamma to
decide arithmetic questions.

## From notation to exact arithmetic

A positive affine Gamma base and a fixed nonnegative shift give a finite
product. The supported Gamma quotient has base `a*n+b`, with `a>=0`, `b>=1`,
and shift at most 64. These conditions keep the original Gamma expressions
away from poles. Rising factorials instead accept arbitrary bounded integer
bases and slopes because their finite-product definition is polynomial,
including zero and negative factors. Fixed-width binomials compile to the
falling product divided by `r!`; their polynomial identity holds even when
`0<=n<r`, where the result is zero.

The public `normalize` result contains ascending integer numerator coefficients,
a positive denominator and its natural-index domain. Polynomial identities are
checked exactly. Gamma quotient continuation across poles is not silently
substituted for the meaning of a supplied expression.

The power equation `D*y^d=N(n)` is transported to
`(D*y)^d=D^(d-1)*N(n)`. Both the natural-index restriction and divisibility of
the transformed witness by D are retained. `analyze_expression` uses the unified
arithmetic analysis from the preceding push and lifts only solutions in this
integer image. An unsupported global equation may still have a complete bounded
answer and necessary residue conditions. Negative requested indices are excluded
by the stated domain, and wholly negative bounded intervals are empty.

## Factorial ratios before factorial evaluation

For positive integer slope lists a and b, `factorial_power` tests the ratio of
`(a_i*n)!` to `(b_j*n)!`. It computes the finite Legendre floor sums. A negative
prime exponent proves that the ratio is not integral. An exponent not divisible
by d proves that it cannot be an integer d-th power. Cheap primes are tried
first; exhausting a partial prime list is not advertised as success. Full
positive decisions require every relevant prime, or an exact cancellation
identity. Successful roots are stored as prime/exponent lists, which avoid
constructing enormous integers merely to describe them.

`factorial_unit` computes the factorial with all p powers removed, modulo
`p^depth`. It first builds the product of nonmultiples of p in one residue block,
then combines complete blocks and recursively treats `floor(n/p)`. `ratio_unit`
inverts only these stripped units. Original factorial denominators may have
large p valuation and need not be invertible. The compiler combines valuation
divisibility with the established odd-prime and dyadic unit-power tests. For
example, `101!/100!` passes the cheap prime-exponent list but fails the square
unit test modulo eight. No factorial is constructed for the rejection.

The classical central-binomial family has an unconditional parameterized Lean
theorem. Bertrand supplies a prime between n and 2n, and its exponent in the
central binomial coefficient is exactly one. Consequently, for every exponent
at least two the natural-index power solutions occur only at n=0, with the
appropriate integer signs. The compiler can restrict this complete result to an
interval as large as `[0,10^100]` without scanning that interval.

## Landau and hypergeometric transport

Balanced factorial ratios have a periodic floor-step function. `landau` computes
all rational breakpoints in [0,1], evaluates the right-continuous step on each
half-open cell, and records whether every value is nonnegative. This is an exact
finite implementation of Landau's criterion. Unbalanced inputs are rejected by
this periodic test rather than assigned a false universal verdict. The full
Landau equivalence and general factorial-unit algorithm are not newly proved in
Lean; the balanced periodicity law and Legendre sum are formalized.

`hypergeometric` derives `Q(n)*A(n+1)=P(n)*A(n)` directly from the factorial
increments. On n>=0 every denominator factor is positive. `hypergeometric_terms`
generates exact rational values with a bit budget. This is a variable-coefficient
recurrence interface; it is not passed off as a constant-operator machine.

The compiler also records the formal generating equation
`Q(theta-1)*F = x*P(theta)*F + Q(-1)*A(0)`, with theta=x*d/dx.
The boundary term is retained, including the denominator-free case. A general
Lean coefficient theorem proves this transport over any ring. No analytic
convergence or spectral diagonalization is assumed.

## Interfaces and commands

The main method is `ArithmeticEngine.analyze_gamma`. The equivalent public
function is `perfectpower.gamma_arithmetic.analyze_gamma`. Structured `kind`
values are `gamma_shift`, `rising`, `finite_product`, `binomial`, `factorial`,
`factorial_ratio`, `central_binomial`, `binomial_linear`, and `multinomial`.
Source syntax, domain, budgets, residual information and result scopes remain
in the returned data. `verify_gamma` replays the complete serialized result;
local unit receipts have separate replay functions. These are Python checks;
they do not automatically make an execution a kernel-accepted Lean proof.

Run from the repository with `PYTHONPATH=python python -m perfectpower`:

```
gamma-analyze --spec '{"kind":"gamma_shift","a":1,"b":1,"shift":3}' --interval '[0,1000]' --verify
gamma-analyze --spec '{"kind":"binomial","width":2}' --interval '[0,100]' --verify
gamma-analyze --spec '{"kind":"central_binomial"}' --interval '[0,1000000000000000000000000000000]' --verify
gamma-analyze --spec '{"kind":"factorial_ratio","numerator":[30,1],"denominator":[15,10,6]}' --n 1000 --verify
gamma-unit --numerator '[2]' --denominator '[1,1]' --n 3 --prime 2 --depth 4
beta-period --m 4
finite-mellin --indices '[1,2]' --s 3
```

## Independent mathematical corpus

`data/gamma_bober52.json` contains all 52 sporadic factorial-ratio parameter
families extracted from Table 2 of Jonathan W. Bober's paper. The original HTML
SHA256 is recorded; only mathematical parameters and provenance are vendored.
`python/ingest_gamma_corpus.py` can fetch the source or read a downloaded copy.

`python/benchmark_gamma.py` checks all 52 Landau certificates, compiles all 52
recurrences, compares their first nine values to independent direct factorial
ratios, and compares 1,404 perfect-power decisions for exponents 2,3,5 to exact
integer root extraction. Every comparison passed. At index 1000 each of the 52
families has a cheap square obstruction without factorial construction. Timing
fields record transformation and decision cost, not a general end-to-end speedup
against an industrial solver. The 21 focused tests additionally check domains,
zero cases, image divisibility, dyadic units, budgets and serialized tampering.

## Lean and the parallel push

`GammaArithmetic.lean` proves Gamma/factorial and fixed-shift identities, the
concrete cubic normalization, binomial polynomial/denominator transport,
Legendre's finite sum, prime exponent obstructions, balanced step periodicity,
recurrence uniqueness, and central-binomial power exclusion for natural and
integer witnesses, including its actual real Gamma quotient. These statements
have explicit parameters and domain hypotheses.

`HypergeometricTransport.lean` proves the formal generating equation.
During development, parallel commit `e51beda` added integral output machines;
it is preserved. `IntegralOutputTransport.lean` proves all finite-word outputs
through commuting quotient maps, split output-fibre equivalence, and the exact
diagonal integer image condition, including zero diagonals. It does not prove
Smith discovery, saturation minimality or every saved machine receipt.

The focused check `scripts/check_gamma_arithmetic.sh` compiles and audits 20 new
Lean theorems, all with only standard axioms. It also runs the focused Python
suite and independent corpus. A full historical Lean library rebuild was not
run locally.

## Geometry, Mellin and the analytic boundary

`beta_period(m)` exports the exact symbolic Beta/Gamma expression for the
positive real branch path from zero to one on `y^2=1-x^m`, for m>=3. Branch and
path are explicit; this is a reference integral, not a complete marked period
matrix or a numerical error estimate. `finite_mellin` gives an exact rational
Gamma(s)*Dirichlet sum for a finite positive hit set and a positive integer s.
Zero hit indices are rejected because their Mellin integral diverges.

Controlled complex-Gamma evaluation, infinite Pell Mellin interchange and
certified Fourier/heat tails remain open. This push does not retroactively
certify the floating approximation in `pell_heat.py`, construct a continuous
p-adic Gamma function, or prove a general analytic period matrix.

## Mathematical sources

The normalization follows [DLMF 5.2](https://dlmf.nist.gov/5.2).
The balanced factorial criterion and independent corpus come from
[Bober, arXiv:0709.1977v1](https://arxiv.org/html/0709.1977v1).
The Beta reference uses [DLMF 5.12](https://dlmf.nist.gov/5.12).
Bertrand, Gamma and Legendre theorems are taken from the pinned Mathlib sources
and checked through the new Lean declarations.

The integrated Python suite ran 763 tests: 759 passed and four existing optional
Lean tests were skipped. The new Gamma-focused suite has 21 passing tests.

A fresh extracted repository ZIP also passed the 21 focused tests and all 1,404
independent corpus decisions.

## Complete polynomial domains and optima

The polynomial capacity expansion adds `gamma-domain` and `gamma-optimize` for fixed normalized expressions. They preserve the nonnegative index domain and positive normalization denominator. Comparisons accept exact rational thresholds and clear positive denominators; global optimization scales the exact numerator optimum while preserving every tie. Serialized replay checks normalization and complete domain or forward-difference evidence. These routes do not turn variable-width factorial ratios into polynomials and add no new Lean proof. See [Polynomial capacity](POLYNOMIAL_CAPACITY_MONOGRAPH.md).
