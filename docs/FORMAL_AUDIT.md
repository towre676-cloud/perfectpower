# Formal boundary and audit

**Release 0.6.** The Lean library builds with Lean `v4.20.0` against Mathlib tag `v4.20.0`. The dependency is a git requirement, with its exact revision recorded in `lake-manifest.json`.

In the build environment of this release, the Mathlib cache and release servers were unreachable, so Mathlib was compiled from source (about 1900 modules). CI uses `leanprover/lean-action` and the ordinary cache.

`./audit/check_axioms.sh` runs `#print axioms` on eighteen declarations. It fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, which excludes both `sorryAx` and custom axioms. This check passed for release 0.6. The results below are therefore `LEAN_VERIFIED` in the sense of [the receipt policy](RECEIPTS.md).

## What changed from 0.5

The 0.5 sources had never been elaborated. On the first build `Basic.lean` and `Dichotomy.lean` compiled unchanged, and `Density.lean`, `Rigid.lean` and `Estimates.lean` failed. The failures and repairs were:

- **`Density.lean`, `limsup_le_of_tendsto_sub`:**
  - A coboundedness lemma received an `Eventually` where it expects a pointwise bound.
  - The final ε-step compared `u n` with `limsup v + ε/2` when only `limsup v + ε` is available. The mathematical statement was correct; the tactic proof was not.
- **`Rigid.lean`:**
  - `binom_remainder`: an `omega` goal needed a rewrite in the goal as well as the hypothesis.
  - `trunc_induction`: an `omega` goal mixed `e * Q.natDegree` with `e * q`, and needed a rewrite by `hQd`.
  - `trunc_induction`: a `field_simp` residue needed `rw [← hN1eq]; ring`.
- **`Estimates.lean`:**
  - A missing `ring` after `field_simp` in `abs_sub_ge_inv`.
  - `le_self_pow` no longer applies to `ℝ` in this Mathlib; replaced by `le_self_pow₀`.
- **Deprecation renames:** `pow_le_pow_left₀`, `div_lt_div_iff₀`, `Finset.card_insert_of_notMem`, and `∑ x ∈ s`.
- **Imports:** `import Mathlib` was replaced by the five modules actually needed.

No theorem statement of 0.5 was changed.

## What the build certifies

| File | Declarations (all compiled, standard axioms only) |
|---|---|
| `Basic.lean` | `IsHit`, `hitSet`, `A`, `ratio`, `HasDensity`, `H`; `H_eq_of_hasDensity` |
| `Density.lean` | `A_succ`, `A_le`, `hasDensity_zero_of_finite`, `A_sub_eq_const` (exact surgery identity), `H_surgery`, `hasDensity_of_periodic` |
| `Rigid.lean` | `exists_denominator`, `frac_periodic`, `integral_closure_step` (Gauss content), `binom_remainder`, `trunc_induction`, `exists_truncated_root` |
| `Estimates.lean` | `abs_sub_ge_inv`, `abs_sub_one_le_abs_pow_sub_one`, `analytic_eventually`, `pow_diff_bound`, `eventually_no_hit` |
| `Dichotomy.lean` | `rigid_dichotomy`: rigid $F\ne0$ is $G^d$ over $\mathbb Z$, or has finitely many hits |
| `ZeroOne.lean` (new) | `hasDensity_one_of_pow`, **`rigid_zero_one`** (density exists and is $1$ or $0$ on the rigid branch), `rigid_H_mem`, `pow_of_mul_pow_eq`, `twisted_hits_subset`, `twisted_finite`, `twisted_density_zero` |

## What it does not certify

- **The nonrigid density-zero branch.** This is Boshernitzan's criterion, or alternatively LeVeque's theorem. Both remain named external theorems.
- **The atlas (Theorems B, C), the explicit Runge thresholds of Theorem R, the shift spectrum, and the transform theorems.** These are paper proofs. The Python implementations are checked against direct scans, but a Python test is not a Lean proof, and the Lean kernel does not certify the Python code.
- **The Python certificate verifier.** It shares its mathematics with `eventually_no_hit` but is a separate artifact.

## Interface notes

`IsHit` accepts every natural $d$. Public theorems assume $2\le d$ where it matters; `hasDensity_one_of_pow` does not need it. Hits are indexed from $n=1$. The shift $k$ is a parameter of `hitSet`/`A`, and the polynomial theorems use $k=0$ with the shift absorbed into $F$.

The next formal targets, in order, are:

1. Theorem P in its $\mathbb Q[x]$ form, derived from `twisted_hits_subset` by clearing denominators.
2. The valuation characterisation behind Theorem B.
3. The explicit threshold inequalities of Theorem R, which would let a certificate be checked by `decide`/`norm_num` rather than trusted Python.
