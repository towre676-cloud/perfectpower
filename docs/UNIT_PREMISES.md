# Thue equations from unit equations: what Lean checks and what it assumes

This page covers the two cubic fields behind the open Mordell work:
- the field of discriminant 756 (`x³ = 6x + 2`), whose seven Thue classes belong to `y² = x³ − D`
  for `D = 7, 28, 63`;
- the field of discriminant 1944 (`δ³ = 9δ + 6`), which carries the `D = 72` residual
  `H(u, v) = −3u³ + 9uv² − 2v³ = ±1`.

Both are proved complete in Lean under **three named premises**. Every other step is
kernel-checked. The direct maximum-exponent reduction, the unit-domain witness, the residue sieve
and the norm-representative localization come from the direct-H handoff, adapted here.

## The chain

For `F(a, b) = c₀a³ + c₁a²b + c₂ab² + c₃b³` and `φ = c₀θ` (`θ` a root of `F(X, 1)`), put
`γ = c₀a − bφ`. Then `N(γ) = c₀² F(a, b)`, so

  `F(a, b) = M  ⇔  N(γ) = c₀²M  and  γ ∈ ℤc₀ + ℤφ`.

The lattice condition matters: the norm equation has many more solutions than the Thue equation.
The steps:

| step | statement | status |
|---|---|---|
| norm and lattice encoding | `nrm(enc(a, b)) = c₀² F(a, b)`; `dec(enc(a, b)) = (a, b)` | **Lean**: by `ring` per class; `UnitBox.dec_enc` |
| unit generation | every unit of `ℤ[x]` is `±ε₁^a ε₂^b` (`UnitPremises.UnitGen`) | **premise**; finite part in Lean (`unit_box`) |
| norm representatives | every element of norm `N` is `γ₀ · unit` (`UnitPremises.NormRep`) | **premise**; finite hypotheses checked exactly |
| analytic input | Siegel + Matveev: `\|κe₁ + e₂ + μ\| ≤ A e^{−cH}` and `H ≤ M₀` (`UnitPremises.Analytic`) | **premise** |
| direct reduction | `H ≤ M₀ ⇒ … ⇒ H ≤ B` | **Lean**: `DirectReduction.chain_sound`, chains by `decide +kernel` |
| the box | every lattice point of `±γ₀ ε₁^{e₁} ε₂^{e₂}`, `\|eᵢ\| ≤ B`, solving `F = M` is listed | **Lean**: `UnitBox.boxB` by `decide +kernel` |
| small `b` | exhaustive search over `\|b\| ≤ V` below Cauchy's root bound | **Lean**: `UnitBox.cauchy`, `smallB` |
| assembly | the three premises and the checks give the complete list | **Lean**: `UnitPremises.extBound_of`, `UnitBox.thue_list` |
| curves | branch transport to classes with complete lists | **Lean**: `DescentThueList.complete_of_lists` |

## The direct reduction (`DirectReduction.lean`)

The analytic estimates bound the linear form by `A e^{−cH}` with `H = max(|e₁|, |e₂|)`. Keep
`H` there; do not weaken it to `|e₁|`. Take an integer `q` and an integer `p` with
`|qκ − p| ≤ η`, and let `δ` be a lower bound for the distance from `qμ` to the integers. With
`z = −pe₁ − qe₂`,

  `qμ − z = q(κe₁ + e₂ + μ) − e₁(qκ − p)`,

so `δ − Mη ≤ qA e^{−cH}` whenever `|e₁| ≤ M`. If `ε = δ − Mη > 0`, both exponents are bounded at
once: `H ≤ log(qA/ε)/c`. In Lean:
- `reduce` uses the finite Taylor sum `Σ_{k<J} (c(B+1))^k / k! ≤ e^{c(B+1)}`
  (`Real.sum_le_exp_of_nonneg`), so no logarithm or exponential is evaluated;
- `step_sound` replaces every real number by a rational enclosure (`κ ∈ [kl, ku]`,
  `μ ∈ [ml, mu]`, `c ≥ cl`, `A ≤ Au`);
- `chain_sound` iterates the steps.

The bounds drop sharply:

| | before | after |
|---|---|---|
| field 756, classes 0, 1, 2, 18, 19, 20, 50 | 11, 13, 10, 12, 13, 12, 10 | **5, 7, 5, 6, 6, 6, 5** |
| boxes (sum of `(2B + 1)²`) | 4,119 | **1,095** |
| `D = 72` | 35 | **4** (`9²` = 81 elements, was 5,041) |

There are 24 cases and 56 stages in all. Each stage is replayed in Python
(`perfectpower.reduction_check`, with the same definitions) and checked by the kernel. All
fourteen field-756 solutions are still found in the smaller boxes, and the `D = 72` box has no
lattice point.

## Unit generation (`python/unit_basis_witness.py`)

Let `v_r` be the log-embedding of `ε_r`. Any unit `u` can be moved by `ε₁^{−e₁} ε₂^{−e₂}`
(nearest integers to its coordinates) into the centered parallelogram
`{r₁v₁ + r₂v₂ : −1/2 ≤ rᵢ < 1/2}`. There every conjugate satisfies

  `|σᵢ(u)| ≤ Uᵢ = sqrt(max(|σᵢε₁|, 1/|σᵢε₁|) · max(|σᵢε₂|, 1/|σᵢε₂|))`.

Lagrange interpolation turns these bounds into a box for the integral coordinates:

| field | box `(A, B, C)` | triples | norm `±1` | outside the parallelogram |
|---|---|---|---|---|
| 756 | `9, 3, 3` | 931 | 12 | all but `±1` |
| 1944 | `28, 8, 5` | 10,659 | 8 | all but `±1` |

The roots are isolated by rational bisection, and every logarithm is enclosed by a rational atanh
series with an explicit remainder. No floating point is used. Lean checks the finite part:
`unit_box` (`UnitPremises.unitBox_sound`) says every box triple of norm `±1` is a listed
candidate. The real-log fundamental-domain argument is still Python, so `UnitGen` remains a
premise. It no longer rests on PARI's unit basis.

## Norm representatives (`python/norm_rep_localization.py`)

Every norm target is supported on 2 and 3:
- field 756: `576, 256, 8, 8192, 512, 64, 64`;
- field 1944: `±9`.

The script checks the finite hypotheses exactly:
- **Dedekind's criterion at 2 and 3**, the only primes with `p² | disc`. For field 756,
  `g ≡ x³ (mod 2)` with `h = −3x − 1`, and `g ≡ (x + 1)³ (mod 3)` with `h = −x² − 3x − 1`. Neither
  `h` vanishes at the repeated root, so `ℤ[x]` is maximal.
- **Total ramification** at every prime of the support: `(2) = 𝔭₂³`, `(3) = 𝔭₃³`.

The only ideal of norm `2^r 3^s` is then `𝔭₂^r 𝔭₃^s`. Any `γ` with the same absolute norm as the
listed `γ₀` therefore generates the same ideal, so `γ = γ₀ · unit`. In field 1944 the prime 2 is
not totally ramified (`x(x + 1)²`), but the targets `±9` only involve 3. Dedekind's criterion
and the Dedekind–Kummer theorem are cited, not formalized, so `NormRep` remains a premise.

## The analytic premise

`Analytic` asks, for each solution with `|b| > V` and each way of writing
`γ = ±γ₀ ε₁^{e₁} ε₂^{e₂}`, for one case whose real `κ, μ, c, A` lie in the recorded rational
enclosures, with `H ≤ M₀` and `|κe₁ + e₂ + μ| ≤ A e^{−cH}`. The evidence is in
`crosscheck/thue_bound.py`:
- Siegel's identity at the nearest conjugate gives `|Λ| ≤ K₁/|b|³`;
- the conjugate estimates give `log|b| ≥ (H − b')/a`;
- Matveev's theorem (Bugeaud–Mignotte–Siksek 2006, Thm 9.4; `n = 3`, degree 6) gives `M₀`.

The numerics use `mpmath.iv` at 900 bits, and the enclosures are rounded outward. This is the
largest remaining dependency.

## Exponent residues (`python/d72_unit_sieve.py`, measurement)

Assume unit generation. Reduce `ℤ[δ]` modulo `q`. Then every `D = 72` solution has its exponent
pair, taken modulo the unit periods, in the following admissible tables:

| q | periods | survivors |
|---|---|---|
| 5 | 62, 62 | 744 of 3,844 |
| 7 | 48, 16 | 96 of 768 |
| 11 | 120, 120 | 1,320 of 14,400 |
| 13 | 42, 168 | 252 of 7,056 |

These are necessary filters, not completeness results. Tables for different moduli share periods,
so their survival fractions do not multiply.

## Next

- A Lean proof of `UnitGen`. It needs the real embeddings, logarithm enclosures and the
  fundamental-domain argument; the finite part is done.
- A Lean proof of `NormRep`. It needs the index criterion and ideal factorization for these
  orders; the modular facts are done.
- The analytic premise: Matveev's theorem is the boundary that stays external.
- Bounded-Pell replacements carried through `push`/`pop` (`Γ ∧ B ∧ C ⇔ Γ ∧ B ∧ L`), and their
  reconstruction in Why3, as is already done for the Mordell replacement.
