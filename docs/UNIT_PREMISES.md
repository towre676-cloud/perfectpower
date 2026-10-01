# Thue equations from unit equations: what Lean checks and what it assumes

This page covers the two cubic fields behind the open Mordell work:
- the field of discriminant 756 (`x³ = 6x + 2`), whose seven Thue classes belong to `y² = x³ − D`
  for `D = 7, 28, 63`;
- the field of discriminant 1944 (`δ³ = 9δ + 6`), which carries the `D = 72` residual
  `H(u, v) = −3u³ + 9uv² − 2v³ = ±1`.

Both are proved complete in Lean under **one kind of named premise**, the analytic one. There is
one `analytic` premise per class: seven for field 756 and one for `D = 72`, since `H = −1` is
transported by sign. The two structural premises are now Lean theorems for both fields:
- unit generation (`UnitGen.lean`, `unitGen_proved`);
- norm representatives (`NormRepProof.lean`, `normRep_*_proved`).

Every other step is kernel-checked. The direct maximum-exponent reduction, the unit-domain witness, the residue sieve
and the norm-representative localization come from the direct-H handoff. The elementary
norm-representative proof comes from the follow-up handoff. Both are adapted here.

## The chain

For `F(a, b) = c₀a³ + c₁a²b + c₂ab² + c₃b³` and `φ = c₀θ` (`θ` a root of `F(X, 1)`), put
`γ = c₀a − bφ`. Then `N(γ) = c₀² F(a, b)`, so

  `F(a, b) = M  ⇔  N(γ) = c₀²M  and  γ ∈ ℤc₀ + ℤφ`.

The lattice condition matters: the norm equation has many more solutions than the Thue equation.
The steps:

| step | statement | status |
|---|---|---|
| norm and lattice encoding | `nrm(enc(a, b)) = c₀² F(a, b)`; `dec(enc(a, b)) = (a, b)` | **Lean**: by `ring` per class; `UnitBox.dec_enc` |
| unit generation | every unit of `ℤ[x]` is `±ε₁^a ε₂^b` (`UnitPremises.UnitGen`) | **Lean**: `UnitGenProof.unitGen_of_cert`, certificates by `decide +kernel` |
| norm representatives | every element of norm `N` is `γ₀ · unit` (`UnitPremises.NormRep`) | **Lean**: `NormRepProof.normRep756`, `normRep_d72` (explicit division) |
| analytic input | Siegel + Matveev: `\|κe₁ + e₂ + μ\| ≤ A e^{−cH}` and `H ≤ M₀` (`UnitPremises.Analytic`) | **premise** |
| direct reduction | `H ≤ M₀ ⇒ … ⇒ H ≤ B` | **Lean**: `DirectReduction.chain_sound`, chains by `decide +kernel` |
| the box | every lattice point of `±γ₀ ε₁^{e₁} ε₂^{e₂}`, `\|eᵢ\| ≤ B`, solving `F = M` is listed | **Lean**: `UnitBox.boxB` by `decide +kernel` |
| small `b` | exhaustive search over `\|b\| ≤ V` below Cauchy's root bound | **Lean**: `UnitBox.cauchy`, `smallB` |
| assembly | the premises and the checks give the complete list | **Lean**: `UnitPremises.extBound_of`, `UnitBox.thue_list` |
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

## Unit generation, proved (`UnitGen.lean`)

`UnitGenProof.unitGen_of_cert` proves `UnitGen` from a certificate that the kernel checks by
evaluation (`ugCheck`). The bridge from an arbitrary unit to the finite box is a Lean proof:

1. **Embeddings.** Rational brackets with a sign change give three real roots `tᵢ`, by the
   intermediate value theorem (`root_in`). The maps `σᵢ(A, B, C) = A + Btᵢ + Ctᵢ²` are
   multiplicative (`sig_mul`), and `nrm = σ₁σ₂σ₃` (`Roots.nrm_eq`). An element is determined by
   its embeddings, by Lagrange interpolation (`Roots.coords`, `Roots.sig_inj`).
2. **Logarithms.** For a unit, `Lᵢ = log|σᵢ|` sums to 0 (`Roots.L_sum`). The `2 × 2` log matrix
   of `ε₁, ε₂` has nonzero determinant. Each entry is enclosed by
   `n(1 − 1/s) ≤ log y ≤ n(s' − 1)` whenever `sⁿ ≤ y ≤ s'ⁿ` (`log_ge_of`, `log_le_of`), where
   `y` is enclosed from the brackets (`encl_sound`).
3. **Rounding** (`round_step`, `Roots.reduce_unit`). Multiply `u` by `ε₁^{−k₁} ε₂^{−k₂}`, with
   `kᵣ` the nearest integers to its log coordinates. Then `|Lᵢ| ≤ (|Lᵢε₁| + |Lᵢε₂|)/2`, so
   `|σᵢ|² ≤ max(|σᵢε₁|, |σᵢε₁|⁻¹) · max(|σᵢε₂|, |σᵢε₂|⁻¹) ≤ Uᵢ²`. No logarithm is evaluated in
   this step.
4. **The box** (`Roots.coord_bounds`). The bracket gaps bound the coordinates. Every norm-`±1`
   triple in the box is listed with an explicit `±ε₁^x ε₂^y`, checked by evaluation, so the
   parallelogram exclusion of the witness is not needed.

| field | Lean box `(A, B, C)` | triples | units in the box | witness box (Python) |
|---|---|---|---|---|
| 756 | `8, 2, 2` | 425 | 6 | `9, 3, 3`, 931 triples |
| 1944 | `27, 7, 4` | 7,425 | 8 | `28, 8, 5`, 10,659 triples |

Every step uses only the standard axioms.

The exact Python witness (`python/unit_basis_witness.py`) stays as an independent cross-check.
It uses atanh-series logarithm enclosures and the parallelogram exclusion.

## Norm representatives, proved by explicit division (`NormRepProof.lean`)

The proof works in the integer coordinates `g = A + Bx + Cx²` and uses no maximal order and no
ideal theory.

- **Adjugate** (`mul_adj`): `g · g# = N(g)` with
  `g# = ((A + PC)² − (PB + QC)B) + (QC² − AB)x + (B² − AC − PC²)x²`. An element of norm `±1` is a
  unit with inverse `±g#` (`unit_of_nrm`). The norm is multiplicative (`nrm_mul`, by `ring`).
- **Field 1944**, `α = x² − 3x − 3`, `N(α) = 9`:
  - if `9 ∣ N(g)`, then `3 ∣ A` and `3 ∣ B` (`d72_res`, all 729 residues modulo 9);
  - so `g/α = (−3A + 2B − 2C) + (−A/3 − C)x + ((A − B)/3)x²` is integral, and `N(g/α) = 1`
    (`d72_div`);
  - hence `normRep_d72`. The target `−9` follows by the sign transport.
- **Field 756**, `π₂ = x` (norm 2) and `π₃ = 1 + x` (norm −3):
  - `2 ∣ N(g)` forces `2 ∣ A`, so `g/x = (B − 3A) + Cx + (A/2)x²` (`div2`);
  - `3 ∣ N(g)` forces `3 ∣ A − B + C`, so `g/(1 + x)` is integral (`div3`). The residue checks run
    over `ZMod 2` and `ZMod 3`.
  - Induction on `N(g) = ±2^r 3^s` gives `g = x^r (1 + x)^s u` with `N(u) = ±1` (`decomp756`),
    keeping track of the sign of `N(1 + x)`.
  - Doing the same for `γ₀` and dividing gives `g = γ₀ · unit`: `normRep756`.
  - This covers all six targets, `576, 256, 8, 8192, 512, 64`.

The earlier exact checks of Dedekind's criterion and total ramification
(`python/norm_rep_localization.py`) remain as a cross-check.

## The analytic premise

`Analytic` asks, for each solution with `|b| > V` and each way of writing
`γ = ±γ₀ ε₁^{e₁} ε₂^{e₂}`, for one case whose real `κ, μ, c, A` lie in the recorded rational
enclosures, with `H ≤ M₀` and `|κe₁ + e₂ + μ| ≤ A e^{−cH}`. The evidence is in
`crosscheck/thue_bound.py`:
- Siegel's identity at the nearest conjugate gives `|Λ| ≤ K₁/|b|³`;
- the conjugate estimates give `log|b| ≥ (H − b')/a`;
- Matveev's theorem (Bugeaud–Mignotte–Siksek 2006, Thm 9.4; `n = 3`, degree 6) gives `M₀`.

The numerics use `mpmath.iv` at 900 bits. Every constant is the safe endpoint of an interval
enclosure:
- the lower end for `c`;
- the upper end for `K₁`, `b`, `K`, `A` and the Matveev constant;
- `V₀` with `(V₀ + 1)³ > 2K₁` checked on the enclosure;
- `H₀` accepted only when the lower end of `cH₀ − log K − C(1 + log H₀)` is positive.

The rational enclosures handed to Lean are then rounded outward again. This is the
largest remaining dependency.

## Exponent residues (`python/d72_unit_sieve.py`, measurement)

Unit generation is proved, so these tables now apply unconditionally to the exponents. Reduce `ℤ[δ]` modulo `q`. Then every `D = 72` solution has its exponent
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

- The analytic premise: Matveev's theorem is the boundary that stays external.
- Bounded-Pell replacements carried through `push`/`pop` (`Γ ∧ B ∧ C ⇔ Γ ∧ B ∧ L`), and their
  reconstruction in Why3, as is already done for the Mordell replacement.
