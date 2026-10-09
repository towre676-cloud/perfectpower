# Certified Stokes data without closed forms, repeated eigenvalues and ramified exponents

This completes the parts of open item N42 that [DYADIC_REDUCTION_AND_STOKES_MONOGRAPH.md](DYADIC_REDUCTION_AND_STOKES_MONOGRAPH.md) left out:

- certified Stokes data for irregular singular systems with no closed form;
- repeated leading eigenvalues;
- ramified (fractional) irregular exponents.

The module is `python/perfectpower/irregular_stokes_general.py`, which imports from `irregular_stokes.py`. The develop script is `python/develop_irregular_stokes_general.py`, which writes `receipts/curve_structure/irregular_stokes_general.json`. A rerun reproduces the receipt byte for byte (sha256 `01abf291…`). The run takes about one minute on one core. There are 15 tests in `python/tests/test_irregular_stokes_general.py`; they take about 3 s.

Closed forms appear only as validation targets. Every certified number comes from one route, described below, which never evaluates a special function.

## Setting and conventions

The system is Y′ = A(z)Y with A(z) = A₀ + A₁/z + … + A_J/z^J, at z = ∞. A₀ must be diagonalisable with real rational eigenvalues λ. The formal fundamental solution is

  Ŷ = P F(z) z^L e^{Λz},  F = Σ F_k z^{-k},  F₀ = I,  L = diag(μ).

The conventions are those of `irregular_stokes.py`:

- Y₁ is the sectorial solution on a sector containing arg z ∈ [0, π].
- Y₀ is the sectorial solution on a sector containing arg z ∈ [−π, 0].
- Y₀ = Y₁ S₀ across arg z = 0.
- Y₂(z) = Y₀(z e^{−2πi}) e^{2πiL}, and Y₂ = Y₁ S_π across arg z = π.
- The monodromy is M = S₀ e^{2πiL} S_π^{−1}.

With eigenvalues in increasing order, S₀ is block upper unipotent and S_π is block lower unipotent.

## Method

### 1. Exact formal data

`formal_data` runs the recursion of `irregular_stokes.formal_normal_form`, generalised from the diagonal to clusters of equal eigenvalues. On each eigenspace of dimension greater than one, the frame is chosen so that the residue block is diagonal. Inside a cluster (λ_i = λ_k), the level-m equation fixes F_{m−1} through

  (m − 1 + μ_i − μ_k) F_{m−1,ik} = −(Σ_{l ∉ cluster} B_{1,il} F_{m−1,lk} + Σ_{j≥2} (B_j F_{m−j})_{ik}).

This requires μ_k − μ_i not to be a positive integer (non-resonance). A Jordan leading term or a resonant residue block raises an error. The defining identity is replayed exactly at every level. When the eigenvalues are distinct, the coefficients are compared with `formal_normal_form`; they agree exactly.

### 2. Volterra enclosure of the sectorial solutions

Truncate F at order N and substitute W = F_N(z)V. Then

  V′ = (Λ + L/z + E)V,  E = F_N^{−1} R_N,

where R_N(z) = Σ_{m=N+1}^{N+J} R_m z^{−m} is an exact Laurent polynomial; its levels 1 to N vanish. For |t| ≥ R:

  ‖E(t)‖ ≤ C |t|^{−N−1},  C = Σ_m ‖R_m‖ R^{N+1−m} / (1 − δ),  δ = Σ_{k≤N} ‖F_k‖ R^{−k} < 1.

Column j is z^{μ_j} e^{λ_j z} (e_j + q), where

  q_i(z) = −∫_z^{z+i∞} e^{(λ_i−λ_j)(z−t)} (z/t)^{μ_i−μ_j} [E(e_j+q)]_i dt.

On the vertical ray above iR the exponential factor has modulus 1, because the λ are real. Also |z/t|^{μ_i−μ_j} ≤ (|t|/|z|)^σ with σ = max μ − min μ. The Volterra operator is therefore a contraction with constant

  φ = C R^{−N} / (N − σ),

and its fixed point satisfies ‖q‖_∞ ≤ η = φ / (1 − φ) on the whole ray (Banach fixed point). The bound is an exact rational number. `best_truncation` chooses the N that minimises η.

This fixed point is Y₁. The difference of the two is a combination of the columns of Y₁, and along the ray it is O(|z|^{μ_j−N}). Look at the component with the largest μ among the nonzero coefficients: every coefficient vanishes once N > σ. Only the classical existence of the sectorial solutions (Hukuhara–Turrittin–Sibuya, or 1-summability) is used; their values never are. The downward ray from −iR gives Y₀ in the same way.

The enclosure is kept in factored form, F_N(z) · (I + D^{−1}QD) · D. The entries of D^{−1}QD are bounded by η R^{μ_k−μ_i}. This keeps the Arb balls close to first-order sharp.

### 3. Certified Taylor transport

`Transporter` works for any n and J in the eigenframe gauge. Around a centre c, take ρ′ = |c|/2. Then

  A(c+u) ≪ K M_J / (1 − u/ρ′),  K = Σ_j ‖B_j‖ |c|^{−j},  M_J = max_k C(k+J−1, k) 2^{−k}.

The Taylor coefficients therefore satisfy ‖Y_m‖ ≤ (κ)_m / (m! ρ′^m) with κ = K M_J ρ′. The tail is bounded in Arb by 2T_N once the ratio is at most ½. Every step is between Gaussian-rational points with |h| ≤ |c|/4.

### 4. Stokes matrices

  S₀ = Y₁(iR)^{−1} T_cw^{−1} Y₀(−iR),  S_π = Y₁(iR)^{−1} T_ccw^{−1} Y₀(−iR) e^{2πiL}.

Here T_cw and T_ccw are the transports along the two half-circles of radius R.

## What is checked, and what each check means

Every run reports these checks, and all of them must hold.

1. **Block-unipotent shape.** S₀ is upper and S_π lower unipotent. Entries between equal eigenvalues overlap 0. A wrong sectorial solution breaks this.
2. **Sectorial enclosures along the axis.** Y₁(iR) is transported to i·5R/4 and compared with the independent Volterra enclosure there, which has its own N. The same is done for Y₀ downward. The product Y(5R/4)^{−1} T Y(R) must contain I. This tests the asymptotic bound directly, column by column.
3. **Cyclic relation.** S₀ e^{2πiL} S_π^{−1} must overlap the monodromy from an independent loop of radius 3. Because both Stokes matrices are built from the same transports, this relation is structural. What it certifies is that the transports agree with an independent loop (homotopy invariance). It is not an independent test of the Stokes multipliers.
4. **Liouville.** det M along the small loop overlaps exp(2πi tr A₁).
5. **Local exponents at 0 (J = 1 only).** The characteristic polynomial of the cyclic product overlaps ∏(x − e^{2πiρ}), where ρ runs over the eigenvalues of A₁. The ρ are enclosed as algebraic numbers with `fmpq_poly.complex_roots`.

Independent evidence on the multipliers themselves comes from four sources:

- **Two radii.** Systems without a closed form are certified at two radii, with independent truncations, enclosures and transports. All balls overlap.
- **Closed forms.** Contained wherever one exists.
- **Earlier numerics.** The numerical-only values from `irregular_stokes.json` are reproduced to 2.4·10⁻¹⁴.
- **Borel–Padé.** Agreement to 3·10⁻¹⁷ and 6·10⁻¹⁸ on the two 2×2 cases checked.

**Negative controls.** For four systems at R = 24 the proven η was divided by 10³. Checks 1 and 2 then fail every time (receipt `negative_controls`). So the checks can tell a wrong enclosure from a right one, and the proven bound is within about three orders of magnitude of sharp.

## Results

### Validation on Kummer

The eight (a, b) pairs of the earlier receipt were rerun at R = 48:

- six generic pairs;
- a Bessel ν = 0 case;
- a polynomial case, a = −1, where s_π = 0.

Every ball contains the closed forms s₀ = 2πi / (Γ(1−a)Γ(b−a)) and s_π = −2πi e^{iπ(b−2a)} / (Γ(a)Γ(1+a−b)). Ball radii run from 3·10⁻²² to 1·10⁻¹² (the widest is the polynomial case, where σ = 5/2).

`birkhoff2_closed_form` maps any 2×2 system A₀ + A₁/z to Kummer, with possibly irrational (a, b). Both roots of its quadratic give the same multipliers. It serves as the closed-form oracle in part B.

### Unramified systems without a closed form

| system | R | N (at larger R) | η | max ball radius |
|---|---|---|---|---|
| 2×2 with A₂ term, the numerical-only system of `irregular_stokes.json` (z = 0 irregular) | 40, 56 | 56 | 1.4e-24 | 1e-22 |
| 2×2 with A₂ and A₃ terms, non-diagonal A₀ (eigenvalues ±1) | 40, 56 | 112 | 8.3e-49 | 9e-28 |
| 3×3 Birkhoff system A₀ + A₁/z, generic A₁ (local exponents algebraic of degree 3) | 40, 56 | 56 | 1.8e-24 | 4e-22 |
| 3×3 Birkhoff system, triangular A₀ with eigenvalues 0, 1, 3 | 36, 48 | 48 | 1.2e-22 | 7e-18 |
| 3×3 with A₂ term (z = 0 irregular) | 40, 56 | 56 | 2.1e-24 | 8e-22 |
| repeated eigenvalue 1 (multiplicity 2), generic residue | 40, 56 | 56 | 8.9e-26 | 4e-24 |

For the first system: s₀ = 1.77711581377346487294869… i and s_π = −0.920243576823378118514… − 1.593908630397004242008… i. Before this work these values were numerical only.

There are two repeated-eigenvalue validations with known answers. Each takes Kummer systems, adds a block, and conjugates the result by a rational matrix:

- Kummer(1/3, 3/4) ⊕ [1 + (2/5)/z] gives eigenvalues 0, 1, 1.
- Kummer(1/3, 3/4) ⊕ Kummer(2/5, 7/3) gives eigenvalues 0, 0, 1, 1.

In both, the Stokes entries that couple different blocks are certified to contain 0, and the normalisation-free products s₀s_π contain the Kummer closed forms. In the 4×4 case the code identifies the matched pairs on its own.

## Part B: Turrittin reduction (repeated Jordan eigenvalues, ramification)

Scalar operators are written in θ-form, Σ a_j(x)θ^j with θ = x d/dx and Laurent coefficients. The code works exactly in sympy:

- Newton polygon at ∞ and edge polynomials (`newton_edges`);
- exponential shifts θ → θ + u x^m;
- ramification x = t^b;
- recursion on repeated roots, restricted to slopes below the parent's (`turrittin_scalar`).

The output is the full list of formal exponential factors q_i(z^{1/q}), each with its power of z. Examples in the receipt:

| operator | exponential factors |
|---|---|
| Airy | e^{∓(2/3)z^{3/2}} z^{−1/4} |
| hyper-Airy w‴ = zw | e^{(3/4)ω z^{4/3}} z^{−1/3}, for the three cube roots of unity ω |
| (θ − z)(θ² − z), mixed slopes | e^{±2z^{1/2}} z^{−1/4} and e^{z} z^{−2} |
| zw″ + (1−2z)w′ + (z−2)w = 0 (double root at slope 1, then slope 1/2) | e^{z ± 2z^{1/2}} z^{−1/4} |
| w‴ = z²w′ + w | 1 and e^{±z²/2} z^{−3/2} |

`reduce_to_rank_one` applies when the factors are ψ(z) + c_i z^{p/q}, with ψ common and the c_i distinct and rational. It performs these steps:

1. Shift w = e^ψ v.
2. Ramify t = z^{1/q}.
3. Form the companion system in θ_t.
4. Shear by diag(t^{kp}).
5. Substitute s = t^p.

The result is a Poincaré-rank-one system in s with distinct eigenvalues c_i. It exists only when the sheared system contains no powers other than t^{p−kp}; otherwise the code raises an error. For every certified example, the Turrittin powers of z equal p/q times the formal exponents μ of the reduced system (exact check). Part A then certifies the system in s. The Stokes rays arg s = 0, π lie at arg z = 0 and qπ/p.

| equation | leading structure | R | certified s₀, s_π | classical value contained |
|---|---|---|---|---|
| Airy w″ = zw | nilpotent A₀, Katz 3/2 | 40, 56 | i, −i (radius 3e-30) | s₀ = i from Ai(z) + ωAi(ωz) + ω²Ai(ω²z) = 0; s_π = −i |
| Weber w″ = (z²/4 + a)w, a = 0, 1/3, −1/4, 1/2, 3/2 | nilpotent A₀, Katz 2 | 96 | e.g. a = 1/3: 0.4503208717991079618 i | s₀ = i√(2π)/Γ(1/2−a), s_π = −i e^{−iπa} √(2π)/Γ(1/2+a); s₀ = 0 at a = 1/2, 3/2 |
| zw″ + (ν+1−2z)w′ + (z−ν−2)w = 0, ν = 0, 1/3, 1/4, 2/5 | A₀ a Jordan block for the double eigenvalue 1, exponents z ± 2z^{1/2} | 24 | ±2i cos πν (radius ≤ 4e-30) | DLMF 10.34.2 for K_ν |
| w″ = (z + 1/(5z²) + 1/(7z⁵))w, no closed form | Katz 3/2, z = 0 irregular (J = 4 in s) | 40, 56 | ±0.20802936960871316158876938530 i | — (two radii overlap; Borel–Padé agrees to 6e-18) |
| θ³ − z³θ + z³/3 + z^{−3}/5, third order, no closed form | exponents 0 and ±(2/3)z^{3/2}, J = 5 in s | 64, 80 | six entries, radius ≤ 2e-16 | — (two radii overlap) |

Where the convention was not already fixed, the classical values were derived by hand for this receipt:

- **Airy:** from the three-term relation, in the normalisation z^{−1/4}e^{∓ξ}.
- **Weber:** from DLMF 12.2.18, in the normalisation z^{−a−1/2}e^{−z²/4}.
- **e^z × Bessel:** from DLMF 10.34.2.

In each case s_π was then obtained from the trace identity tr M = e₁ + e₂ − s₀s_π e₂. Each is also contained in the Kummer-map closed form.

## Not claimed

- **Eigenvalues off the real line.** Leading eigenvalues that are not real rational, or whose differences are not collinear, are out of scope: Bessel J_ν with ±i, hyper-Airy, general 3×3 Stokes geometries with six or more Stokes rays. The Volterra kernel bound uses |e^{(λ_i−λ_j)(z−t)}| = 1 on vertical rays, which needs real λ, and the formal recursion needs rational λ. Rotating the variable would handle collinear cases, but this is not implemented. For hyper-Airy only the formal Turrittin data is given.
- **General Turrittin reduction for systems.** There is no matrix splitting lemma for Jordan leading blocks, no Moser reduction and no cyclic-vector step. Jordan and nilpotent leading terms are reached only through scalar equations.
- **Non-quasi-homogeneous ramified cases.** When the sheared system has powers other than t^{p−kp}, for example w″ = (z + 1/z)w, the reduction stops with an error. Certified Stokes data at higher Poincaré rank in t, or with mixed slopes, is not provided.
- **Resonant or non-diagonalisable residue blocks** on a repeated eigenvalue: these would need logarithmic formal solutions.
- **The cyclic relation is not independent evidence.** S₀e^{2πiL}S_π^{−1} versus the loop monodromy is a transport-consistency check by construction. The independent evidence on the multipliers is listed in the checks section above.
- **Edge-polynomial roots** are needed in closed form (sympy `roots`). Higher-degree irreducible edge polynomials are rejected.
- No Lean. The trust base is Python with exact rationals, sympy for eigenvectors and edge roots, and Arb (python-flint) for every enclosure. The existence of sectorial solutions (Sibuya, Balser) is cited, not proved.

## Replay

```
PYTHONPATH=python python python/develop_irregular_stokes_general.py
PYTHONPATH=python python -m unittest python/tests/test_irregular_stokes_general.py
```
