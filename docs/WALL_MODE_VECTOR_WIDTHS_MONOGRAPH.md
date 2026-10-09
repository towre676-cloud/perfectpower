# Gauged vector widths and the electroweak lifetime of the 154.225 GeV wall mode

This note addresses open item N38 ("the electroweak (gauged) lifetime in real time: WW/ZZ channels") and the physics remainder of the declared-wall section of [REMAINING_FRONTS_CONTINUATION.md](REMAINING_FRONTS_CONTINUATION.md) ("the full constrained longitudinal-vector spectrum"). It completes the earlier transverse-electric (TE) calculation of `wall_pair_decay` in four ways:

1. it adds the two remaining physical vector polarizations, the in-plane TM polarization and the normal/longitudinal TM polarization, both with the position-dependent wall mass, and gives the all-polarization WW and ZZ pair widths at g = 0.3, 0.4, 0.5 and 0.6 (g' = 0.36);
2. it checks the Goldstone-boson equivalence limit against the independently computed ungauged Goldstone width;
3. at the physical benchmark g = 0.65, where on-shell pairs are closed, it computes the off-shell VV* → V f f̄ width, the direct Yukawa and gluon channels, and gives a lifetime bracket;
4. it proves, by composing the existing interval certificate of the retuned wall with exact factorizations, that the constrained longitudinal (and transverse) vector spectrum is exactly [m0², ∞) with no localized state and no threshold resonance, and backs this with box and zero-energy numerics.

Code: `python/perfectpower/wall_mode_vector_widths.py`. Replay: `OPENBLAS_NUM_THREADS=1 PYTHONPATH=python python python/develop_wall_mode_vector_widths.py` (about an hour on one core). Receipt: `receipts/flavor_cosmology/wall_mode_vector_widths.json`. Tests: `PYTHONPATH=python python -m unittest python/tests/test_wall_mode_vector_widths.py` (10 tests, about 20 s).

All inputs are the main-branch candidate: v = 30000 GeV, M_heavy = 300000 GeV, g_source = 3000 GeV, v_H = 246 GeV, lambda_H = 0.13, kappa = 1e-7 and the retuned source quartic. The mode mass is M = 154.2250242 GeV. The wall scale is kv = 89.0419 GeV. The Higgs barrier is weak: max(h²/h0² − 1) = 0.0077. The gauge couplings g and g' are declared benchmarks, not a matched extraction.

## 1. The three physical polarizations on a planar wall

Work in unitary gauge with Proca mass m(z) = c h(z) (c = g/2 for W, sqrt(g²+g'²)/2 for Z). This is legitimate because h > 0 everywhere (certified, section 5). The wall preserves the 2+1 Lorentz group of the parallel directions. Every bulk vector mode is therefore a 2+1 particle with 3-momentum P, P² = s3 = k_z² + m0², labelled by its normal momentum k_z. For fixed P the three physical polarizations are:

| polarization | parallel components A^a | normal component A^z | normal profile |
|---|---|---|---|
| TE | (0, ŷ) f | 0 | L_T f = s3 f |
| TM_par | (\|p\|, ω p̂)/sqrt(s3) · f | 0 | L_T f = s3 f |
| TM_n | −i P^a D/sqrt(s3), D = (mχ)'/m² | sqrt(s3) χ/m | L_L χ = s3 χ |

Here L_T = −∂² + m² and L_L = −∂² + m² + 2(m'/m)² − m''/m, the operator derived in the gauge-channel monograph. The polarization ŷ is perpendicular to both the parallel momentum and the wall normal.

**Exact checks** (`exact_identities`, 31 symbolic identities, all reducing to zero):
- the TM_n ansatz satisfies all four components of ∂_μF^{μν} + m(z)² A^ν = 0 when L_L χ = s3 χ;
- its conserved Proca charge density is Im(A*_ν F^{0ν}) = ω χ², exactly, with no boundary term. So χ is delta-normalized exactly like f, and far from the wall the three polarizations reduce to the standard unit vacuum polarizations;
- the vacuum completeness relation Σ ε ε = −g + KK/m² holds;
- the factorization L_L = (−∂ + a_m)(∂ + a_m) + m² holds, with a_m = m'/m;
- the m → 0 intertwining relations hold: χ = (∂ − h'/h)G/k maps Goldstone waves to the massless TM_n waves, and (hχ)' = −k h G.

**Pair amplitudes.** The cubic vertex is (dm²/dH) δH for W⁺W⁻ and for ZZ (the latter with S = 1/2), with δH the canonical Higgs profile of the wall mode. This matches the normalization of `wall_pair_decay`. With parallel momenta P1 = (ω1, p), P2 = (ω2, −p), P1 + P2 = (M, 0), the amplitudes per parity are:
- TE·TE: G_TT;
- TM_par·TM_par: G_TT (P1·P2)/sqrt(s1 s2);
- TM_par·TM_n: G_{T,D} p M/sqrt(s1 s2), coupling an f wave of one parity to a χ wave of the opposite parity;
- TM_n·TM_n: −(P1·P2)/sqrt(s1 s2) G_{DD} − sqrt(s1 s2) G_{CC}, with C = χ/m.

Distinct polarization and parity final states do not interfere. The width is Γ = S/(8M²) ∫ dk dl Σ |amp|² over the open normal-momentum domain, exactly as in `wall_pair_decay`.

**Independent normalization tests.**
- *Vacuum polarization sum.* For a flat background with a Gaussian vertex, the polarization-resolved standing-wave width equals an independent plane-wave formula with the covariant polarization sum 2 + (K1·K2)²/(m1² m2²), to 2e-6 relative. Equal and unequal leg masses were tested.
- *Bulk limit.* For a wall-mode profile of width σ, the width tends to the textbook 3+1 Higgs widths as σ grows: Γ(H→WW) = 2 M³/(32π v²) sqrt(1−4x)(1−4x+12x²), Γ(H→ZZ) with δ = 1, Γ(H→f f̄) and the heavy-top Γ(H→gg). The error is O(1/(Mσ)²): it falls by a factor 3.5–4.5 when σ doubles and is below 0.3% at Mσ = 24.
- *TE reproduction.* The TE sector reproduces the main receipt's TE widths. At the finest resolution, W_TE = 9.2014893763e-10 GeV and Z_TE = 8.4471546270e-10 GeV, against main's 9.20148937628e-10 and 8.44715462700e-10.

## 2. On-shell all-polarization pair widths

Resolution: 193 momentum nodes, 2601 spatial nodes, phase-space order 64. g' = 0.36. Widths in GeV. "mixed" is TM_par·TM_n plus TM_n·TM_par.

| g | m_W | WW total | TE | TM_par pair | mixed | TM_n pair | ZZ total | VV total | τ from VV only |
|---|---|---|---|---|---|---|---|---|---|
| 0.3 | 36.90 | 1.76920e-8 | 3.4494e-10 | 5.4029e-9 | 5.3598e-9 | 6.5843e-9 | 5.35076e-9 | 2.30427e-8 | 2.86e-17 s |
| 0.4 | 49.20 | 1.34752e-8 | 9.2015e-10 | 5.4400e-9 | 2.6781e-9 | 4.4370e-9 | 3.81350e-9 | 1.72887e-8 | 3.81e-17 s |
| 0.5 | 61.50 | 9.40262e-9 | 1.6039e-9 | 4.0570e-9 | 7.0576e-10 | 3.0359e-9 | 7.02480e-10 | 1.01051e-8 | 6.51e-17 s |
| 0.6 | 73.80 | 3.23903e-9 | 9.8568e-10 | 1.1742e-9 | 1.0961e-11 | 1.0681e-9 | closed | 3.23903e-9 | 2.03e-16 s |
| 0.65 | 79.95 | closed | | | | | closed | 0 | |

The ZZ breakdown at g = 0.4 is: TE 8.447e-10, TM_par pair 1.583e-9, mixed 1.436e-10, TM_n pair 1.242e-9. At g = 0.6, 2m_Z = 172.1 GeV > M, so ZZ is closed.

**Earlier TE-only partial widths underestimated the vector-pair width.** At g = 0.4 the total is 9.8 times the TE-only sum (1.7649e-9 GeV), and at g = 0.3 it is 21.9 times.

**Numerical controls.**
- At g = 0.4 the WW width changes by 2.0e-4 relative from (97, 1301, 32) to (193, 2601, 64), and by 1.1e-6 from there to (289, 3901, 96).
- At g = 0.6 the corresponding changes are 1.3e-6 and 7.8e-8.
- A length-18 reconstruction of the wall and mode agrees with length 22 to 5e-10 relative.

**Threshold law.** The WW scan approaches the threshold M − 2m_W = ε from 0.1 GeV down to 3e-5 GeV. The local log slopes between the last two points are 2.98889 (TE), 2.98889 (TM_par pair) and 2.98877 (TM_n pair), approaching 3. The mixed sector approaches 4.0 (3.99555), because it carries an extra |p|² ∝ ε. Near threshold the three diagonal sectors become equal (6.1768e-19, 6.1768e-19 and 6.1825e-19 GeV at ε = 1e-4 GeV), as non-relativistic spin independence requires.

The ε³ law is the signature of a non-resonant threshold in both L_T and L_L. Section 5 proves that there is no threshold resonance. The ε³ regime sets in only for ε well below about 1/(m_W a²) ≈ 0.008 GeV, where a ≈ 1.2 GeV⁻¹ is the even zero-energy scattering length. That is why the slopes are still 1.6–2.7 at ε ≥ 1e-3 GeV.

## 3. Goldstone-boson equivalence

Hold the wall and the vertex fixed and let m_V/M → 0. Equivalence requires the W⁺_L W⁻_L width to tend to the G⁺G⁻ width. That is 2/3 of the three-Goldstone ungauged width Γ_GG = 3.83233456e-8 GeV, which `wall_pair_decay.candidate_pair_data` recomputes in the same run (and the real-time study of `wall_mode_lifetime` confirmed).

The longitudinal amplitude contains only the Higgs component ψ_H of the mode. The Goldstone vertex contains both the λ_H h ψ_H and the portal κ u ψ_u terms. The equivalence therefore also tests the cubic Ward identity h c_GG = Eψ_H + ψ_H'' − (h''/h)ψ_H and the intertwining identities of section 1.

| m_W [GeV] | 24.6 | 12.3 | 6.15 | 3.075 | 1.5375 | 0.769 | 0.384 |
|---|---|---|---|---|---|---|---|
| Γ(TM_n TM_n)/(2Γ_GG/3) | 0.39628 | 0.62086 | 0.78365 | 0.88366 | 0.93955 | 0.96917 | 0.98443 |

The deficit is linear in m_V at small mass: it halves with each halving of m_V. Two Richardson steps (linear, then quadratic) on this halving ladder give 0.99999 for the extrapolated ratio. The successive second-level extrapolants are 0.98011, 0.99607, 0.99936, 0.99991 and 0.99999.

The other sectors vanish as the equivalence theorem predicts:
- the mixed TM_par·TM_n width vanishes linearly in m_V (its amplitude is O(g));
- the TM_par pair and TE widths vanish as m_V² and m_V⁴.

So the transverse/longitudinal decomposition, the χ normalization and the vertex normalization are mutually consistent with the ungauged calculation.

## 4. Physical coupling g = 0.65: off-shell VV*, fermions and gluons

At g = 0.65, g' = 0.36, the vacuum masses are m_W = 79.95 GeV and m_Z = 91.393 GeV. Both on-shell pairs are closed: M = 154.225 GeV < 2m_W = 159.90 GeV. Section 5 shows that no wall-localized vector state lowers these thresholds. The leading electroweak decays are therefore VV* → V f f̄ (and the four-fermion tails), the direct Yukawa pairs and the loop-induced gluon pair.

**Declared vector widths and fermion content.** These are tree-level widths to massless fermions from the declared couplings, with top excluded:
- W: e, μ, τ doublets plus (u,d) and (c,s) with three colours and unitary CKM. Γ_W = 9 g² m_W/(48π) = 2.01603 GeV.
- Z: three ν; e, μ, τ; u, c, d, s, b with three colours; sin²θ_W = g'²/(g²+g'²) = 0.23474. Γ_Z = 2.43417 GeV.
- Variant: quark channels times (1 + α_s/π) with α_s = 0.110, giving 2.06309 and 2.49300 GeV.

**Off-shell method.** The unitary-gauge propagator numerator, contracted with a conserved massless-fermion current, reduces to −g_{μν}: the polarization sum of a vector of mass sqrt(s). An off-shell leg is therefore the same distorted-wave leg with kinematic mass sqrt(s). Its normal wave keeps the physical barrier and its label k_z, so its 2+1 mass² is k_z² + s. This is the "physical" leg prescription. It treats the fermion pair as plane waves away from the wall.

The width is the double spectral convolution

  Γ = ∫ ds1 ds2 ρ(s1) ρ(s2) Γ_2(M; sqrt s1, sqrt s2),   ρ(s) = (1/π) (sΓ_V/m_V) / ((s−m_V²)² + (sΓ_V/m_V)²),

over sqrt s1 + sqrt s2 < M, using Gauss–Legendre nodes in the Breit–Wigner angle. The numerator sΓ_V/m_V is sqrt(s) Γ_V(sqrt s) for massless fermions.

A fixed-width numerator m_V Γ_V would weight a light virtual leg incorrectly. The longitudinal polarization of that leg grows like 1/s, so the fixed-width form is infrared-sensitive. It is reported only as a diagnostic: it roughly doubles WW* and raises ZZ* about sixfold. It is excluded from the bracket.

OFFSHELL_RESULTS

## 5. The constrained longitudinal-vector spectrum on the certified retuned wall

The Arb certificate `wall_profile_intervals.json` (160 bits; retuned quartic λ = 1.76188164948e-5 ± 1e-15) certifies the following for the exact whole-line wall:
- h > 0;
- h ≥ h0 everywhere, and h > h0 in the interior;
- monotone profiles.

`wall_stability_certified.json` certifies whole-line existence and the asymptotic vacuum. `certified_threshold_statement` reads these flags from the receipts. It composes them with the exact factorization of section 1, as follows. For every declared coupling g > 0, with m0 = g v_H/2:

1. **Spectral floor.** ⟨f, L_T f⟩ = ∫ |f'|² + m²|f|² ≥ m0²‖f‖², and ⟨f, L_L f⟩ = ∫ |f' + a_m f|² + m²|f|² ≥ m0²‖f‖². Both use m² = c²h² ≥ c²h0² = m0².
2. **Essential spectrum.** Both potentials tend to m0² exponentially, so σ_ess = [m0², ∞). There is no discrete eigenvalue, that is, no wall-localized transverse or longitudinal vector state. Hence σ(L_L) = σ(L_T) = [m0², ∞).
3. **No threshold resonance.** Suppose (L − m0²)χ = 0 with χ bounded. Integrating χ(L − m0²)χ gives ∫ |Bχ|² + ∫ (m² − m0²)χ² = 0, because the boundary terms vanish for a bounded zero-energy solution of an exponentially decaying potential. Then χ = 0 wherever h > h0, which is a nonempty open set, so χ ≡ 0.

**Consequence.** The vector-pair threshold of the localized mode is exactly 2m0 at every coupling. On-shell VV is closed if and only if M < 2m0, and the pair widths obey the generic ε³ threshold law of section 2. This closes the positive-profile hypothesis that the TE threshold law of `wall_pair_decay` had left uncertified.

The **trust base** is the Arb profile certificate, the exact symbolic factorization, and standard one-dimensional Schrödinger facts (Weyl's essential-spectrum theorem; asymptotics of zero-energy solutions for exponentially decaying potentials). It is not a Lean theorem. It concerns the retuned wall. The declared λ = 0.1 wall also has a certified h ≥ h0 (REMAINING_FRONTS_CONTINUATION), and the same composition applies to it verbatim, but that wall has no computed mode or widths here.

**Why the factorization is needed.** The longitudinal potential is not pointwise above m0². At g = 0.65 its excess m² + 2a_m² − m''/m − m0² dips to −0.0973 GeV² (maximum 78.6 GeV²). The W transverse excess stays in [0, 49.5] GeV². For Z the dip is at roundoff level (−2.4e-13 GeV²). A potential-based bound fails; the square-plus-mass form does not.

**Numerical controls.**

*Box spectrum.* The box is cell-centred and symmetric tridiagonal, with Dirichlet at R and a parity condition at 0. Beyond the computed profile the excess potential is continued by zero. The lowest W levels above m0², in GeV², at g = 0.65 are:

| R [GeV⁻¹] | L_L even | L_T even | free even (Neumann) | L_L odd | free odd |
|---|---|---|---|---|---|
| 0.247 | 46.8437 | 46.8301 | 40.4188 | 161.784 | 161.675 |
| 0.988 | 3.95534 | 3.96086 | 2.52618 | 10.1058 | 10.1047 |
| 3.953 | 0.397194 | 0.397854 | 0.157886 | 0.631556 | 0.631544 |
| 15.81 | 0.034151 | 0.034175 | 0.009868 | 0.039472 | 0.039472 |

- Every level is above m0².
- Halving dx changes the levels by less than 2e-6 relative.
- The even levels follow the non-resonant law k = π/(R − a) rather than the free π/(2R). At R = 15.81 GeV⁻¹ the prediction with a = −1.2066 GeV⁻¹ is 0.03407 GeV², against 0.034151 measured.
- The Z levels behave the same way.

*Zero-energy scattering lengths.* For the even channel, L_L / L_T:

| g | 0.65 | 0.4 | 0.1 | 0.01 |
|---|---|---|---|---|
| a [GeV⁻¹], L_L / L_T | −1.2066 / −1.2003 | −3.214 / −3.197 | −51.67 / −51.41 | −5169 / −5142 |

|a| grows like 1/g² as the barrier weakens. The resonance appears only at g = 0, where L_L becomes the supersymmetric partner of the ungauged Goldstone operator with the bounded zero mode 1/h. This is the m → 0 limit of section 3. The odd-channel lengths are of order 1e-4 GeV⁻¹.

## 6. Scope and what is not claimed

- **Approximation order.** All widths are tree-level distorted-wave Born rates in unitary gauge on the fixed numerical wall. They are floating-point numbers with numerical controls, not interval enclosures.
- **Off-shell prescription.** Off-shell legs use the double Breit–Wigner factorization with declared tree widths and massless fermions. The near-wall propagation of a virtual leg is approximated by the physical-barrier prescription, and the alternative rescaled-barrier prescription is part of the bracket. No full one-loop vector self-energy in the wall background is computed.
- **Fermion and gluon channels.** These treat fermions and gluons as bulk plane waves. They neglect the wall shift of fermion masses (below 0.4% in h). The gluon pair uses the heavy-top operator at leading order, with a 2× allowance for NLO.
- **Channels not computed.** γγ, Zγ and other loop-induced channels; electroweak and QCD loop corrections to the vertices; the top-mass form factor; thermal effects; real-time nonlinear gauged evolution.
- **Equivalence check.** The Goldstone equivalence is a numerical extrapolation (deficit linear in m_V). It is not an analytic proof of the limit, although the intertwining identities that underlie it are exact.
- **Longitudinal spectrum.** The statement is a composition of an existing Arb certificate with exact algebra and standard spectral facts. It is not a new interval computation and not a Lean theorem. It is made for the retuned wall, whose mode is the one computed.
- **Couplings.** g and g' are declared benchmarks, not experimentally matched couplings. The scan in g is a parameter scan.
- **Replay.** Byte-identical replay on another platform was not verified.
