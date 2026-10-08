# Nucleation corrections and a certified wall stability gap

This advance does two separate things.

- **Part A** adds radiative corrections to the biased-vacuum nucleation analysis of `wall_nucleation.py` for the declared model: lambda=0.1, v=30 TeV, M_heavy=300 TeV, g=3 TeV, c=0.025000033. The corrections are the zero-temperature one-loop Coleman-Weinberg potential, the full one-loop thermal function in place of its high-temperature truncation, two-loop thermal estimates, and the thermal vector free energy treated as a tension shift. Part A then recomputes the critical biases, S3/T and S4, and a nucleation temperature for amplified-bias benchmarks, each with a bracket.
- **Part B** upgrades the wall's linear stability to an Arb-certified quantitative spectral gap. It applies to the exact wall certified by `wall_profile_intervals.py`, which is the retuned-quartic candidate.

Both parts follow the honest-scope conventions of the earlier monographs. Part A uses floating-point bounces and estimated two-loop terms. Part B uses interval arithmetic plus analytic steps.

## Part A. Corrected effective potential for the biased-vacuum bounce

### Setup and scheme

The reduced variables are as before. With x = phi/v_T and the potential in units of lambda v_T^4, U_tree = (x^2-1)^2/4 - eps x, where v_T^2 = v^2 - cT^2/lambda, r = v/v_T and tau = T/v_T. The field-dependent singlet mass is m^2(phi) = lambda(3phi^2 - v^2), so M = m^2/(lambda v_T^2) = 3x^2 - r^2.

1. **One-loop Coleman-Weinberg, on-shell (zero-momentum) scheme.**
   V_CW = (1/64 pi^2)[m^4(log(m^2/m_v^2) - 3/2) + 2 m^2 m_v^2] with m_v^2 = 2 lambda v^2.
   This form enforces V'(v) = 0 and V''(v) = 2 lambda v^2 at T=0, so the tree vev and curvature mass are kept. The receipt checks both conditions to 1e-14. Where m^2 < 0, between |phi| < v/sqrt 3, the real part (log|m^2|) is used. The heavy mediator enters through M_S^2 = M^2 + 4g^2 phi^2/M^2 in the same scheme. Its field dependence after the on-shell subtraction is below 1e-13 in reduced units, so it decouples. Higgs loops depend on phi only through kappa = 1e-7 and are bounded by 2e-12 in reduced units, so they are not added. The singlet's Z2-even CW potential leaves the bias term -h phi untouched. The MS-bar form at mu = m_v, with tree parameters held fixed, is recorded as a scheme comparison only, because it moves the vev and the mass.
2. **One-loop thermal function beyond the high-T truncation.** The declared c T^2 phi^2/2 contains the phi self-loop piece lambda/4. That piece is replaced by (T^4/2 pi^2) Re J_B(m^2/T^2). For T >= 2000 GeV, |m^2|/T^2 < 4 pi^2 holds on the whole bounce domain. Re J_B is then free of the tachyonic log|sin| singularities and is used directly. The daisy-shifted J_B(m^2/T^2 + lambda/4) is the alternative that enters the bracket. Below that temperature, Re J_B oscillates unphysically in the deep tachyonic region. There the high-T piece is removed, which is the Boltzmann limit since |m| >> T for every non-tachyonic mode, and keeping it is the bracket alternative.
3. **Two-loop thermal estimates (scalar sector, lambda_std = 6 lambda).** The figure-eight term is (lambda_std/8) I_T^2, with the exact massive thermal tadpole I_T = (T^2/2 pi^2) i(|y|). The sunset term is estimated in magnitude as (lambda_std^2 phi^2/12)(T^2/16 pi^2)(|log(3m/T)| + 1) rho, where rho = I_T(m)/I_T(0) accounts for Boltzmann suppression. Zero-temperature two-loop terms are bracketed by (beta_lambda/lambda)|delta s_CW| = (18 lambda/16 pi^2)|delta s_CW|. All of these enter the bracket only, through first-order shifts integrated as Omega_d times the integral of r^{d-1}|delta V(phi_b) - delta V(phi_f)|.
4. **IR sensitivity of CW.** The one-loop curvature has a log singularity at m^2(phi) = 0, which sits next to the spinodal. The bracket includes the first-order change when log|M| is regulated by the bounce's own momentum scale, M_IR = 1/R_core^2. Here R_core is the radius where the field is halfway between phi(0) and the false vacuum.
5. **Thermal vector free energy.** Main's commit 0546f58 computed the relative TE vector free energy per area of the retuned radial candidate wall, for 2W + 1Z at g = 0.65 and g' = 0.36. The values are 7.652, 132.13, 1083.30 and 3098.61 GeV^3 at T = 25, 50, 100 and 150 GeV (receipt sha256 71b8a658...). It is applied as a positive tension shift where it applies, namely the thermal O(3) bounce at those temperatures: delta(S3/T) = dF 4 pi R^2/T, with R = R_core/(sqrt(lambda) v_T). For the declared bias it is applied to the thin-wall tension. Above about 160 GeV the vector masses vanish, and below 25 GeV the shift is exponentially small. This is an order-of-magnitude transport: the free energy was computed for a different quartic and is not recomputed for the lambda = 0.1 wall.

### Results

**The potential.** The on-shell CW correction reshapes the barrier region at the 0.5 percent level. The corrected spinodal moves from eps_sp = 0.384900 to 0.382755, a relative shift of -0.557 percent. The local cubic coefficient changes from sqrt 3 to 2.140 because the IR log is nearby. The unbiased kink tension falls by 0.199 percent. In MS-bar at mu = m_v the spinodal stays at 0.384967. This shows that the on-shell shift mostly reflects the renormalization conditions in the barrier region, and the on-shell scheme is the physically normalized one.

**Critical biases and actions.** Each row below lists the action required for one bubble per Hubble volume and time, S* (central prefactor). It gives the tree critical bias, the corrected action evaluated at the tree critical bias, and the corrected critical bias with its bracket.

| T (GeV) | channel | S* | eps*_tree | corrected S at tree eps* | eps*_corr [bracket] |
|---|---|---|---|---|---|
| 0.03 | O(4) | 245.64 | 0.375866 | 209.0 | 0.374017 [0.373963, 0.374071] |
| 1 | O(4) | 212.69 | 0.377570 | 173.6 | 0.375684 [0.375629, 0.375738] |
| 100 | O(4) | 175.46 | 0.379416 | 132.0 | 0.377486 [0.377430, 0.377542] |
| 300 | O(4) | 166.57 | 0.379840 | 122.0 | 0.377912 [0.377843, 0.377980] |
| 1000 | O(3) | 141.45 | 0.378984 | 103.9 +/- 4.2 | 0.377148 [0.376939, 0.377357] |
| 2000 | O(3) | 138.64 | 0.371641 | 126.9 +/- 0.5 | 0.370365 [0.370312, 0.370418] |
| 2999 | O(3) | 137.01 | 0.364128 | 132.7 +/- 0.3 | 0.363415 [0.363362, 0.363468] |

The O(4) actions at the tree critical biases drop by 15 to 27 percent. The O(4) critical bias shifts down by 0.47 to 0.51 percent below 1 TeV, and by 0.38 and 0.29 percent at 2000 and 2999 GeV. The thermal O(3) critical bias shifts down by 0.48, 0.34 and 0.20 percent at 1000, 2000 and 2999 GeV.

The partial compensation at the highest temperatures comes from the full one-loop thermal function. There the corrected O(3) S3/T at the tree critical bias is 132.7 +/- 0.3 instead of 137.0. At 25 to 300 GeV the tree critical bias of the O(3) channel lies above the corrected spinodal, so the corrected barrier is absent there. That channel is not the easier one at those temperatures, and its near-spinodal corrected numbers inherit the uncontrolled IR log.

**Which corrections dominate.** The zero-temperature one-loop CW term dominates at every temperature. Its first-order action shift is -3.6 to -4.6 in s4 and -0.34 to -0.79 in s3, against bracket half-widths of 0.07 to 0.12 and 0.005 to 0.04 respectively. The largest bracket entries differ by channel and temperature:

- For O(4) the leading entry is the CW IR sensitivity (about 0.07 in s4), followed by the two-loop zero-temperature beta estimate (about 0.04).
- At 1000 GeV the leading entry is the one-loop thermal truncation ambiguity: 0.35 in s4 and 0.033 in s3.
- At 2000 to 2999 GeV the two-loop thermal sunset estimate reaches 0.03 to 0.05 in s4.

The figure-eight term never exceeds 0.003. The thermal vector tension shift is at most 8e-5 in S3/T at 100 to 150 GeV, the only temperatures where a thermal O(3) bounce exists alongside a computed vector free energy. For the declared-bias thin wall the vector shift is below 4e-10 of the tension. It is negligible everywhere.

**Nucleation temperature.** Consider the amplified-bias benchmarks eps_A(T) = q eps_sp (1 - (T/3000 GeV)^2)(v/v_T)^3. Their nucleation temperature is defined as the highest grid-interpolated T at which eps_A reaches the easier critical bias.

| q | amplification over declared bias | T_n tree (GeV) | T_n corrected (GeV) [bracket] |
|---|---|---|---|
| 0.990 | 3.98e24 | 175.5 | 268.4 [265.2, 271.6] |
| 0.995 | 4.00e24 | 267.4 | 323.1 [321.8, 324.5] |
| 1.000 | 4.02e24 | 322.6 | 358.1 [356.6, 359.5] |

The corrections raise T_n by 35 to 93 GeV, because nucleation becomes easier at fixed bias. The brackets omit the linear-in-T interpolation between grid points (0.03, 1, 25, 50, 100, 150, 300, 1000, 2000 and 2999 GeV). They also omit the declared prefactor band of exp(+-20), which moves eps* by about +/-0.001, comparable to or larger than the radiative bracket.

**Declared bias.** With the declared bias, eps is about 1e-25 and the thin-wall S3/T is about 10^52 to 10^58 on the grid. The CW tension shift changes log10(S3/T) by -0.0026 and the vector shift by less than 1e-9. **No nucleation temperature exists for the declared bias.** The conclusions of the nucleation section in the flavor-cosmology monograph are unchanged. The bias would have to reach about 98 percent of the corrected spinodal, which is now 0.5 percent lower, rather than the tree value.

### Part A scope

- **Model and channel coverage.** The analysis covers the supplied spectator model with single-field reduced bounces. The three-field sandwich of `wall_nucleation` is not recomputed for the corrected potential, although it is insensitive at the 1e-6 level.
- **Bracket.** The fluctuation determinant is still the declared exp(+-20) band and is not in the radiative bracket.
- **Two-loop terms.** These are estimates: the figure-eight with exact massive tadpoles, a Boltzmann-weighted high-T sunset log, and a beta-function bracket at T=0. They are not diagrams computed with counterterms.
- **Tachyonic region.** Re J_B is used only where it is free of tachyonic singularities.
- **Vector free energy.** It belongs to a different wall and is used as an order-of-magnitude positive tension shift.
- **Numerics.** Bounces are floating point with virial defects of at most 6e-8. There is no interval enclosure, lattice or real-time simulation.
## Part B. An Arb-certified spectral gap for the certified wall

### What was known and what is new

Two earlier results bear on the wall's linear stability. The floating-point theorem in `wall_continuum_stability.py` (declared quartic lambda=0.1) used exact operator identities: a cooperative ground-state identity in the translation sector and a Schur complement in the opposite sector. It checked their hypotheses (P1)-(P5) on a numerical profile. The interval monograph `WALL_PROFILE_INTERVAL_MONOGRAPH.md` then certified a nearby exact whole-line wall for the retuned quartic lambda = 1.76188164948e-5 +/- 1e-15, with alpha=1/10, mu=10, lambda_H=13/100, h0=41/5000 and kappa=1e-7. Its proof uses Python and Arb: a C2 quintic-Hermite trial profile a(x) on 4096 cells of [0,22], continued by the exact vacuum, and a coercive energy ball. It bounds the true solution w by ||w-a||_Q <= eta, where eta = (residual L2 bound)/sqrt(1/2) = 4.78e-7, and ||w-a||_inf <= 8.05e-7. On that certificate, nonnegativity of the translation sector and a kernel spanned by Phi' follow from qualitative arguments. No quantitative gap had been certified.

This part adds a quantitative statement. Every inequality is an outward-rounded Arb comparison, and the tail beyond x=22 is handled analytically.

**Theorem (certified).** Work in x = sqrt(lambda/2) rho with k2 = lambda/2. Let L be the radial Hessian of the certified wall on L^2(R)^3 in the (source, singlet, Higgs) components. For every f in the form domain with <f, Phi'> = 0,

  <f, (L/k2) f> >= gamma ||f||^2,  with gamma > 1.98194114.

Hence L >= 0, ker L = span(Phi') (the translation zero mode is simple), and the radial spectrum contains nothing in (0, gamma k2 v^2). In physical units this interval is (0, 15713.76 GeV^2); the gap is at least 125.3545 GeV. The bottom of the essential spectrum is at most 2 lambda_H h0^2/k2 = 1.98451468, which equals the Higgs threshold m_h = 125.4359 GeV. That upper bound follows from Weyl's theorem and a Rayleigh quotient of the vacuum Hessian on the Higgs direction. The certified gap is therefore within 0.13 percent of the largest value it could have. Below the Higgs continuum, the translation zero mode is the only radial state. The 154.225 GeV odd source shape mode, eigenvalue 3 of the reference kink, lies inside the continuum and is not a bound state.

### Proof

Each step is either exact algebra, checked symbolically in `exact_identities()`, or an Arb inequality.

1. **Reference spectrum (exact).** Set A = d + 2 tanh and B = d + tanh. Then A^dagger A = -d^2 + 6 tanh^2 - 2 and A A^dagger = -d^2 + 4 - 2 sech^2. Similarly B^dagger B = -d^2 + 1 - 2 sech^2 and B B^dagger = -d^2 + 1 >= 1. So -d^2 - 2 sech^2 has spectrum {-1} union [0, infinity). A A^dagger has spectrum {3} union [4, infinity), and q_ref = A^dagger A has spectrum {0, 3} union [4, infinity) on the line. Its eigenvectors are sech^2 (even) and sech tanh (odd). On the half-line with a Neumann condition for f_u (the translation sector: u' even, y' and h' odd), q_ref(f_u) >= 4(||f_u||^2 - |<e0, f_u>|^2), where e0 = sech^2/sqrt(2/3) and the half-line integral of sech^4 is 2/3. With a Dirichlet condition (the opposite sector), q_ref >= 3||f_u||^2. Parity (u odd; y, h even) makes both sectors invariant, so they can be treated separately.

2. **Pointwise Schur/Young bound at the exact solution.** The Hessian entries over k2 are H_uu = 6u^2 - 2 + [2 alpha r_S + 4 alpha^2 u^2/mu^2 + kappa r_H + 2 kappa^2 u^2/lambda_H]/k2, H_yy = mu^2/k2, H_uy = 2 alpha u/k2, H_hh = [lambda_H(3h^2 - h0^2) + kappa(u^2 - 1)]/k2 and H_uh = 2 kappa u h/k2.

   For the source-singlet cross term, Young's inequality with weight (1 - tau) mu^2/k2 and tau = 1/1000 leaves an excess of 4 alpha^2 u^2 tau/(mu^2 k2 (1 - tau)) over the matching 4 alpha^2 u^2/mu^2 entry. The singlet keeps tau mu^2/k2. For the source-Higgs cross term, weight theta B_H with theta = 1/1000 gives a penalty (2 kappa B_u B_h/k2)^2/(theta B_H). The Higgs keeps (1 - theta) B_H. The 2 kappa^2 u^2 term is nonnegative and is dropped, as are the singlet and Higgs kinetic terms. Thus

   q(f) >= q_ref(f_u) - E||f_u||^2 + F_y||f_y||^2 + F_h||f_h||^2,

   with E = 6 dev(2 + dev) + 2 alpha|r_S|/k2 + kappa|r_H|/k2 + (the two penalties). Here dev = sup|u - tanh|.

3. **Enclosures on the exact solution.** On every cell the checker takes the main certificate's quintic trial polynomials. It forms Bernstein enclosures of a_u - (Taylor model of tanh about the cell midpoint), with remainder (0.7699/2)(dx/2)^2 since max|tanh''| = 4/(3 sqrt 3). It does the same for a_u' - sech^2, with remainder 2(dx/2)^2/2. It also encloses |a_u|, |a_h|, r_S(a), r_H(a) and the Higgs entry lambda_H(3a_h^2 - h0^2) + kappa(a_u^2 - 1), and accumulates L2 sums of the derivative quantities. Each enclosure is moved to the exact solution with the uniform error 8.05e-7 and the sharper singlet error 1.61e-9. For x >= 22 the trial is the exact vacuum. There |1 - tanh x| <= 2e^{-2x}, the integral of sech^4 from 22 to infinity is at most 4e^{-88}, r_S = r_H = 0 and H_hh = 2 lambda_H h0^2.

4. **Zero-mode leakage.** Suppose <f_u, u'> + <f_y, y'> + <f_h, h'> = 0. Then <e0, f_u> = c[<sech^2 - u', f_u> - <y', f_y> - <h', f_h>] with c^2 = 3/2. Hence |<e0, f_u>|^2 <= Delta^2 ||f||^2, where Delta^2 = (3/2)(sqrt(||a_u' - sech^2||^2 + ||a_y'||^2 + ||a_h'||^2 + tail) + eta/sqrt(1/4))^2. The derivative error is controlled by the Q norm: ||(w - a)'||_2 <= eta/sqrt(d) with d = 1/4.

5. **Conclusion.** The translation sector satisfies gamma_T = min(4 - E, F_y, F_h) - 4 Delta^2. The opposite sector satisfies gamma_O = min(3 - E, F_y, F_h). Take gamma = min(gamma_T, gamma_O). Because L Phi' = 0 exactly, any f equals a multiple of Phi' plus a component orthogonal to it, and q(f) is the form of the orthogonal part. That gives L >= 0 and the stated kernel.

### Certified numbers (160-bit Arb, replayed at 192 bits)

| quantity | value |
|---|---|
| sup over the half-line of the bound on dev = |u - tanh| | 6.47e-6 |
| E (total source error) | 0.045624, of which the singlet Schur penalty is 0.045452 |
| F_y (singlet floor) | 11351.5 |
| B_H (Higgs Hessian minimum / k2) | 1.983928 |
| F_h = (1 - theta) B_H | 1.981944 |
| Delta^2 (zero-mode leakage) | 8.09e-7 |
| gamma, translation sector | 1.98194114 |
| gamma, opposite sector | 1.98194438 |
| essential-edge upper bound | 1.98451468 |
| gap (GeV) | > 125.3545, versus m_h = 125.4359 |

Tightening the splitting is deliberately rejected: tau = 0.999 or theta = 1 - 1e-7 make the certificate fail, as recorded in the receipt. A damaged seed is rejected by the existence checker, which this module calls first.

### What Part B does not claim

The gap is certified for the retuned-quartic wall of the interval monograph only. The declared lambda = 0.1 wall still rests on the floating-point theorem of `wall_continuum_stability.py`. The main interval checker could not certify that wall in its present form: the Higgs floor 2 lambda_H h0^2/k2, about 3.5e-4, is far below its fixed coercivity constant 1/2, and the Higgs tail decay length of about 53 in x exceeds the support of 22. The angular Goldstone and gauge sectors are not re-certified here. Their nonnegativity remains the exact factorization argument. There is no nonlinear, thermal or quantum stability claim and no Lean check. The trust base is Python, python-flint/Arb 0.9.0, and the analytic steps above.

## Reproduction

Run all commands from the repository root:

- `PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_wall_nucleation_corrections.py` (about 50 minutes on one core) writes `receipts/flavor_cosmology/wall_nucleation_corrections.json`.
- `PYTHONPATH=python python python/develop_wall_stability_certified.py` (about one minute) writes `receipts/flavor_cosmology/wall_stability_certified.json`.

The second command uses the committed seed `wall_profile_interval_seed.json` (sha256 61a94fc3...) and the main module `wall_profile_intervals.py`, both copied byte-identically from main. It needs `python -m pip install -r python/requirements-wall-intervals.txt`.

Tests are in `python/tests/test_wall_nucleation_corrections.py` and `python/tests/test_wall_stability_certified.py`:

- **Thermal functions:** J_B and its high-T expansion, and dJ_B/dy = i/2.
- **Corrected potential:** the on-shell conditions and the analytic derivatives of every correction, including the fast scalar path.
- **Spinodals:** the tree spinodal constants and the on-shell spinodal shift.
- **Bounces:** the generic bounce against `wall_nucleation`, and the first-order CW shift against the nonlinear shift.
- **Receipts:** structure of both receipts, and the 160-bit gap certificate replayed bit-for-bit.
- **Rejections:** bad splittings and a damaged seed are rejected.
- **Identities:** the SUSY/Schur identities and Taylor-cell enclosures.
