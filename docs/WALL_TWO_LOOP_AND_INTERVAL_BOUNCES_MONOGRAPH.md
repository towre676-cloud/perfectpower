# Computed two-loop thermal potential for the biased-vacuum bounces (N40, part 1)

This monograph covers item N40. It replaces the two-loop *estimates* in `wall_nucleation_corrections` (see WALL_NUCLEATION_CORRECTIONS_AND_CERTIFIED_STABILITY, Part A) with computed scalar-sector two-loop diagrams. The second half of N40, interval-certified bounce actions for the tree potential, is in "Interval bounces" at the end.

Code: `python/perfectpower/wall_two_loop_thermal.py`, `python/develop_wall_two_loop_thermal.py`, `python/tests/test_wall_two_loop_thermal.py`.
Receipts: `receipts/flavor_cosmology/wall_two_loop_thermal.json` and `wall_two_loop_thermal_validation.json`.

## Scheme

The model is the declared one: lambda = 0.1, v = 30 TeV, lam_s = 6 lambda, and field-dependent mass x = lambda(3 phi^2 - v^2).

- **Diagrams.** V_2 = (lam_s/8) I^2 - (lam_s^2 phi^2/12) H, both in MS-bar.
  - The tadpole splits exactly as I = kappa A(x) + I_T.
  - The sunset splits exactly as H = kappa^2 I_sun(x) + 3 I_T B_on(x) + H_2.
  - B_on = kappa(log(mu^2/x) + 2 - pi/sqrt3) is the T=0 bubble at on-shell external momentum.
  - H_2 is the UV-finite piece with two Bose factors. It is a 2-d integral, derived from the Matsubara identity, which has no n1 n2 n3 term. The angular integral is done in closed form.
  - I_sun is the Ford-Jack-Jones sunset, x(-3/2 L^2 + 6L - 15/2 + 2 sqrt3 Cl_2(pi/3)).
  - The thermal sunset is numerically exact at every m/T. The high-T expansion is never used.
- **Counterterms.** The 1/eps poles proportional to I_T cancel between three sources: the figure-eight cross term, the sunset subdivergence and the one-loop coupling counterterm.
- **Tachyonic masses.** Where m^2 < 0, every function is evaluated at x+i0 and the real part is taken (Weinberg-Wu). Thermal integrals use the contour E = sqrt(x+i0) + u^2.
- **Conversion to the one-loop on-shell scheme of the earlier work.**
  - Hold (lambda, v) fixed. Then delta_lam = 9 kappa lambda^2 L_v and delta_m0^2 = 3 kappa lambda^2 v^2 (2 - L_v).
  - Add the term (1/2)[kappa A + I_T] delta x(phi).
  - Add a two-loop polynomial a2 phi^2 + a4 phi^4, which restores V'(v) = 0 and V''(v) = 2 lambda v^2 at T=0.
  - The resulting potential is **mu-independent to floating-point rounding**: 0.03 GeV^4, against loop terms of order 1e14 GeV^4.
- **Daisy resummation.** This is Parwani-type, applied to the thermal parts, with a Boltzmann-exact thermal mass Pi = (lam_s/2) Re I_T. The thermal pieces are evaluated at M^2 = x + Pi, and the term -Pi I_T(M^2)/2 is added. The figure-eight's M T^3 term is cancelled, so no daisy is double-counted (checked numerically).
- **IR regulator.** Near M^2 = 0 the zero-mode log is cut at y_IR = Pi/T^2, with Gaussian smoothing in M^2. The regulator variation (x1/4, x4) is part of the bracket.
- **Thermal loops by temperature.** Thermal loops are included for T >= 2000 GeV. At T <= 1000 GeV the central value keeps the Boltzmann limit of the earlier work, and the Re-continued thermal loops are a bracket entry.

## Validation (receipt `wall_two_loop_thermal_validation.json`)

| Check | Result |
|---|---|
| Matsubara decomposition vs brute-force double sum | 9e-14 relative |
| Contour Re J_B vs the earlier log-sin quadrature | agreement to 1e-12 |
| Contour J_B vs the convergent high-T series (both signs of y) | agreement to 1e-12 |
| Massless figure-eight: I_T(0) = T^2/12, giving the lam_s T^4/1152 free energy | exact |
| Sunset small-m limit: H_2/T^2 + log(m/T)/32pi^2 -> -0.005523 (predicted from the Arnold-Espinosa 3-d sunset) | -0.005496 at y = 1e-6, converging like sqrt(y) |
| Log angular formula vs numerical angle, including y < 0 | agreement to 1e-10 |
| Parwani linear term | resummed 2.8e-8; unresummed -9.944e-4 vs -lam_s/192pi = -9.947e-4 |
| On-shell conditions at T = 0 | V'(v) = 0, V''(v) residual 1e-3 GeV^2 |
| Scale dependence, spread for mu in [m_v/2, 2m_v] | 1.4e13 GeV^4 (two-loop, one-loop matched) vs 1.55e15 GeV^4 (one-loop), a factor of about 110 smaller |

## Results (receipt `wall_two_loop_thermal.json`)

**S3/T at the tree critical bias.** "Scale" is the half-width of the MS-bar scan.

| T (GeV) | one-loop (earlier) | two-loop central | scale | eps*_two-loop [total band] | eps*_one-loop |
|---|---|---|---|---|---|
| 1000 | 103.94 | 104.10 | +-0.048 | 0.377156 [0.377133, 0.377179] | 0.377148 |
| 2000 | 126.92 | 127.00 | +-0.025 | 0.370374 [0.370348, 0.370400] | 0.370365 |
| 2999 | 132.71 | 132.75 | +-0.019 | 0.363421 [0.363393, 0.363449] | 0.363415 |

The two-loop terms raise S3/T by 0.03 to 0.15 percent and shift eps* by +2e-5 or less. The earlier estimate brackets were 0.3 to 4 in S3/T, so the computed values sit well inside them.

The residual bracket is dominated by the one-loop CW IR sensitivity carried over from the earlier work. The scale band and the two-loop IR-regulator band are each at the 1e-3 to 1e-2 level in S3/T. The O(4) critical biases shift by about +1e-5 below 300 GeV.

**Amplified-bias nucleation temperatures**

| q | T_n one-loop | T_n two-loop | scale band | total band |
|---|---|---|---|---|
| 0.990 | 268.40 | 268.05 | [267.93, 268.17] | [266.73, 269.37] |
| 0.995 | 323.10 | 322.97 | [322.92, 323.01] | [322.46, 323.47] |
| 1.000 | 358.06 | 357.92 | [357.88, 357.97] | [357.43, 358.42] |

Two loops lower T_n by 0.1 to 0.35 GeV, against one-loop brackets of 1.4 to 3.2 GeV. The conclusions of the earlier work are unchanged: the declared bias still does not nucleate.

## Scope

- Scalar-sector two loops only. Gauge and Higgs loops enter through kappa = 1e-7 and are not added.
- The on-shell conditions use the zero-momentum curvature, not the pole mass.
- The potential near m^2 = 0 is IR-regulated, and that region is not under perturbative control.
- Bounces are single-field, reduced and floating-point.
- Scale bands are first-order action shifts.
- The fluctuation determinant is still the declared exp(+-20) band.
- T_n uses linear interpolation on the coarse temperature grid.

## Not done (part 1)

- **Interval bounces (Arb).** Done for the tree potential; see "Interval bounces" below. The corrected potentials are still floating.
- Gauge-sector two-loop diagrams, and the pole-mass on-shell scheme.

## Interval bounces

Code: `python/perfectpower/wall_bounce_intervals.py`, `python/develop_wall_bounce_intervals.py`, `python/tests/test_wall_bounce_intervals.py`.
Receipt: `receipts/flavor_cosmology/wall_bounce_intervals.json` (deterministic; about 20 minutes on one core).

### Method

Every number below is an Arb enclosure. Floating values are only compared against it.

- **Validated integrator.** The state is (phi, P=r^{d-1}phi', q=1/r), so the field is polynomial and the friction term drops out of the Jacobian.
  - Each step is a degree-36 Taylor model at 160 bits. A strict inclusion res + h J eps < eps on the tube shows that the solution stays in the tube. The endpoint error comes from the vector Gronwall bound exp(hJ) res, computed by scaling and squaring.
  - The first step, from r=0, uses the exact regular-singular Picard operator.
  - Ranges are taken from Bernstein coefficients.
- **Existence.** This is Coleman's argument with finitely many checks. phi0 = seed - 1e-20 is a certified undershoot (phi' > 0 while phi > f), and seed + 1e-20 is a certified overshoot (phi < f while phi' < 0). The two sets are open, so some phi0* between them is in neither. Its solution is monotone and tends to f; the limit cannot be the barrier top, because the solution would oscillate there.
- **Action.** The 2e-20 family is integrated to the radius R where phi - f < 1e-9.
  - The tail has an exact bound: int_R^inf r^{d-1} phi'^2 lies in [0, u(R)|P(R)|], from integration by parts with u V'(f+u) >= 0. The same interval bounds the tail of the potential term.
  - Then s = (Omega_d/d) int r^{d-1} phi'^2, by Derrick's identity.
  - The direct T+U enclosure overlaps in every case.
- **Least action, quartic.** By Coleman-Glaser-Martin, the least-action bounce is radially non-increasing with values in [f, t], so its phi0 lies in [e, t). Every other phi0 in that range is excluded:
  - **Near the seed.** The box [seed-1e-8, seed+1e-8] is handled by the variational equation. psi and Psi share a strict sign at an R where phi < -1/sqrt3, so the difference of two bounces could not decay.
  - **Away from the seed.** [e_lo, seed-1e-8] and [seed+1e-8, t-eta] are covered by adaptive classification. Each box is run as a mean-value family: the centre trajectory, plus the variational pair over the whole box, with phi in phi_c + [-w, w]|psi|. The boxes are bisected in log-distance to the seed and to t. This takes 312 to 532 runs per benchmark, and 2460 at the most spinodal point.
  - **Near t.** [t-eta, t) is excluded by an energy bound, with eta between 6.5e-8 and 1.0e-5:
    - E = phi'^2/2 - (V - V_f) decreases by D = int (d-1) phi'^2/r.
    - A comparison with sinh(z)/z, or 2I_1(z)/z, gives r1 > (d-1)A/(E_0 - D_1) before t - phi reaches 0.05.
    - The remaining dissipation is at most (d-1)A/r1, so E stays positive and the solution overshoots.
- **Least action, cubic.** Uniqueness is Kwong's theorem: Delta w = w - w^2, p=2, which is subcritical in d=3,4.

### Results

Universal cubic, near-spinodal constants C_d = (2*3^{1/4})^{(6-d)/2} s_cubic(d)/3:

| | certified | floating (wall_nucleation) |
|---|---|---|
| s_cubic(3) | [43.66023671624716, 43.66023671624719] | 43.66023671624231 |
| s_cubic(4) | [204.4284433419092, 204.4284433419093] | 204.4284433419212 |
| C3 | [62.14844908992001, 62.14844908992003] | 62.14844908991308 (quoted 62.148 is a certified rounding) |
| C4 | [179.3619745270784, 179.3619745270785] | 179.36197452708896 (quoted 179.36 is a certified rounding) |

Tree-potential actions at the critical biases eps* of `wall_nucleation`. eps* is taken as the exact dyadic value of the floating root.

- S3/T = (v_T/(sqrt(lam) T)) s3, with v_T computed in Arb from the declared (v, lam, c).
- S4 = s4/lam.
- "Least action" means the full exclusion above was certified.

| T (GeV) | S3/T certified | floating | S4 certified | floating | least action |
|---|---|---|---|---|---|
| 0.03 | [188.16730795, 188.16730808] | 188.14201 (asymptotic law) | [245.63703164051, 245.63703164052] | 245.63703163 | yes |
| 1 | [169.56829631, 169.56829632] | 169.34811 (asymptotic law) | [212.68668279741, 212.68668279742] | 212.68668279 | yes |
| 100 | [150.75295333059, 150.75295333060] | 150.75295336 | [175.46050348403, 175.46050348404] | 175.46050346 | yes |
| 1000 | [141.44703737808, 141.44703737809] | 141.44703737 | [156.81457280180, 156.81457280181] | 156.81457279 | yes |
| 2999 | [137.00607161228, 137.00607161229] | 137.00607161 | [147.90693271252, 147.90693271253] | 147.90693270 | yes |

What the comparison shows:

- **Floating bounce rows.** The floating values agree with the certified intervals to a relative 3.3e-10 or better, which is the trapezoid and brentq error of the floating code. They are not inside the 1e-15-wide intervals, and are not claimed to be.
- **Near-spinodal rows.** Two floating S3/T values, at T = 0.03 and 1 GeV, came from the asymptotic law C3 (eps_sp - eps)^{3/4}. The exact certified actions are higher by factors 1.0001344 and 1.0013002, so S3/T is 188.167 instead of 188.142, and 169.568 instead of 169.348.
- **Effect on conclusions.** All these shifts are far inside the declared exp(+-20) prefactor band. No conclusion of the nucleation analysis changes.

### Not claimed

- The corrected potentials (one-loop CW, thermal and two-loop) are not enclosed. They contain log|m^2(phi)|, which is non-analytic inside the bounce, and spline-interpolated thermal functions. Their bounces remain floating.
- The near-spinodal law is asymptotic. Only C_d and the exact actions at the benchmark biases are certified.
- eps* is a floating root. The certified actions are at those exact dyadic biases; the location of eps* is not certified.
- The fluctuation determinant, which is still the declared band, and the three-field sandwich factor are not certified.
- The least-action identification uses two cited theorems that are not re-proved: Coleman-Glaser-Martin (the minimiser is radial and monotone) and Kwong (uniqueness for the cubic).
