# Computed two-loop thermal potential for the biased-vacuum bounces (N40, part 1)

This monograph covers item N40. It replaces the two-loop *estimates* in `wall_nucleation_corrections` (see WALL_NUCLEATION_CORRECTIONS_AND_CERTIFIED_STABILITY, Part A) with computed scalar-sector two-loop diagrams. The second half of N40, interval bounces, is **not** delivered in this commit; see "Not done" below.

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

## Not done (N40 remains partly open)

- **Interval bounces (Arb).** A draft module was not finished, so it is not committed. It used validated Taylor shooting, an analytic tail, a Coleman-Glaser-Martin upper bound and a uniqueness covering. No certified interval for S3/T or S4 is claimed.
- Gauge-sector two-loop diagrams, and the pole-mass on-shell scheme.
