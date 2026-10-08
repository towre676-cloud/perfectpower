# Real-time lifetime of the 154.225 GeV localized wall mode

This note addresses the open item "nonlinear lifetime of the 154.225 GeV localized wall mode, compared with the computed widths". It evolves the static source/Higgs wall plus a small excitation of its localized radial mode in real time on a lattice. It measures two decay channels separately: (i) classical second-harmonic radiation, and (ii) Goldstone pair emission seeded by vacuum fluctuations. It compares (ii) with the distorted-wave width Gamma_GG = 3.83233455848e-8 GeV that the main branch computed (`wall_pair_decay`, commit 0546f58). The comparison is made in the ungauged global O(4) theory. The gauged electroweak lifetime is not simulated.

Code: `python/perfectpower/wall_mode_lifetime.py`. Replay: `OPENBLAS_NUM_THREADS=1 PYTHONPATH=python python python/develop_wall_mode_lifetime.py` (about 40 minutes on one core). Receipt: `receipts/flavor_cosmology/wall_mode_lifetime.json`. Tests: `python/tests/test_wall_mode_lifetime.py` (7 tests, about 4 s).

## 1. Reduced theory and units

The inputs are the main-branch candidate: v = 30000 GeV, M_heavy = 300000 GeV, g_source = 3000 GeV, v_H = 246 GeV, lambda_H = 0.13 and kappa = 1e-7. The retuned source quartic is lambda = 1.7618816494787725e-5, copied from the main receipt `wall_embedded_states.json` and not re-derived here.

**Scale.** With this quartic the wall is not a 1/v-thin object. Its inverse thickness is k v = v sqrt(lambda/2) = 89.042 GeV, so the source mass 2kv, the Higgs mass sqrt(1.9845) kv and the mode frequency sqrt(3) kv all lie within a factor of two of one another. The only large hierarchy left is the heavy singlet.

**Singlet elimination.** The singlet is removed through its constraint S = -g phi^2/M^2. This removal is exact for the static wall and for the zero-frequency Hessian. Its dynamical remainder shifts the Hessian by about 1.2e-5 k^2. As a check, the reduced lattice mode reproduces the main three-field mass to 6.5e-6 relative at dx = 0.125.

**Variables and equations.** Use x = k v z and t → k v t. The fields are u = phi/v and the four real Higgs-doublet components Phi = (h, pi_1, pi_2, pi_3) in units of v_H. The equations of motion are

    u_tt = u_xx - 2u(u^2-1) - c_k u X,   Phi_tt = Phi_xx - (lambda_H/k^2) X Phi,
    X = h0^2(|Phi|^2-1) + (kappa/lambda_H)(u^2-1),   c_k = kappa/k^2 = 0.011352,

with (lambda_H/k^2) h0^2 = 0.99226.

**Where hbar enters.** The planar action carries an overall factor 1/k^2. The canonical fields u/k and h0 Phi/k therefore have hbar = 1 in these units. The source sector has hbar_eff = k^2 = 8.8e-6 and the Higgs/Goldstone sector has hbar_eff = k^2/h0^2 = 0.131. Classical dynamics never contains hbar. It enters only through the seeded vacuum fluctuations.

**Lattice.** The lattice is a half line with a fourth-order Laplacian. Parity ghosts sit at x = 0, with u odd and h even. The integrator is velocity Verlet. The static wall is solved by Newton iteration on the same discrete operator, so it is exactly static under the evolution (|dX| < 1e-15 over 400 steps). The discrete Ward identity holds to 1e-14: the Goldstone operator -Delta + (lambda_H/k^2) X annihilates the lattice Higgs profile.

**Mode on the lattice.** The mode is the odd source eigenvector plus the driven even Higgs response, with an outgoing condition on the response. Its mass is 154.2075 GeV at dx = 0.25 and 154.2240 GeV at dx = 0.125, against 154.2250 GeV on main. The residual radiation-node detuning gives a linear Higgs-leak energy rate of 8e-13 GeV at dx = 0.25 and 2.5e-15 GeV at dx = 0.125. Both are negligible against every rate below.

## 2. Classical channel: no pairs, second-harmonic radiation

**No classical pair emission.** The Goldstone force is proportional to pi. A classical field with pi = 0 therefore keeps pi = 0 exactly; the receipt shows Goldstone energy 0.0 after t = 100 at A = 0.1. A classical, noise-free excitation of the radial mode cannot emit Goldstone pairs. Pair emission needs seeded fluctuations: either quantum vacuum modes or a classical-statistical ensemble.

**Second-harmonic radiation.** What a classical excitation does do is radiate at the second harmonic. The source term (1/2)V3[eta,eta] oscillates at 2 omega, and 2 omega = 3.46 lies above the source threshold 2. This channel was simulated with an absorbing layer (x in 150–250), and the per-period envelope A(t) of the source projection was fitted to d(1/A^2)/dt = C, which is equivalent to Gamma_E(A) = C A^2. The closed form from `wall_shape_radiation.kink_closed_form`, converted to x units, is C = (9 sqrt6/4) pi^2/sinh^2(sqrt2 pi) = 0.0301092.

| dx | A0 | fitted C | C / closed form |
|---|---|---|---|
| 0.25 | 0.05 | 0.030644 | 1.0178 |
| 0.25 | 0.10 | 0.030722 | 1.0204 |
| 0.25 | 0.15 | 0.030809 | 1.0232 |
| 0.25 | 0.20 | 0.030897 | 1.0262 |
| 0.125 | 0.10 | 0.030268 | 1.0053 |

The A → 0 extrapolation at dx = 0.25 is 1.0178 times the closed form. Most of that offset is lattice error: halving dx cuts the excess from 2.0% to 0.5% at A = 0.1. The remaining growth with A is the next order in A. The leakage into the Higgs channel at 2 omega is suppressed by h0^2 and is invisible in these runs. In GeV the second-harmonic energy-loss rate is Gamma_NL = C A^2 kv = 2.68 A^2 GeV (closed form).

## 3. Pair channel in real time, including transverse momenta

**Why 1+1 alone is not enough.** A purely 1+1-dimensional simulation contains only p_parallel = 0. The planar width, by contrast, integrates over the pair's parallel momentum. This study handles that as follows.

**Exact decomposition.** At quadratic order in the Goldstones, which is the order of the leading pair width, each real Goldstone component decomposes exactly. It becomes independent 1+1 fields of mass p = |p_parallel|, one per transverse Fourier mode. All of them are driven by the same background X(x,t), and that background comes from the nonlinear classical (u, h) simulation itself, including its anharmonic and second-harmonic content.

**Exact Gaussian evolution.** For each p and each parity sector, the full set of vacuum mode functions of the static-wall Goldstone operator is evolved in real time. This is the infinite-ensemble limit of the classical-statistical method with half-quantum seeding. Because the Goldstone dynamics are linear here, it is also the exact quantum evolution of the Gaussian state. Two implementation details matter:
- The mode functions start on the eigenvectors of the Verlet map, so the undriven energy is constant to rounding (test: |P| < 1e-12).
- The coupling to the oscillation is ramped on over t = 20. This removes the sudden-quench pair burst and its slow infrared tail.

The secular Goldstone energy gain, averaged over one period at each end of the window, gives P_1D(p).

**Integration over parallel momentum.** The emitted power per unit wall area is n_G int d^2p/(2 pi)^2 P_1D(p) = (3/2 pi) int_0^{omega/2} p P_1D dp, evaluated by Gauss–Legendre quadrature. The rate is then Gamma = P_area/E_area, with E_area = omega^2 A^2 N/(2k^2). Numerically this p-integration performs the parallel phase-space identity of 0546f58, int d^2p/(2pi)^2 2pi delta/(4 omega_1 omega_2) = 1/(4M). It is not substituted analytically.

**Normalization test.** The real-time machinery was checked independently against a Fermi golden rule for a free massive 1+1 field with a Gaussian drive, P = Omega (pi/16) int dk dl |c(k,l)|^2 delta(Omega - omega_1 - omega_2)/(omega_1 omega_2). The real-time power matches the golden rule to 0.16% (even sector) and 0.03% (odd sector).

**Results at A = 0.05**, with the mode width from main as the target:

| configuration | Gamma_GG [GeV] | ratio to main |
|---|---|---|
| base: L=60, dx=0.25, 10 p-nodes, window t=30–100 | 3.85985e-8 | 1.0072 |
| base, window t=30–65 | 3.79683e-8 | 0.9907 |
| 14 p-nodes | 3.85761e-8 | 1.0066 |
| long box L=120, window t=30–220 | 3.92074e-8 | 1.0231 |
| dx = 0.125 | 3.85006e-8 | 1.0046 |
| main (distorted-wave Born) | 3.83233e-8 | 1 |

The parity split matches main. In the long box the even–even part is 3.1735e-8 GeV and the odd–odd part is 7.472e-9 GeV, that is 1.022 and 1.026 times main's 3.1040e-8 and 7.283e-9.

The momentum profile explains the parity asymmetry:
- At small p, P_1D/A^2 is about 1.13e-4 in both parities.
- Toward the pair threshold p → omega/2 the even channel rises to about 9.6e-4. This is the zero-energy Ward half-bound state h(x)/h0 of the Goldstone operator.
- The odd channel vanishes there, because its normal-momentum waves vanish linearly at threshold.

The spread among the controls is −0.9% to +2.3%. The near-threshold node (p = 0.855, slow normal momenta) is the least converged in time; its value moves by a few percent between the short and long boxes.

**Conclusion of this section.** At the 2–3% level, the real-time vacuum-seeded evolution agrees with the distorted-wave pair width. No additional mechanism appears at small amplitude.

**Amplitude dependence** (6 p-nodes, ratio to A = 0.05 at the same quadrature):

| A | 0.02 | 0.05 | 0.1 | 0.2 |
|---|---|---|---|---|
| Gamma_pair(A)/Gamma_pair(0.05) | 0.984 | 1 | 1.034 | 1.134 |

The A^2 growth comes from O(A^2) terms in the drive: the second harmonic of X, which corresponds to two mode quanta annihilating into a Goldstone pair, and the amplitude-dependent frequency. These terms were not separated further. Pairs driven at 2 omega with omega/2 < p < omega fall outside the integration range, so at A ≥ 0.1 these numbers slightly undercount that O(A^2) piece. Extrapolating linearly in A^2 from A = 0.02 and 0.05, and transferring the 6-to-10-node quadrature offset measured at A = 0.05, gives an A → 0 ratio of about 0.99. That arithmetic is done here from receipt values; it is not a separate receipt entry.

**Classical-statistical Monte Carlo check.** This check uses the fully nonlinear equations with one odd Goldstone component in the p = 0 sector. Pi^2 is even, so the truncation is consistent. The run keeps Goldstone self-interaction and backreaction on u and h.
- **Seeding.** Gaussian noise at 1e-4 of a half quantum, with the result rescaled linearly. Full half-quantum noise in 1+1 has <pi^2> of order 0.06, an infrared/ultraviolet-enhanced lattice artefact.
- **Estimator.** An antithetic common-noise estimator, [E(A)+E(-A)-2E(0)]/2.
- **Sample.** 4096 samples with fixed seeds.

The result is P/A^2 = 9.8e-5 ± 2.2e-5, against the exact Gaussian value 1.136e-4 (−0.7 standard errors). The check is consistent at its 20% statistical resolution. Its variance makes a direct 3+1 Monte Carlo lifetime at percent precision impractical with this estimator, which is why the exact Gaussian evolution carries the quantitative result.

## 4. Lifetime synthesis

**Single-quantum lifetime.** For one quantum the pair channel is the only open decay in the ungauged O(4) theory (2 m_h > M closes radial pairs). Second-harmonic radiation is the classical limit of a 2 → 1 process with rate proportional to n(n−1), so it is absent for a single quantum. Hence

    tau_1 = hbar/Gamma_GG = 1.68e-17 s (long-box real time), main: 1.718e-17 s.

**Coherent excitation of amplitude A.** For a coherent excitation,

    dE/dt = -(Gamma_GG + C A^2 kv) E,   A(t)^2 = Gamma A0^2 e^{-Gamma t}/(Gamma + C' A0^2 (1-e^{-Gamma t})),

with C' = C kv = 2.73 GeV at the lattice extrapolation (2.68 GeV closed form). The two channels are equal at A_c = 1.20e-4. That amplitude corresponds to a coherent mode occupation of 1.4e-3 quanta per (1/kv)^2, or about 11 quanta per GeV^-2 of wall area.

Above A_c the classical second-harmonic radiation dominates and A^-2 grows linearly in time. Below A_c the pair channel sets an exponential tail with Gamma_GG. The linear Higgs leak from residual node detuning is below 1e-12 GeV.

## 5. Scope and what is not claimed

- **Agreement claimed.** The numerical agreement with main's Gamma_GG is at the 2–3% level across finite-window, lattice-spacing and quadrature controls. These are numerical controls, not interval enclosures.
- **No 3+1 lattice.** No full 3+1-dimensional nonlinear classical-statistical lattice was run. Transverse momenta enter through the exact quadratic-order decomposition, with the background from a nonlinear 1+1 simulation.
- **Ungauged theory only.** Everything is computed in the ungauged global O(4) theory. After gauging, the three Goldstones are not physical particles. The WW/ZZ TE widths of 0546f58 were not simulated, and no electroweak lifetime is claimed.
- **Omitted physics.** Not included: loop and self-energy corrections, renormalized Goldstone mass shifts, Goldstone rescattering beyond the Gaussian order (except in the small-noise Monte Carlo), a thermal bath, and singlet dynamics beyond its static constraint.
- **Monte Carlo precision.** The classical-statistical Monte Carlo check is statistically limited to about 20%.
- **Replay not verified.** The receipt is produced with fixed seeds and deterministic floating-point code, but byte-identical replay on another platform was not verified.
