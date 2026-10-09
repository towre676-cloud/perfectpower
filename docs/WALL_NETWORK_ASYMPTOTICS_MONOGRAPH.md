# Wall network asymptotics: the annihilation law and the GW peak

This continues the annihilation-phase study in [WALL_ANNIHILATION_GW_MONOGRAPH.md](WALL_ANNIHILATION_GW_MONOGRAPH.md). There, 192³ physical-wall runs gave an annihilation exponent p≈0.25 instead of the pressure-balance value 1/2, because the network formed late and the window was short.

## Method

The runs use the PRS s-family `phi''+(3-s)phi'/tau-lap phi=-tau^(2s)(phi^2-1)(lam phi+e(tau))` with a=tau. The cubic bias is chosen so that the physical ratio X=σ/ΔV is constant; it switches on with a C¹ ramp. s=1 is the physical equation of the previous study. s=0 is the PRS fixed-width ("fat-wall") equation, which keeps walls resolved for the whole run and so extends the dynamic range. Boxes are float32 and periodic, 320³ with a 384³ control. Formation starts from a Gaussian field at tau_i=1, so the network forms by tau≈10 rather than tau≈45. The code is `python/perfectpower/wall_network_asymptotic.py` and `python/develop_wall_network_asymptotic.py`. The series caches and the analysis receipt are `receipts/flavor_cosmology/wall_network_asymptotic*.json`.

## Results (s=0, seed 0, X from 240 to 6700)

| Criterion | p (all points) | p (asymptotic subset X≥1480) | Offset-law K |
|---|---|---|---|
| False fraction < 10% | 0.477 ± 0.003 | 0.487 ± 0.004 | 1.24 |
| False fraction < 1% | 0.459 ± 0.005 | 0.447 ± 0.020 | 2.09 |

The local exponents for the 10% criterion rise from 0.46 at X≈320 to 0.50 at X≈3400. The 384³ control gives p=0.458 at the same X and annihilation times within 0.6% of the 320³ run, so the result is not box-limited. **With early formation and fixed-width walls, the exponent approaches the pressure-balance value 1/2.** The earlier 0.25 was a transient caused by late formation, as that monograph suspected. For comparison, the lattice network value C_ann·A is 1.79.

GW (tensor runs at 192³ to 320³): the peak is resolved at f/H between 0.58 and 1.07 and does not reach the box scale at the end of the s=0 runs. The infrared slope on resolved subhorizon bins is 2.3–2.7, consistent with the causal k³ tail at the stated resolution. The ultraviolet slope is about −1.06 (spread −1.03 to −1.40).

## Not claimed

- The fat-wall (s=0) equations change the wall profile and its scalar radiation. Only the network dynamics is physical. The s=1 and s=1/2 asymptotic runs were not completed, so the exponent for the physical equation in the asymptotic regime is not measured here.
- One seed for the main scan, so the stated errors are fit errors, not seed-to-seed variance.
- Float32, no backreaction, and no certified integration. The infrared-slope estimate uses few bins.

## Completed scan (three s=0 seeds, s=1/2 and the physical s=1 equation)

The remaining runs of the develop script have finished: s=0 seeds 1 and 2, the s=1/2 family (two seeds), and the physical s=1 family (one seed, X from 1000 to 6700). The receipt now holds all 36 runs.

| Family | Criterion | p (all X) | p (asymptotic X subset) | Seed spread (asymptotic) |
|---|---|---|---|---|
| s=0, 3 seeds | 10% | 0.478 ± 0.003 | 0.497 ± 0.006 | 0.487, 0.489, 0.516 |
| s=0, 3 seeds | 1% | 0.475 ± 0.005 | 0.492 ± 0.014 | 0.447, 0.501, 0.528 |
| s=1/2, 2 seeds | 10% | 0.470 ± 0.003 | 0.449 ± 0.006 (X≥3000) | 0.446, 0.453 |
| s=1 (physical), 1 seed | 10% | 0.27 ± 0.08 | 0.51 ± 0.18 (X≥2600) | — |
| s=1 (physical), 1 seed | 1% | 0.53 ± 0.09 | 0.78 ± 0.11 (X≥2600) | — |

The receipt combines statistical and systematic errors for the s=0 asymptotic exponent. The systematics come from the box-size (256³, 384³) and wall-width (w=3) controls. The result is p = 0.492 ± 0.024 (statistical) ± 0.098 (systematic), or ± 0.10 in total. That is 0.08σ from 1/2. Measured against the lattice network value, K is 1.28 times K_PRS.

**Conclusion.** For the fixed-width equations the annihilation exponent is consistent with the pressure-balance value 1/2. The s=1/2 family is somewhat lower, at 0.45, which suggests that width growth delays the asymptotic regime. The physical s=1 family with one seed and five X values now gives exponents straddling 1/2 in the asymptotic subset. That is a large change from the early-window value of 0.25, but its errors (0.1 to 0.2) are too large to confirm 1/2 for the physical equation. More seeds and a wider X range at s=1 are the next step.

## Physical equation with three seeds

Seeds 1 and 2 of the physical s=1 family have now finished, giving 15 runs.

| Criterion | p (all X) | p (X≥2600) | Seeds (X≥2600) |
|---|---|---|---|
| false fraction < 10% | 0.262 ± 0.005 | **0.497 ± 0.007** | 0.510, 0.493, 0.487 |
| false fraction < 1% | 0.510 ± 0.017 | 0.781 ± 0.006 | 0.777, 0.773, 0.793 |

Errors are standard errors over seeds. With the 10% criterion, the physical equation reproduces the pressure-balance exponent 1/2 at large X, and the seeds agree closely. Fits over all X include the formation transient and give about 0.26, as the earlier 192³ study found.

The 1% criterion does not converge to 1/2. Its asymptotic slope of 0.78 measures the final clean-up of isolated false-vacuum remnants. In the physical equation those remnants persist while the walls thin towards the lattice spacing, so the late-time tail depends on the criterion and on resolution. It is not taken as a test of pressure balance.
