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
