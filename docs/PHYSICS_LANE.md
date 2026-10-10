# The physics lane: benchmarks, inputs and a split manifest

The flavor and wall-cosmology work shares the repository's exact and interval machinery, but it carries a kind of risk the arithmetic does not: its conclusions depend on declared model inputs. This page records which inputs every wall result uses, where the chain is not yet end to end, and which files a separate physics repository would carry.

## Two walls, not one

The wall results fall into two families that use different source quartics.

| | Declared wall | Retuned radiation-node wall |
|---|---|---|
| Source quartic | λ = 0.1 | λ ≈ 1.76188164948e-5 (tuned so a radial radiation node holds) |
| Shared inputs | v = 30 TeV, M_heavy = 300 TeV, g_source = 3 TeV, v_H = 246 GeV, λ_H = 0.13, κ = 1e-7 | same |
| Results | tension and annihilation template (`dimensionful_walls`); nucleation with Coleman–Weinberg, two-loop and interval bounces; float and certified stability (gap > 124.40 GeV); Jost scattering; shape radiation | embedded 154.225 GeV mode; Goldstone and gauge channels; pair widths; real-time lifetime; vector widths and electroweak lifetime (≈1.6e-15 s); thermal cooling; Kibble–Zurek formation; certified gap > 125.35 GeV |
| Receipts | `dimensionful_walls.json`, `wall_nucleation*.json`, `wall_two_loop_thermal.json`, `wall_bounce_intervals.json`, `wall_stability*.json`, `wall_declared_stability_certified.json`, `wall_jost_scattering.json`, `wall_shape_radiation.json` | `wall_embedded_states.json`, `wall_gauge_channels.json`, `wall_pair_decay*.json`, `wall_mode_lifetime.json`, `wall_mode_vector_widths.json`, `wall_cooling.json`, `wall_kibble_zurek.json`, `wall_stability_certified.json` |

The lattice network and gravitational-wave studies (`wall_network*`, `wall_gw*`, `wall_annihilation_gw*`, `wall_network_asymptotic*`) are dimensionless φ⁴ networks. They enter the physical template only through the area parameter A, the annihilation factor C_ann, the efficiency ε_gw and the spectral shape. The template then uses the declared wall's tension.

**Consequence.** No single wall currently carries the whole chain: formation, network, annihilation and gravitational waves, plus mode decay and stability. The declared wall has the cosmology but no localized mode. The retuned wall has the mode and its decays, but its tension, nucleation and template have not been recomputed.

## What is declared and what is matched

| Input | Status |
|---|---|
| v_H = 246 GeV, λ_H = 0.13, physical g = 0.65, g′ = 0.36 | matched to the Standard Model at tree level |
| v, M_heavy, g_source, κ | declared benchmarks, not derived from data |
| λ = 0.1 or the retuned value | declared, or tuned to a radiation node; not predicted |
| bias ΔV | declared; the nucleation temperature benchmarks amplify it about 4×10²⁴ to make nucleation possible at all |
| gauge couplings g = 0.3–0.6 | parameter scans only |

At the declared bias there is no thermal or quantum nucleation, and the network annihilates by pressure balance. The pressure-balance law (p = 1/2) is confirmed on the lattice with the physical equation. The resulting signal (peak Ω h² ≈ 1.6×10⁻¹² near 2.7 nHz) is conditional on the declared inputs. No observable is predicted from first principles: finding 25 of [FRONTIER.md](FRONTIER.md) records that CKM, physical CP selection and α(0) remain unpredicted.

## Making it end to end

The concrete next step is to pick one wall and rerun the missing half of the chain on it:

- **Retuned wall:** rerun `dimensionful_walls`, nucleation (tree, CW and two-loop) and the GW template with λ ≈ 1.76e-5. These are inexpensive reruns of existing develop scripts with one changed input.
- **Declared wall:** solve the embedded-mode problem at λ = 0.1. The radial radiation node does not hold there, so the localized mode may not exist; that would itself be a result.

Either choice should be recorded as a new finding in `contracts/current_frontier.json`.

## Split manifest

`python scripts/physics_lane_manifest.py` lists the tracked files of this lane: wall and flavor modules, develop scripts, tests, receipts under `receipts/flavor_cosmology/` and `receipts/m22_interactions/`, the WALL/VALENTINER/FLAVOR monographs, and their figure scripts. That comes to about 400 files out of 6,600. `--files` prints the full list. The manifest moves nothing. A split would also need the shared modules it imports (interval arithmetic, polynomial algebra, certificate replay), so the cleaner path is a separate repository that depends on the `perfectpower` package rather than copying it.
