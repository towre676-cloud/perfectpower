# Dyadic reduction, tame extension clusters and certified Stokes data

This extends the cluster machinery of [SINGULAR_RICHELOT_AND_CLUSTERS_MONOGRAPH.md](SINGULAR_RICHELOT_AND_CLUSTERS_MONOGRAPH.md) and the semistable Tamagawa adapter (open item N41). It also extends the resonant Frobenius charts with irregular singular points (N42). The modules are `dyadic_reduction.py`, `tame_cluster_frobenius.py` and `irregular_stokes.py`. The develop script is `python/develop_dyadic_reduction_and_stokes.py`, which writes the receipts in `receipts/curve_structure/` (`dyadic_reduction.json`, `tame_extension_clusters.json`, `irregular_stokes.json`). There are 18 tests in `python/tests/test_dyadic_reduction_and_stokes.py`.

## Tame extension-field clusters

Roots may lie in a tamely ramified splitting field over Q_p, recorded by its residue degree f and ramification index e. Frobenius and inertia act on the roots as permutations. From these permutations the code derives the action on clusters and sheets, then the conductor and reduction data. The genus-2 conductor exponent was cross-checked against PARI `genus2red` on 190 curves with 0 disagreements. The sample has e=1 to 6, plus 70 curves whose tame splitting field lies outside the search bounds; for those the code reports no result.

## p=2

The odd-p cluster formula is wrong at p=2: it disagrees with Tate's algorithm on 312 of 314 tamely split cubics. That disagreement is kept in the receipt as evidence. For p=2 the module uses other routes:

- **Tate's algorithm for genus 1:** it agrees with PARI `elllocalred` on 11,859 local reductions, including all Kodaira types at 2 and 3, with 0 disagreements.
- **Genus-1 hyperelliptic models:** 958 local reductions via an explicit Weierstrass transfer, with 0 disagreements.
- **Good reduction at 2 for genus 2:** a certificate gives a model y²+Q(x)y=P(x) with good reduction. It agrees exactly with PARI on 1,452 curves: 510 good, 942 bad, and no curve classified differently.
- **Bielliptic genus-2 conductors:** the exponent at 3 agrees with `genus2red` on 400 of 400 curves. The exponent at 2 is reported as a histogram without a claim of correctness.

## Irregular singular points

For confluent hypergeometric (Kummer) equations z w''+(b−z)w'−a w=0 at eight rational (a,b) pairs, the code computes Stokes matrices at 128 bits by Arb-certified Taylor transport around the irregular point. Every case passes all four checks:

- the Stokes matrices are unipotent upper and lower triangular;
- the balls contain the classical closed-form multipliers, built from Γ-functions;
- the cyclic relation with the formal monodromy holds (ball overlap);
- the formal solutions match the classical ₂F₀.

Formal Hukuhara–Turrittin normal forms are computed exactly for n×n systems with distinct leading eigenvalues. Borel–Padé estimates of Stokes data are recorded as numerical only.

## Not claimed

- Wild ramification at p=2 in general: genus-2 conductor exponents at 2, minimal regular models and Swan conductors beyond the cases above.
- Repeated leading eigenvalues or ramified (fractional) irregular exponents.
- Certified Stokes data for systems without closed forms. Those are numerical only.
- No Lean. The trust base is Python, Arb and PARI as an independent oracle.
