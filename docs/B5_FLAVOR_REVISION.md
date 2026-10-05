# B₅ flavor scaffold: an exact and testable revision

This revision revisits **A monograph on the B₅/C₅ Weyl scaffold behind α-bounded mass ratios**, retained as `Pasted text (3)(17).txt`, Library identity `libfile_c6f71648d68c8191bb495e00bc28233d`. All 384 rendered lines were inspected. The neighboring **Universal Lattice Law** transcript was located and its initial running implementation inspected; the entire neighboring transcript was not audited. The later finite-Clebsch and PSG flavor projects are distinct sources and are not silently substituted for B₅.

## What survives

The original model searches rational exponents in the five labeled basis quantities α(μ), α_s(μ), π, φ, and m_p/m_e. Taking logarithms makes each monomial prediction a linear form. A frozen finite exponent alphabet produces a finite, queryable candidate domain. This is a useful arithmetic research instrument. It does not by itself derive particle masses.

The signed-permutation group on five exponent axes has order 2⁵·5! = 3840. Its canonical chamber representative is the descending list of **all absolute** exponents, not a list retaining relative signs followed by one global sign change. For z zeros and multiplicities m_j of distinct nonzero absolute values, the exact orbit size is

\[
 |O(r)|=\frac{2^{5-z}5!}{z!\prod_j m_j!}.
\]

Full support alone does not imply size 3840: (1,1,1,1,1) has only 32 orbit members. The original planted sparse vector (1/12,−1/3,0,0,1/5) has 480. Independent explicit enumeration of signed permutations checks these cases in the tests.

## Corrections that change the interpretation

**Physical basis labels matter.** Swapping α and π exponents while holding the basis fixed usually changes the predicted mass ratio. A group orbit is a combinatorial classification, not necessarily an equivalence of likelihoods. Consequently the revised optimizer scores every labeled candidate. It records orbit classes separately and never discards a competing fit solely because it lies in an already-seen orbit. Simultaneously transforming both a basis and its coefficient vector preserves a dot product; transforming the coefficients alone does not.

**Whitening is not evidence of B₅ physics.** For the rational quadratic objective rᵀGr−2cᵀr, full signed-permutation invariance requires G to be a scalar identity and c=0. A spherical quadratic term with a nonzero target linear term fails this test. Axis-specific φ penalties also break permutation invariance. General whitening changes the rational alphabet lattice, and does not turn that changed lattice into the original signed-permutation lattice.

**The scale design cannot have five independent columns.** The three constant columns log π, log φ and log(m_p/m_e) are multiples of the same constant sample vector. With two running columns, the design rank is at most three. Subtracting column means removes the three constant columns entirely, so centered covariance rank is at most two. Adding a tiny diagonal ridge creates an invertible numerical matrix but supplies no new measured directions. A finite rational alphabet can still identify one vector uniquely despite deficient continuous rank; the second synthetic example demonstrates precisely that distinction. Neither uniqueness nor five named inputs establishes a measured rank-five physical law.

**The covariance formula needs consistent centering.** The squared-error expansion uses the uncentered Gram G=Σ_j w_j X_j X_jᵀ, c=Σ_j w_j X_j y_j and s=Σ_j w_j y_j². Then error=s−2rᵀc+rᵀGr. If a centered covariance is used, means must be restored, or both target and design centered with an explicit intercept. The original text combined a centered covariance with uncentered cross terms.

**Freeze observations once.** The original sketch calls a noise-generating target function inside candidate scoring, so candidates see different data. It also reads denominators from binary floats: the binary representation of 1/3 has an enormous denominator unrelated to the intended rational exponent. The replacement accepts integers, rational strings and Fraction values; it rejects floats and booleans. Supplied rows and targets are materialized once.

## Executable showcase

Run from the repository root:

```sh
PYTHONPATH=python python python/develop_b5_revision.py
PYTHONPATH=python python -m unittest discover -s python/tests -p test_weyl_scaffold.py -v
```

The retained `receipts/b5_revision/showcase.json` contains two complete searches of 7⁵=16,807 labeled candidates. One independently probes five axes and uniquely recovers the planted vector at exact zero error. The other uses two varying columns and three constant columns and also recovers it uniquely in the finite alphabet. These are deliberately synthetic fixtures, not measured flavor evidence or physical RG evolution.

A counterexample with basis (1,2), target 1 and alphabet {0,1} keeps the winning labeled vector (1,0); the same-orbit vector (0,1) predicts 2. A tie example retains all three zero-error vectors (−1,1), (0,0), (1,−1). Orbit classification, exact scoring, minimum selection and all-tie recovery now agree without conflating their meanings.

`perfectpower.weyl_scaffold.search` supports nonnegative sample weights, support bounds, rational support and denominator penalties, and per-axis activation penalties. It reports complete coverage only for the supplied finite alphabet and objective, refusing oversized candidate domains before enumeration. Its quadratic symmetry check concerns the polynomial objective only; prior and domain invariance need independent checks. This is exact Python rational computation with executable tests, not a new Lean theorem or certified transcendental logarithm evaluator.

## How this becomes useful flavor physics

A credible next physical campaign freezes mass definitions, uncertainties, correlations, scheme, scale, threshold matching and the exponent prior before searching. Same-scheme, same-scale pure-QCD quark mass ratios cancel the common mass renormalization; quark/lepton ratios generally need explicit transport. The [PDG quark-mass review](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-quark-masses.pdf) explains the scheme and scale requirements. The [NIST CODATA tables](https://physics.nist.gov/cuu/pdf/JPCRD2022CODATA.pdf) provide documented constant inputs. Those primary references were checked for the scope of these requirements; their numerical tables were not used to manufacture a new fit here.

Rounded numerical logarithms can be supplied as rational decimal strings, but exact optimization of those rounded inputs is not exact certification of real logarithms. Close rankings require propagated input intervals or a certified logarithm enclosure. Correlated ratios cannot be counted as independent measurements; artificial scale samples cannot multiply experimental evidence.

A valid evidence calculation must normalize the finite-model prior and sum likelihoods, not call a penalized best score a Bayes factor. A null campaign must repeat the entire fixed search and any tuning inside its calibration. Holdout mass ratios need a shared rule predicting their exponents: independently fitting a fresh exponent vector to each held-out target is another fit, not prediction. The old claims of decisive evidence, a uniquely forced rank five, and physical Weyl degeneracy are therefore left unestablished rather than carried forward as results.

## Assessment

The upgrade is a reproducible mathematical scaffold with explicit physical responsibilities. PerfectPower's strength here is complete finite candidate handling, arithmetic structure and recovery of all admissible outcomes. It cannot turn approximate experimental mass ratios into exact polynomial power identities or create a physical mechanism from the size of a search group. The revised machinery gives the original idea a much firmer route to falsifiable testing and makes its useful combinatorics available without the original inference errors.

The subsequent [real-data prediction monograph](B5_FLAVOR_PREDICTION.md) implements a shared CKM coefficient, ingests pinned physical reviews, evaluates the full lattice, and supplies actual withheld-observable predictions and comparisons.
