# Completing the Mordell frontier

October 8, 2026. This continuation starts from commit 7a99f461b0268b7bdc4b10f63a8c4dac269ec196, where all 457 residual Mordell rank intervals already had matching exact point witnesses. It closes the computational saturation, complete-basis and integral-list obligations for these curves. It does not add a Lean global completeness theorem.

## Results

All 457 curves completed full automatic saturation and integral enumeration. There are 443 rank-one curves and 14 rank-two curves. Every original witness subgroup has index one in the resulting complete basis, and native good-reduction certificates prove trivial rational torsion on every curve. No enlargement was necessary. The integral lists contain 270 signed points on 134 curves; 323 curves have no integral points. No historical integral list changed. All 457 lists agree exactly with the independent complete census of Michael A. Bennett and Amir Ghadermarzi.

The frontier overlay now has zero remaining computational list obligations, 457 external-computation list closures and zero constructive rank-witness gaps. The historical 457-row witness frontier is retained separately. Existing Lean closures and the historical census are preserved rather than relabelled as new formal results.

## From witnesses to complete bases

Each isolated worker transports the retained rational witnesses to a minimal model and processes them in eclib without preliminary saturation. It then calls mwrank_MordellWeil.saturate(max_prime=-1, min_prime=2). The negative cutoff selects eclib's automatically computed global saturation index bound and its required primes, including the primes selected from the curve's reduction data. This is not an arbitrary finite cutoff.

The worker requires the explicit successful saturation status and an empty list of unsaturated primes. Sage's higher-level saturation wrapper does not propagate the failure status in its return tuple; the runner therefore uses the lower-level interface. A failed result, timeout or incomplete run never closes a curve. The returned basis rank must equal the retained external upper bound and independently verified native lower bound.

Canonical heights at 192-bit precision propose the integer relations between original witnesses and the returned basis. Every relation is then checked by exact rational group arithmetic twice, in Sage and in the native arithmetic engine. The gcd of the full-rank relation minors verifies the subgroup index, including redundant source generators. At k=-9257 the three original points have relation rows (1,0), (0,1), (3,-1); the subgroup index is one. Approximate heights only find coefficients and never establish an equality.

## Independent prime saturation checks

The native finite-reduction sieve checks 788 required prime-saturation cases across all 457 bases. For each prime ell, it enumerates normalized nonzero coefficient lines modulo ell. At good auxiliary primes q, it counts the full finite group, computes the exact image ell E(F_q), and removes coefficient lines whose reduced point is outside that image. If every line is excluded, no nonzero basis combination modulo ell is divisible by ell over the rationals. Full rank and the trivial-torsion certificate turn this into an ell-saturation check.

All 788 cases terminate with no surviving line. The largest auxiliary prime is 197, and the largest external automatically computed saturation index bound is 14. This local arithmetic sieve is exact and replayable without Sage. It does not independently prove the global height bound identifying all primes that must be checked. That bound remains an eclib result.

## Complete integral enumeration

Sage integral_points receives the globally saturated basis explicitly and returns both ordinate signs. Its elliptic-logarithm and LLL stage supplies the global enumeration bound. The runner replaces a historical PARI interval-search crash path with an exhaustive integer scan of exactly the same finite interval. It refuses intervals beyond its work budget instead of truncating them. Every output coordinate is checked on the original equation, and both signs, duplicate freedom and the abscissa list are verified natively.

Verbose logs and interval scans are retained per curve. The published cross-check downloads the two Bennett–Ghadermarzi tables automatically unless supplied paths are requested, verifies pinned SHA-256 hashes, parses the complete range covering |k| at most 10000, checks each displayed coordinate equation and compares both signs. The checked numerical excerpt and provenance are stored; the source PDFs are not redistributed in the repository.

## Reproduction and acceptance

Install the pinned passage packages with python -m pip install --only-binary=:all: passagemath-schemes==10.8.12 passagemath-eclib==10.8.12 passagemath-symbolics==10.8.12. The environment receipt records versions, source hashes and the installation command. Run PYTHONPATH=python python python/develop_mordell_completion.py --workers 4, then python/develop_mordell_saturation_reductions.py and python/develop_mordell_integral_crosscheck.py with the same PYTHONPATH. Finally run python/reconcile_mordell_frontier.py. A refresh of worker receipts must be followed by the saturation-reduction enrichment before reconciliation.

The native acceptance function checks the unbounded saturation contract, exact source relations and index, independence, torsion and integral-point arithmetic, and replays every retained required-prime exclusion. The reconciler also checks the source receipt hash and rank match, binds saturation metadata to the SHA-256 of the backend log, and requires prime checks for every prime up to the retained global index bound. Regression tests reject changed relations, coordinates, finite-field group orders, failed saturation, finite cutoffs and unsupported Lean claims. The completion tests replay all 457 packets; the focused Mordell and quartic suites cover the surrounding machinery.

## What remains

This is a complete computational closure of the former 457-curve frontier. The difficult remaining formal work is now explicit: prove or import the global saturation index bound, justify the external rank upper bounds, and prove the completeness of the elliptic-logarithm/LLL integral enumeration inside the chosen formal trust boundary. The reusable native finite-field saturation sieve supplies exact local evidence for that future work. No claim about all arbitrary Mordell curves or all perfect-power equations follows from this finite release.

Official backend documentation: https://doc.sagemath.org/html/en/reference/libs/sage/libs/eclib/interface.html and https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/ell_rational_field.html. Independent census: https://www.math.ubc.ca/~bennett/BeGh-data.html.
