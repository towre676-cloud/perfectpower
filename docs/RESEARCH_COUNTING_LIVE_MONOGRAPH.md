# Exact research populations and live Explorer data

The `research-count` command adds three finite applications motivated by
[arXiv:2605.22763](https://arxiv.org/abs/2605.22763). This implementation does not
claim to reproduce the paper's Lean proofs or settle additional infinite conjectures.

## Monomial populations

For a nonnegative exponent vector `g`, let `D(g)={u in N^n: u_i<=g_i}`. We count
distinct vectors in a union of these boxes, optionally at a fixed total degree.
Duplicate and dominated generators are removed. The intersection of any subset
of boxes is their coordinatewise minimum box; inclusion-exclusion combines
identical intersections. Without a degree constraint a box contains
`product(g_i+1)` vectors. At degree `d`, stars-and-bars gives

$$h_g(d)=\sum_{J\subseteq\{1,\ldots,n\}}(-1)^{|J|}
\binom{d-\sum_{j\in J}(g_j+1)+n-1}{n-1},$$

with a zero term for negative remaining degree. Lexicographic rank/select
restricts successive prefixes and uses this same formula. Binary search selects
the first coordinate whose cumulative population exceeds the remaining rank.
Huge finite populations therefore need not be enumerated. Histograms have a
separate explicit work budget; exhausting a query budget returns no partial
exact answer. Python arbitrary-size integers and browser BigInt preserve counts.

Zanello's solved case has three variables and two maximal monomials of equal
degree. Its sequence obeys `h(d)^2 >= h(d-1)h(d+1)`. We compute finite histograms
and exact slacks, without asserting this property for arbitrary CNF counts or
arbitrary box unions. The broader nonmonomial level-algebra case remains outside
this result. See [Zanello](https://arxiv.org/abs/2210.09447) and the
[pure O-sequence monograph](https://arxiv.org/abs/1003.3825).

## CRT and restricted digits

A CRT population is an inclusive interval with finite allowed residues. Classes
`a mod m` and `b mod n` intersect precisely when `gcd(m,n)` divides `b-a`; a
consistent pair becomes one class modulo `lcm(m,n)`. Thus noncoprime moduli and
inconsistent constraints are explicit. Normalized final classes are disjoint,
and each contributes

$$\left\lfloor\frac{hi-a}{M}\right\rfloor-
\left\lfloor\frac{lo-1-a}{M}\right\rfloor.$$

This also handles negative intervals. Cumulative counts provide rank/select by
binary search. Empty allowed sets yield no integers; no constraints yield the
whole interval. This is reusable finite machinery for CRT block constructions
such as Erdős #12, without deriving an infinite density theorem from bounded
counts. [Elsholtz–Planitzer](https://arxiv.org/abs/1609.07935) gives the background.

The restricted-digit adapter forms fixed-length expansions in supplied bases.
On `[0,stop)` it reports distinct sums, representation counts and collision
excess separately, with an exact rational finite density. This is not a claim
about natural, lower or upper asymptotic density. The paper's Erdős #125 proof
uses synchronized powers of 3 and 4 and inductive thinning; a finite sumset
receipt alone cannot establish that conclusion.

## Live data and release contract

`python scripts/export_explorer_live.py` recomputes the example receipts and
`data/explorer_live.json`. The feed binds its payload to SHA-256, records input
digests, and preserves decimal integer answers. Its `input_json` retains literal
large integers for editors; JavaScript must not round them through ordinary
floating-point JSON conversion. `source_parent` is the commit checked out when
generation ran, not the containing feed commit. The content digest identifies
the actual displayed research results.

The download Site reads the current public-main feed and verifies its digest,
falling back to its bundled copy. Desktop and Android use `/api/research` and
retain a valid cached feed in their state directories. Offline operation uses
that cache or the bundled copy. Invalid data is rejected. Open research views
refresh every five minutes and have an explicit Refresh action. Saved runs and
executable files are never overwritten by data refresh.

The installed engine commit is displayed separately from the live data digest.
Executable changes require a new package. Android 1.1 adds live data and these
workbenches; Android 1.0 must first install this update. The CI workflow refreshes
data after relevant source/input changes and supports manual dispatch. Publishing
uses fast-forward Git semantics and rebases over concurrent commits; a conflict
fails rather than discarding another session's work. Future research additions
should extend the deterministic exporter and its model/receipt contract.

The mobile bundle builder accepts `--root`, `--ref`, `--ui` and `--output`. It
reads every original file from the selected Git commit, verifies all original
bytes in the generated archive, and derives counts and identities from that
snapshot. It no longer depends on a deleted desktop archive, an absolute recovery
path, a fixed 7,501-file count or the old `a150215` commit. ZIP timestamps are
fixed. Generated mobile UI and Android native overlays accompany the snapshot.

## Evidence and boundaries

Differential tests compare finite monomial counts, histograms and every rank/select
result with direct enumeration. CRT tests compare counts and every rank/select
result against filtering over negative and positive intervals. A huge-degree
case checks the binomial formula without population expansion. Tests also cover
all pairs of three-variable monomials of degree five, representation collisions,
work-limit rejection, feed tampering, cache fallback and refresh caching.

The earlier 200-instance comparison completed 800 outcomes and reported 18 exact
0.10.2 counts versus 12 in the paired 0.10.1 run, 18 for Ganak and 19 for D4.
These aggregate results were recovered after the interrupted publication and
loss of the local raw package. They remain historical aggregate evidence, not
newly replayable measurements in this release. The live feed states this
distinction. A reconstructed raw package must precede a public reproduction claim.

Further leads are [Short proofs II](https://arxiv.org/abs/2604.06609) and
[Pollack's bounds](https://arxiv.org/abs/1508.05035), for quadratic residues, CRT
and Möbius inversion. Their finiteness conclusion has an ineffective bound and
does not provide a certified search cutoff. [Anchored GDA](https://arxiv.org/abs/2604.03782)
provides discrete recurrence and schedule-search techniques for squared gradient
norms in smooth convex-concave optimization. It has not been implemented or
benchmarked as a CNF-counter optimization here. The
[released Lean sources](https://github.com/google-deepmind/alphaproof-nexus-results/tree/main/APNOutputs)
retain the original theorem scopes; recompiling them remains separate work.
