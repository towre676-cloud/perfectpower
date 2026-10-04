# Deeper monograph machinery made reusable

This release develops four mechanisms that were present in the monographs but were isolated, conservative or expensive to use: exact Sturm roots, effective power gaps with exceptional fibres, determinant-weighted graph bases, and generated operator algebras. It joins them to the arithmetic compiler and graph interfaces. It also improves the previous release's coordinate normalization. These are adaptations of existing and classical machinery, with new exact implementations and checks, rather than claims of new mathematical theorems.

## Excavation and selection

The deeper reading included the native Runge and higher-power monographs, the Lean-backlog cutoff analysis, effective quartics, positive geometry's support-rank and basis-polynomial sections, operator and sequence recovery, covering/lattice arithmetic, the literature routes, and the older `expert_push` and formula-transport companions. Historical retrieval also identified Morphonic's rational-polynomial/Sturm work. The exact original Morphonic experiments are not needed or claimed as reproduced. The source review and hashes are in `receipts/monograph_development/source_review.json`.

The full text of the 3.8 MB `level_deformation_monograph_v4_20_0.html`, *The Level and the Deformation*, was also scanned: 14,110 text lines and 403 headings. The selected DAO operator-switch section is retained with the heading inventory in `giant_monograph_index.json`. This is a complete text scan and selected-section development, not a claim to have independently proved every chapter. Its generated-algebra/commutant distinction directly supplies the fourth new component.

Three connections proved particularly productive. Root isolation already existed in `polyalg.py`, but the divisor solver instead trial-divided polynomial constants. The monographs retained residual-zero fibres, but the previous integrated Python solver enlarged its bound until those roots were forced inside the interval. Positive geometry computed edge marginals by enumerating every basis; its determinant identities also allow those questions to be answered directly by an inverse matrix.

The general Baker, Mordell height, unit-generation and norm-representative obligations stay explicit. A rank-two modular survivor table does not supply an exponent bound. Numerical geometric periods do not enter the new integer-completeness certificates. The prior unsuccessful industrial portfolio remains opt-in. These boundaries help select mechanisms with executable exact contracts.

## Certified integer roots instead of factoring a huge constant

The new `sturm_fibres.py` adapts the existing exact rational polynomial core. For nonzero `F∈Z[x]`, it constructs a squarefree factorization

\[
F=c\prod_j S_j^j,\qquad S=\prod_j S_j,
\]

and a Sturm chain for S. Coefficients are primitive integer multiples with their signs preserved. A Cauchy bound contains every root. Subdivision uses integer endpoint intervals `(a,b]`; the variation difference counts distinct real roots there. Zero-count intervals are discarded. At width one, exact evaluation of the sole candidate integer b decides whether it is a root. A root at a belongs to the preceding interval, so endpoint roots are neither lost nor double-counted. Repeated roots are returned once.

The certificate contains the factorization, chain, bound and complete subdivision transcript. `verify_roots` checks the factorization identity, the product S, every signed remainder and a final nonzero constant in the chain. That final constant proves S is squarefree. It then checks every node and required child interval, and tests every surviving singleton. It does not rediscover a gcd or repeat root isolation. Missing branches, altered root counts, false factors and bad endpoints are rejected. A node limit raises without returning a partial root list. Rational coefficients in the certificate are strings, so JSON serialization is exact without a custom decoder.

For `y²=P(x)²+k`, k nonzero, factor pairs give

\[
u=y-P(x),\quad v=y+P(x),\quad uv=k,
\qquad P(x)=(v-u)/2,\quad y=(u+v)/2.
\]

Only pairs with the required parity are retained. Each polynomial value fibre is solved once using its Sturm certificate. `verify_square_fibres` checks the complete parameter cover and every fibre. The work counter counts factor trials plus subdivision nodes, not every rational arithmetic operation. Trial division of k still has an explicit budget; this is not an arbitrary fast factoring algorithm. The compiler uses a centered-cost check to preserve cheap existing integer translations, prefers Sturm when the centered polynomial constant is enormous, and falls back to it when the old fibre budget fails. Existing public divisor APIs retain their earlier behavior.

For the constructed polynomial

\[
P(x)=(x-1)(x-10^{100}),\qquad y^2=P(x)^2+1,
\]

the complete answer is `(1,±1)` and `(10¹⁰⁰,±1)`. The new route uses 1,330 factor-trial/subdivision work units and also enters the main compiler. This polynomial has widely separated roots; translating to their mean cannot make its constant small. A second example checks a triple root at `10¹⁰⁰`, a noninteger real root at `−1/2`, and a factor with no real roots. The complete integer-root list contains only `10¹⁰⁰`.

## Sharp power gaps with a separate exceptional branch

For a rigid input, the existing truncation produces

\[
F=Q^d+R,\qquad Q=P/D\in\mathbb Q[x],\quad D>0,
\qquad r=\deg R<(d-1)q,\quad q=\deg Q.
\]

The new `sharp_power_gap.py` uses the actual Horner tail sums, rather than replacing every lower monomial by the largest possible contribution. At an integer threshold B, define

\[
A(B)=|Q_q|-\sum_{i<q}|Q_i|B^{i-q}.
\]

It checks A(B)>0 and

\[
D\sum_i |R_i|B^{i-(d-1)q}<A(B)^{d-1}.
\]

For odd d, it additionally checks `Σ|R_i|B^(i-dq)<A(B)^d`, forcing the root to have Q's sign. A(B) increases with B while the residual ratios decrease, so doubling followed by exact binary search finds the smallest admissible positive integer B for these inequalities. The same estimates hold for both signs of x because they use `|x|`.

If `|x|≥B` and R(x) is nonzero, a hypothetical integer d-th root z on Q's sign branch would satisfy

\[
|Dz-P(x)|\le D|R(x)|/|Q(x)|^{d-1}<1.
\]

The integer on the left must be zero, contradicting R(x)≠0. For even d the sign branch uses the matching signed root, retaining both original witnesses. Every solution therefore belongs either to `[-B+1,B-1]` or to the complete integer-root list of R. The latter is certified by the new Sturm interface. These exceptional coordinates are tested in the original equation even when they lie outside the interval. Requiring Q(x) to be an integer or preserving witness-scale divisibility remains necessary after transport.

For `y²=x⁴+x−100`, the short interval has radius 10, but the complete answer is `(100,±10000)`: the residual vanishes at 100. Removing that exceptional branch would produce a false empty answer. For the difficult rational-completion quartic `y²=x⁴+x³+x²+x−199`, the earlier conservative normalization used 25,587 interval positions. The redesigned leaf uses 85 positions and two surviving residue-filter candidates, returning exactly `(7,±51)`.

The arithmetic engine now chooses these leaves. Previous-release integral/rational quartic and root-gap receipts still replay through their original checker paths. The new Horner/exceptional interface has a mathematical derivation and exact Python replay; no new Lean theorem was compiled.

## Better coordinate normalization

The prior affine/power map used the entire denominator least common multiple s as a witness scale. It is enough that each denominator divides `s^d`. If the centering denominator is a and the original degree is N, all centered denominators divide `a^N`, making `s=a^ceil(N/d)` a safe candidate. An exact d-th root of the denominator lcm supplies another candidate. The engine chooses the smallest of these verified candidates and checks the complete coefficient identity afterwards. It does not claim to compute the globally minimal scale by factoring the denominator.

Power compression remains first. When a rational q=1 centering changes no degree, its scaled leaf can be larger than the original equation. A nearest-integer centering is now tried before that map. It is a bijection on integer coordinates and clears no denominators. Both refinements preserve every integer image condition and also improve canonical reuse.

On the same 12,320 stored pullbacks and constructed affine variants, all complete answers still match: 5,255 plain and 1,362 affine point occurrences. Combined sharper bounds and better normalization reduce the summed leaf interval positions from 5,098,757 to 114,485, and surviving root checks from 438,934 to 11,203, approximately 39 times fewer root checks. Totals include repeated queries and exceptional checks; leaf positions count the main intervals. This is reduced search work, not a claim of 39-times-faster wall time. The current run took 16.40 seconds including discovery and the larger certificates' replay, while the preceding release recorded 11.97 seconds in a separate run. Those timings are not a controlled paired speed comparison. The practical gain includes resolving cases that previously exceeded finite-search budgets.

## Graph basis probabilities without listing the bases

Let B be the cyclotomic connection incidence matrix, W nonnegative rational diagonal edge weights, and

\[
L=B^*WB,\qquad Z=\det L.
\]

For full-rank positive-weight support, the existing Cauchy–Binet identity defines a distribution on maximal edge bases I, with weight `|det B_I|²∏_(i∈I)w_i/Z`. The new `connection_measure.py` constructs

\[
T=WB L^{-1}B^*.
\]

The asymmetric form avoids irrational square roots of the weights. It has the same principal minors as the usual Hermitian projection kernel, with zero-weight cases obtained directly by the determinant identity. Its factorization and the inverse identity give `T²=T` and `trace T=n`, where n is the vertex count. Each diagonal entry is an edge marginal. For required set A, its inclusion probability is `det T_A`.

For disjoint required edges A and forbidden edges C, concatenate their indices and subtract one from the C diagonal entries. The joint probability is

\[
(-1)^{|C|}\det\begin{pmatrix}
T_{AA}&T_{AC}\\ T_{CA}&T_{CC}-I
\end{pmatrix}.
\]

This follows by expanding the C diagonal corrections, equivalently inclusion–exclusion on the principal minors. Conditional marginals are ratios of the corresponding joint events. A zero-probability conditioning event is rejected. When the positive support is rank deficient, the basis distribution is undefined and the receipt contains no probabilities. It is never replaced by a vector of zero importance.

All arithmetic stays in `Q[z]/Φ_d(z)`, with the existing exact conjugation. Event probabilities can be real algebraic values, not only rational numbers. A receipt supplies L's inverse and T; `verify_measure` checks the inverse and factorization without discovering an inverse or enumerating bases. `from_receipt` reuses that checked inverse for subsequent events. `verify_conditioning` independently replays the requested conditional marginals. Matrix-shape and event determinant budgets remain explicit; these are not universal rational-bit-complexity guarantees.

The runner processes all 196 actual connection packets from the positive-geometry release. It matches every stored determinant and marginal, checks 989 stored basis terms, and validates 4,528 mixed events against their independent stored expansions. Conditioned distributions also replay. A constructed 10-vertex, 40-edge graph has 847,660,528 candidate maximal-minor subsets; the new implementation answers its event and conditional queries with zero basis enumerations. That number counts possible subsets, not proved nonzero bases. This supports reusable exact reliability/importance questions on the supplied graph models; it is not a probability model for integer solutions.

The determinant probability machinery is classical. Primary background is [Lyons, *Determinantal probability measures*](https://arxiv.org/abs/math/0204325). Primary root-isolation background is [Moreno Maza's tutorial](https://www.csd.uwo.ca/~mmorenom/Publications/RS-SAV-Tutorial.pdf); [Eberl's Isabelle Sturm development](https://isa-afp.org/entries/Sturm_Sequences.html) supplies an existing formally verified account, without making our Python implementation formally verified.

## Generated operators, commuting operators, and a concrete gap

Appendix DAO of the large monograph distinguishes three objects: the algebra generated by a context family, its commutant, and its bicommutant. Their dimensions alone do not supply a ring isomorphism or settle every representation-theoretic interpretation. The new `operator_algebra.py` develops that distinction over exact rational matrices, up to dimension six.

For generators `A₁,…,Aₖ`, start with the identity and extend the span by left products `AᵢBⱼ` whenever they are independent. Every retained basis matrix records a word in the generators. At closure, every generator-times-basis product is given by exact coordinates in that basis. These facts prove equality with the unital generated algebra: its recorded matrices are generated words, while the closed span contains every word. A product limit and coefficient-size guards raise rather than return an incomplete closure.

`verify_algebra` checks the words, basis independence and every multiplication coordinate without discovering the closure again. Membership supplies a rational linear combination of basis words. A nonmember supplies a linear functional annihilating the whole algebra but pairing nontrivially with the requested operator. Membership is membership in the algebraic span of words; it is not a claim that a single product realizes the operator or that the coordinates are integral.

The commutant is the complete solution space of all simultaneous commutation equations. The bicommutant applies the same construction to the commutant basis. Their replay checks the equations, independent basis and exact constraint rank. When the generated algebra and bicommutant differ, the profile supplies an actual bicommutant matrix outside the algebra, together with its separating functional. Thus an obstruction is a replayable object, rather than a dimension mismatch alone.

For two off-diagonal matrix units, the dimensions `(generated algebra, commutant, bicommutant)` are `(4,1,4)`. For the upper-triangular algebra they are `(3,1,4)`, and the profile supplies the missing lower-triangular direction and an obstruction functional. For a nonzero square-zero operator they are `(2,2,2)`: bicommutant equality holds even though its generated algebra contains a nonzero square-zero ideal. Consequently the software does not label bicommutant equality as semisimplicity, irreducibility or a Wedderburn decomposition.

All 135 stored reconstructed recurrence operators receive complete algebra profiles and replay. Their companion algebras have dimension equal to the recurrence order. This concerns the supplied models, not proofs of the OEIS definitions. The two actual field-756 unit multiplication matrices generate a three-dimensional algebra with a three-dimensional commutant and bicommutant. The original complex modular-data switch experiments, their universality claims and general ring-level correspondences are not reproduced. The adaptation gives reusable exact algebra and obstruction calculations on our arithmetic data.

## Validation and use

The full Python suite passes 635 tests with four skipped dependency tests. Twenty-seven new tests cover independent integer scans, repeated and enormous roots, half-integer nonroots, signed factor pairs, complete transcript replay, lost exceptional fibres, old certificate compatibility, independent full graph-basis event comparisons, loops, parallel edges, zero weights, rank deficiency, conditioning, large non-enumerated graphs, exact word closure, algebra membership/obstructions, bicommutant gaps, malformed receipts, budgets and all four CLI commands. Validation includes a fresh-copy, standard-library-only run and byte comparisons of eleven deterministic runner receipts. Code hashes and retained logs appear in `validation.json`.

```sh
python python/develop_monographs.py
PYTHONPATH=python python -m unittest discover -s python/tests
PYTHONPATH=python python -m perfectpower integer-roots --coeff '[0,0,2,-3,1]' --verify
PYTHONPATH=python python -m perfectpower square-fibres --coeff '[2,-3,1]' --k 1 --verify
PYTHONPATH=python python -m perfectpower connection-measure --vertices 2 --edges '[[0,1,0],[0,1,2],[0,1,1]]' --power 4 --include '[0]' --exclude '[1]' --verify
PYTHONPATH=python python -m perfectpower operator-algebra --operators '[[[1,0],[0,0]],[[0,1],[0,0]]]' --verify
```

Optional `--benchmark` records timing separately. All new execution receipts retain `execution_verified: false`; this development performed zero new Lean compilations. The previous release's receipts remain unchanged as historical evidence. The new arithmetic run has its own directory and source references. Further useful directions include a formally checked Sturm transport interface, more economical residual-offset branches and rigorous analytic geometry, each with its actual missing hypotheses rather than assumed completeness.

Publication integrates the concurrent [parallel Lean formalization](PARALLEL_LEAN_MONOGRAPH.md), commit `fb20e9fd8dced27829b28a487ad78ef1dada4fd4`. Its recorded compilation covers 177 modules and its axiom ledger covers 12,835 declarations in 577 groups. We replayed that ledger's exact-name coverage and allowed-axiom checks and verified its manifest/log hashes after integration; we did not recompile those Lean modules here. That inherited formalization concerns the earlier algebra and lifting mechanisms. It does not formally verify the new Sturm, Horner-gap, graph-event or operator-algebra Python implementations described here.
