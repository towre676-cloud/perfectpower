# Scalar-ray completeness, weighted offsets and spectral traces in Lean

This continuation closes three formalization gaps recorded in the pushed prediction-mechanism study. The scalar-ray list is now a complete classification over the reals; weighted block addresses have exact prefix-sum ranks; and mixed matrix-power traces are proved to equal spectral mixing moments when the spectral frames are supplied. All statements are Lean theorems, rather than imported numerical or computer-algebra assertions.

The focused audit compiles seven modules and checks the axioms of 56 public theorems, including 20 new declarations. It permits only `propext`, `Classical.choice` and `Quot.sound`. It records the source hashes and compiler version in `receipts/m22_interactions/prediction-mechanisms-lean.json`. This is a focused build, not a whole-repository build.

## A complete real scalar census

`PerfectPower/FlavorRGCensus.lean` imports the literal four-equation `FlavorRG.ScalarRay` predicate already pushed. `scalar_ray_iff` proves that every real solution is either zero or one of the following five tuples `(a,c,d,h)`:

| a | c | d | h |
|---|---|---|---|
| 1/128 | 0 | 0 | 0 |
| 1/144 | −1/144 | 0 | 0 |
| 1/192 | 1/96 | 0 | 0 |
| 1/256 | 5/512 | 3/160 | 1/64 |
| 1/576 | 7/1152 | 1/40 | 1/48 |

`scalar_ray_nonzero_iff` gives the exact five-ray equivalence with the zero tuple excluded. It makes no positivity or rationality assumption on the unknown coefficients. In particular, the theorem excludes undiscovered irrational real solutions of this restriction.

Subtracting 6/5 times the fourth beta equation from the third gives

\[
(5d-6h)(480a+480c+10d-192h-15)=0.
\]

The second factor cannot vanish at a real solution. Substitute its affine expression for `d` into the first, second and fourth equations. Their residuals, with coefficients `1`, `2/7` and `9/50`, sum to three squares with strictly positive rational weights plus the strictly positive constant `15920948593/2819101438720`. The complete identity is checked by `linear_combination`; positivity supplies the contradiction. Thus `scalar_ray_alignment` proves `d=6h/5` for every real solution, upgrading the earlier two literal force-cancellation checks to a universal theorem.

When `h=0`, two small factorizations give zero and the three rays with vanishing trace channel. Otherwise the fourth equation gives `h=(1−32(a+c))/36`. Write `s=a+c`. An exact elimination identity gives

\[
(128s-1)(512s-7)(40960s^2-640s+7)=0.
\]

The last factor equals `40960(s−1/128)²+9/2`, so it is strictly positive. Back-substitution gives the two remaining rays. This proof uses no Groebner-basis membership premise, root-isolation result or external CAS axiom. The larger seven-dimensional finite-channel discovery remains a search rather than a complete census. The theorem classifies the declared beta polynomial; it does not formally derive that polynomial from Feynman diagrams.

## Weighted block addresses

`PerfectPower/WeightedBlockAddresses.lean` models a concatenation of block sizes `[n₀,…,nₖ]` as a recursive sum of `Fin nᵢ`. Its executable equivalence with `Fin(sum nᵢ)` provides rank/select inverses, injectivity, surjectivity and cardinality.

`block_rank_offset` proves the literal indexing law

\[
\operatorname{rank}(a)=\sum_{i<\operatorname{blockIndex}(a)}n_i+
\operatorname{blockLocal}(a).
\]

The index is within the block list, the local rank is strictly below the selected block's size, and `block_rank_interval` places the rank in that block's exact half-open interval. Consequently zero-size blocks are skipped. The empty list has no addresses. The examples include `[0,2,0,5]`, where rank 6 selects block 3 and local rank 4. `block_source_rank_iff` proves that supplied source semantics remain complete after this indexing.

This closes the typed weighted-offset core. Parsing arbitrary JSON, identifying the typed blocks with a particular Python execution, normalized CRT traversal and chart semantics remain separate obligations.

## Trace-to-moment transport

`PerfectPower/SpectralTrace.lean` proves the finite-dimensional trace identity over any commutative star ring:

\[
\operatorname{tr}(D_a W D_b W^\dagger)
=\sum_{i,j}a_i b_j W_{ij}\overline{W_{ij}}.
\]

`spectral_frame_trace` derives the mixing frame `W=U†V` for two supplied frames. `spectral_frame_power` proves conjugation transport through every natural power, including power zero, using both inverse identities explicitly. `diagonalized_power_trace` then proves

\[
\operatorname{tr}(A^pB^q)
=\sum_{i,j}a_i^p b_j^q W_{ij}\overline{W_{ij}}
\]

from the hypotheses `A=U D_a U†`, `B=V D_b V†` and the two-sided unitary identities for each frame. In complex matrices the entrywise weights are the squared mixing magnitudes. This is the missing algebraic connection to the already-proved Vandermonde recovery theorem; it does not assert existence of a particular physical diagonalization or identify fitted model inputs with measured CKM entries.

## Reproduction and scope

With the pinned Lean 4.20.0 toolchain and Mathlib dependency/cache, run `make prediction-mechanisms-lean`. The script compiles `FactorAddresses`, `FlavorRG`, `SpectralMoments`, `WeilOldLevel`, `FlavorRGCensus`, `WeightedBlockAddresses` and `SpectralTrace`, then evaluates the audit and verifies every expected theorem's axiom list. The existing seven flavor-RG Python regressions also pass.

The latest Mordell completion bridge remains separate: it proves composition from genuine global prime support and bounded enumeration from a proved coordinate bound. The 457 curve-specific global proof inputs are still open. Efficient Sturm checking, Matveev premises, literal Fourier/chirp intertwining, all-level orbit bounds and the concrete Brainpool field instantiation are also not closed by this continuation. No observed CKM parameters or fine-structure constant are predicted by these formal results.
