# Integral sparse native ISA and presentation-stable task schedules — v0.21

## 1. Why v0.21 changes the arithmetic question

V0.20 solved task-adapted section synthesis for the synchronized Wilson fiber product, but its primitive native generators `g,h` had an important historical defect: they were chosen as uniform elements of the good-prime algebra `F_1000003^486`.  Their residues were excellent generic generators, but they had no canonical characteristic-zero lift.  It was therefore not meaningful to optimize rational coefficient height of `g/h` word programs as though those residues were distinguished integers.

V0.21 removes that ambiguity.  We replace the historical random field pair by an explicit deterministic integral pair

`G,H in {-1,0,1}^486`

inside the exact five-arrow characteristic-zero native algebra.  The pair has coefficient height one, only 209 nonzero native coordinates in total, and yet reproduces the maximal filtered growth of the historical pair through native closure and synchronized Chinese-remainder separation.

The resulting statement is stronger than a lift of one modular computation.  It gives the five-arrow compiler an honest integral instruction set whose word depth, sparsity and right-multiplication cost can be compared without choosing arbitrary representatives of field residues.

## 2. The explicit height-one pair

The pair is generated deterministically by NumPy PCG64 seed `1` with alphabet `{-1,0,1}` and zero probability `0.7785`, then frozen explicitly in `integral_native_isa_v21.npz`.  Its block support is:

- `G`: 101 nonzero coordinates: 38 in `M_15`, 7 in `M_5`, 3 in the two plus arrows and 53 in the three minus arrows; its scalar vertex coordinate is zero.
- `H`: 108 nonzero coordinates: scalar coordinate one, 44 in `M_15`, 3 in `M_5`, 2 in the plus arrows and 58 in the minus arrows.

Thus the two 486-coordinate generators contain only 209 nonzero coordinates out of 972 possible, or 21.50 percent occupancy.  Their maximum absolute coefficient is exactly one.

This 209-coordinate witness is not claimed to be a global minimum over all integral generator pairs.  Along the frozen seed-one one-parameter sparsification path it is locally sharp: increasing the zero probability to `0.779` gives 208 nonzeros but drops the degree-eight native rank from 486 to 482.  The release therefore labels 209 as a certified sparse witness and a local boundary in that deterministic family, not as an absolute sparsity optimum.

## 3. Maximal native and synchronized filtration survives

Pair `G,H` with the same Wilson Hecke generators used since v0.19,

`X=A_49`,

`Y=-A_12-A_48-A_59+A_95+A_116+A_125`.

Evaluate every binary word in the common free language.  Modulo the certified good prime `p=1000003`, the ranks through degree nine are

| degree | formal words | native rank | Hecke rank | paired rank |
|---:|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 | 1 |
| 1 | 3 | 3 | 3 | 3 |
| 2 | 7 | 7 | 7 | 7 |
| 3 | 15 | 15 | 15 | 15 |
| 4 | 31 | 31 | 30 | 31 |
| 5 | 63 | 63 | 59 | 63 |
| 6 | 127 | 127 | 113 | 127 |
| 7 | 255 | 255 | 152 | 255 |
| 8 | 511 | 486 | 152 | 511 |
| 9 | 1023 | 486 | 152 | 638 |

The native degree-eight rank is the full ambient dimension 486.  The synchronized degree-eight rank equals the complete formal word count 511, so there is no common relation through degree eight.  At degree nine the paired rank is `638=486+152`, so the common language is the full direct product.

Because the native structure constants, `G,H`, and the Hecke orbital structure constants are integral, every displayed full-rank good-prime minor is a nonzero integer minor.  Hence these lower bounds hold over `Q`; the ambient dimensions give equality.  The characteristic-zero conclusions are therefore:

`A_native = Q<G,H>` by degree eight,

and

`A_native x H_Wilson = Q<(G,X),(H,Y)>` by degree nine.

The old optimal depth bounds survive an integral height-one presentation.

## 4. The quartic separator is an exact characteristic-zero unit

The first Hecke relation remains

`q(t)=t^4-26t^3-131t^2+300t+900`.

As before, `q(X)=0`.  On the new native generator, however, `q(G)` is a unit.  V0.21 upgrades the old good-prime unit witness to an explicit characteristic-zero certificate.  In the native block decomposition its scalar coordinate is `900`, its `15x15` vertex determinant is

`266092742509031435590420279021907538485760000`,

and its `5x5` vertex determinant is

`1010100119040000`.

Both are nonzero integers.  The release also freezes the complete two-sided rational inverse of `q(G)`: after clearing denominators, all 486 inverse coordinates share denominator

`59087919283075457878432420806675435295027200`,

of bit length 146, and the largest numerator has bit length 136.  Exact symbolic multiplication verifies both `q(G) q(G)^(-1)=1` and `q(G)^(-1) q(G)=1`.

Thus the Chinese-remainder separation is not an accident of the old random field presentation.  A generator-preserving common quotient would still have to send a native unit to zero.

## 5. Cost-aware execution: generator count is not the hardware objective

EQ-LAB v0.10 independently formalizes the distinction between algebraically minimal instruction count and hardware-aware sparse-message cost.  The same distinction is decisive here.

For right multiplication by a fixed native element, exploit sparsity in the right factor.  In the frozen scalar MAC proxy:

- an `M_15` nonzero costs 15 scalar MACs;
- an `M_5` nonzero contributes 52 MACs across the semisimple, plus and minus right actions;
- a plus-arrow nonzero contributes one scalar operation;
- a minus-arrow nonzero contributes 15 MACs;
- a nonzero scalar vertex contributes one.

The historical `g,h` are completely dense.  Each contains all 486 nonzero coordinates and costs exactly 8,061 MACs per generic right multiplication, agreeing with the v0.17 dense `(2,3)` product model.

The new integral pair costs only

`cost(G)=1732`, `cost(H)=1689`.

Relative to 8,061 this is a reduction of 78.51 percent for `G` and 79.05 percent for `H`, or about 4.65x and 4.77x respectively.  The average primitive-extension proxy drops by about 4.71x while the filtered algebraic depth remains unchanged.

This is the central compiler result of v0.21: a sparse integral ISA is simultaneously arithmetically canonical enough to discuss height and materially cheaper under a replayable native execution model, without paying a depth penalty.

The proxy is deliberately not presented as measured silicon time.  It counts scalar arithmetic induced by the exact block formulas when the right primitive is sparse.  Cache locality, vector width, memory traffic and fused kernels are downstream hardware questions.

## 6. The degree-eight cooperative lock survives a genuinely different presentation

Recompute the degree-eight fiber product from scratch using `G,H`, rather than transporting the old coordinates by a chosen algebra automorphism.  The dimensions remain

- synchronized image: 511;
- pure-native image: 359;
- pure-Hecke image: 25;
- coupling quotient: 127.

So the exact short sequence dimensions of v0.19 survive unchanged.

The coordinate realization of the 127-dimensional quotient is not frozen as a claimed canonical integral lattice.  It is recomputed over the same certified good prime.  What is significant is that the task optima survive even though the primitive native presentation has changed substantially.

For the current degree-eight Hecke tasks, the minimum faithful native masks remain:

| task | task dimension | optimal degree-eight native stratum | native dimension |
|---|---:|---:|---:|
| Paley line | 1 | `(0,2)` | 150 |
| `C_3` line | 1 | `(0,2)` | 150 |
| seven-route bank | 7 | `(0,2)` | 150 |
| identity + seven routes | 8 | `(0,2)` | 150 |
| current EQ application span | 9 | `(0,2)` | 150 |
| full Hecke teacher | 152 | `(1,2)` | 155 |

The full teacher still has signature rank 127 and needs 25 kernel dimensions; the mixed `(1,2)` code has signature kernel 28.  The small named application spaces retain injective coupling signatures and still require two minus channels at degree eight.

Therefore the v0.20 schedule table was not an artifact of the historical random native generators.  It is stable under at least one radically sparser integral presentation that keeps the same filtered closure depths.

## 7. What EQ-LAB v0.10 adds to the interpretation

WILSON-EQ-LAB v0.10 is imported byte-for-byte.  Its exact application-side advances are complementary to the Forge compiler:

1. It introduces cost-aware finite-action ISA search and exhibits a 231-state example in which a two-route ISA costs 110 routed neighbor reads per node while the algebraically minimum one-route ISA costs 480.
2. It adapts the stochastic Witt list ranker to deployment-prior shift using unlabelled list evidence.
3. It makes Formation projective features conditional: cheap marginals are used until an exact blindness certificate forces escalation to the projective carrier.
4. It removes a redundant rational Fano terminal program by reconstructing Paley from the recovered primitive route outputs.

The first and third points directly sharpen how v0.21 should be read.  Primitive count is not enough; execution cost matters.  Likewise, a cheap representation should be retained until a certified task quotient says it has discarded decisive information.

Forge does not import EQ-LAB's application metrics as proofs about the native 486-dimensional algebra.  It imports the archive as an application handoff and uses the same compiler discipline.

## 8. What Formation v35 contributes

Formation Polarization v35 is also imported byte-for-byte.  Its new group-theoretic theorem gives an exact accessibility dichotomy for copy-minimal cyclic `p`-primary packets on section-separated palettes.  After local minimization, proper-factor rank one disappears.  A multi-species packet is formation-critical exactly when its global atom has full support and its cancellation-tether rank is at most one; every other packet has exact proper-factor generation number two.  The independent regression checks 1,758 packets with zero mismatches.

The relevance to Forge is structural rather than functorial.  V35 provides another exact example in which a small local summary is sufficient only after the correct support/tether state has been retained.  It reinforces the v0.20/v0.21 design rule: use cheap marginals when certified sufficient, but preserve the joint state whenever a theorem says decomposition loses essential coupling information.

No identification between Formation tethers and Wilson arrow channels is asserted.

## 9. Evidence boundary and the next arithmetic compiler

V0.21 closes the ill-posed part of the previous frontier.  The native primitive ISA now has an honest integral height-one realization, and its exact depth and application schedules are certified.

What is still open is subtler: low-height **word-section synthesis** in this integral ISA.  EQ-LAB v0.8-v0.10 already supplies height-one native coordinate sections after degree-nine decoupling.  To execute those sections through the common `G/H` word language, however, one must solve a rational/integer basis problem in the filtered synchronized algebra.  A naive `638x638` inverse is neither computationally attractive nor likely height-optimal.

The correct next problem is therefore to choose a degree-nine synchronized word basis and section simultaneously, minimizing a multi-objective arithmetic/backend cost such as

`(max coefficient height, nonzero word count, shared-prefix DAG cost, native primitive cost, word depth)`

subject to exact Hecke target preservation and, when required, exact native faithfulness.

The new height-one sparse ISA makes that objective mathematically meaningful.  V0.20 could formulate the section problem; v0.21 supplies an integral execution language in which arithmetic height is no longer an artifact of arbitrary finite-field lifts.
