# Complete CRT products of source-bound residue atlases

## The arithmetic bridge

A complete local atlas records every pair of residues on which the original integer polynomial vanishes modulo a prime power. The preceding atlas foundation already includes smooth lifts in both coordinate directions, all singular children, completeness for arbitrary integer coordinates, and exact rectangle populations. This extension composes those complete objects across distinct primes. It preserves the fixed-divisor and scalar-feedback additions already present on the consolidated branch.

Let R_m and R_n be the complete local root tables for the same source F, with positive coprime moduli m and n. Choose integers u and v satisfying um+vn=1. Define the normalized coordinate combination by

$$
C(a,b)=(anv+bmu)\;\mathrm{mod}\;mn.
$$

The Lean module proves that C reduces to a modulo m and b modulo n, lies in the canonical interval, and recovers x modulo mn when applied to the two reductions of x. Apply C independently to the two coordinates. These identities give an injection from the Cartesian product of the local root tables into normalized residue pairs modulo mn. Completeness and divisibility by the product give a bijection onto the complete product root table.

$$
|R_{mn}|=|R_m|\,|R_n|.
$$

The proof uses neither a search over the product-modulus square nor a premise that the source solutions are already known. `roots_card`, `roots_complete`, `product_zero`, `merged_periodic` and `merged_checked` build a new typed `AtlasPacket` from the local packets. Iteration supplies any supported finite collection of distinct prime-power factors. Every original integer zero survives the conjunction, and any empty local table certifies a global modular obstruction.

## Exact populations from local products

For a normalized residue r, the number of integers in the inclusive interval [L,H] with that residue modulo M is the exact signed floor difference

$$
N(M,r;L,H)=\lfloor(H-r)/M\rfloor-\lfloor(L-1-r)/M\rfloor.
$$

For each local root pair z,w, the combined two-coordinate cell contributes the product of its two axis counts. Distinct local tuples give disjoint cells. The general `merged_count` theorem therefore rewrites the population of the merged atlas as a nested sum over the two original root tables. The certificate can evaluate that sum directly rather than first computing a deduplicated image.

These are counts of modular candidates. Exact source scans evaluate F at every surviving candidate and return only literal integer zeros. Completeness applies to the declared rectangle; a finite rectangle supplies no global height theorem.

## Factored storage and exact pruning

The `pp-residue-atlas-product/1` packet keeps every independently replayed local table. Its modulus and combination count are literal products. When the Cartesian product exceeds the explicit representation limit, `roots` is null and the packet remains a complete factored cover. Increasing the root count changes storage representation without removing residue combinations.

The interpreter traverses factor tuples in sorted factor order, with each local root table sorted lexicographically. At each prefix it computes the exact current residue-cell axis counts. If either count is zero, every descendant is empty in the rectangle, so the branch can be discarded there. Empty local tables terminate the entire traversal immediately, even when the empty table is the last factor. Traversal budgets bound work and raise an error before a partial population or scan can be reported.

Selection and rank share one declared ordering: local-factor root tuples first, then x, then y inside the final CRT cell. This ordering is identical for explicit and factored packets; it is distinct from global coordinate sorting. Source scans sort their final literal points. A scan finishes a complete candidate count before enforcing its candidate budget and evaluating the source.

## Worked arithmetic

For F(x,y)=y-x squared, the factors 8, 9 and 25 give modulus 1800 and exactly 1800 combined residue pairs. The packet stores only the three local tables. In the rectangle with both coordinates between minus 10 to the twelfth and plus 10 to the twelfth, the exact modular candidate population is 2222222222216666666667. The generated Lean program proves that integer count through the general nested-sum identity.

The eight prime factors 2, 3, 5, 7, 11, 13, 17 and 19 give 9699690 combined classes for the same parabola, represented by only 77 local roots. In the small rectangle [-10,10] squared, exact prefix pruning leaves seven candidates and source evaluation recovers all seven solutions. This demonstrates useful pruning, rather than a uniform complexity bound for arbitrary huge rectangles.

The six persisted native examples also include the horizontal parabola, the singular cusp, the Mordell source y squared minus x cubed plus 2, a global modular obstruction, and a linear source with different smooth chart directions. The Mordell scan in the declared small box returns (3,5) and (3,-5). The obstruction source y squared minus x squared minus 2 has no integer zeros because its complete factor atlas is empty.

## Proof and execution boundary

`PerfectPower/ResidueAtlasCRT.lean` contains twelve general theorem declarations. The Python service exposes composition, replay, membership, population, rank, selection, complete source scans and native certificate generation. Replay checks every local source table independently, source agreement, factor order, distinct primes, exact cardinality products and the representation fields. Explicit tables additionally undergo canonicality, uniqueness and all local congruence checks.

Generated native programs prove each local atlas, exact Bezout coefficients, coprimality, product cardinalities, arbitrary-integer modular completeness and literal rectangle counts. Supported small scans also prove their complete source solution lists. The focused audit covers 362 declarations, with only the standard Lean axioms or no axioms; neither sorryAx nor Lean.ofReduceBool appears. Python replay continues to report execution_verified=false: individual native theorems do not establish a general source-to-native compiler refinement.

## Bounded next implementation

The highest-value next push is a Lean refinement theorem for the factored traversal itself. Add a typed factor sequence and a prefix-state invariant to `ResidueAtlasCRT.lean` or a dedicated `ResidueAtlasProductInterpreter.lean`. Prove by induction that the unpruned leaves biject with the iterated merged root table, that zero axis count implies every extension contributes zero, and that a successful traversal returns the exact nested population sum. Then define block offsets and prove rank and selection inverse on the declared tuple ordering.

Keep the Python service schema stable and add generated certificates instantiating those general interpreter theorems. Validate empty factors in every position, negative interval endpoints, empty rectangles, explicit/factored equivalence, and budget rejection before any purported complete result. The separate noncoprime intersection extension is now implemented in `RESIDUE_ATLAS_INTERSECTION_FACTORED_MONOGRAPH.md`: shared-prime projection gives compatibility tables and an LCM period, followed by coprime assembly, including different source equations. The generic traversal refinement remains open. Global Mordell bounds, explicit Matveev premises and singular-endpoint period certification retain their independent mathematical obligations.
